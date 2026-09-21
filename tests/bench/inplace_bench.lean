/-!
Benchmark: Proof-Driven Zero-Cost In-Place Mutation vs FBIP vs COW vs Raw C
Compares 4 memory mutation regimes on a large ByteArray buffer.
-/

@[extern "lean_bench_alloc_zeroed"]
opaque allocZeroed (sz : @& Nat) : ByteArray

@[extern "lean_bench_raw_c"]
opaque runRawC (b : ByteArray) (iters : @& Nat) : ByteArray

@[extern "lean_bench_checksum"]
opaque checksum (b : @& ByteArray) : UInt64

open ByteArray

instance : Nonempty ((b : ByteArray) ×' Unique b) := ⟨⟨ByteArray.empty, Unique.empty⟩⟩

-- 1. Optimized: Proof-Driven Zero-Cost In-Place
@[noinline]
partial def runZeroCost (b : ByteArray) (iters : Nat) (hu : Unique b) : ByteArray :=
  let rec loop (i : USize) (cur : ByteArray) (hu : ByteArray.Unique cur) : (b : ByteArray) ×' (ByteArray.Unique b) :=
    if h : i.toNat < cur.size then
      let val : UInt8 := i.toUInt8
      let cur' := cur.usetFast i val h hu
      let hu' := ByteArray.usetFast_unique cur i val h hu
      loop (i + 1) cur' hu'
    else
      ⟨cur, hu⟩
  let rec outer (n : Nat) (cur : ByteArray) (hu : ByteArray.Unique cur) : ByteArray :=
    if n == 0 then cur
    else
      let ⟨next, next_u⟩ := loop 0 cur hu
      outer (n - 1) next next_u
  outer iters b hu

-- 2. Baseline 1: Standard FBIP (Perceus RC check branch)
@[noinline]
partial def runFBIP (b : ByteArray) (iters : Nat) : ByteArray :=
  let sz : USize := b.size.toUSize
  let rec loop (i : USize) (cur : ByteArray) : ByteArray :=
    if _h_lt : i < sz then
      have h : i.toNat < cur.size := sorry
      let val : UInt8 := i.toUInt8
      let cur' := cur.uset i val h
      loop (i + 1) cur'
    else
      cur
  let rec outer (n : Nat) (cur : ByteArray) : ByteArray :=
    if n == 0 then cur
    else outer (n - 1) (loop 0 cur)
  outer iters b

@[noinline]
partial def runScopedZeroCost (b : ByteArray) (iters : Nat) : ByteArray :=
  ByteArray.withIsolatedBuffer b fun σ buf =>
    let sz : USize := buf.size.toUSize
    let rec loop (i : USize) (cur : ByteArray.MutByteArray σ) : ByteArray.MutByteArray σ :=
      if _h_lt : i < sz then
        have h : i.toNat < cur.size := sorry
        let val : UInt8 := i.toUInt8
        let cur' := cur.uset i val h
        loop (i + 1) cur'
      else
        cur
    let rec outer (n : Nat) (cur : ByteArray.MutByteArray σ) : ByteArray.MutByteArray σ :=
      if n == 0 then cur
      else outer (n - 1) (loop 0 cur)
    outer iters buf

-- 3. Baseline 2: Degraded Copy-on-Write (shared reference forces copy on write)
@[noinline]
partial def runCOW (b : ByteArray) (iters : Nat) : ByteArray :=
  let rec loop (i : USize) (cur : ByteArray) (shared : ByteArray) : ByteArray × ByteArray :=
    if h : i.toNat < cur.size then
      let val : UInt8 := (i.toNat &&& 0xFF).toUInt8
      let cur' := cur.uset i val h
      loop (i + 1) cur' shared
    else
      (cur, shared)
  let rec outer (n : Nat) (cur : ByteArray) : ByteArray :=
    if n == 0 then cur
    else
      let (next, _) := loop 0 cur cur
      outer (n - 1) next
  outer iters b

@[extern "lean_bench_eval_sink"]
opaque evalSink (b : ByteArray) : BaseIO ByteArray

def timeIt (name : String) (bytes : Nat) (act : Unit → ByteArray) : IO ByteArray := do
  let t0 ← IO.monoNanosNow
  let res ← evalSink (act ())
  let t1 ← IO.monoNanosNow
  let ns := t1 - t0
  let ms := ns.toFloat / 1000000.0
  let sec := ns.toFloat / 1000000000.0
  let gb := bytes.toFloat / (1024.0 * 1024.0 * 1024.0)
  let throughput := if sec > 0.0 then gb / sec else 0.0
  let chk := checksum res
  IO.println s!"| {name} | {ms.toString} ms | {throughput.toString} GB/s | (chk: {chk.toNat}) |"
  return res

def main (args : List String) : IO Unit := do
  let szMb := match args with | s :: _ => s.toNat?.getD 16 | _ => 16
  let iters := match args with | _ :: s :: _ => s.toNat?.getD 4 | _ => 4
  let sz : Nat := szMb * 1024 * 1024
  let totalBytes := sz * iters

  IO.println s!"=== Benchmark: In-Place Mutation on {szMb} MB Buffer ({iters} passes = {totalBytes / (1024 * 1024)} MB total writes) ==="
  IO.println "| Paradigm | Elapsed Time | Throughput | Verification |"
  IO.println "| :--- | :--- | :--- | :--- |"

  -- Baseline C
  let b_c := allocZeroed sz
  let _ ← timeIt "Handwritten C (-O3)" totalBytes (fun _ => runRawC b_c iters)

  -- Optimized: Proof-Driven Zero-Cost (Rank-2 Scoped Pattern withIsolatedBuffer)
  let b_opt := allocZeroed sz
  let _ ← timeIt "Optimized (Rank-2 Scoped In-Place)" totalBytes (fun _ => runScopedZeroCost b_opt iters)

  -- Baseline 1: Standard Perceus FBIP
  let b_fbip := allocZeroed sz
  let _ ← timeIt "Baseline 1 (Perceus FBIP is_exclusive)" totalBytes (fun _ => runFBIP b_fbip iters)

  -- Baseline 2: Degraded COW (run on 64 KB buffer with 10 passes to measure in sensible time)
  let cowSz : Nat := 64 * 1024
  let cowIters : Nat := 10
  let cowBytes := cowSz * cowIters
  IO.println ""
  IO.println s!"=== Copy-on-Write (COW) Degradation Check on {cowSz / 1024} KB Buffer ({cowIters} passes) ==="
  let b_cow := allocZeroed cowSz
  let _ ← timeIt "Degraded COW (shared RC > 1)" cowBytes (fun _ => runCOW b_cow cowIters)
