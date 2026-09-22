/-!
Benchmark: Scoped In-Place Mutation vs FBIP vs COW vs Raw C
Compares memory mutation regimes on ByteArray buffers with hardware PMU metrics.
-/

@[extern "lean_bench_alloc_zeroed"]
opaque allocZeroed (sz : @& Nat) : ByteArray

@[extern "lean_bench_raw_c"]
opaque runRawC (b : ByteArray) (iters : @& Nat) : ByteArray

@[extern "lean_bench_checksum"]
opaque checksum (b : @& ByteArray) : UInt64

@[extern "lean_bench_perf_start"]
opaque perfStart : IO Unit

@[extern "lean_bench_perf_stop"]
opaque perfStop : IO String

open ByteArray

instance : Nonempty ((b : ByteArray) ×' Unique b) := ⟨⟨ByteArray.empty, Unique.empty⟩⟩

def mkUniqueArray (sz : Nat) : (a : ByteArray) ×' Unique a :=
  let rec loop (i : Nat) (cur : ByteArray) (hu : Unique cur) : (a : ByteArray) ×' Unique a :=
    if i < sz then
      loop (i + 1) (cur.push 0) (Unique.push cur 0 hu)
    else
      ⟨cur, hu⟩
  loop 0 ByteArray.empty Unique.empty

-- 1. Baseline 1: Standard FBIP (Perceus RC check branch)
@[noinline]
partial def runFBIP (b : ByteArray) (iters : Nat) : ByteArray :=
  if h_b : b.size < USize.size then
    let sz := USize.ofNatLT b.size h_b
    let rec loop (sz : USize) (h_sz_eq : sz.toNat = b.size) (i : USize) (cur : ByteArray) (h_sz : cur.size = b.size) : ByteArray :=
      if h_lt : i < sz then
        have h : i.toNat < cur.size := by
          have : i.toNat < sz.toNat := h_lt
          rw [h_sz_eq, ← h_sz] at this
          exact this
        let val : UInt8 := i.toUInt8
        let cur' := cur.uset i val h
        have h_sz' : cur'.size = b.size := by rw [ByteArray.size_uset, h_sz]
        loop sz h_sz_eq (i + 1) cur' h_sz'
      else
        cur
    let rec outer (n : Nat) (cur : ByteArray) : ByteArray :=
      if n == 0 then cur
      else
        if h_sz : cur.size = b.size then
          outer (n - 1) (loop sz rfl 0 cur h_sz)
        else
          cur
    outer iters b
  else
    b

-- 2. Optimized: Scoped In-Place Mutation (RC-Free Inner Loop)
@[noinline]
partial def runScopedInplace (b : ByteArray) (iters : Nat) : ByteArray :=
  ByteArray.withIsolatedBuffer b fun σ buf =>
    if h_buf : buf.size < USize.size then
      let sz := USize.ofNatLT buf.size h_buf
      let rec loop (sz : USize) (h_sz_eq : sz.toNat = buf.size) (i : USize) (cur : ByteArray.MutByteArray σ) (h_sz : cur.size = buf.size) : ByteArray.MutByteArray σ :=
        if h_lt : i < sz then
          have h : i.toNat < cur.size := by
            have : i.toNat < sz.toNat := h_lt
            rw [h_sz_eq, ← h_sz] at this
            exact this
          let val : UInt8 := i.toUInt8
          let cur' := cur.uset i val h
          have h_sz' : cur'.size = buf.size := by rw [ByteArray.MutByteArray.size_uset, h_sz]
          loop sz h_sz_eq (i + 1) cur' h_sz'
        else
          cur
      let rec outer (n : Nat) (cur : ByteArray.MutByteArray σ) : ByteArray.MutByteArray σ :=
        if n == 0 then cur
        else
          if h_sz : cur.size = buf.size then
            outer (n - 1) (loop sz rfl 0 cur h_sz)
          else
            cur
      outer iters buf
    else
      buf

-- 3. Micro-benchmark: Isolated Gate vs Proof-Friendly vs Native Set
@[noinline]
partial def runSetBench (b : ByteArray) (iters : Nat) : ByteArray :=
  let rec loop (i : Nat) (cur : ByteArray) : ByteArray :=
    if h : i < cur.size then
      let cur' := cur.set i 0x42 h
      loop (i + 1) cur'
    else cur
  let rec outer (n : Nat) (cur : ByteArray) : ByteArray :=
    if n == 0 then cur
    else outer (n - 1) (loop 0 cur)
  outer iters b

@[noinline]
partial def runCheckedSetBench (b : ByteArray) (iters : Nat) : ByteArray :=
  let rec loop (i : Nat) (cur : ByteArray) : ByteArray :=
    if h : i < cur.size then
      let cur' := (ensureExclusive cur).set i 0x42 h
      loop (i + 1) cur'
    else cur
  let rec outer (n : Nat) (cur : ByteArray) : ByteArray :=
    if n == 0 then cur
    else outer (n - 1) (loop 0 cur)
  outer iters b

@[noinline]
partial def runSetFastBench (b : ByteArray) (iters : Nat) (hu : Unique b) : ByteArray :=
  let rec loop (i : Nat) (cur : ByteArray) (hu : Unique cur) (h_sz : cur.size = b.size) : (c : ByteArray) ×' Unique c :=
    if h : i < cur.size then
      let cur' := cur.setFast i 0x42 h hu
      have hu' : Unique cur' := setFast_unique cur i 0x42 h hu
      have h_sz' : cur'.size = b.size := by rw [size_setFast, h_sz]
      loop (i + 1) cur' hu' h_sz'
    else
      ⟨cur, hu⟩
  let rec outer (n : Nat) (cur : ByteArray) (hu : Unique cur) : ByteArray :=
    if n == 0 then cur
    else
      if h_sz : cur.size = b.size then
        let ⟨next, next_u⟩ := loop 0 cur hu h_sz
        outer (n - 1) next next_u
      else
        cur
  outer iters b hu

-- 4. Baseline 2: Degraded Copy-on-Write (shared reference forces copy on write)
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

structure BenchResult where
  res : ByteArray
  perfStr : String

def timeIt (name : String) (bytes : Nat) (act : Unit → ByteArray) : IO BenchResult := do
  perfStart
  let t0 ← IO.monoNanosNow
  let res ← evalSink (act ())
  let t1 ← IO.monoNanosNow
  let perfData ← perfStop
  let ns := t1 - t0
  let ms := ns.toFloat / 1000000.0
  let sec := ns.toFloat / 1000000000.0
  let gb := bytes.toFloat / (1024.0 * 1024.0 * 1024.0)
  let throughput := if sec > 0.0 then gb / sec else 0.0
  let chk := checksum res
  IO.println s!"| {name} | {ms.toString} ms | {throughput.toString} GB/s | (chk: {chk.toNat}) |"
  return { res := res, perfStr := s!"| {name} | {perfData} |" }

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
  let r_c ← timeIt "Handwritten C (-O3)" totalBytes (fun _ => runRawC b_c iters)

  -- Optimized: Scoped In-Place Mutation (Rank-2 Scoped Pattern withIsolatedBuffer)
  let b_opt := allocZeroed sz
  let r_opt ← timeIt "Optimized (Rank-2 Scoped In-Place)" totalBytes (fun _ => runScopedInplace b_opt iters)

  -- Baseline 1: Standard Perceus FBIP
  let b_fbip := allocZeroed sz
  let r_fbip ← timeIt "Baseline 1 (Perceus FBIP is_exclusive)" totalBytes (fun _ => runFBIP b_fbip iters)

  IO.println ""
  IO.println "=== Hardware Performance Counters (Linux PMU via perf_event_open) ==="
  IO.println "| Paradigm | Instructions | Cycles | IPC | Branches | Branch Misses | Cache Refs | Cache Misses |"
  IO.println "| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |"
  IO.println r_c.perfStr
  IO.println r_opt.perfStr
  IO.println r_fbip.perfStr

  -- Baseline 2: Degraded COW (run on 64 KB buffer with 10 passes to measure in sensible time)
  let cowSz : Nat := 64 * 1024
  let cowIters : Nat := 10
  let cowBytes := cowSz * cowIters
  IO.println ""
  IO.println s!"=== Copy-on-Write (COW) Degradation Check on {cowSz / 1024} KB Buffer ({cowIters} passes) ==="
  let b_cow := allocZeroed cowSz
  let _ ← timeIt "Degraded COW (shared RC > 1)" cowBytes (fun _ => runCOW b_cow cowIters)

  -- Micro-benchmark: Single-Point Checked Mutation (set vs checked set vs setFast)
  let setSz : Nat := 1024 * 1024
  let setIters : Nat := 4
  let setBytes := setSz * setIters
  IO.println ""
  IO.println s!"=== Micro-benchmark: Discrete Checked Mutation Breakdown ({setSz / (1024 * 1024)} MB Buffer, {setIters} passes) ==="
  IO.println "| Operation | Elapsed Time | Throughput | Verification |"
  IO.println "| :--- | :--- | :--- | :--- |"
  let b_set := allocZeroed setSz
  let _ ← timeIt "1. Native ByteArray.set (Perceus FBIP)" setBytes (fun _ => runSetBench b_set setIters)
  let b_cset := allocZeroed setSz
  let _ ← timeIt "2. Gate-Only Checked set (ensureExclusive + set, no proof)" setBytes (fun _ => runCheckedSetBench b_cset setIters)
  let ⟨b_setFast, hu⟩ := mkUniqueArray setSz
  let _ ← timeIt "3. Proof-Carrying ByteArray.setFast (with Unique proof)" setBytes (fun _ => runSetFastBench b_setFast setIters hu)
