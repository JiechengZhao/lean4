import Init.Data.ByteArray.Basic

/-!
Tests that deep indirect escaping via composite data structures (tuples, records, nested containers)
is detected by the compiler's transitive alias analysis in `ExplicitRC`, safely downgrading
to standard Perceus reference counting and preventing dirty writes / state corruption.
-/

/--
Exploit Case:
The buffer `raw` is packed inside a tuple `tuple := (raw, 42)`.
A closure `reader := fun () => tuple.1[0]!` is created, which only references `tuple` (indirectly capturing `raw`).
A mutation `raw.setFast 0 99` is then invoked on `raw`.
Transitive alias analysis must identify that `tuple` depends on `raw`, and `reader` depends on `tuple`.
Hence `raw` is aliased in live variables through `reader`, and the call must downgrade to `ByteArray.set`.
-/
def evilEscapeViaTuple (raw : ByteArray) (hu : ByteArray.Unique raw) : ByteArray × (Unit → UInt8) :=
  if h_bound : 0 < raw.size then
    let tuple := (raw, 42)
    let reader := fun () => tuple.1[0]!
    let raw_mut := raw.setFast 0 99 h_bound hu
    (raw_mut, reader)
  else
    (raw, fun () => 0)

/--
Even deeper exploit: 3-level nested tuple `nested := (10, (20, (raw, 30)))`.
-/
def evilEscapeDeepNested (raw : ByteArray) (hu : ByteArray.Unique raw) : ByteArray × (Unit → UInt8) :=
  if h_bound : 0 < raw.size then
    let nested := (10, (20, (raw, 30)))
    let reader := fun () => nested.2.2.1[0]!
    let raw_mut := raw.setFast 0 88 h_bound hu
    (raw_mut, reader)
  else
    (raw, fun () => 0)

def main : IO Unit := do
  let b0 := ByteArray.empty.push 1
  let hu0 : ByteArray.Unique b0 := ByteArray.Unique.push ByteArray.empty 1 ByteArray.Unique.empty
  let (mutated, reader) := evilEscapeViaTuple b0 hu0
  let capturedVal := reader ()
  let mutatedVal := mutated[0]!
  -- Assert that the captured closure read the original value, not the overwritten 99
  assert! capturedVal == 1
  assert! mutatedVal == 99

  -- Test 3-level deep nested container
  let b1 := ByteArray.empty.push 2
  let hu1 : ByteArray.Unique b1 := ByteArray.Unique.push ByteArray.empty 2 ByteArray.Unique.empty
  let (mutatedDeep, deepReader) := evilEscapeDeepNested b1 hu1
  let deepVal := deepReader ()
  let mutatedDeepVal := mutatedDeep[0]!
  assert! deepVal == 2
  assert! mutatedDeepVal == 88

  IO.println "Deep closure escape defense verified successfully: zero dirty reads."
