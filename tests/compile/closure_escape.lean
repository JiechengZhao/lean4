/-!
Tests escape defense when an isolated buffer is captured in an escaping closure.
Verifies that LCNF `scopedInplace` pass detects that the buffer escapes into the closure,
downgrading `setFast` to safe Perceus copy-on-write `ByteArray.set` to prevent
use-after-free and data corruption.
-/

open ByteArray

def escapingClosureTest (raw : ByteArray) (hu : ByteArray.Unique raw) : (Unit → UInt8) × ByteArray :=
  if h_bound : 0 < raw.size then
    -- Closure captures raw:
    let readClosure := fun () => raw[0]!
    -- Local mutation on raw while raw is captured in closure:
    let raw_mut := raw.setFast 0 77 h_bound hu
    (readClosure, raw_mut)
  else
    ((fun () => 0), raw)

def main : IO Unit := do
  let initial := ByteArray.empty.push 1 |>.push 2 |>.push 3 |>.push 4
  let hu : ByteArray.Unique initial :=
    ByteArray.Unique.push _ 4 (
      ByteArray.Unique.push _ 3 (
        ByteArray.Unique.push _ 2 (
          ByteArray.Unique.push _ 1 ByteArray.Unique.empty
        )
      )
    )
  let (closure, b_mut) := escapingClosureTest initial hu
  let capturedVal := closure ()
  let mutatedVal := b_mut[0]!
  IO.println s!"capturedVal: {capturedVal}"
  IO.println s!"mutatedVal: {mutatedVal}"
  -- Invariant assertions:
  assert! capturedVal == 1
  assert! mutatedVal == 77
  IO.println "Closure escape defense passed safely with zero use-after-free!"
