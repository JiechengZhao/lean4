/-!
Tests graceful fallback in LCNF `scopedInplace` pass when an isolated buffer is aliased in scope.
Verifies that forking a buffer into multiple `setFast` calls triggers automatic downgrade
to Perceus copy-on-write (`ByteArray.set`), preventing data corruption.
-/

open ByteArray

def forkBuffer (raw : ByteArray) (hu : ByteArray.Unique raw) : ByteArray × ByteArray :=
  if h_bound : 0 < raw.size then
    -- raw is used in both b1 and b2 (aliased in scope)
    let b1 := raw.setFast 0 100 h_bound hu
    let b2 := raw.setFast 0 200 h_bound hu
    (b1, b2)
  else
    (raw, raw)

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
  let (b1, b2) := forkBuffer initial hu
  IO.println s!"b1[0]: {b1[0]!}"
  IO.println s!"b2[0]: {b2[0]!}"
  -- Invariant assertions: referential transparency preserved, no dirty overwrite
  assert! b1[0]! == 100
  assert! b2[0]! == 200
  IO.println "Aliasing fallback passed safely without memory corruption!"
