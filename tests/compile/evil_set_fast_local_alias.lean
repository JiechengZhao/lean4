import Init.Data.ByteArray.Basic

/-!
Tests that `ByteArray.setFast` is completely immune to intra-procedural aliasing.
When `let backup := a` creates a local alias before calling `setFast`,
the compiler pass `scopedInplace` detects that `backup` is in the transitive alias set
and safely downgrades `setFast` to standard Perceus `ByteArray.set`.
At runtime, `backup` remains pristine with its initial value (zero dirty write).
-/

open ByteArray

def evilSetFast (a : ByteArray) (h : 0 < a.size) (hu : Unique a) : ByteArray × ByteArray :=
  let backup := a
  let modified := a.setFast 0 0xEE h hu
  (backup, modified)

def main : IO Unit := do
  let a0 := ByteArray.empty.push 1 |>.push 2 |>.push 3
  let hu0 : Unique a0 :=
    Unique.push _ 3 (Unique.push _ 2 (Unique.push _ 1 Unique.empty))
  have h0 : 0 < a0.size := by decide

  let (backup, modified) := evilSetFast a0 h0 hu0

  IO.println s!"backup[0]: {backup[0]!}"
  IO.println s!"modified[0]: {modified[0]!}"

  -- 断言：backup 必须稳定读出初值 1，绝对不能被 0xEE (238) 污染！
  assert! backup[0]! == 1
  assert! modified[0]! == 238
  IO.println "evilSetFast local alias defense verified: backup intact, zero dirty write!"
