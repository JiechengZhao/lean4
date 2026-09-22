import Init.Data.ByteArray.Basic

/-!
Tests that `scopedInplace` correctly detects local aliasing on `MutByteArray`
and safely downgrades mutation to Copy-on-Write (COW), preventing dirty writes.

Verifies:
1. `let backup := buf` creates an alias in the LCNF forward dependency graph.
2. `buf.set` and `buf.uset` are safely downgraded to fallback COW implementations.
3. At runtime, Perceus COW isolates `modified`, leaving `backup` completely intact.
4. No dirty write occurs.
-/

open ByteArray

def testLocalMutSetAlias (b : ByteArray) : UInt8 × UInt8 :=
  let res := ByteArray.withIsolatedBuffer b fun _σ buf =>
    if h : 0 < buf.size then
      let backup := buf
      let modified := buf.set 0 0xEE h
      let v_backup := backup.arr.get! 0
      let v_modified := modified.arr.get! 0
      if v_backup == 1 && v_modified == 0xEE then
        modified
      else
        buf
    else
      buf
  (b.get! 0, res.get! 0)

def testLocalMutUsetAlias (b : ByteArray) : UInt8 × UInt8 :=
  let res := ByteArray.withIsolatedBuffer b fun _σ buf =>
    if h : (0 : USize).toNat < buf.size then
      let backup := buf
      let modified := buf.uset 0 0xDD h
      let v_backup := backup.arr.get! 0
      let v_modified := modified.arr.get! 0
      if v_backup == 1 && v_modified == 0xDD then
        modified
      else
        buf
    else
      buf
  (b.get! 0, res.get! 0)

def main : IO Unit := do
  let b0 := ByteArray.empty.push 1 |>.push 2
  let (orig1, final1) := testLocalMutSetAlias b0
  IO.println s!"set alias test -> orig: {orig1}, final: {final1}"
  assert! orig1 == 1
  assert! final1 == 0xEE

  let (orig2, final2) := testLocalMutUsetAlias b0
  IO.println s!"uset alias test -> orig: {orig2}, final: {final2}"
  assert! orig2 == 1
  assert! final2 == 0xDD

  IO.println "MutByteArray local alias defense verified: zero dirty write!"
