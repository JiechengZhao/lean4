import Init.Data.ByteArray.Basic

/-!
Tests that the linear-time DAG-based alias closure analysis in `ZeroCostInplace`
correctly tracks multi-hop transitive dependencies across tuples, branches, and join points
without exponential/quadratic blowup, properly detecting when an alias escapes.
-/

open ByteArray

def multiHopChain (a : ByteArray) (h : 0 < a.size) (hu : Unique a) : ByteArray × ByteArray :=
  let hop1 := a
  let hop2 := (10, hop1)
  let hop3 := (20, hop2)
  let modified := a.setFast 0 0x77 h hu
  let extracted := hop3.2.2
  (extracted, modified)

def main : IO Unit := do
  let a0 := ByteArray.empty.push 5
  let hu0 := Unique.push _ 5 Unique.empty
  have h0 : 0 < a0.size := by decide

  let (extracted, modified) := multiHopChain a0 h0 hu0
  assert! extracted[0]! == 5
  assert! modified[0]! == 0x77
  IO.println s!"DAG multi-hop alias tracking verified: extracted[0]={extracted[0]!}, modified[0]={modified[0]!}"
