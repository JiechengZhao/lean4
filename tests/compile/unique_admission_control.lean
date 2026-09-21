import Init.Data.ByteArray.Basic

/-!
Tests `Unique` as an inductive admission control mechanism for `setFast` and `usetFast`.
Verifies that:
1. `Unique` acts as a static admission ticket requiring proven linear construction history.
2. Definitional equality `setFast_eq` and `usetFast_eq` hold via `rfl` in theorem proving.
3. Actual runtime safety is unconditionally backed by the entry physical gate `ensureExclusive.impl`.
-/

open ByteArray

-- 下游定理证明：setFast 在逻辑上就是纯 a.set，完全由 rfl 化简
theorem verify_setFast_def (a : ByteArray) (i : Nat) (v : UInt8) (h : i < a.size) (hu : Unique a) :
    a.setFast i v h hu = a.set i v h := rfl

theorem verify_usetFast_def (a : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < a.size) (hu : Unique a) :
    a.usetFast i v h hu = a.uset i v h := rfl

def main : IO Unit := do
  let b0 := ByteArray.empty.push 10 |>.push 20
  let hu0 := Unique.push _ 20 (Unique.push _ 10 Unique.empty)
  have h0 : 0 < b0.size := by decide

  -- 顺序执行通过 Unique 准入控制的更新
  let b1 := b0.setFast 0 99 h0 hu0
  let hu1 := ByteArray.setFast_unique b0 0 99 h0 hu0
  if h1 : (1 : USize).toNat < b1.size then
    let b2 := b1.usetFast 1 88 h1 hu1
    assert! b2[0]! == 99
    assert! b2[1]! == 88
    IO.println s!"Unique admission control execution verified: b2 = {b2.toList}"
  else
    throw <| IO.userError "Out of bounds"
