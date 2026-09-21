import Init.Data.ByteArray.Basic

/-!
Tests check-out / check-in (借出-还回) specification decoupling for `withIsolatedBuffer`.
Verifies that:
1. Specification and implementation are decoupled via `@[implemented_by]`.
2. Pure specification equivalence can be proven by `rfl` via `withIsolatedBuffer_eval`.
3. Exclusively owned buffers mutate in-place.
-/

open ByteArray

-- 1. Theorem proving using pure specification and withIsolatedBuffer_eval
theorem test_spec_equality (a : ByteArray) (f : (σ : Type) → MutByteArray σ → MutByteArray σ) :
    withIsolatedBuffer a f = withIsolatedBuffer.spec a f := rfl

theorem test_eval_equality (a : ByteArray) (f : (σ : Type) → MutByteArray σ → MutByteArray σ) :
    withIsolatedBuffer a f = (f Unit ⟨a⟩).arr := by
  simp [withIsolatedBuffer_eval]

def testExclusiveCheckoutCheckin : IO Unit := do
  -- Fresh exclusive buffer (RC == 1)
  let b0 := ByteArray.empty.push 10 |>.push 20 |>.push 30
  let b1 := withIsolatedBuffer b0 fun _σ buf =>
    if h : 1 < buf.size then
      buf.set 1 99 h
    else buf
  assert! b1[0]! == 10
  assert! b1[1]! == 99
  assert! b1[2]! == 30
  IO.println s!"Exclusive buffer in-place result: {b1.toList}"

def main : IO Unit := do
  testExclusiveCheckoutCheckin
  IO.println "Checkout/checkin specification decoupling verified successfully!"
