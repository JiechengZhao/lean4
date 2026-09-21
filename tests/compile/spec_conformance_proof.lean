import Init.Data.ByteArray.Basic

/-!
Tests pure mathematical theorem proving on `withIsolatedBuffer` specifications.
Verifies that downstream users can prove properties of `withIsolatedBuffer` algorithms
purely by relying on `withIsolatedBuffer_eval` and `simp` / `rfl`, completely unimpeded
by the operational physical implementation `withIsolatedBuffer.impl`.
-/

open ByteArray

-- 1. 下游纯函数操作：恒等作用域操作
def touchBuffer (a : ByteArray) : ByteArray :=
  withIsolatedBuffer a fun _σ buf => buf

-- 定理 1：touchBuffer a 恒等于 a，直接由 simp [withIsolatedBuffer_eval] 证明
theorem touchBuffer_eq (a : ByteArray) : touchBuffer a = a := by
  unfold touchBuffer
  simp [withIsolatedBuffer_eval]

-- 2. 下游操作：多阶段流水线组合规约
def doubleStep (a : ByteArray) : ByteArray :=
  let b := withIsolatedBuffer a fun _σ buf => buf
  withIsolatedBuffer b fun _σ buf => buf

-- 定理 2：流水线可直接由 withIsolatedBuffer_eval 展开并化简
theorem doubleStep_eq (a : ByteArray) : doubleStep a = a := by
  unfold doubleStep
  simp [withIsolatedBuffer_eval]

-- 3. 下游操作：算法规约直接等价于纯函数规格
def applyAlg (a : ByteArray) (f : (σ : Type) → MutByteArray σ → MutByteArray σ) : ByteArray :=
  withIsolatedBuffer a f

theorem applyAlg_spec (a : ByteArray) (f : (σ : Type) → MutByteArray σ → MutByteArray σ) :
    applyAlg a f = (f Unit ⟨a⟩).arr := by
  unfold applyAlg
  simp [withIsolatedBuffer_eval]

def main : IO Unit := do
  let b0 := ByteArray.empty.push 100
  let b1 := touchBuffer b0
  assert! b1[0]! == 100
  let b2 := doubleStep b0
  assert! b2[0]! == 100
  IO.println s!"Verified downstream specification theorems: b1[0]={b1[0]!}, b2[0]={b2[0]!}"
  IO.println "Downstream specification conformance proof verified successfully!"
