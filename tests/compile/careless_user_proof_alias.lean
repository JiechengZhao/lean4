import Init.Data.ByteArray.Basic

/-!
Tests that external alias defense holds even when a careless user holds a `Unique` proof.
Verifies that `withIsolatedBuffer` always passes through the physical check-out gate (`ensureExclusive.impl`).
When `let backup := a` creates an external alias (`RC > 1`), the physical gate triggers COW,
ensuring `backup` is never corrupted by in-place mutations in the isolated scope.
-/

open ByteArray

def carelessUserWithProof (a : ByteArray) (_hu : Unique a) : ByteArray × ByteArray :=
  -- 用户拥有证明 _hu : Unique a，但随手执行了别名备份
  let backup := a
  -- 进入 withIsolatedBuffer 作用域进行修改
  let modified := withIsolatedBuffer a fun _σ buf =>
    if h : 0 < buf.size then
      buf.uset 0 0xEE h
    else
      buf
  (backup, modified)

def main : IO Unit := do
  let a0 := ByteArray.empty.push 1 |>.push 2 |>.push 3
  let hu0 : Unique a0 :=
    Unique.push _ 3 (Unique.push _ 2 (Unique.push _ 1 Unique.empty))
  let (backup, modified) := carelessUserWithProof a0 hu0

  IO.println s!"backup[0]: {backup[0]!}"
  IO.println s!"modified[0]: {modified[0]!}"

  -- 【铁律断言】
  -- backup 必须稳定读出初值 1，绝对严禁被内部覆写的 238 (0xEE) 污染！
  assert! backup[0]! == 1
  assert! modified[0]! == 238
  IO.println "Careless user proof alias defense verified: backup intact, zero dirty write!"
