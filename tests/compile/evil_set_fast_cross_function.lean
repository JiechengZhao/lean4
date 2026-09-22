import Init.Data.ByteArray.Basic

/-!
Tests that `ByteArray.setFast` is completely immune to inter-procedural (cross-function) aliasing.
Even when `setFast` is executed inside a separate non-inlined worker where intra-procedural
compiler passes cannot see the caller's alias, `setFast.impl`'s physical check-out gate
(`ensureExclusive.impl`) intercepts the shared buffer dynamically (`RC > 1`),
performing copy-on-write isolation.
At runtime, `backup` in the caller remains pristine (zero dirty write).
-/

open ByteArray

@[noinline]
def evilWorker (a : ByteArray) (h : 0 < a.size) (hu : Unique a) : ByteArray :=
  a.setFast 0 0xEE h hu

def evilCaller (a : ByteArray) (h : 0 < a.size) (hu : Unique a) : ByteArray × ByteArray :=
  let backup := a
  let modified := evilWorker a h hu
  (backup, modified)

def main : IO Unit := do
  let a0 := ByteArray.empty.push 1 |>.push 2 |>.push 3
  let hu0 : Unique a0 :=
    Unique.push _ 3 (Unique.push _ 2 (Unique.push _ 1 Unique.empty))
  have h0 : 0 < a0.size := by decide

  let (backup, modified) := evilCaller a0 h0 hu0

  IO.println s!"cross-fn backup[0]: {backup[0]!}"
  IO.println s!"cross-fn modified[0]: {modified[0]!}"

  -- 断言：跨函数调用下，物理安检门必须生效，backup 绝对不能被 238 污染！
  assert! backup[0]! == 1
  assert! modified[0]! == 238
  IO.println "evilSetFast cross-function alias defense verified: physical gate works!"
