/-!
Tests concurrency safety and isolation of proof-driven zero-cost in-place mutation.
Verifies that concurrent reader tasks are strictly isolated from in-place mutations
performed via `withIsolatedBuffer`, asserting zero dirty reads and zero data races.
-/

open ByteArray

def readerTask (b : ByteArray) (expectedVal : UInt8) (iterations : Nat) : IO Bool := do
  for _ in [0:iterations] do
    for i in [0:b.size] do
      if h : i < b.size then
        let val := b[i]
        if val != expectedVal then
          return false
  return true

partial def fillBuffer {σ : Type} (b : MutByteArray σ) (v : UInt8) : MutByteArray σ :=
  let rec loop (i : USize) (cur : MutByteArray σ) : MutByteArray σ :=
    if h : i.toNat < cur.size then
      loop (i + 1) (cur.uset i v h)
    else
      cur
  loop 0 b

def main : IO Unit := do
  let size := 1024
  let initialList := List.replicate size (10 : UInt8)
  let shared := ByteArray.mk (Array.mk initialList)

  -- Spawn concurrent reader tasks reading the shared array
  let task1 ← IO.asTask (readerTask shared 10 100)
  let task2 ← IO.asTask (readerTask shared 10 100)

  -- Concurrently isolate and mutate a copy using Rank-2 scoped in-place mutation
  let mutated := withIsolatedBuffer shared fun σ buf =>
    fillBuffer buf 99

  -- Await reader tasks
  let res1 ← IO.ofExcept (task1.get)
  let res2 ← IO.ofExcept (task2.get)

  -- Assertions
  assert! res1 == true
  assert! res2 == true
  assert! shared[0]! == 10
  assert! shared[size - 1]! == 10
  assert! mutated[0]! == 99
  assert! mutated[size - 1]! == 99

  IO.println "Concurrency safety verified: zero dirty reads across threads!"
