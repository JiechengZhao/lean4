import Init.Data.ByteArray.Basic

/-!
Tests proof-driven zero-cost in-place mutation on `ByteArray`.
Verifies that `ByteArray.setFast`, `ByteArray.usetFast`, and `ByteArray.fillFast`
execute correctly with constructive uniqueness proofs.
-/

open ByteArray

def make16 : (b : ByteArray) ×' (Unique b) :=
  let rec loop (i : Nat) (b : ByteArray) (hu : Unique b) : (b : ByteArray) ×' (Unique b) :=
    if h : i < 16 then
      loop (i + 1) (b.push 0) (Unique.push b 0 hu)
    else
      ⟨b, hu⟩
  loop 0 ByteArray.empty Unique.empty

def modifyBuffer (b : ByteArray) (h_u : Unique b) : (res : ByteArray) ×' (Unique res) :=
  let rec loop (i : Nat) (cur : ByteArray) (hu : Unique cur) (h_sz : cur.size = b.size) : (res : ByteArray) ×' (Unique res) :=
    if h : i < cur.size then
      let val : UInt8 := (i % 256).toUInt8
      let next := cur.setFast i val h hu
      have hu' : Unique next := ByteArray.setFast_unique cur i val h hu
      have h_sz' : next.size = b.size := by rw [ByteArray.size_setFast, h_sz]
      loop (i + 1) next hu' h_sz'
    else
      ⟨cur, hu⟩
  termination_by b.size - i
  decreasing_by
    rw [h_sz] at h
    omega
  loop 0 b h_u rfl

partial def modifyBufferUSize (b : ByteArray) (h_u : Unique b) : ByteArray :=
  let rec loop (i : USize) (cur : ByteArray) (hu : Unique cur) : ByteArray :=
    if h : i.toNat < cur.size then
      let next := cur.usetFast i 0xAA h hu
      let hu' := ByteArray.usetFast_unique cur i 0xAA h hu
      loop (i + 1) next hu'
    else
      cur
  loop 0 b h_u

def main : IO Unit := do
  let ⟨b0, h0⟩ := make16
  let ⟨b1, h1⟩ := modifyBuffer b0 h0
  IO.println s!"b1 size: {b1.size}"
  IO.println s!"b1[0]: {b1[0]!}"
  IO.println s!"b1[5]: {b1[5]!}"
  IO.println s!"b1[15]: {b1[15]!}"

  let b2 := b1.fillFast 42 h1
  IO.println s!"b2[0]: {b2[0]!}"
  IO.println s!"b2[7]: {b2[7]!}"
  IO.println s!"b2[15]: {b2[15]!}"

  let ⟨b2_fresh, h2_fresh⟩ := make16
  let b3 := modifyBufferUSize b2_fresh h2_fresh
  IO.println s!"b3[0]: {b3[0]!}"
  IO.println s!"b3[8]: {b3[8]!}"
