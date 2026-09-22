/-!
Tests that `ByteArray.Unique` cannot be forged.
Verifies rejection of trivial constructors `Unique.intro`, `Unique.mk`, `Unique.isolate`, and arbitrary forging.
-/

-- Attempt 1: Trivial intro constructor does not exist
def forgeIntro (buf : ByteArray) : ByteArray.Unique buf :=
  ByteArray.Unique.intro

-- Attempt 2: Trivial mk constructor does not exist
def forgeMk (buf : ByteArray) : ByteArray.Unique buf :=
  ByteArray.Unique.mk

-- Attempt 3: Empty cannot prove uniqueness of an arbitrary buffer
def forgeEmpty (buf : ByteArray) : ByteArray.Unique buf :=
  ByteArray.Unique.empty

-- Attempt 4: Unconditional isolate constructor does not exist
def forgeIsolate (buf : ByteArray) : ByteArray.Unique buf :=
  ByteArray.Unique.isolate buf
