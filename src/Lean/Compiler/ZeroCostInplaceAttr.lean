/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Attributes
public import Lean.Elab.InfoTree

public section

namespace Lean.Compiler

/--
Parametric attribute for proof-driven zero-cost in-place mutation primitives.
Stores the Perceus fallback function name to which the compiler will safely
downgrade if aliasing, escaping, or sharing is detected.
-/
@[builtin_doc]
builtin_initialize zeroCostInplaceAttr : ParametricAttribute Name ← registerParametricAttribute {
  name := `zero_cost_inplace
  descr := "marks a function as a proof-driven zero-cost in-place mutation primitive with an automatic Perceus fallback"
  getParam := fun declName stx => do
    let decl ← getConstInfo declName
    let fnNameStx ← Attribute.Builtin.getIdent stx
    withoutExporting do
      let fnName ← Elab.realizeGlobalConstNoOverloadWithInfo fnNameStx
      let fnDecl ← getConstVal fnName
      if decl.name == fnDecl.name then
        throwError "Invalid `zero_cost_inplace` argument `{fnName}`: Definition cannot fall back to itself"
      return fnName
}

/--
Built-in fallback mappings for standard library primitives.
Ensures bootstrap compatibility when attributes are parsed before full elaboration.
-/
private def builtinFallback (n : Name) : Option Name :=
  if n == `ByteArray.setFast || n == `ByteArray.setFast.impl then some `ByteArray.set
  else if n == `ByteArray.usetFast || n == `ByteArray.usetFast.impl then some `ByteArray.uset
  else if n == `ByteArray.MutByteArray.set || n == `ByteArray.MutByteArray.set.impl then some `ByteArray.MutByteArray.setFallback
  else if n == `ByteArray.MutByteArray.uset || n == `ByteArray.MutByteArray.uset.impl then some `ByteArray.MutByteArray.usetFallback
  else none

/--
Retrieves the Perceus fallback function for a declaration tagged with `@[zero_cost_inplace]`.
Returns `some fallbackFn` if the declaration is a zero-cost in-place primitive,
or `none` otherwise.
-/
public partial def getZeroCostInplaceFallback? (env : Environment) (n : Name) : Option Name :=
  if let some fallback := builtinFallback n then
    some fallback
  else if let some fallback := zeroCostInplaceAttr.getParam? env n then
    some fallback
  else if n.isInternal then
    getZeroCostInplaceFallback? env n.getPrefix
  else
    none

/-- Backward-compatible predicate checking if a declaration is a zero-cost in-place primitive. -/
public def hasZeroCostInplaceAttribute (env : Environment) (n : Name) : Bool :=
  getZeroCostInplaceFallback? env n matches some _

end Lean.Compiler
