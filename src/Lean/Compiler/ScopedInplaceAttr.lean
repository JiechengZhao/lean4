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
Parametric attribute for scoped in-place mutation primitives.
Stores the Perceus fallback function name to which the compiler will safely
downgrade if aliasing, escaping, or sharing is detected.
-/
@[builtin_doc]
builtin_initialize scopedInplaceAttr : ParametricAttribute Name ← registerParametricAttribute {
  name := `scoped_inplace
  descr := "marks a function as a scoped in-place mutation primitive with an automatic Perceus fallback"
  getParam := fun declName stx => do
    let decl ← getConstInfo declName
    let fnNameStx ← Attribute.Builtin.getIdent stx
    withoutExporting do
      let fnName ← Elab.realizeGlobalConstNoOverloadWithInfo fnNameStx
      let fnDecl ← getConstVal fnName
      if decl.name == fnDecl.name then
        throwError "Invalid `scoped_inplace` argument `{fnName}`: Definition cannot fall back to itself"
      return fnName
}

/--
Built-in fallback mappings for standard library primitives.
Ensures bootstrap compatibility when attributes are parsed before full elaboration.
-/
private def builtinFallback (n : Name) : Option Name :=
  if n == `ByteArray.MutByteArray.set then some `ByteArray.MutByteArray.setFallback
  else if n == `ByteArray.MutByteArray.uset then some `ByteArray.MutByteArray.usetFallback
  else if n == `ByteArray.setFast || n == `ByteArray.setFast.impl then some `ByteArray.set
  else if n == `ByteArray.usetFast || n == `ByteArray.usetFast.impl then some `ByteArray.uset
  else none

/--
Retrieves the Perceus fallback function for a declaration tagged with `@[scoped_inplace]`.
Returns `some fallbackFn` if the declaration is a scoped in-place primitive,
or `none` otherwise.
-/
public partial def getScopedInplaceFallback? (env : Environment) (n : Name) : Option Name :=
  if let some fallback := builtinFallback n then
    some fallback
  else if let some fallback := scopedInplaceAttr.getParam? env n then
    some fallback
  else if n.isInternal then
    getScopedInplaceFallback? env n.getPrefix
  else
    none

/-- Backward-compatible predicate checking if a declaration is a scoped in-place primitive. -/
public def hasScopedInplaceAttribute (env : Environment) (n : Name) : Bool :=
  getScopedInplaceFallback? env n matches some _

/-- Compatibility alias for `getScopedInplaceFallback?`. -/
public def getZeroCostInplaceFallback? (env : Environment) (n : Name) : Option Name :=
  getScopedInplaceFallback? env n

/-- Compatibility alias for `hasScopedInplaceAttribute`. -/
public def hasZeroCostInplaceAttribute (env : Environment) (n : Name) : Bool :=
  hasScopedInplaceAttribute env n

end Lean.Compiler
