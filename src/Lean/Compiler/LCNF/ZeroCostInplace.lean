/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean FRO, LLC
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
public import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.DependsOn
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Compiler.ZeroCostInplaceAttr

public section

namespace Lean.Compiler.LCNF

/-!
# Zero-Cost In-Place Mutation Optimization Pass

This pass inspects impure LCNF code for calls to functions registered with
the `@[zero_cost_inplace fallbackFn]` attribute (such as `ByteArray.MutByteArray.uset`
or `ByteArray.setFast`).

It performs a transitive alias and escape analysis on the target buffer. If the target
buffer or any of its aliases are captured in a closure or used again in the continuation `k`,
the call is safely rewritten to `fallbackFn` (standard Perceus copy-on-write).
Otherwise, the call is preserved as the zero-cost in-place primitive, which subsequent
passes (like `explicitRc`) will compile with zero reference counting overhead.
-/

/--
Compute the transitive alias set of `target`, excluding `exclude` (the linear successor produced
by this very let-declaration).
-/
def getTransitiveAliasSet (target : FVarId) (exclude : FVarId) : CompilerM FVarIdSet := do
  let lctx := (← get).lctx
  let rec loop (aliasSet : FVarIdSet) (fuel : Nat) : FVarIdSet :=
    match fuel with
    | 0 => aliasSet
    | fuel + 1 =>
      let updated := Id.run do
        let mut s := aliasSet
        for (_, (decl : LetDecl .impure)) in lctx.letDeclsImpure do
          if decl.fvarId != exclude && !s.contains decl.fvarId && decl.dependsOn s then
            s := s.insert decl.fvarId
        for (_, (funDecl : FunDecl .impure)) in lctx.funDeclsImpure do
          if !s.contains funDecl.fvarId && funDecl.dependsOn s then
            s := s.insert funDecl.fvarId
        return s
      if updated.size == aliasSet.size then
        aliasSet
      else
        loop updated fuel
  let maxFuel := lctx.letDeclsImpure.size + lctx.funDeclsImpure.size + 1
  return loop (({} : FVarIdSet).insert target) maxFuel

/--
Transform `code` to rewrite aliased/escaping zero-cost in-place mutations to their safe fallbacks.
-/
partial def Code.zeroCostInplace (code : Code .impure) : CompilerM (Code .impure) := do
  match code with
  | .let decl k =>
    modifyLCtx fun lctx => lctx.addLetDecl decl
    let k ← k.zeroCostInplace
    if let .fap f args := decl.value then
      if let some fallbackF := getZeroCostInplaceFallback? (← getEnv) f then
        let targetInfo : Option (Nat × FVarId) := Id.run do
          for i in [0:args.size] do
            if let .fvar fvarId := args[i]! then
              return some (i, fvarId)
          return none
        if let some (_targetIdx, fvarId) := targetInfo then
          let aliasSet ← getTransitiveAliasSet fvarId decl.fvarId
          if k.dependsOn aliasSet then
            let fallbackPs := (← getImpureSignature? fallbackF).get!.params
            let fallbackArgs := if args.size > fallbackPs.size then args.extract 0 fallbackPs.size else args
            let decl ← decl.updateValue (.fap fallbackF fallbackArgs)
            return code.updateLet! decl k
    return code.updateLet! decl k
  | .jp decl k =>
    modifyLCtx fun lctx => lctx.addFunDecl decl
    let value ← decl.value.zeroCostInplace
    let decl ← decl.updateValue value
    let k ← k.zeroCostInplace
    return code.updateFun! decl k
  | .cases cs =>
    let alts ← cs.alts.mapMonoM (·.mapCodeM Code.zeroCostInplace)
    return code.updateAlts! alts
  | .jmp .. | .return .. | .unreach .. => return code
  | .uset (k := k) .. | .sset (k := k) .. | .oset (k := k) ..
  | .inc (k := k) .. | .dec (k := k) .. | .setTag (k := k) .. | .del (k := k) .. =>
    let k ← k.zeroCostInplace
    return code.updateCont! k

def Decl.zeroCostInplace (decl : Decl .impure) : CompilerM (Decl .impure) := do
  for param in decl.params do
    modifyLCtx fun lctx => lctx.addParam param
  let value ← decl.value.mapCodeM Code.zeroCostInplace
  return { decl with value }

def zeroCostInplace : Pass :=
  Pass.mkPerDeclaration `zeroCostInplace .impure Decl.zeroCostInplace 0

builtin_initialize
  registerTraceClass `Compiler.zeroCostInplace (inherited := true)

end Lean.Compiler.LCNF
