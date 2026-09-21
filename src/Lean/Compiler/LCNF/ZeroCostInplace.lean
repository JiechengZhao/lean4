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
Extract free variables directly used in a `LetDecl` value.
-/
def getUsedFVarIdsOfLet (decl : LetDecl pu) : Array FVarId := Id.run do
  let mut vars := #[]
  match decl.value with
  | .proj _ _ fvarId _ | .oproj _ fvarId _ | .uproj _ fvarId _ | .sproj _ _ fvarId _
  | .reset _ fvarId _ | .box _ fvarId _ | .unbox fvarId _ | .isShared fvarId _ =>
    vars := vars.push fvarId
  | .fvar fvarId args | .reuse fvarId _ _ args _ =>
    vars := vars.push fvarId
    for arg in args do
      if let .fvar fv := arg then vars := vars.push fv
  | .const _ _ args _ | .ctor _ args _ | .fap _ args _ | .pap _ args _ =>
    for arg in args do
      if let .fvar fv := arg then vars := vars.push fv
  | .erased | .lit .. => ()
  return vars

/--
Extract all free variables used in a `Code` block.
-/
partial def collectUsedFVarsInCode (c : Code pu) : FVarIdSet :=
  let rec visit (c : Code pu) (s : FVarIdSet) : FVarIdSet :=
    match c with
    | .let decl k =>
      let s := getUsedFVarIdsOfLet decl |>.foldl (init := s) fun s fv => s.insert fv
      visit k s
    | .jp decl k | .fun decl k _ =>
      let s := visit decl.value s
      visit k s
    | .cases cs =>
      let s := s.insert cs.discr
      cs.alts.foldl (init := s) fun s alt => visit alt.getCode s
    | .jmp fvarId args =>
      let s := s.insert fvarId
      args.foldl (init := s) fun s arg =>
        match arg with
        | .fvar fv => s.insert fv
        | _ => s
    | .return fvarId =>
      s.insert fvarId
    | .unreach .. => s
    | .oset fv1 _ arg k _ =>
      let s := s.insert fv1
      let s := match arg with | .fvar fv2 => s.insert fv2 | _ => s
      visit k s
    | .uset fv1 _ fv2 k _ | .sset fv1 _ _ fv2 _ k _ =>
      let s := s.insert fv1 |>.insert fv2
      visit k s
    | .inc (fvarId := fv) (k := k) .. | .dec (fvarId := fv) (k := k) ..
    | .del (fvarId := fv) (k := k) .. | .setTag (fvarId := fv) (k := k) .. =>
      let s := s.insert fv
      visit k s
  visit c {}

/--
Build the forward dependency DAG: mapping each variable `v` to the list of declarations
that directly depend on `v`.
Constructed in a single linear pass over the function body code.
-/
partial def buildForwardDepGraph (c : Code pu) : FVarIdMap (Array FVarId) :=
  let rec visit (c : Code pu) (g : FVarIdMap (Array FVarId)) : FVarIdMap (Array FVarId) :=
    match c with
    | .let decl k =>
      let g := getUsedFVarIdsOfLet decl |>.foldl (init := g) fun g fv =>
        let succs := g.getD fv #[]
        g.insert fv (succs.push decl.fvarId)
      visit k g
    | .jp decl k | .fun decl k _ =>
      let used := collectUsedFVarsInCode decl.value
      let g := used.foldl (init := g) fun g fv =>
        let succs := g.getD fv #[]
        g.insert fv (succs.push decl.fvarId)
      let g := visit decl.value g
      visit k g
    | .cases cs =>
      cs.alts.foldl (init := g) fun g alt => visit alt.getCode g
    | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _
    | .inc (k := k) .. | .dec (k := k) .. | .del (k := k) .. | .setTag (k := k) .. =>
      visit k g
    | .jmp .. | .return .. | .unreach .. => g
  visit c {}

/--
Compute transitive alias set of `target` in linear time O(V + E) using BFS over the forward dependency DAG.
Excludes `exclude` (the linear successor produced by the mutation).
-/
partial def getTransitiveAliasSetFast (target : FVarId) (exclude : FVarId) (g : FVarIdMap (Array FVarId)) : FVarIdSet :=
  let rec loop (head : Nat) (queue : Array FVarId) (visited : FVarIdSet) : FVarIdSet :=
    if h : head < queue.size then
      let curr := queue[head]
      if let some succs := g.get? curr then
        let (visited, queue) := succs.foldl (init := (visited, queue)) fun (vis, q) succ =>
          if succ != exclude && !vis.contains succ then
            (vis.insert succ, q.push succ)
          else
            (vis, q)
        loop (head + 1) queue visited
      else
        loop (head + 1) queue visited
    else
      visited
  loop 0 #[target] (({} : FVarIdSet).insert target)

def padArgs (args : Array (Arg .impure)) (targetSize : Nat) : Array (Arg .impure) :=
  let rec loop (args : Array (Arg .impure)) : Array (Arg .impure) :=
    if args.size < targetSize then loop (args.push .erased) else args
  loop args

/--
Transform `code` to rewrite aliased/escaping zero-cost in-place mutations to their safe fallbacks.
Uses the precomputed forward dependency DAG `g` to evaluate alias closures in linear time.
-/
partial def Code.zeroCostInplace (g : FVarIdMap (Array FVarId)) (code : Code .impure) : CompilerM (Code .impure) := do
  match code with
  | .let decl k =>
    modifyLCtx fun lctx => lctx.addLetDecl decl
    let k ← k.zeroCostInplace g
    if let .fap f args := decl.value then
      if let some fallbackF := getZeroCostInplaceFallback? (← getEnv) f then
        let targetInfo : Option (Nat × FVarId) := Id.run do
          for i in [0:args.size] do
            if let .fvar fvarId := args[i]! then
              return some (i, fvarId)
          return none
        if let some (_targetIdx, fvarId) := targetInfo then
          let aliasSet := getTransitiveAliasSetFast fvarId decl.fvarId g
          if k.dependsOn aliasSet then
            let fallbackPs := (← getImpureSignature? fallbackF).get!.params
            let fallbackArgs := if args.size > fallbackPs.size then args.extract 0 fallbackPs.size else padArgs args fallbackPs.size
            let decl ← decl.updateValue (.fap fallbackF fallbackArgs)
            return code.updateLet! decl k
    return code.updateLet! decl k
  | .jp decl k =>
    modifyLCtx fun lctx => lctx.addFunDecl decl
    let value ← decl.value.zeroCostInplace g
    let decl ← decl.updateValue value
    let k ← k.zeroCostInplace g
    return code.updateFun! decl k
  | .cases cs =>
    let alts ← cs.alts.mapMonoM (·.mapCodeM (Code.zeroCostInplace g))
    return code.updateAlts! alts
  | .jmp .. | .return .. | .unreach .. => return code
  | .uset (k := k) .. | .sset (k := k) .. | .oset (k := k) ..
  | .inc (k := k) .. | .dec (k := k) .. | .setTag (k := k) .. | .del (k := k) .. =>
    let k ← k.zeroCostInplace g
    return code.updateCont! k

def Decl.zeroCostInplace (decl : Decl .impure) : CompilerM (Decl .impure) := do
  for param in decl.params do
    modifyLCtx fun lctx => lctx.addParam param
  let value ← match decl.value with
    | .code c =>
      let g := buildForwardDepGraph c
      let c ← Code.zeroCostInplace g c
      pure (.code c)
    | .extern .. => pure decl.value
  return { decl with value }

def zeroCostInplace : Pass :=
  Pass.mkPerDeclaration `zeroCostInplace .impure Decl.zeroCostInplace 0

builtin_initialize
  registerTraceClass `Compiler.zeroCostInplace (inherited := true)

end Lean.Compiler.LCNF
