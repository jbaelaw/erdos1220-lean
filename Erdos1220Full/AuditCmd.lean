import Lean

/-!
# The `#audit_axioms` command

Walks every constant of the environment in the namespaces `Erdos1220`,
`Erdos1220Full`, `Flypitch.Erdos1220`, and every non-internal constant declared in
a module `Erdos1220.*`/`Erdos1220Full.*` or in the current file, computes its axioms (memoized transitive
closure over constants used in type and value, as `#print axioms`), and reports
declarations whose axioms are not within `{propext, Classical.choice, Quot.sound}`,
plus every opaque/axiom/unsafe/partial/`implemented_by`/`extern` declaration.
-/

open Lean Elab Command

namespace Erdos1220Audit

abbrev Memo := Std.HashMap Name (Array Name)

partial def axiomsOf (env : Environment) (n : Name) : StateM Memo (Array Name) := do
  if let some s := (← get)[n]? then return s
  modify (·.insert n #[])
  let some ci := env.find? n | return #[]
  let mut acc : Array Name := #[]
  if let .axiomInfo _ := ci then acc := acc.push n
  for c in ci.getUsedConstantsAsSet do
    let s ← axiomsOf env c
    for a in s do
      unless acc.contains a do acc := acc.push a
  modify (·.insert n acc)
  return acc

def inScope (n : Name) : Bool :=
  [`Erdos1220, `Erdos1220Full, `Flypitch.Erdos1220].any (fun p => p.isPrefixOf n)

elab "#audit_axioms" : command => do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut names : Array Name := #[]
  let mut nMod := 0
  for (n, _) in env.constants.toList do
    let fromProject : Bool := match env.getModuleIdxFor? n with
      | some idx => match env.header.moduleNames[idx.toNat]? with
        | some m => (`Erdos1220).isPrefixOf m || (`Erdos1220Full).isPrefixOf m
        | none => false
      | none => true
    if inScope n || (fromProject && !n.isInternal) then
      names := names.push n
      unless inScope n do nMod := nMod + 1
  names := names.qsort (fun a b => a.toString < b.toString)
  let mut memo : Memo := {}
  let mut bad : Array (Name × Array Name) := #[]
  let mut nThm := 0
  let mut nDef := 0
  let mut nOther := 0
  let mut odd : Array Name := #[]
  let mut axiomUse : Std.HashMap Name Nat := {}
  for n in names do
    let some ci := env.find? n | continue
    match ci with
    | .thmInfo _ => nThm := nThm + 1
    | .defnInfo d =>
      nDef := nDef + 1
      if d.safety != .safe then odd := odd.push n
    | .opaqueInfo _ => nOther := nOther + 1; odd := odd.push n
    | .axiomInfo _ => nOther := nOther + 1; odd := odd.push n
    | _ => nOther := nOther + 1
    if (Lean.Compiler.getImplementedBy? env n).isSome || isExtern env n then
      odd := odd.push n
    let (axs, memo') := (axiomsOf env n).run memo
    memo := memo'
    for a in axs do
      axiomUse := axiomUse.insert a (axiomUse.getD a 0 + 1)
    if axs.any (fun a => !allowed.contains a) then bad := bad.push (n, axs)
  logInfo m!"AUDIT: {nMod} of them lie outside the three namespaces but are declared in project modules"
  logInfo m!"AUDIT: {names.size} declarations in scope ({nThm} theorems, {nDef} definitions, {nOther} other)"
  logInfo m!"AUDIT: axioms used (declaration counts): {axiomUse.toList}"
  logInfo m!"AUDIT: opaque/axiom/unsafe/partial/implemented_by/extern declarations in scope: {odd}"
  -- Cross-check the memoized closure against Lean's own `collectAxioms`
  -- on every 10th declaration and on all of `Erdos1220.Final`.
  let mut checked := 0
  let mut mismatch : Array Name := #[]
  for h : i in [0:names.size] do
    let n := names[i]
    if i % 10 == 0 || (`Erdos1220.Final).isPrefixOf n then
      let ref ← Lean.collectAxioms n
      let (mine, _) := (axiomsOf env n).run memo
      checked := checked + 1
      unless ref.all mine.contains && mine.all ref.contains do mismatch := mismatch.push n
  logInfo m!"AUDIT: cross-checked {checked} declarations against Lean.collectAxioms; mismatches: {mismatch}"
  if bad.isEmpty then
    logInfo m!"AUDIT: OK — every declaration depends only on [propext, Classical.choice, Quot.sound]"
  else
    logInfo m!"AUDIT: {bad.size} declarations with non-standard axioms: {bad}"

end Erdos1220Audit

