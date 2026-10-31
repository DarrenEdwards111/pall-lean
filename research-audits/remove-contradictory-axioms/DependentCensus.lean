import PallLean

/-!
# Transitive-dependent census for the PAC / MatrixSPDP gadget axioms

Meta script (no proofs): walks every constant in the environment of the
active entrypoint `PallLean`, and for each constant decides (memoised DFS over
`ConstantInfo.getUsedConstantsAsSet`, i.e. type + value) whether it
transitively mentions one of the target axioms.  Constants from non-project
modules (Init/Std/Lean/Mathlib/…) cannot mention project axioms and are
skipped.  Output: one line per (axiom, dependent, module).
-/

open Lean Meta Elab Command

/-- Pre-fix axioms (present on main @ 7f53946) and their post-fix replacements
(plain `Prop`s).  Absent names are reported and skipped, so the same script runs on
both trees.  Pre-fix output: `dependents_main7f53946.tsv`; post-fix: `dependents_postfix.tsv`. -/
def targets : List Name :=
  [`PAC.gadget_spdp_subspace_factoring,
   `MatrixSPDP.gadget_factoring_linearmap_form,
   `PAC.gadget_spdp_subspace_factoring_paperFaithful,
   `PAC.GadgetSpdpSubspaceFactoring,
   `MatrixSPDP.GadgetFactoringLinearMapForm]

/-- Modules that (reflexively, transitively) import module `m`. -/
def importersOf (env : Environment) (m : Name) : NameSet := Id.run do
  let mods := env.header.moduleNames
  let data := env.header.moduleData
  let mut s : NameSet := NameSet.empty.insert m
  -- moduleNames is topologically sorted (imports first)
  for i in [0:mods.size] do
    let imps := data[i]!.imports
    if imps.any (fun imp => s.contains imp.module) then s := s.insert mods[i]!
  return s

partial def depends (env : Environment) (ax : Name) (rel : NameSet)
    (memo : IO.Ref (Std.HashMap Name Bool)) (c : Name) : IO Bool := do
  if c == ax then return true
  if let some b := (← memo.get).get? c then return b
  -- only constants in modules that import the axiom's module can depend on it
  let ok := match env.getModuleIdxFor? c with
    | some idx => rel.contains env.header.moduleNames[idx.toNat]!
    | none => true
  if !ok then memo.modify (·.insert c false); return false
  memo.modify (·.insert c false) -- cycle guard
  let some ci := env.find? c | return false
  let mut r := false
  for d in ci.getUsedConstantsAsSet do
    if ← depends env ax rel memo d then r := true; break
  memo.modify (·.insert c r)
  return r

run_cmd do
  let env ← getEnv
  let mut out : Array String := #[]
  for ax in targets do
    let memo ← IO.mkRef ({} : Std.HashMap Name Bool)
    if !(env.contains ax) then
      logInfo m!"{ax}: not in this environment (skipped)"
      continue
    let some axMod := env.getModuleIdxFor? ax | throwError "no module for {ax}"
    let rel := importersOf env env.header.moduleNames[axMod.toNat]!
    logInfo m!"{ax}: {rel.toList.length} modules import its module"
    let mut n := 0
    for (c, _) in env.constants.toList do
      match env.getModuleIdxFor? c with
      | some idx =>
        let m := env.header.moduleNames[idx.toNat]!
        if rel.contains m && c != ax then
          if ← depends env ax rel memo c then
            n := n + 1
            out := out.push s!"{ax}\t{c}\t{m}"
      | none => pure ()
    logInfo m!"{ax}: {n} transitive dependents"
  let tag := if env.contains `PAC.GadgetSpdpSubspaceFactoring then "postfix" else "main7f53946"
  IO.FS.writeFile s!"research-audits/remove-contradictory-axioms/dependents_{tag}.tsv"
    (String.intercalate "\n" out.toList ++ "\n")
