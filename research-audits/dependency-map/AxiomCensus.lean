import PallLean
import PallLean.Step4Compiler

/-! Census: for every theorem declared in a `PallLean.*` module imported by the
active entrypoint, collect its axiom dependencies and report any that use
something other than `propext`, `Classical.choice`, `Quot.sound`. -/

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut total := 0
  let mut tally : Std.HashMap Name Nat := {}
  let mut examples : Std.HashMap Name (Array Name) := {}
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`PallLean).isPrefixOf mod do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternal then continue
    total := total + 1
    let axs ← liftCoreM <| Lean.collectAxioms n
    for a in axs do
      unless std.contains a do
        tally := tally.insert a (tally.getD a 0 + 1)
        let ex := examples.getD a #[]
        if ex.size < 8 then examples := examples.insert a (ex.push n)
  logInfo m!"theorems scanned: {total}"
  for (a, c) in tally.toList do
    logInfo m!"{a}: used by {c} theorems, e.g. {examples.getD a #[]}"
