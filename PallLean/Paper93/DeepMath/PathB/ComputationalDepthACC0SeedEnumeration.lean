import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0GuessableProver
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DerandCollapse

/-!
# `PRG ⟹ MA ⊆ NP` — Arthur's coins replaced by deterministic seed enumeration (proved mechanism)

Entry 222 left **`PRGCollapsesMAtoNP`** (`PRGExists → MA ⊆ NP`) as a named socket.  This file proves its mechanism: an
`MA` computation is `∃ Merlin message, Arthur's randomised check accepts`; a PRG that *fools* Arthur lets the randomised
check be replaced by a deterministic enumeration over the polynomially-many PRG seeds, so the language is decided by
`∃ Merlin message, deterministic check` — an `NP` computation.

## What is proved (clean axioms, no `sorry`)

* **`PRGFools Arthur ArthurDet := ∀ x w, Arthur x w ↔ ArthurDet x w`** — the PRG-fooling socket: the deterministic
  seed-enumeration check `ArthurDet` agrees with the randomised check `Arthur` on every input/witness.
* **`maLang_eq_detLang`** (PROVED) — `PRGFools Arthur ArthurDet → MALang Arthur = MALang ArthurDet`: replacing Arthur's
  randomised check by the (fooled) deterministic one preserves the language.
* **`prgCollapses_of_realizes`** (PROVED) — discharges the entry-222 `PRGCollapsesMAtoNP` socket from `PRGRealizesNP`
  (the PRG provides, for each `MA` language, a fooling deterministic check whose language lands in `NP`).

## Honest scope

This proves that **a fooling deterministic check preserves the language** (`maLang_eq_detLang`) — so the `MA → NP`
collapse is the language equality "randomised Arthur = seed-enumerated Arthur" — and threads it into the class-level
`PRGCollapsesMAtoNP` socket.  What remains the named socket is **`PRGFools`** (bundled into `PRGRealizesNP`): that the
PRG *actually* fools Arthur — `|Pr_coins[accept] - avg_seeds[accept]| < ε`, so the threshold over seeds matches the
threshold over true coins — the pseudorandomness content needing the PRG's fooling guarantee.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SeedEnumeration

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (Lang CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0GuessableProver (MALang)
open PallLean.Paper93.DeepMath.PathB.ACC0DerandCollapse (PRGCollapsesMAtoNP)

/-- **The PRG-fooling socket.**  The deterministic seed-enumeration check `ArthurDet` (count accepting over the
poly-many PRG seeds, threshold) agrees with Arthur's randomised check `Arthur` on every input/witness — `∀ x w,
Arthur x w ↔ ArthurDet x w`.  This is the PRG's fooling guarantee.  Stated, not proved. -/
def PRGFools {Wit : Type} (Arthur ArthurDet : List Bool → Wit → Prop) : Prop :=
  ∀ x w, Arthur x w ↔ ArthurDet x w

/-- **The fooled deterministic check preserves the language (PROVED).**  If the seed-enumeration check `ArthurDet`
agrees with the randomised `Arthur` (`PRGFools`), then `MALang Arthur = MALang ArthurDet` — the `MA` language equals the
`NP` language "guess Merlin, deterministically check over the seeds". -/
theorem maLang_eq_detLang {Wit : Type} (Arthur ArthurDet : List Bool → Wit → Prop)
    (hf : PRGFools Arthur ArthurDet) :
    MALang Arthur = MALang ArthurDet := by
  funext x
  apply propext
  constructor
  · rintro ⟨w, hw⟩; exact ⟨w, (hf x w).mp hw⟩
  · rintro ⟨w, hw⟩; exact ⟨w, (hf x w).mpr hw⟩

/-- **The realization socket.**  A PRG provides, for each `MA` language `L = MALang Arthur`, a fooling deterministic
check `ArthurDet` (`PRGFools`) whose deterministic language `MALang ArthurDet` lands in `NP`. -/
def PRGRealizesNP (PRGExists : Prop) (MA NP : CClass) : Prop :=
  PRGExists → ∀ L ∈ MA, ∃ (Wit : Type) (Arthur ArthurDet : List Bool → Wit → Prop),
    L = MALang Arthur ∧ PRGFools Arthur ArthurDet ∧ MALang ArthurDet ∈ NP

/-- **Discharges the entry-222 `PRGCollapsesMAtoNP` socket (PROVED).**  From `PRGRealizesNP`, given the PRG, each `MA`
language equals `MALang Arthur = MALang ArthurDet ∈ NP`. -/
theorem prgCollapses_of_realizes (PRGExists : Prop) (MA NP : CClass)
    (h : PRGRealizesNP PRGExists MA NP) :
    PRGCollapsesMAtoNP PRGExists MA NP := by
  intro hprg L hL
  obtain ⟨Wit, Arthur, ArthurDet, hLeq, hfool, hmem⟩ := h hprg L hL
  rw [hLeq, maLang_eq_detLang Arthur ArthurDet hfool]
  exact hmem

end PallLean.Paper93.DeepMath.PathB.ACC0SeedEnumeration

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SeedEnumeration.maLang_eq_detLang
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SeedEnumeration.prgCollapses_of_realizes
