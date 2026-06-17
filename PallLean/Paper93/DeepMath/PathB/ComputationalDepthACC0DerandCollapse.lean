import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CollapseIngredients
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0KarpLiptonCollapse

/-!
# The derandomisation collapse — `MA = NP` via a PRG, structure exposed (proved glue)

Entry 202 decomposed `DerandCollapsesMAtoNP` (`Derandomisation ⟹ MA = NP`) into `DerandMASubsetNP` (the deep direction
`Derandomisation ⟹ MA ⊆ NP`, socketed) + the trivial `NP ⊆ MA` + antisymmetry.  This file opens up that deep direction
into its genuine **hardness–randomness** structure and proves the composition glue (parallel to the entry-221 BFL-IKW
decomposition of `KarpLiptonCollapse`).

The structure.  An `MA` computation is `∃ Merlin message, Arthur's *randomised* check accepts (w.h.p.)`.  The
derandomisation supplies a **pseudorandom generator** (Nisan–Wigderson / Impagliazzo–Wigderson, from a hard function)
that fools Arthur's verifier; replacing Arthur's coins by the polynomially-many PRG seeds makes the check decidable
without true randomness, so `MA ⊆ NP` (guess Merlin's message, deterministically check over the seeds).

## What is proved (clean axioms, no `sorry`)

* **`DerandGivesPRG Derand PRGExists := Derand → PRGExists`** — the derandomisation yields a PRG (the
  hardness–randomness tradeoff; named socket).
* **`PRGCollapsesMAtoNP PRGExists MA NP := PRGExists → MA ⊆ NP`** — a PRG fooling Arthur collapses `MA ⊆ NP` (seed
  enumeration; named socket).
* **`derandMASubsetNP_via_PRG`** — the composition glue: `DerandGivesPRG` + `PRGCollapsesMAtoNP` ⇒ the entry-202
  `DerandMASubsetNP` (`Derand ⟹ MA ⊆ NP`), by `fun hd => prg_collapses (derand_gives_prg hd)`.
* **`derandCollapsesMAtoNP_via_PRG`** — the full `DerandCollapsesMAtoNP` from the hardness–randomness ingredients
  (`DerandGivesPRG`, `PRGCollapsesMAtoNP`, the trivial `NPSubsetMA`), via entry-202's antisymmetry.

## Honest scope

This **exposes the hardness–randomness structure** of the deep derandomisation direction — that `Derandomisation ⟹
MA ⊆ NP` factors as `Derandomisation ⟹ PRG` composed with `PRG ⟹ MA ⊆ NP` — and proves the *composition* (implication
chaining).  The two genuine classical ingredients remain named sub-sockets: **`DerandGivesPRG`** (the
Nisan–Wigderson / Impagliazzo–Wigderson hardness-to-pseudorandomness tradeoff) and **`PRGCollapsesMAtoNP`** (replacing
Arthur's randomness by PRG-seed enumeration), each requiring pseudorandomness infrastructure absent here.  This proves
the *structure and composition* of the derandomisation collapse, not its two deep ingredients.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DerandCollapse

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0KarpLiptonCollapse (DerandCollapsesMAtoNP)
open PallLean.Paper93.DeepMath.PathB.ACC0CollapseIngredients
  (DerandMASubsetNP NPSubsetMA derandCollapsesMAtoNP_discharge)

/-- **The hardness-to-PRG socket.**  The derandomisation supplies a pseudorandom generator (Nisan–Wigderson /
Impagliazzo–Wigderson, from a hard function) — `Derand → PRGExists`.  Stated, not proved. -/
def DerandGivesPRG (Derandomization PRGExists : Prop) : Prop := Derandomization → PRGExists

/-- **The PRG-collapse socket.**  A PRG fooling Arthur's verifier collapses `MA ⊆ NP` (replace Arthur's coins by the
poly-many PRG seeds, decided nondeterministically) — `PRGExists → MA ⊆ NP`.  Stated, not proved. -/
def PRGCollapsesMAtoNP (PRGExists : Prop) (MA NP : CClass) : Prop := PRGExists → MA ⊆ NP

/-- **The deep direction, factored through a PRG (PROVED glue).**  `DerandGivesPRG` (derandomisation ⟹ PRG) and
`PRGCollapsesMAtoNP` (PRG ⟹ `MA ⊆ NP`) compose to the entry-202 `DerandMASubsetNP` (`Derandomisation ⟹ MA ⊆ NP`):
`fun hd => prg_collapses (derand_gives_prg hd)`. -/
theorem derandMASubsetNP_via_PRG (Derandomization PRGExists : Prop) (MA NP : CClass)
    (derand_gives_prg : DerandGivesPRG Derandomization PRGExists)
    (prg_collapses : PRGCollapsesMAtoNP PRGExists MA NP) :
    DerandMASubsetNP Derandomization MA NP :=
  fun hd => prg_collapses (derand_gives_prg hd)

/-- **`DerandCollapsesMAtoNP` from the hardness–randomness ingredients (PROVED glue).**  `DerandGivesPRG` +
`PRGCollapsesMAtoNP` + the trivial `NPSubsetMA` give `DerandCollapsesMAtoNP Derandomization MA NP`
(`Derandomisation ⟹ MA = NP`), via the deep direction (`derandMASubsetNP_via_PRG`) and entry-202's antisymmetry
(`derandCollapsesMAtoNP_discharge`). -/
theorem derandCollapsesMAtoNP_via_PRG (Derandomization PRGExists : Prop) (MA NP : CClass)
    (derand_gives_prg : DerandGivesPRG Derandomization PRGExists)
    (prg_collapses : PRGCollapsesMAtoNP PRGExists MA NP)
    (triv : NPSubsetMA NP MA) :
    DerandCollapsesMAtoNP Derandomization MA NP :=
  derandCollapsesMAtoNP_discharge Derandomization MA NP
    (derandMASubsetNP_via_PRG Derandomization PRGExists MA NP derand_gives_prg prg_collapses) triv

end PallLean.Paper93.DeepMath.PathB.ACC0DerandCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DerandCollapse.derandMASubsetNP_via_PRG
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DerandCollapse.derandCollapsesMAtoNP_via_PRG
