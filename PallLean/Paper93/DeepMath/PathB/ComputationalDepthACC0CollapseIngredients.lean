import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0KarpLiptonCollapse

/-!
# The two Karp–Lipton collapse ingredients — `DerandCollapsesMAtoNP` and `KarpLiptonCollapse` (antisymmetry glue proved)

Entry 199 decomposed `DerandKarpLiptonSeparation` into three sub-sockets: `KarpLiptonCollapse`
(`NEXP ⊆ ACC⁰ ⟹ NEXP = MA`), `DerandCollapsesMAtoNP` (`Derandomisation ⟹ MA = NP`), and `NexpNeqNp` (the hierarchy,
discharged in entry 200).  This file opens the two *class-equality* ingredients into their genuine **two-inclusion**
structure and proves the **antisymmetry glue** for each: a class equality `X = Y` is exactly `X ⊆ Y` and `Y ⊆ X`, one
of which is the trivial inclusion and the other the deep direction.

* **`DerandCollapsesMAtoNP`** `= MA = NP`: `NP ⊆ MA` is trivial (an `NP` computation is an `MA` protocol with no
  interaction); `MA ⊆ NP` is the derandomisation direction (replace Arthur's coins by nondeterministic guessing over
  PRG seeds).
* **`KarpLiptonCollapse`** `= NEXP = MA`: `MA ⊆ NEXP` is trivial (`MA ⊆ NEXPTIME`); `NEXP ⊆ MA` is the deep
  Babai–Fortnow–Lund collapse, available *only* under the circuit hypothesis `NEXP ⊆ ACC⁰`.

## What is proved (clean axioms, no `sorry`)

* **`DerandMASubsetNP`** / **`NPSubsetMA`** — the two inclusions of the derandomisation collapse (named sockets).
* **`derandCollapsesMAtoNP_discharge`** — `DerandMASubsetNP` + `NPSubsetMA` ⇒ the entry-199 `DerandCollapsesMAtoNP`
  socket, by `Set.Subset.antisymm`.
* **`NexpSubsetMA_ofCircuits`** / **`MASubsetNexp`** — the two inclusions of the Karp–Lipton collapse (named sockets).
* **`karpLiptonCollapse_discharge`** — `NexpSubsetMA_ofCircuits` + `MASubsetNexp` ⇒ the entry-199 `KarpLiptonCollapse`
  socket, by `Set.Subset.antisymm`.

## Honest scope

This proves the **antisymmetry glue** turning the two collapse class-equalities into pairs of inclusions, discharging
both entry-199 sockets from those inclusions.  Each equality's *trivial* inclusion (`NP ⊆ MA`, `MA ⊆ NEXP`) and its
*deep* inclusion (`MA ⊆ NP` via derandomisation, `NEXP ⊆ MA` via the BFL collapse) remain named sub-sockets — the deep
ones are proven classical theorems (the hardness–randomness tradeoff; the doubly-exponential guess-verify collapse)
requiring complexity-theory infrastructure absent here.  This proves the logical structure of the collapses, not the
deep inclusions.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CollapseIngredients

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0KarpLiptonCollapse (DerandCollapsesMAtoNP KarpLiptonCollapse)

/-- **The derandomisation inclusion socket.**  A derandomisation places `MA ⊆ NP` (Arthur's coins replaced by
nondeterministic guessing over PRG seeds).  Stated, not proved. -/
def DerandMASubsetNP (Derandomization : Prop) (MA NP : CClass) : Prop := Derandomization → MA ⊆ NP

/-- **The trivial reverse inclusion socket.**  `NP ⊆ MA` (an `NP` computation is an `MA` protocol with no
interaction).  Stated, not proved (but the *easy* direction). -/
def NPSubsetMA (NP MA : CClass) : Prop := NP ⊆ MA

/-- **Discharging `DerandCollapsesMAtoNP` (PROVED).**  The two inclusions give `MA = NP` by antisymmetry: a
derandomisation yields `MA ⊆ NP`, and `NP ⊆ MA` always holds. -/
theorem derandCollapsesMAtoNP_discharge (Derandomization : Prop) (MA NP : CClass)
    (fwd : DerandMASubsetNP Derandomization MA NP) (bwd : NPSubsetMA NP MA) :
    DerandCollapsesMAtoNP Derandomization MA NP :=
  fun hd => Set.Subset.antisymm (fwd hd) bwd

/-- **The Karp–Lipton deep-inclusion socket.**  Under the circuit hypothesis `NEXP ⊆ ACC⁰`, `NEXP ⊆ MA` — the
Babai–Fortnow–Lund collapse (doubly-exponential guess-and-verify).  Stated, not proved. -/
def NexpSubsetMA_ofCircuits (NEXP ACC0 MA : CClass) : Prop := NEXP ⊆ ACC0 → NEXP ⊆ MA

/-- **The trivial reverse inclusion socket.**  `MA ⊆ NEXP` (`MA ⊆ NEXPTIME`).  Stated, not proved (the *easy*
direction). -/
def MASubsetNexp (MA NEXP : CClass) : Prop := MA ⊆ NEXP

/-- **Discharging `KarpLiptonCollapse` (PROVED).**  The two inclusions give `NEXP = MA` by antisymmetry: under
`NEXP ⊆ ACC⁰` the BFL collapse yields `NEXP ⊆ MA`, and `MA ⊆ NEXP` always holds. -/
theorem karpLiptonCollapse_discharge (NEXP ACC0 MA : CClass)
    (deep : NexpSubsetMA_ofCircuits NEXP ACC0 MA) (triv : MASubsetNexp MA NEXP) :
    KarpLiptonCollapse NEXP ACC0 MA :=
  fun hsub => Set.Subset.antisymm (deep hsub) triv

end PallLean.Paper93.DeepMath.PathB.ACC0CollapseIngredients

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CollapseIngredients.derandCollapsesMAtoNP_discharge
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CollapseIngredients.karpLiptonCollapse_discharge
