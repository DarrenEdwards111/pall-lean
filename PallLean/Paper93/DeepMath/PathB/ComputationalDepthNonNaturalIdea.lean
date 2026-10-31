import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWhatRemains

/-!
# The non-natural idea: specification, why it must be self-reference, and the open step

The wall closes only with a **non-natural idea that sees SAT's structure**.  This file does the honest
maximum: it *specifies* such an idea precisely, proves it would win, proves it must be substantive
(not trivial/natural), and names the one concrete candidate — **self-reference / universality** — with
the load-bearing step left explicitly open.  It does **not** find a proof; finding one is `P ≠ NP`.

## Why the idea must be non-natural (the barrier)

The natural-proofs barrier kills any property that is **large** — satisfied by most functions.  Random
functions are *hard*, so any property capturing *hardness* is large, hence barred.  The escape is to
capture **structure, not hardness**: SAT is not merely hard, it is **universal** — it encodes circuit
evaluation.  Random functions are hard but *not* universal, so a property capturing universality is
**rare** (non-natural) and SAT-specific.  That is the shape the idea must have.

## The specification

An `Idea` is a structural property `seesSAT` of the SAT tower's cost `cbudget` that forces the
doubling:

* **`idea_forces_doubling`** — the idea gives `WhatIsLeft cbudget` (= `cost_super`).
* **`idea_gives_separation`** — hence no polynomial budget survives: `SAT ∉ P`, `P ≠ NP`.  A genuine
  idea *wins*, by the proved reduction.
* **`idea_cannot_be_flat`** — but the idea cannot be trivial: a property compatible with a *flat*
  (constant) budget would force the doubling on a constant, which is false.  So `seesSAT` must be
  **substantive** — it must track real growth.  A trivial (maximally natural) property cannot be the
  idea.

## The candidate: self-reference

The concrete non-natural idea the field has is **self-reference**.  SAT evaluates circuits, so it can
reason about its *own* candidate small circuit — the diagonal/universal structure a generic function
lacks (Williams' program: a fast Circuit-SAT algorithm from a small SAT circuit contradicts a known
separation).  This is the one idea family that threads all three barriers, because it uses SAT's
*universality* (rare, non-natural, SAT-specific) rather than its hardness (generic, natural).

* **`SelfReferenceForcesDoubling`** — the open conjecture, named: SAT's universality forces the
  doubling.  This is the `excludes` step of the idea, made concrete.
* **`selfref_closes`** — *if* the conjecture holds and SAT is universal, the wall falls (proved
  reduction).

## Honest scope — specified and named, not found

The idea is specified precisely (`Idea`), proved to win (`idea_gives_separation`), proved to be
non-trivial (`idea_cannot_be_flat`), and its concrete candidate is named — self-reference /
universality, with the open step `SelfReferenceForcesDoubling` isolated.  This does **not** find the
idea: proving `SelfReferenceForcesDoubling` — that SAT's universality actually forces the doubling — is
`cost_super`, and it is `P ≠ NP`.  I have specified the missing idea and pointed at the genuine
candidate; I have not, and cannot here, complete it.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NonNaturalIdea

open PallLean.Paper93.DeepMath.PathB.WhatRemains

/-- **The non-natural idea, specified.**  A structural property `seesSAT` of the SAT tower's cost that
SAT satisfies (`holds`) and that forces the doubling (`excludes`).  To be non-natural, `seesSAT` must
be rare (SAT-specific) — captured concretely by self-reference. -/
structure Idea where
  /-- the SAT tower's cost at composition depth `d` -/
  cbudget : ℕ → ℕ
  /-- the base: the ground is nonlinear -/
  base : 1 ≤ cbudget 0
  /-- the structural property the idea uses — instantiated by self-reference/universality -/
  seesSAT : Prop
  /-- SAT has the structure -/
  holds : seesSAT
  /-- the structure forces the doubling (the load-bearing step) -/
  excludes : seesSAT → WhatIsLeft cbudget

/-- **The idea forces the doubling (proved).**  `seesSAT` holds for SAT and forces `WhatIsLeft`. -/
theorem idea_forces_doubling (I : Idea) : WhatIsLeft I.cbudget := I.excludes I.holds

/-- **The idea wins (proved).**  A genuine idea delivers the separation: no polynomial budget survives,
so `SAT ∉ P`, `P ≠ NP`.  The reduction is proved; only a genuine `Idea` is missing. -/
theorem idea_gives_separation (I : Idea) (B : ℕ) (hbdd : ∀ d, I.cbudget d ≤ B) : False :=
  left_breaks_P I.cbudget (idea_forces_doubling I) I.base B hbdd

/-- **The idea cannot be trivial (proved).**  A property compatible with a *flat* (constant) budget
would force the doubling on a constant — `2·cbudget 0 ≤ cbudget 0` with `cbudget 0 ≥ 1` — which is
false.  So `seesSAT` must be **substantive**: a trivial (maximally natural) property cannot be the
idea.  The idea must track real structure, not vacuously hold. -/
theorem idea_cannot_be_flat (I : Idea) (hflat : ∀ d, I.cbudget d = I.cbudget 0) : False := by
  have hd : 2 * I.cbudget 0 ≤ I.cbudget 1 := idea_forces_doubling I 0
  have h1 := hflat 1
  have hb := I.base
  omega

/-! ### The candidate: self-reference -/

/-- **The self-reference conjecture (OPEN).**  SAT's universality — its ability to evaluate circuits,
hence to reason about its own candidate small circuit — forces the doubling.  This is the idea's
`excludes` step, made concrete: the load-bearing open statement. -/
def SelfReferenceForcesDoubling (cbudget : ℕ → ℕ) (Universal : Prop) : Prop :=
  Universal → WhatIsLeft cbudget

/-- **Self-reference closes the wall, if it holds (proved reduction).**  *Given* that SAT is universal
and that universality forces the doubling, the separation follows.  The reduction is proved; the
conjecture `SelfReferenceForcesDoubling` is the open `P ≠ NP` core. -/
theorem selfref_closes (cbudget : ℕ → ℕ) (hbase : 1 ≤ cbudget 0) (Universal : Prop)
    (huniv : Universal) (hconj : SelfReferenceForcesDoubling cbudget Universal)
    (B : ℕ) (hbdd : ∀ d, cbudget d ≤ B) : False :=
  left_breaks_P cbudget (hconj huniv) hbase B hbdd

/-- **Self-reference instantiates the idea (proved).**  Given the universality of SAT and the
self-reference conjecture, we obtain a genuine `Idea`.  So self-reference *is* an idea of the required
shape — the only open part is the conjecture. -/
def selfReferenceIdea (cbudget : ℕ → ℕ) (hbase : 1 ≤ cbudget 0) (Universal : Prop)
    (huniv : Universal) (hconj : SelfReferenceForcesDoubling cbudget Universal) : Idea where
  cbudget := cbudget
  base := hbase
  seesSAT := Universal
  holds := huniv
  excludes := hconj

end PallLean.Paper93.DeepMath.PathB.NonNaturalIdea

#print axioms PallLean.Paper93.DeepMath.PathB.NonNaturalIdea.idea_gives_separation
#print axioms PallLean.Paper93.DeepMath.PathB.NonNaturalIdea.idea_cannot_be_flat
#print axioms PallLean.Paper93.DeepMath.PathB.NonNaturalIdea.selfref_closes
