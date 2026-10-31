import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPcoNP

/-!
# Attacking the NP-intermediate horn: it is not an escape — it *is* P ≠ NP

`MCSPcoNP` boxed `MCSP ∈ coNP` into `MCSP NP-intermediate ∨ NP = coNP`.  The NP-intermediate horn looks like
a soft alternative to the PH-collapse.  It is not.  Attacking it directly, it dissolves into P ≠ NP.

The `NPIntermediate` used before was *loose* — `in NP ∧ not NP-complete`.  A problem in P also satisfies
that (it is not NP-complete unless P = NP).  The *genuine* notion adds the missing clause: **in NP, not in
P, and not NP-complete**.  And "in NP, not in P" is, verbatim, a witness that `NP ⊄ P` — i.e. **P ≠ NP**.
So a genuinely NP-intermediate MCSP forces P ≠ NP (`genuine_intermediate_forces_p_ne_np`).  This is the easy
half of Ladner's theorem; the hard half (P ≠ NP ⟹ *some* intermediate language exists, by delayed
diagonalization) is neither needed nor claimed here.

Splitting the loose horn (`loose_intermediate_splits`) gives the sharpened picture:
```
   MCSP ∈ coNP   ⟹   MCSP ∈ P   ∨   P ≠ NP   ∨   NP = coNP.
```
Every horn detonates.  `MCSP ∈ P` breaks cryptography — Kabanets–Cai / Razborov–Rudich: a polynomial-time
MCSP algorithm is a natural distinguisher that defeats every pseudorandom generator, so no one-way functions
(`mcsp_conp_all_horns_explode`, with that consequence as the named RR/KC hypothesis).  `P ≠ NP` is the prize
itself.  `NP = coNP` collapses the polynomial hierarchy.  There is no soft exit.

## What is proved

* **`NPneP` / `GenuinelyIntermediate`** — `P ≠ NP` as `NP ⊄ P`; the genuine NP-intermediate notion (in NP,
  not in P, not NP-complete).
* **`genuine_intermediate_forces_p_ne_np`** — a genuinely NP-intermediate language witnesses `P ≠ NP`.  The
  NP-intermediate horn *is* the prize.
* **`loose_intermediate_splits`** — the loose horn `in NP ∧ ¬NP-complete` splits into `MCSP ∈ P` or
  genuinely intermediate.
* **`refined_mcsp_dichotomy`** — `MCSP ∈ coNP ⟹ MCSP ∈ P ∨ P ≠ NP ∨ NP = coNP`.
* **`mcsp_conp_all_horns_explode`** — with the Kabanets–Cai/Razborov–Rudich fact (`MCSP ∈ P ⟹ ¬OWF`):
  `MCSP ∈ coNP ⟹ ¬OWF ∨ P ≠ NP ∨ NP = coNP`.  Every exit is a major consequence.

## Honest verdict — the horn was never an escape; the box has no soft side

Attacking the NP-intermediate horn does not settle whether MCSP is intermediate — that is open, and pinning
it either way is `cost_super`.  What it does, provably, is remove the illusion that this horn is easier than
the rest: genuinely NP-intermediate *means* not in P while in NP, which *is* `P ≠ NP`
(`genuine_intermediate_forces_p_ne_np`).  So the refined box `MCSP ∈ coNP ⟹ ¬OWF ∨ P ≠ NP ∨ NP = coNP`
(`mcsp_conp_all_horns_explode`) has three sides and every one is a landmark: no one-way functions, or P ≠ NP,
or a hierarchy collapse.  The collapse condition is load-bearing on all faces — which is the same wall,
`cost_super`, seen from the meta-complexity side.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPintermediate

open PallLean.Paper93.DeepMath.PathB.MCSPcoNP
open PallLean.Paper93.DeepMath.PathB.MCSPcoNP.ComplexityWorld

/-- `P ≠ NP`, phrased as `NP ⊄ P`: some NP language is not in P. -/
def NPneP (W : ComplexityWorld) (InP : W.Lang → Prop) : Prop := ∃ L, W.InNP L ∧ ¬ InP L

/-- The *genuine* NP-intermediate notion: in NP, not in P, and not NP-complete. -/
def GenuinelyIntermediate (W : ComplexityWorld) (InP : W.Lang → Prop) (L : W.Lang) : Prop :=
  W.InNP L ∧ ¬ InP L ∧ ¬ W.NPComplete L

/-! ### The horn is P ≠ NP -/

/-- **A genuinely NP-intermediate language forces P ≠ NP (proved).**  It is in NP and not in P — a witness
to `NP ⊄ P`.  The easy half of Ladner; the NP-intermediate horn *is* the prize. -/
theorem genuine_intermediate_forces_p_ne_np (W : ComplexityWorld) (InP : W.Lang → Prop) {L : W.Lang}
    (h : GenuinelyIntermediate W InP L) : NPneP W InP :=
  ⟨L, h.1, h.2.1⟩

/-- **The loose horn splits (proved).**  `in NP ∧ ¬NP-complete` is either `in P`, or genuinely
intermediate — there is no third option. -/
theorem loose_intermediate_splits (W : ComplexityWorld) (InP : W.Lang → Prop) {L : W.Lang}
    (h : W.NPIntermediate L) : InP L ∨ GenuinelyIntermediate W InP L := by
  by_cases hp : InP L
  · exact Or.inl hp
  · exact Or.inr ⟨h.1, hp, h.2⟩

/-! ### The refined box: every horn detonates -/

/-- **The refined MCSP ∈ coNP dichotomy (proved).**  `MCSP ∈ coNP ⟹ MCSP ∈ P ∨ P ≠ NP ∨ NP = coNP`. -/
theorem refined_mcsp_dichotomy (W : ComplexityWorld) (InP : W.Lang → Prop) (mcsp : W.Lang)
    (hnp : W.InNP mcsp) (hconp : W.IncoNP mcsp) :
    InP mcsp ∨ NPneP W InP ∨ W.NPeqcoNP := by
  by_cases hcomplete : W.NPComplete mcsp
  · exact Or.inr (Or.inr (np_eq_conp_of_npcomplete_conp W hcomplete hconp))
  · by_cases hp : InP mcsp
    · exact Or.inl hp
    · exact Or.inr (Or.inl ⟨mcsp, hnp, hp⟩)

/-- **Every horn detonates (proved).**  With the Kabanets–Cai/Razborov–Rudich fact that a polynomial-time
MCSP algorithm breaks one-way functions (`MCSP ∈ P → ¬OWF`, taken as the named hypothesis `rr_owf`):
`MCSP ∈ coNP ⟹ ¬OWF ∨ P ≠ NP ∨ NP = coNP` — no one-way functions, or the prize, or a hierarchy collapse. -/
theorem mcsp_conp_all_horns_explode (W : ComplexityWorld) (InP : W.Lang → Prop) (mcsp : W.Lang)
    (SecureOWF : Prop) (rr_owf : InP mcsp → ¬ SecureOWF)
    (hnp : W.InNP mcsp) (hconp : W.IncoNP mcsp) :
    ¬ SecureOWF ∨ NPneP W InP ∨ W.NPeqcoNP := by
  rcases refined_mcsp_dichotomy W InP mcsp hnp hconp with hp | hpne | hcoll
  · exact Or.inl (rr_owf hp)
  · exact Or.inr (Or.inl hpne)
  · exact Or.inr (Or.inr hcoll)

end PallLean.Paper93.DeepMath.PathB.MCSPintermediate

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPintermediate.genuine_intermediate_forces_p_ne_np
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPintermediate.loose_intermediate_splits
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPintermediate.refined_mcsp_dichotomy
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPintermediate.mcsp_conp_all_horns_explode
