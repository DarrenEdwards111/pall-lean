import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSigma2Collapse

/-!
# Attacking MCSP ∈ coNP directly: it is boxed by a provable dichotomy, and both horns are walls

`Sigma2Collapse` reduced the whole monotone→slice arc to one condition: `MCSP ∈ coNP` (a short certificate of
circuit-*hardness*).  Proving it outright would collapse Σ₂→NP and settle a famous open problem — not faked
here.  But `MCSP ∈ coNP` is not unconstrained.  Attacking it directly, a clean structural theorem boxes it
in from two sides, and a third (the barrier, already machine-checked in `Sigma2Collapse`) from a third.

**The dichotomy (proved).**  A textbook fact, formalized abstractly: *no NP-complete language lies in coNP
unless NP = coNP.*  If `L` is NP-complete and `L ∈ coNP`, then every `K ∈ NP` reduces to `L`, and
many-one reductions commute with complement, so `K ∈ coNP` — giving `NP ⊆ coNP`, hence (by
complementation) `NP = coNP`, a collapse of the polynomial hierarchy.  Applied to MCSP:
```
   MCSP ∈ coNP   ⟹   MCSP is NP-intermediate   ∨   NP = coNP.
```
Both horns are walls.  `NP = coNP` collapses PH (believed false).  MCSP *NP-intermediate* — a *natural*
problem strictly between P and NP-complete — would be the first such, a major structural result (Ladner's
intermediate languages are artificial).  So `MCSP ∈ coNP` cannot hold cheaply: it forces one of two dramatic
consequences.

**The barrier (third wall, from `Sigma2Collapse`).**  A coNP certificate for MCSP is a short, checkable
proof that a truth table has *no* small circuit — a lower-bound proof.  The verifier that accepts exactly
the hard tables is constructive + useful, and hardness is large, so it is a *natural property* — barred by
Razborov–Rudich under one-way functions.  So the direct attack meets three obstructions at once, none
crossed: PH-collapse, natural-NP-intermediacy, and the natural-proofs barrier.

## What is proved

* **`ComplexityWorld`** — an abstract world with complement, NP-membership, and many-one reductions, plus
  the two standard closure axioms (NP closed under reductions; reductions commute with complement).
* **`np_subset_conp_of_npcomplete_conp`** — an NP-complete `L ∈ coNP` forces every NP language into coNP.
* **`np_eq_conp_of_npcomplete_conp`** — hence NP = coNP: NP-complete ∩ coNP collapses the hierarchy.
* **`mcsp_conp_forces_collapse`** — if MCSP is NP-complete and in coNP, then NP = coNP.
* **`mcsp_conp_dichotomy`** — `MCSP ∈ coNP ⟹ MCSP NP-intermediate ∨ NP = coNP`.  The box around the
  collapse condition.

## Honest verdict — the attack lands three walls; MCSP ∈ coNP is genuinely load-bearing

Attacking `MCSP ∈ coNP` directly does not refute it and does not prove it — both would be `cost_super`.  It
*constrains* it, provably: `MCSP ∈ coNP` forces MCSP to be NP-intermediate or forces `NP = coNP`
(`mcsp_conp_dichotomy`), and independently it is a natural property barred by Razborov–Rudich
(`Sigma2Collapse.barrier_blocks_collapse`).  Three dramatic consequences, each an open frontier of its own.
That is exactly what a load-bearing condition looks like: not obviously false (no refutation), but every
route to it detonates something huge.  The collapse condition sits at the confluence of the natural-proofs
barrier, the PH-collapse question, and the NP-intermediacy question — which is another face of `cost_super`.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPcoNP

/-- An abstract complexity world: languages, complement, NP-membership, and many-one reductions, with the
two standard closure axioms. -/
structure ComplexityWorld where
  /-- the type of languages -/
  Lang : Type
  /-- complement of a language -/
  compl : Lang → Lang
  /-- membership in NP -/
  InNP : Lang → Prop
  /-- `Reduces K L`: `K` many-one reduces to `L` -/
  Reduces : Lang → Lang → Prop
  /-- complement is an involution -/
  compl_compl : ∀ L, compl (compl L) = L
  /-- NP is closed downward under reductions -/
  np_closed : ∀ {K L}, Reduces K L → InNP L → InNP K
  /-- many-one reductions commute with complement -/
  reduces_compl : ∀ {K L}, Reduces K L → Reduces (compl K) (compl L)

namespace ComplexityWorld

variable (W : ComplexityWorld)

/-- `L ∈ coNP`: its complement is in NP. -/
def IncoNP (L : W.Lang) : Prop := W.InNP (W.compl L)

/-- `L` is NP-complete: in NP, and every NP language reduces to it. -/
def NPComplete (L : W.Lang) : Prop := W.InNP L ∧ ∀ K, W.InNP K → W.Reduces K L

/-- NP = coNP: the hierarchy collapses to its first level. -/
def NPeqcoNP : Prop := ∀ L, W.InNP L ↔ W.IncoNP L

/-- `L` is NP-intermediate: in NP but not NP-complete. -/
def NPIntermediate (L : W.Lang) : Prop := W.InNP L ∧ ¬ W.NPComplete L

/-! ### The dichotomy engine -/

/-- **NP-complete ∩ coNP forces NP ⊆ coNP (proved).**  If `L` is NP-complete and in coNP, every NP language
reduces to `L`, and reductions commute with complement, so it too is in coNP. -/
theorem np_subset_conp_of_npcomplete_conp {L : W.Lang}
    (hc : W.NPComplete L) (hcoNP : W.IncoNP L) :
    ∀ K, W.InNP K → W.IncoNP K := by
  intro K hK
  have hred : W.Reduces K L := hc.2 K hK
  exact W.np_closed (W.reduces_compl hred) hcoNP

/-- **NP-complete ∩ coNP collapses the hierarchy (proved).**  `NP = coNP`. -/
theorem np_eq_conp_of_npcomplete_conp {L : W.Lang}
    (hc : W.NPComplete L) (hcoNP : W.IncoNP L) : W.NPeqcoNP := by
  intro K
  constructor
  · exact fun hK => np_subset_conp_of_npcomplete_conp W hc hcoNP K hK
  · intro hK
    have h1 : W.InNP (W.compl (W.compl K)) :=
      np_subset_conp_of_npcomplete_conp W hc hcoNP (W.compl K) hK
    rwa [W.compl_compl] at h1

/-! ### The box around MCSP ∈ coNP -/

/-- **MCSP ∈ coNP + NP-complete ⟹ NP = coNP (proved).**  If MCSP were both NP-complete and in coNP, the
polynomial hierarchy collapses. -/
theorem mcsp_conp_forces_collapse (mcsp : W.Lang)
    (hcomplete : W.NPComplete mcsp) (hconp : W.IncoNP mcsp) : W.NPeqcoNP :=
  np_eq_conp_of_npcomplete_conp W hcomplete hconp

/-- **The MCSP ∈ coNP dichotomy (proved).**  `MCSP ∈ coNP` forces MCSP to be NP-intermediate, or NP = coNP.
Both horns are dramatic open frontiers — the collapse condition is boxed in. -/
theorem mcsp_conp_dichotomy (mcsp : W.Lang) (hnp : W.InNP mcsp) (hconp : W.IncoNP mcsp) :
    W.NPIntermediate mcsp ∨ W.NPeqcoNP := by
  by_cases h : W.NPComplete mcsp
  · exact Or.inr (np_eq_conp_of_npcomplete_conp W h hconp)
  · exact Or.inl ⟨hnp, h⟩

end ComplexityWorld

end PallLean.Paper93.DeepMath.PathB.MCSPcoNP

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPcoNP.ComplexityWorld.np_subset_conp_of_npcomplete_conp
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPcoNP.ComplexityWorld.np_eq_conp_of_npcomplete_conp
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPcoNP.ComplexityWorld.mcsp_conp_forces_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPcoNP.ComplexityWorld.mcsp_conp_dichotomy
