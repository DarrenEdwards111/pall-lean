import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRankSurface

/-!
# Bridge from full-ring raw rows to Boolean-ambient SPDP rows

This file is the first migration bridge for the Boolean refactor.  It avoids the
old problematic `mlProj` socket: define the raw derivative/shift row span in the
full polynomial ring, then show that mapping it through `liftToBoolLinearMap`
lands exactly in the Boolean-ambient row span.

So existing full-ring row-generation work can be reused by transporting raw rows
through the paper quotient boundary, rather than pretending full-ring `mlProj`
is the quotient reduction.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

namespace BoolPoly

/-- Full-ring raw strict-κ derivative/shift row span, with no `mlProj`.  This is
only a source span for transport into the Boolean ambient. -/
noncomputable def rawBlockedSpdpSubspace {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  Submodule.span ℚ
    { q | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) ℚ),
        S.length = κ ∧ m.totalDegree ≤ ℓ ∧
        m.vars ⊆ S.toFinset ∧
        isBlockAdmissible B S ∧
        q = m * iterDerivList S p }

/-- Full-ring raw inclusive-κ derivative/shift row span, with no `mlProj`. -/
noncomputable def rawBlockedSpdpSubspaceInc {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  Submodule.span ℚ
    { q | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) ℚ),
        S.length ≤ κ ∧ m.totalDegree ≤ ℓ ∧
        m.vars ⊆ S.toFinset ∧
        isBlockAdmissible B S ∧
        q = m * iterDerivList S p }

/-- Raw strict-κ rows have bounded total degree. -/
theorem rawBlockedSpdpSubspace_le_restrictTotalDegree {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    rawBlockedSpdpSubspace B κ ℓ p ≤
      MvPolynomial.restrictTotalDegree (Fin n) ℚ (ℓ + p.totalDegree) := by
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨S, m, _hlen, hdeg, _hvars, _hadm, rfl⟩
  have hdeg' : (m * iterDerivList S p).totalDegree ≤ ℓ + p.totalDegree :=
    le_trans (MvPolynomial.totalDegree_mul m (iterDerivList S p))
      (Nat.add_le_add hdeg (totalDegree_iterDerivList_le S p))
  exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hdeg'

/-- Raw inclusive-κ rows have bounded total degree. -/
theorem rawBlockedSpdpSubspaceInc_le_restrictTotalDegree {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    rawBlockedSpdpSubspaceInc B κ ℓ p ≤
      MvPolynomial.restrictTotalDegree (Fin n) ℚ (ℓ + p.totalDegree) := by
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨S, m, _hlen, hdeg, _hvars, _hadm, rfl⟩
  have hdeg' : (m * iterDerivList S p).totalDegree ≤ ℓ + p.totalDegree :=
    le_trans (MvPolynomial.totalDegree_mul m (iterDerivList S p))
      (Nat.add_le_add hdeg (totalDegree_iterDerivList_le S p))
  exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hdeg'

/-- Raw strict-κ source spans are finite-dimensional. -/
noncomputable instance rawBlockedSpdpSubspace_finite {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    Module.Finite ℚ (rawBlockedSpdpSubspace B κ ℓ p) := by
  have hle := rawBlockedSpdpSubspace_le_restrictTotalDegree B κ ℓ p
  have : Module.Finite ℚ (MvPolynomial.restrictTotalDegree (Fin n) ℚ (ℓ + p.totalDegree)) :=
    MvPolynomial.instFiniteSubtypeMemSubmoduleRestrictTotalDegreeOfFinite _ _ _
  exact Module.Finite.of_injective
    (Submodule.inclusion hle)
    (Submodule.inclusion_injective _)

/-- Raw inclusive-κ source spans are finite-dimensional. -/
noncomputable instance rawBlockedSpdpSubspaceInc_finite {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    Module.Finite ℚ (rawBlockedSpdpSubspaceInc B κ ℓ p) := by
  have hle := rawBlockedSpdpSubspaceInc_le_restrictTotalDegree B κ ℓ p
  have : Module.Finite ℚ (MvPolynomial.restrictTotalDegree (Fin n) ℚ (ℓ + p.totalDegree)) :=
    MvPolynomial.instFiniteSubtypeMemSubmoduleRestrictTotalDegreeOfFinite _ _ _
  exact Module.Finite.of_injective
    (Submodule.inclusion hle)
    (Submodule.inclusion_injective _)

/-- Mapping the raw strict-κ full-ring row span through the Boolean quotient map
is exactly the Boolean-ambient strict row span. -/
theorem map_liftToBool_rawBlockedSpdpSubspace_eq_bool {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : BoolPoly n) :
    Submodule.map (liftToBoolLinearMap n)
        (rawBlockedSpdpSubspace B κ ℓ (p : MvPolynomial (Fin n) ℚ)) =
      boolBlockedSpdpSubspace B κ ℓ p := by
  apply le_antisymm
  · rw [rawBlockedSpdpSubspace, Submodule.map_span]
    apply Submodule.span_le.mpr
    intro q hq
    rcases hq with ⟨r, hr, rfl⟩
    rcases hr with ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
    exact Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
  · rw [boolBlockedSpdpSubspace]
    apply Submodule.span_le.mpr
    intro q hq
    rcases hq with ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
    refine Submodule.mem_map_of_mem ?_
    exact Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩

/-- Mapping the raw inclusive-κ full-ring row span through the Boolean quotient
map is exactly the Boolean-ambient inclusive row span. -/
theorem map_liftToBool_rawBlockedSpdpSubspaceInc_eq_bool {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : BoolPoly n) :
    Submodule.map (liftToBoolLinearMap n)
        (rawBlockedSpdpSubspaceInc B κ ℓ (p : MvPolynomial (Fin n) ℚ)) =
      boolBlockedSpdpSubspaceInc B κ ℓ p := by
  apply le_antisymm
  · rw [rawBlockedSpdpSubspaceInc, Submodule.map_span]
    apply Submodule.span_le.mpr
    intro q hq
    rcases hq with ⟨r, hr, rfl⟩
    rcases hr with ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
    exact Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
  · rw [boolBlockedSpdpSubspaceInc]
    apply Submodule.span_le.mpr
    intro q hq
    rcases hq with ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
    refine Submodule.mem_map_of_mem ?_
    exact Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩

/-- Boolean strict row spaces are finite-dimensional, as images of finite raw
source row spaces under the quotient map. -/
noncomputable instance boolBlockedSpdpSubspace_finite {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : BoolPoly n) :
    Module.Finite ℚ (boolBlockedSpdpSubspace B κ ℓ p) := by
  rw [← map_liftToBool_rawBlockedSpdpSubspace_eq_bool]
  exact Module.Finite.map
    (rawBlockedSpdpSubspace B κ ℓ (p : MvPolynomial (Fin n) ℚ))
    (liftToBoolLinearMap n)

/-- Boolean inclusive row spaces are finite-dimensional, as images of finite raw
source row spaces under the quotient map. -/
noncomputable instance boolBlockedSpdpSubspaceInc_finite {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : BoolPoly n) :
    Module.Finite ℚ (boolBlockedSpdpSubspaceInc B κ ℓ p) := by
  rw [← map_liftToBool_rawBlockedSpdpSubspaceInc_eq_bool]
  exact Module.Finite.map
    (rawBlockedSpdpSubspaceInc B κ ℓ (p : MvPolynomial (Fin n) ℚ))
    (liftToBoolLinearMap n)

/-- Membership transport from a raw strict full-ring row certificate into the
Boolean-ambient strict row space. -/
theorem liftToBool_mem_boolBlockedSpdpSubspace_of_mem_raw {n : ℕ}
    {B : BlockPartition n} {κ ℓ : ℕ} {p : BoolPoly n}
    {r : MvPolynomial (Fin n) ℚ}
    (hr : r ∈ rawBlockedSpdpSubspace B κ ℓ
      (p : MvPolynomial (Fin n) ℚ)) :
    liftToBool r ∈ boolBlockedSpdpSubspace B κ ℓ p := by
  rw [← map_liftToBool_rawBlockedSpdpSubspace_eq_bool]
  exact Submodule.mem_map_of_mem hr

/-- Membership transport from a raw inclusive full-ring row certificate into the
Boolean-ambient inclusive row space. -/
theorem liftToBool_mem_boolBlockedSpdpSubspaceInc_of_mem_raw {n : ℕ}
    {B : BlockPartition n} {κ ℓ : ℕ} {p : BoolPoly n}
    {r : MvPolynomial (Fin n) ℚ}
    (hr : r ∈ rawBlockedSpdpSubspaceInc B κ ℓ
      (p : MvPolynomial (Fin n) ℚ)) :
    liftToBool r ∈ boolBlockedSpdpSubspaceInc B κ ℓ p := by
  rw [← map_liftToBool_rawBlockedSpdpSubspaceInc_eq_bool]
  exact Submodule.mem_map_of_mem hr

/-! ## Axiom audit anchors -/

#print axioms rawBlockedSpdpSubspace_le_restrictTotalDegree
#print axioms rawBlockedSpdpSubspaceInc_le_restrictTotalDegree
#print axioms rawBlockedSpdpSubspace_finite
#print axioms rawBlockedSpdpSubspaceInc_finite
#print axioms map_liftToBool_rawBlockedSpdpSubspace_eq_bool
#print axioms map_liftToBool_rawBlockedSpdpSubspaceInc_eq_bool
#print axioms boolBlockedSpdpSubspace_finite
#print axioms boolBlockedSpdpSubspaceInc_finite
#print axioms liftToBool_mem_boolBlockedSpdpSubspace_of_mem_raw
#print axioms liftToBool_mem_boolBlockedSpdpSubspaceInc_of_mem_raw

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
