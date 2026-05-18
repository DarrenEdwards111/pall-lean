import PallLean.Paper93.DeepMath.PathC.PiPlusBoolLinear

/-!
# Boolean-ambient SPDP rank surface

This is the first rank-facing surface for the paper-faithful Boolean ambient.
The old `mlBlockedSpdpSubspace` lives in the full polynomial ring and uses
`mlProj`, which kills square monomials.  Here the rows live in `BoolPoly` and
are obtained by canonical Boolean normalization into the paper ambient.

This file intentionally provides interfaces, not final rank theorems.  It gives
future Route-C payloads a target that no longer depends on the false full-ring
`mlProj ∘ Pi+` commutation heuristic.
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

noncomputable instance {n : ℕ} : Nontrivial (BoolPoly n) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have hc := congrArg (fun p : BoolPoly n => (p : MvPolynomial (Fin n) ℚ)) h
  simp at hc

/-- Strict-κ Boolean-ambient SPDP row space.  Rows are derivatives/shifts of the
normal representative, then canonical Boolean-normalized into `BoolPoly`. -/
noncomputable def boolBlockedSpdpSubspace {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : BoolPoly n) :
    Submodule ℚ (BoolPoly n) :=
  Submodule.span ℚ
    { q | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) ℚ),
        S.length = κ ∧ m.totalDegree ≤ ℓ ∧
        m.vars ⊆ S.toFinset ∧
        isBlockAdmissible B S ∧
        q = liftToBool (m * iterDerivList S
          (p : MvPolynomial (Fin n) ℚ)) }

/-- Strict-κ Boolean-ambient SPDP rank. -/
noncomputable def boolBlockedSpdpRank {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : BoolPoly n) : ℕ :=
  Module.finrank ℚ (boolBlockedSpdpSubspace B κ ℓ p)

/-- Paper-faithful inclusive-κ Boolean-ambient SPDP row space. -/
noncomputable def boolBlockedSpdpSubspaceInc {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : BoolPoly n) :
    Submodule ℚ (BoolPoly n) :=
  Submodule.span ℚ
    { q | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) ℚ),
        S.length ≤ κ ∧ m.totalDegree ≤ ℓ ∧
        m.vars ⊆ S.toFinset ∧
        isBlockAdmissible B S ∧
        q = liftToBool (m * iterDerivList S
          (p : MvPolynomial (Fin n) ℚ)) }

/-- Paper-faithful inclusive-κ Boolean-ambient SPDP rank. -/
noncomputable def boolBlockedSpdpRankInc {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : BoolPoly n) : ℕ :=
  Module.finrank ℚ (boolBlockedSpdpSubspaceInc B κ ℓ p)

/-- The strict-κ Boolean row space is contained in the inclusive-κ Boolean row
space. -/
theorem boolBlockedSpdpSubspace_le_inc {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : BoolPoly n) :
    boolBlockedSpdpSubspace B κ ℓ p ≤ boolBlockedSpdpSubspaceInc B κ ℓ p := by
  apply Submodule.span_mono
  intro q hq
  rcases hq with ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
  exact ⟨S, m, le_of_eq hlen, hdeg, hvars, hadm, rfl⟩

/-- Rank monotonicity for a Boolean-ambient linear map, strict-κ version. -/
def BoolRankMonotonicity {n : ℕ}
    (B : BlockPartition n) (T : BoolPoly n →ₗ[ℚ] BoolPoly n) : Prop :=
  ∀ (κ ℓ : ℕ) (p : BoolPoly n),
    boolBlockedSpdpRank B κ ℓ (T p) ≤ boolBlockedSpdpRank B κ ℓ p

/-- Rank monotonicity for a Boolean-ambient linear map, paper-faithful
inclusive-κ version. -/
def BoolRankMonotonicityInc {n : ℕ}
    (B : BlockPartition n) (T : BoolPoly n →ₗ[ℚ] BoolPoly n) : Prop :=
  ∀ (κ ℓ : ℕ) (p : BoolPoly n),
    boolBlockedSpdpRankInc B κ ℓ (T p) ≤ boolBlockedSpdpRankInc B κ ℓ p

/-- Boolean-ambient Route-C rank invariance obligation, strict-κ version. -/
def PiPlusBoolRankInvariant
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  ∀ (κ ℓ : ℕ)
    (p : BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars),
    boolBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        κ ℓ (piPlusBoolLinearMap piP p) =
      boolBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        κ ℓ p

/-- Boolean-ambient Route-C rank invariance obligation, paper-faithful
inclusive-κ version. -/
def PiPlusBoolRankInvariantInc
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  ∀ (κ ℓ : ℕ)
    (p : BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars),
    boolBlockedSpdpRankInc
        (cook_levin_compilation M n hn2 htb hns).partition
        κ ℓ (piPlusBoolLinearMap piP p) =
      boolBlockedSpdpRankInc
        (cook_levin_compilation M n hn2 htb hns).partition
        κ ℓ p

/-- Rank invariance gives Boolean rank monotonicity. -/
theorem boolRankMonotonicity_of_rankInvariant
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (h : PiPlusBoolRankInvariant piP) :
    BoolRankMonotonicity
      (cook_levin_compilation M n hn2 htb hns).partition
      (piPlusBoolLinearMap piP) := by
  intro κ ℓ p
  exact le_of_eq (h κ ℓ p)

/-- Inclusive rank invariance gives paper-faithful Boolean rank monotonicity. -/
theorem boolRankMonotonicityInc_of_rankInvariantInc
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (h : PiPlusBoolRankInvariantInc piP) :
    BoolRankMonotonicityInc
      (cook_levin_compilation M n hn2 htb hns).partition
      (piPlusBoolLinearMap piP) := by
  intro κ ℓ p
  exact le_of_eq (h κ ℓ p)

/-! ## Axiom audit anchors -/

#print axioms boolBlockedSpdpSubspace_le_inc
#print axioms boolRankMonotonicity_of_rankInvariant
#print axioms boolRankMonotonicityInc_of_rankInvariantInc

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
