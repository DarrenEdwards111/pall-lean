/-
  GoodSeed4.lean — Prove depth4_good_seed at n = 4 directly

  Key insight: a restriction that fixes ALL variables makes the restricted
  polynomial a constant. All partial derivatives of a constant are 0,
  so spdpSubspace = ⊥ and spdpRank = 0 ≤ 9.

  This bypasses both Axiom 2 (hil_multi_switching) and Axiom 3
  (rowspace_signature_bound) for the n = 4 case.
-/
import PallLean.SPDPDefs
import PallLean.RestrictedSPDP
import PallLean.BoolEval
import PallLean.PaperAxioms

namespace GoodSeed4

open MvPolynomial BoolEval PaperAxioms Restriction RestrictedSPDP SPDP

/-- The "fix all to false" restriction. -/
def allFalse : Restriction.Restriction 4 := fun _ => some false

/-- pderiv of restrictPoly allFalse is 0 for any variable.
    Proof: allFalse substitutes every X_i with 0, so the result
    has no variables. By induction on p. -/
theorem pderiv_restrictPoly_allFalse (i : Fin 4) (p : MvPolynomial (Fin 4) ℚ) :
    MvPolynomial.pderiv i (Restriction.restrictPoly allFalse p) = 0 := by
  unfold Restriction.restrictPoly
  induction p using MvPolynomial.induction_on with
  | C r =>
    simp [MvPolynomial.aeval_C, MvPolynomial.pderiv_C]
  | mul_X q j ih =>
    simp only [map_mul, MvPolynomial.aeval_X, allFalse, mul_zero, map_zero]
  | add p q ihp ihq =>
    simp only [map_add, map_add, ihp, ihq, add_zero]

/-- foldl pderiv on 0 gives 0. -/
private lemma foldl_pderiv_zero (S : List (Fin 4)) :
    S.foldl (fun q i => MvPolynomial.pderiv i q) (0 : MvPolynomial (Fin 4) ℚ) = 0 := by
  induction S with
  | nil => rfl
  | cons i tl ih => simp only [List.foldl, map_zero]; exact ih

/-- iterDerivList of (restrictPoly allFalse p) is 0 for any list of length ≥ 1. -/
theorem iterDerivList_restrictPoly_allFalse (S : List (Fin 4))
    (p : MvPolynomial (Fin 4) ℚ) (hS : S ≠ []) :
    iterDerivList S (Restriction.restrictPoly allFalse p) = 0 := by
  cases S with
  | nil => exact absurd rfl hS
  | cons i tl =>
    unfold iterDerivList
    simp only [List.foldl]
    rw [pderiv_restrictPoly_allFalse i p]
    exact foldl_pderiv_zero tl

/-- spdpSubspace of (restrictPoly allFalse p) is ⊥ (for κ ≥ 1). -/
theorem spdpSubspace_allFalse (κ ℓ : ℕ) (p : MvPolynomial (Fin 4) ℚ) (hκ : κ ≥ 1) :
    spdpSubspace κ ℓ (Restriction.restrictPoly allFalse p) = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro q hq
    obtain ⟨S, m, hS, _, hq⟩ := hq
    rw [hq]
    have hS_ne : S ≠ [] := by intro h; subst h; simp at hS; omega
    rw [iterDerivList_restrictPoly_allFalse S p hS_ne, mul_zero]
    exact Submodule.zero_mem ⊥
  · exact bot_le

/-- spdpRank of (restrictPoly allFalse p) is 0 (for κ ≥ 1). -/
theorem spdpRank_allFalse (κ ℓ : ℕ) (p : MvPolynomial (Fin 4) ℚ) (hκ : κ ≥ 1) :
    spdpRank κ ℓ (Restriction.restrictPoly allFalse p) = 0 := by
  unfold spdpRank
  rw [spdpSubspace_allFalse κ ℓ p hκ]
  simp [finrank_bot]

/-- The good seed theorem at n = 4, proved directly.
    Uses the "fix all variables" restriction. -/
theorem depth4_good_seed_at_4 :
    ∃ (ρ : Restriction.Restriction 4),
    ∀ (p : MvPolynomial (Fin 4) ℚ),
      p.totalDegree ≤ (Nat.log 2 4) ^ 2 →
      IsMultilinear p →
      restrictedSpdpRank (Nat.log 2 4) (Nat.log 2 4)
        p ρ ≤ (Nat.log 2 4 + 1) ^ 2 := by
  refine ⟨allFalse, fun p _ _ => ?_⟩
  unfold restrictedSpdpRank
  rw [spdpRank_allFalse]
  · simp
  · -- κ = Nat.log 2 4 = 2 ≥ 1
    have : Nat.log 2 4 = 2 := by native_decide
    omega

end GoodSeed4
