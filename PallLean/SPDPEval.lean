/-
  SPDPEval.lean — SPDP Rank Monotonicity Under Evaluation

  Supporting lemmas for spdp_rank_eval_le.
-/
import PallLean.CompiledPoly
import PallLean.SPDPMonotone
import Mathlib.Tactic

namespace SPDPEval

open MvPolynomial CompiledPoly SPDP

variable {N : ℕ}

-- Evaluate a single variable X_j to constant c.
noncomputable def evalOne (j : Fin N) (c : ℚ) :
    MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ :=
  MvPolynomial.aeval (fun i => if i = j then MvPolynomial.C c else X i)

-- The general evaluation map.
noncomputable def evalMap (assignments : Fin N → Option ℚ) :
    MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ :=
  MvPolynomial.aeval (fun i =>
    match assignments i with
    | none => X i
    | some c => MvPolynomial.C c)

-- pderiv at j of (evalOne j c p) = 0.
lemma pderiv_evalOne_self (j : Fin N) (c : ℚ) (p : MvPolynomial (Fin N) ℚ) :
    pderiv j (evalOne j c p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    simp [evalOne, pderiv_C]
  | add p q ihp ihq =>
    simp [map_add, ihp, ihq]
  | mul_X p i ih =>
    have hmul : evalOne j c (p * X i) = evalOne j c p * evalOne j c (X i) := map_mul _ _ _
    rw [hmul]
    by_cases hij : i = j
    · rw [hij]
      have hXj : evalOne j c (X j) = MvPolynomial.C c := by
        simp [evalOne, aeval_X]
      rw [hXj, pderiv_mul, ih, zero_mul, zero_add, pderiv_C, mul_zero]
    · have hXi : evalOne j c (X i) = X i := by
        simp [evalOne, aeval_X, if_neg hij]
      rw [hXi, pderiv_mul, ih, zero_mul, zero_add]
      -- Goal: evalOne j c p * pderiv j (X i) = 0
      -- pderiv j (X i) simplifies to Pi.single j 1 i = 0 when j ≠ i
      have : (pderiv j) (X i : MvPolynomial (Fin N) ℚ) = 0 := by
        simp [pderiv_X, Pi.single_apply, Ne.symm hij]
      rw [this, mul_zero]

-- pderiv at free variable commutes with evalOne.
lemma pderiv_evalOne_comm (i j : Fin N) (c : ℚ) (p : MvPolynomial (Fin N) ℚ)
    (hij : i ≠ j) :
    pderiv i (evalOne j c p) = evalOne j c (pderiv i p) :=
  SPDPMonotone.pderiv_eval_comm i j c p hij

-- iterDerivList with free vars commutes with evalOne.
lemma iterDerivList_evalOne_comm (j : Fin N) (c : ℚ)
    (S : List (Fin N)) (p : MvPolynomial (Fin N) ℚ)
    (hfree : ∀ i ∈ S, i ≠ j) :
    iterDerivList S (evalOne j c p) = evalOne j c (iterDerivList S p) := by
  induction S generalizing p with
  | nil => simp [iterDerivList]
  | cons i S' ih =>
    have hi : i ≠ j := hfree i (by simp)
    have hS' : ∀ k ∈ S', k ≠ j := fun k hk => hfree k (by simp [hk])
    -- Unfold iterDerivList for cons
    show (i :: S').foldl (fun q k => pderiv k q) (evalOne j c p) =
         evalOne j c ((i :: S').foldl (fun q k => pderiv k q) p)
    simp only [List.foldl_cons]
    rw [pderiv_evalOne_comm i j c p hi]
    exact ih (pderiv i p) hS'

-- If S contains j and is Nodup, iterDerivList S (evalOne j c p) = 0.
lemma iterDerivList_evalOne_zero (j : Fin N) (c : ℚ)
    (S : List (Fin N)) (p : MvPolynomial (Fin N) ℚ)
    (hj : j ∈ S) (hnd : S.Nodup) :
    iterDerivList S (evalOne j c p) = 0 := by
  induction S generalizing p with
  | nil => simp at hj
  | cons i S' ih =>
    show (i :: S').foldl (fun q k => pderiv k q) (evalOne j c p) = 0
    simp only [List.foldl_cons]
    have hnd' : S'.Nodup := (List.nodup_cons.mp hnd).2
    by_cases hij : i = j
    · rw [hij, pderiv_evalOne_self j c p]
      exact SPDP.foldl_pderiv_zero S'
    · rw [pderiv_evalOne_comm i j c p hij]
      have hj' : j ∈ S' := by
        rcases List.mem_cons.mp hj with h | h
        · exact absurd h.symm hij
        · exact h
      exact ih (pderiv i p) hj' hnd'

end SPDPEval
