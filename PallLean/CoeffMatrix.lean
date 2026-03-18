/-
  CoeffMatrix.lean — Derivative subspace monotonicity under evaluation
-/
import PallLean.SPDPDefs
import PallLean.SPDPEval
import PallLean.CompiledPoly
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace CoeffMatrix

open MvPolynomial SPDP

variable {N : ℕ}

/-! ## Key lemma: pderiv j of a polynomial not using x_j is 0.

  After evalOne j c, the result doesn't use x_j. So pderiv j of it is 0.
  This is already proved as SPDPEval.pderiv_evalOne_self.

  We extend: if j ∈ S, then iterDerivList S (evalOne j c p) = 0,
  even without S.Nodup. The argument: at the first occurrence of j
  in the foldl, we apply pderiv j to something that doesn't use x_j
  (since all previous pderiv's were at different variables, and evalOne
  killed x_j). So pderiv j gives 0, and remaining foldl on 0 gives 0. -/

/-- pderiv at i of (evalOne j c q) for i ≠ j doesn't reintroduce x_j. -/
lemma evalOne_pderiv_still_no_xj (j i : Fin N) (c : ℚ)
    (q : MvPolynomial (Fin N) ℚ) (hij : i ≠ j) :
    SPDPEval.evalOne j c (pderiv i q) =
    pderiv i (SPDPEval.evalOne j c q) := by
  rw [← SPDPEval.pderiv_evalOne_comm i j c q hij]

/-- Applying pderiv j to evalOne j c of anything gives 0. -/
lemma pderiv_of_evalOne_zero (j : Fin N) (c : ℚ)
    (q : MvPolynomial (Fin N) ℚ) :
    pderiv j (SPDPEval.evalOne j c q) = 0 :=
  SPDPEval.pderiv_evalOne_self j c q

/-- Key: if j appears anywhere in S, iterDerivList S (evalOne j c p) = 0.
    No Nodup requirement. Proof: track through the foldl. Before hitting j,
    all pderiv's commute with evalOne. When we hit j, pderiv_evalOne_self
    gives 0. After that, foldl on 0 gives 0. -/
lemma iterDerivList_evalOne_zero_no_nodup (j : Fin N) (c : ℚ)
    (S : List (Fin N)) (p : MvPolynomial (Fin N) ℚ)
    (hj : j ∈ S) :
    iterDerivList S (SPDPEval.evalOne j c p) = 0 := by
  -- Proof by induction on S
  induction S generalizing p with
  | nil => exact absurd hj (by simp)
  | cons i S' ih =>
    show (i :: S').foldl (fun q k => pderiv k q) (SPDPEval.evalOne j c p) = 0
    simp only [List.foldl_cons]
    by_cases hij : i = j
    · -- i = j: pderiv j (evalOne j c p) = 0, then foldl on 0 = 0
      rw [hij, pderiv_of_evalOne_zero j c p]
      exact SPDP.foldl_pderiv_zero S'
    · -- i ≠ j: pderiv i commutes with evalOne, then recurse
      rw [SPDPEval.pderiv_evalOne_comm i j c p hij]
      have hj' : j ∈ S' := by
        cases List.mem_cons.mp hj with
        | inl h => exact absurd h.symm hij
        | inr h => exact h
      exact ih (pderiv i p) hj'

/-! ## Derivative subspace -/

noncomputable def derivSubspace (κ : ℕ) (p : MvPolynomial (Fin N) ℚ)
    (bp : CompiledPoly.BlockPartition N) : Submodule ℚ (MvPolynomial (Fin N) ℚ) :=
  Submodule.span ℚ
    { d | ∃ (S : List (Fin N)),
        S.length ≤ κ ∧
        (S.toFinset.image bp.blockOf).card ≤ κ ∧
        d = iterDerivList S p }

/-- Derivative subspace of φ(p) ⊆ φ-image of derivative subspace of p. -/
lemma derivSubspace_map_le (κ : ℕ) (p : MvPolynomial (Fin N) ℚ)
    (bp : CompiledPoly.BlockPartition N) (j : Fin N) (c : ℚ) :
    derivSubspace κ (SPDPEval.evalOne j c p) bp ≤
    Submodule.map (SPDPEval.evalOne j c).toLinearMap (derivSubspace κ p bp) := by
  apply Submodule.span_le.mpr
  intro d hd
  obtain ⟨S, hlen, hblk, hd_eq⟩ := hd
  rw [hd_eq]
  by_cases hj : j ∈ S
  · -- j ∈ S: derivative is 0, which is in any submodule
    rw [iterDerivList_evalOne_zero_no_nodup j c S p hj]
    exact Submodule.zero_mem _
  · -- j ∉ S: commutation applies
    have hfree : ∀ i ∈ S, i ≠ j := fun i hi hc => hj (hc ▸ hi)
    rw [SPDPEval.iterDerivList_evalOne_comm j c S p hfree]
    exact Submodule.mem_map_of_mem
      (Submodule.subset_span ⟨S, hlen, hblk, rfl⟩)

end CoeffMatrix
