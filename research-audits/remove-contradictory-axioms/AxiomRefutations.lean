import PallLean.PAC

/-!
# Regression: the two former PAC / MatrixSPDP gadget axioms are refutable

Until this PR, `PallLean/PAC.lean` and `PallLean/MatrixSPDP.lean` declared

* `axiom PAC.gadget_spdp_subspace_factoring`  (Lemma 40(c), Finset-span form), and
* `axiom MatrixSPDP.gadget_factoring_linearmap_form`  (Lemma 40(c), linear-map form),

both inside the import closure of the default target `PallLean`.  Each one is
refutable, so either axiom let Lean prove `False` (the environment was inconsistent).
The statements are now the plain propositions `PAC.GadgetSpdpSubspaceFactoring` and
`MatrixSPDP.GadgetFactoringLinearMapForm`; this file proves their negations using only
the standard axioms.  (Before the PR, the identical proof with `hfact := <axiom>`
produced `False`; see `research/dependency-map:research-audits/dependency-map/AxiomInconsistency.lean`.)

Instance (both statements): N = 2, gadget g = X₀ (supportSize 1, degreeBound 1),
p = X₁, κ = 1, ℓ = 0, two singleton blocks.

* Shifted side: the statement bounds the target by the SPDP data of p at
  (κ + d, ℓ + d) = (2, 1).  Every length-2 derivative of the degree-1 polynomial X₁
  vanishes, so `mlBlockedSpdpSubspace B 2 1 X₁ = ⊥` (rank 0).
  - Span form: |G| ≤ 2^(1+1) · 0 = 0, hence G = ∅ and span G = ⊥.
  - Linear-map form: map L ⊥ = ⊥.
* Unshifted side: the admissible row (S = [0], u = 1) of g·p = X₀X₁ gives
  mlProj(∂₀(X₀X₁)) = X₁ ∈ `mlBlockedSpdpSubspace B 1 0 (X₀X₁)`.
* So X₁ ∈ ⊥, i.e. X₁ = 0; comparing the coefficient of x₁ gives 1 = 0.

Check with:  `lake env lean research-audits/remove-contradictory-axioms/AxiomRefutations.lean`
Expected `#print axioms` output: only `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace RemoveContradictoryAxioms


open MvPolynomial SPDP MultilinearSPDP

noncomputable def g0 : PAC.BoundedGadget 2 where
  poly := X 0
  supportSize := 1
  degreeBound := 1
  vars_card_le := by rw [vars_X]; simp
  totalDegree_le := by rw [totalDegree_X]

def B2 : BlockPartition 2 := ⟨2, fun i => i⟩

theorem not_gadgetSpdpSubspaceFactoring : ¬ PAC.GadgetSpdpSubspaceFactoring := by
  intro hfact
  classical
  obtain ⟨G, hcard, hsub⟩ :=
    hfact g0 B2 1 0 (X 1 : MvPolynomial (Fin 2) ℚ)
  -- shifted rank of X₁ at κ = 2 is zero (every length-2 derivative kills X₁)
  have hbot : mlBlockedSpdpSubspace B2 (1 + g0.degreeBound) (0 + g0.degreeBound)
      (X 1 : MvPolynomial (Fin 2) ℚ) = ⊥ := by
    unfold mlBlockedSpdpSubspace
    rw [Submodule.span_eq_bot]
    rintro x ⟨S, m, hlen, _, _, _, hx⟩
    have hiter : iterDerivList S (X 1 : MvPolynomial (Fin 2) ℚ) = 0 :=
      iterDerivList_eq_zero_of_totalDegree_lt S _ (by
        rw [hlen, totalDegree_X]; simp [g0])
    rw [hx, hiter, mul_zero, mlProj_zero]
  have hr : mlBlockedSpdpRank B2 (1 + g0.degreeBound) (0 + g0.degreeBound)
      (X 1 : MvPolynomial (Fin 2) ℚ) = 0 := by
    unfold mlBlockedSpdpRank; rw [hbot]; exact finrank_bot _ _
  rw [hr, mul_zero] at hcard
  have hG : G = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
  subst hG
  -- but the unshifted space contains mlProj(∂₀(X₀X₁)) = X₁ ≠ 0
  have hder : iterDerivList [(0 : Fin 2)] (g0.poly * (X 1 : MvPolynomial (Fin 2) ℚ))
      = X 1 := by
    simp [iterDerivList, g0, pderiv_X]
  have hmem : mlProj ((1 : MvPolynomial (Fin 2) ℚ) *
      iterDerivList [(0 : Fin 2)] (g0.poly * X 1)) ∈
      mlBlockedSpdpSubspace B2 1 0 (g0.poly * (X 1 : MvPolynomial (Fin 2) ℚ)) := by
    apply Submodule.subset_span
    refine ⟨[(0 : Fin 2)], 1, rfl, by simp, by simp, ?_, rfl⟩
    refine ⟨by simp, ?_⟩
    intro b
    simp only [List.filter]
    split <;> simp
  have h0 := hsub hmem
  simp only [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at h0
  rw [hder, one_mul] at h0
  have hc := congrArg (coeff (Finsupp.single (1 : Fin 2) 1)) h0
  rw [coeff_zero] at hc
  change (Finsupp.filter (fun α => Finsupp.IsMultilinear α) (X 1 : MvPolynomial (Fin 2) ℚ))
      (Finsupp.single 1 1) = 0 at hc
  rw [Finsupp.filter_apply_pos _ _ (by
    intro i; fin_cases i <;> simp)] at hc
  have h1 : coeff (Finsupp.single (1 : Fin 2) 1) (X 1 : MvPolynomial (Fin 2) ℚ) = 1 :=
    coeff_X _
  exact one_ne_zero (h1.symm.trans hc)

/-- The same instance refutes the companion statement `MatrixSPDP.GadgetFactoringLinearMapForm`
(formerly `axiom MatrixSPDP.gadget_factoring_linearmap_form`). -/
noncomputable def g0' : MatrixSPDP.BoundedGadget 2 where
  poly := X 0
  supportSize := 1
  degreeBound := 1
  vars_card_le := by rw [vars_X]; simp
  totalDegree_le := by rw [totalDegree_X]

theorem not_gadgetFactoringLinearMapForm : ¬ MatrixSPDP.GadgetFactoringLinearMapForm := by
  intro hfact
  classical
  obtain ⟨L, hsub, -⟩ :=
    hfact g0' B2 1 0 (X 1 : MvPolynomial (Fin 2) ℚ)
  have hbot : mlBlockedSpdpSubspace B2 (1 + g0'.degreeBound) (0 + g0'.degreeBound)
      (X 1 : MvPolynomial (Fin 2) ℚ) = ⊥ := by
    unfold mlBlockedSpdpSubspace
    rw [Submodule.span_eq_bot]
    rintro x ⟨S, m, hlen, _, _, _, hx⟩
    have hiter : iterDerivList S (X 1 : MvPolynomial (Fin 2) ℚ) = 0 :=
      iterDerivList_eq_zero_of_totalDegree_lt S _ (by
        rw [hlen, totalDegree_X]; simp [g0'])
    rw [hx, hiter, mul_zero, mlProj_zero]
  rw [hbot, Submodule.map_bot] at hsub
  have hder : iterDerivList [(0 : Fin 2)] (g0'.poly * (X 1 : MvPolynomial (Fin 2) ℚ))
      = X 1 := by
    simp [iterDerivList, g0', pderiv_X]
  have hmem : mlProj ((1 : MvPolynomial (Fin 2) ℚ) *
      iterDerivList [(0 : Fin 2)] (g0'.poly * X 1)) ∈
      mlBlockedSpdpSubspace B2 1 0 (g0'.poly * (X 1 : MvPolynomial (Fin 2) ℚ)) := by
    apply Submodule.subset_span
    refine ⟨[(0 : Fin 2)], 1, rfl, by simp, by simp, ?_, rfl⟩
    refine ⟨by simp, ?_⟩
    intro b
    simp only [List.filter]
    split <;> simp
  have h0 := hsub hmem
  rw [Submodule.mem_bot, hder, one_mul] at h0
  have hc := congrArg (coeff (Finsupp.single (1 : Fin 2) 1)) h0
  rw [coeff_zero] at hc
  change (Finsupp.filter (fun α => Finsupp.IsMultilinear α) (X 1 : MvPolynomial (Fin 2) ℚ))
      (Finsupp.single 1 1) = 0 at hc
  rw [Finsupp.filter_apply_pos _ _ (by
    intro i; fin_cases i <;> simp)] at hc
  have h1 : coeff (Finsupp.single (1 : Fin 2) 1) (X 1 : MvPolynomial (Fin 2) ℚ) = 1 :=
    coeff_X _
  exact one_ne_zero (h1.symm.trans hc)

end RemoveContradictoryAxioms

#print axioms RemoveContradictoryAxioms.not_gadgetSpdpSubspaceFactoring
#print axioms RemoveContradictoryAxioms.not_gadgetFactoringLinearMapForm
