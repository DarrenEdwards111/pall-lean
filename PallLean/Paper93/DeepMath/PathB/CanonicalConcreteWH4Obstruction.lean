import PallLean.Paper93.DeepMath.PathB.AugmentedConcreteWH4

/-!
# Canonical concreteW H4 obstruction

This file records the sharp obstruction to proving H4 for the unaugmented
canonical row

`fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau`.

The canonical adjacency branch is the rename of `span {1, X0 * X1}`.  If it
were closed under the H4 derivative interface, differentiating the adjacency
generator `X σ0 * X σ1` in the `σ1` direction would force `X σ0` to lie in
that same adjacency branch.  The coefficient at the source monomial `X0`
separates `X0` from `span {1, X0 * X1}`, so this is impossible.

The corrected target is the endpoint-augmented family from
`AugmentedConcreteWH4`, which adds `span {1, X σ0, X σ1}` and is already closed
under `DerivClosurePerType`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial SymmetricPowerBound
open PallLean.Paper93
open PallLean.Paper93.Bridge
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring (concreteW)

attribute [local instance] Classical.dec

private theorem canonicalEndpoint0_ne_endpoint1
    (n : ℕ) (hn4 : n ≥ 4) :
    concreteWEndpoint0 n hn4 ≠ concreteWEndpoint1 n hn4 := by
  intro h
  have h01 :
      (0 : Fin 4) = (1 : Fin 4) :=
    (Fin.castLEEmb hn4).injective h
  norm_num at h01

private theorem source_adjacency_endpoint0_not_mem :
    ¬ (MvPolynomial.X (0 : Fin 4) : MvPolynomial (Fin 4) ℚ) ∈
      perTypeInterfaceSpace ConstraintType.adjacency := by
  intro hx
  let m : Fin 4 →₀ ℕ := Finsupp.single (0 : Fin 4) 1
  have hcoeff_zero :
      MvPolynomial.coeff m
        (MvPolynomial.X (0 : Fin 4) : MvPolynomial (Fin 4) ℚ) = 0 := by
    unfold perTypeInterfaceSpace at hx
    refine Submodule.span_induction
      (s := ({(1 : MvPolynomial (Fin 4) ℚ),
        MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (1 : Fin 4)} :
          Set (MvPolynomial (Fin 4) ℚ)))
      (p := fun q _ => MvPolynomial.coeff m q = 0)
      ?_ ?_ ?_ ?_ hx
    · intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl
      · have hne : (0 : Fin 4 →₀ ℕ) ≠ m := by
          intro h
          have h0 := congrArg (fun f : Fin 4 →₀ ℕ => f (0 : Fin 4)) h
          simp [m] at h0
        rw [MvPolynomial.coeff_one, if_neg hne]
      · rw [MvPolynomial.coeff_X_mul']
        simp [m]
    · simp
    · intro p q _ _ hp hq
      simp [MvPolynomial.coeff_add, hp, hq]
    · intro a p _ hp
      simp [MvPolynomial.coeff_smul, hp]
  rw [MvPolynomial.coeff_X] at hcoeff_zero
  norm_num at hcoeff_zero

/-- The canonical adjacency product itself is in canonical `concreteW`. -/
theorem canonicalConcreteW_adjacency_product_mem
    (n : ℕ) (hn4 : n ≥ 4) :
    (MvPolynomial.X (concreteWEndpoint0 n hn4) *
        MvPolynomial.X (concreteWEndpoint1 n hn4) :
          MvPolynomial (Fin n) ℚ) ∈
      concreteW n hn4 (Fin.castLEEmb hn4) ConstraintType.adjacency := by
  unfold concreteW ambientPerTypeSpace
  refine Submodule.mem_map.mpr ?_
  refine ⟨MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (1 : Fin 4), ?_, ?_⟩
  · unfold perTypeInterfaceSpace
    exact Submodule.subset_span (by simp)
  · simp [concreteWEndpoint0, concreteWEndpoint1]

/-- The endpoint variable `X σ0` is not in the unaugmented canonical adjacency
space `span {1, X σ0 * X σ1}`. -/
theorem canonicalConcreteW_adjacency_endpoint0_not_mem
    (n : ℕ) (hn4 : n ≥ 4) :
    ¬ (MvPolynomial.X (concreteWEndpoint0 n hn4) :
          MvPolynomial (Fin n) ℚ) ∈
      concreteW n hn4 (Fin.castLEEmb hn4) ConstraintType.adjacency := by
  intro h
  unfold concreteW ambientPerTypeSpace at h
  rw [Submodule.mem_map] at h
  obtain ⟨q, hq, hqeq⟩ := h
  have hqX0 :
      q = (MvPolynomial.X (0 : Fin 4) : MvPolynomial (Fin 4) ℚ) := by
    have hqeq' :
        (MvPolynomial.rename ((Fin.castLEEmb hn4 : Fin 4 ↪ Fin n).toFun) q :
            MvPolynomial (Fin n) ℚ) =
          MvPolynomial.X (concreteWEndpoint0 n hn4) := by
      simpa using hqeq
    apply MvPolynomial.rename_injective (R := ℚ)
      ((Fin.castLEEmb hn4 : Fin 4 ↪ Fin n).toFun)
      (Fin.castLEEmb hn4).injective
    rw [hqeq']
    simp [concreteWEndpoint0]
  exact source_adjacency_endpoint0_not_mem (by simpa [hqX0] using hq)

/-- Any H4 proof for canonical `concreteW` would force the missing endpoint
variable into the canonical adjacency space. -/
theorem canonicalConcreteW_derivClosure_forces_adjacency_endpoint0_mem
    (n : ℕ) (hn4 : n ≥ 4)
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau)) :
    (MvPolynomial.X (concreteWEndpoint0 n hn4) :
        MvPolynomial (Fin n) ℚ) ∈
      concreteW n hn4 (Fin.castLEEmb hn4) ConstraintType.adjacency := by
  classical
  let e0 := concreteWEndpoint0 n hn4
  let e1 := concreteWEndpoint1 n hn4
  have hSlen : [e1].length ≤ Nat.log 2 n :=
    singleton_length_le_log_two_of_ge_four n hn4 e1
  have hProd :
      (MvPolynomial.X e0 * MvPolynomial.X e1 :
          MvPolynomial (Fin n) ℚ) ∈
        concreteW n hn4 (Fin.castLEEmb hn4) ConstraintType.adjacency := by
    simpa [e0, e1] using canonicalConcreteW_adjacency_product_mem n hn4
  have hInDeriv :
      SPDP.iterDerivList [e1]
          (MvPolynomial.X e0 * MvPolynomial.X e1 :
            MvPolynomial (Fin n) ℚ) ∈
        iterDerivSubmodule_forH5 [e1]
          (concreteW n hn4 (Fin.castLEEmb hn4) ConstraintType.adjacency) :=
    iterDerivList_mem_iterDerivSubmodule_forH5 [e1]
      (concreteW n hn4 (Fin.castLEEmb hn4) ConstraintType.adjacency)
      (MvPolynomial.X e0 * MvPolynomial.X e1 :
        MvPolynomial (Fin n) ℚ) hProd
  have hClosed :
      SPDP.iterDerivList [e1]
          (MvPolynomial.X e0 * MvPolynomial.X e1 :
            MvPolynomial (Fin n) ℚ) ∈
        concreteW n hn4 (Fin.castLEEmb hn4) ConstraintType.adjacency :=
    hDeriv ConstraintType.adjacency [e1] hSlen hInDeriv
  have hIter :
      SPDP.iterDerivList [e1]
          (MvPolynomial.X e0 * MvPolynomial.X e1 :
            MvPolynomial (Fin n) ℚ) =
        (MvPolynomial.X e0 : MvPolynomial (Fin n) ℚ) := by
    have h01 : e0 ≠ e1 := by
      simpa [e0, e1] using canonicalEndpoint0_ne_endpoint1 n hn4
    simp [SPDP.iterDerivList, MvPolynomial.pderiv_X_of_ne h01]
  simpa [hIter, e0] using hClosed

/-- No-go theorem: the unaugmented canonical concreteW family cannot satisfy
the H4 derivative-closure interface. -/
theorem not_canonicalConcreteW_derivClosurePerType
    (n : ℕ) (hn4 : n ≥ 4) :
    ¬ DerivClosurePerType (n := n)
      (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau) := by
  intro hDeriv
  exact canonicalConcreteW_adjacency_endpoint0_not_mem n hn4
    (canonicalConcreteW_derivClosure_forces_adjacency_endpoint0_mem
      n hn4 hDeriv)

/-- The corrected H4 target: add the endpoint variables to canonical
`concreteW`. -/
theorem corrected_endpointAugmentedConcreteW_derivClosurePerType
    (n : ℕ) (hn4 : n ≥ 4) :
    DerivClosurePerType (n := n) (endpointAugmentedConcreteW n hn4) :=
  endpointAugmentedConcreteW_derivClosurePerType n hn4

/-- Compact package: canonical H4 is obstructed, while the endpoint-augmented
target is closed. -/
theorem canonicalConcreteW_H4_no_go_and_corrected_target
    (n : ℕ) (hn4 : n ≥ 4) :
    (¬ DerivClosurePerType (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau)) ∧
      DerivClosurePerType (n := n) (endpointAugmentedConcreteW n hn4) :=
  ⟨not_canonicalConcreteW_derivClosurePerType n hn4,
    corrected_endpointAugmentedConcreteW_derivClosurePerType n hn4⟩

/-- Consequently, the old canonical `concreteW` H3/H4/I5 closure-frontier
route cannot be discharged unconditionally: its H4 component is already
refuted by the endpoint-variable derivative. -/
theorem not_CookLevinConcreteWRowEmbeddingClosureFrontier
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4) :
    ¬ CookLevinConcreteWRowEmbeddingClosureFrontier M n hn htb hns hn4 := by
  intro hFrontier
  exact not_canonicalConcreteW_derivClosurePerType n hn4 hFrontier.2.1

/-- Compact Route B diagnostic: canonical closure-frontier is impossible, but
the endpoint-augmented H4 replacement is available.  The remaining corrected
Route B work is therefore the charged/profile-aware shift and `mlProj`
transport around the endpoint-augmented family, not the old canonical H4. -/
theorem canonicalConcreteW_closureFrontier_no_go_and_endpointH4
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4) :
    (¬ CookLevinConcreteWRowEmbeddingClosureFrontier M n hn htb hns hn4) ∧
      DerivClosurePerType (n := n) (endpointAugmentedConcreteW n hn4) :=
  ⟨not_CookLevinConcreteWRowEmbeddingClosureFrontier M n hn htb hns hn4,
    corrected_endpointAugmentedConcreteW_derivClosurePerType n hn4⟩

#print axioms canonicalConcreteW_adjacency_product_mem
#print axioms canonicalConcreteW_adjacency_endpoint0_not_mem
#print axioms canonicalConcreteW_derivClosure_forces_adjacency_endpoint0_mem
#print axioms not_canonicalConcreteW_derivClosurePerType
#print axioms corrected_endpointAugmentedConcreteW_derivClosurePerType
#print axioms canonicalConcreteW_H4_no_go_and_corrected_target
#print axioms not_CookLevinConcreteWRowEmbeddingClosureFrontier
#print axioms canonicalConcreteW_closureFrontier_no_go_and_endpointH4

end PallLean.Paper93.DeepMath.PathB
