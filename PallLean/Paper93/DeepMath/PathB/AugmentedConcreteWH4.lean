import PallLean.Paper93.DeepMath.PathB.ConcreteWShiftMlprojClosure

/-!
# Augmented concreteW H4 attempt

The canonical `concreteW` adjacency space contains `1` and the quadratic
endpoint product, but not the endpoint variables themselves.  A first
derivative of that product therefore falls out of the current `concreteW`.

This file records the checked repair: augment every canonical concrete
per-type space by the endpoint span `span {1, X σ0, X σ1}`.  The resulting
family is closed under all iterated derivative lists, hence satisfies the H4
interface `DerivClosurePerType`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial SymmetricPowerBound
open PallLean.Paper93
open PallLean.Paper93.Bridge
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring (concreteW)

attribute [local instance] Classical.dec

/-- The first endpoint of the canonical `Fin 4 ↪ Fin n` embedding. -/
def concreteWEndpoint0 (n : ℕ) (hn4 : n ≥ 4) : Fin n :=
  (Fin.castLEEmb hn4) (0 : Fin 4)

/-- The second endpoint of the canonical `Fin 4 ↪ Fin n` embedding. -/
def concreteWEndpoint1 (n : ℕ) (hn4 : n ≥ 4) : Fin n :=
  (Fin.castLEEmb hn4) (1 : Fin 4)

/-- The endpoint-variable repair space: constants and the two adjacency
endpoint variables. -/
noncomputable def concreteWEndpointSpan (n : ℕ) (hn4 : n ≥ 4) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  Submodule.span ℚ
    ({(1 : MvPolynomial (Fin n) ℚ),
      MvPolynomial.X (concreteWEndpoint0 n hn4),
      MvPolynomial.X (concreteWEndpoint1 n hn4)} :
        Set (MvPolynomial (Fin n) ℚ))

/-- Canonical concreteW augmented by the endpoint-variable repair space. -/
noncomputable def endpointAugmentedConcreteW (n : ℕ) (hn4 : n ≥ 4)
    (τ : ConstraintType) : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  concreteWCanonical n hn4 τ ⊔ concreteWEndpointSpan n hn4

private theorem one_mem_concreteWEndpointSpan
    (n : ℕ) (hn4 : n ≥ 4) :
    (1 : MvPolynomial (Fin n) ℚ) ∈ concreteWEndpointSpan n hn4 := by
  unfold concreteWEndpointSpan
  exact Submodule.subset_span (by simp)

private theorem endpoint0_mem_concreteWEndpointSpan
    (n : ℕ) (hn4 : n ≥ 4) :
    MvPolynomial.X (concreteWEndpoint0 n hn4) ∈
      concreteWEndpointSpan n hn4 := by
  unfold concreteWEndpointSpan
  exact Submodule.subset_span (by simp)

private theorem endpoint1_mem_concreteWEndpointSpan
    (n : ℕ) (hn4 : n ≥ 4) :
    MvPolynomial.X (concreteWEndpoint1 n hn4) ∈
      concreteWEndpointSpan n hn4 := by
  unfold concreteWEndpointSpan
  exact Submodule.subset_span (by simp)

private theorem endpoint0_ne_endpoint1
    (n : ℕ) (hn4 : n ≥ 4) :
    concreteWEndpoint0 n hn4 ≠ concreteWEndpoint1 n hn4 := by
  intro h
  have h01 :
      (0 : Fin 4) = (1 : Fin 4) :=
    (Fin.castLEEmb hn4).injective h
  norm_num at h01

private theorem pderiv_endpoint0_mem_concreteWEndpointSpan
    (n : ℕ) (hn4 : n ≥ 4) (i : Fin n) :
    MvPolynomial.pderiv (R := ℚ) i
        (MvPolynomial.X (concreteWEndpoint0 n hn4) :
          MvPolynomial (Fin n) ℚ) ∈
      concreteWEndpointSpan n hn4 := by
  by_cases hi : i = concreteWEndpoint0 n hn4
  · subst i
    simpa using one_mem_concreteWEndpointSpan n hn4
  · have hne : concreteWEndpoint0 n hn4 ≠ i := by
      intro h
      exact hi h.symm
    rw [MvPolynomial.pderiv_X_of_ne hne]
    exact Submodule.zero_mem _

private theorem pderiv_endpoint1_mem_concreteWEndpointSpan
    (n : ℕ) (hn4 : n ≥ 4) (i : Fin n) :
    MvPolynomial.pderiv (R := ℚ) i
        (MvPolynomial.X (concreteWEndpoint1 n hn4) :
          MvPolynomial (Fin n) ℚ) ∈
      concreteWEndpointSpan n hn4 := by
  by_cases hi : i = concreteWEndpoint1 n hn4
  · subst i
    simpa using one_mem_concreteWEndpointSpan n hn4
  · have hne : concreteWEndpoint1 n hn4 ≠ i := by
      intro h
      exact hi h.symm
    rw [MvPolynomial.pderiv_X_of_ne hne]
    exact Submodule.zero_mem _

private theorem pderiv_endpoint0_sq_mem_concreteWEndpointSpan
    (n : ℕ) (hn4 : n ≥ 4) (i : Fin n) :
    MvPolynomial.pderiv (R := ℚ) i
        ((MvPolynomial.X (concreteWEndpoint0 n hn4) :
          MvPolynomial (Fin n) ℚ) ^ 2) ∈
      concreteWEndpointSpan n hn4 := by
  by_cases hi : i = concreteWEndpoint0 n hn4
  · subst i
    rw [pow_two, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self]
    simpa using
      Submodule.add_mem (concreteWEndpointSpan n hn4)
        (endpoint0_mem_concreteWEndpointSpan n hn4)
        (endpoint0_mem_concreteWEndpointSpan n hn4)
  · have hne : concreteWEndpoint0 n hn4 ≠ i := by
      intro h
      exact hi h.symm
    rw [pow_two, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_of_ne hne]
    simp

private theorem pderiv_endpoint0_mul_endpoint1_mem_concreteWEndpointSpan
    (n : ℕ) (hn4 : n ≥ 4) (i : Fin n) :
    MvPolynomial.pderiv (R := ℚ) i
        (MvPolynomial.X (concreteWEndpoint0 n hn4) *
          MvPolynomial.X (concreteWEndpoint1 n hn4) :
            MvPolynomial (Fin n) ℚ) ∈
      concreteWEndpointSpan n hn4 := by
  by_cases hi0 : i = concreteWEndpoint0 n hn4
  · subst i
    have h10 : concreteWEndpoint1 n hn4 ≠ concreteWEndpoint0 n hn4 :=
      (endpoint0_ne_endpoint1 n hn4).symm
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self,
      MvPolynomial.pderiv_X_of_ne h10]
    simpa using endpoint1_mem_concreteWEndpointSpan n hn4
  · by_cases hi1 : i = concreteWEndpoint1 n hn4
    · subst i
      have h01 : concreteWEndpoint0 n hn4 ≠ concreteWEndpoint1 n hn4 :=
        endpoint0_ne_endpoint1 n hn4
      rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_of_ne h01,
        MvPolynomial.pderiv_X_self]
      simpa using endpoint0_mem_concreteWEndpointSpan n hn4
    · have h0 : concreteWEndpoint0 n hn4 ≠ i := by
        intro h
        exact hi0 h.symm
      have h1 : concreteWEndpoint1 n hn4 ≠ i := by
        intro h
        exact hi1 h.symm
      rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_of_ne h0,
        MvPolynomial.pderiv_X_of_ne h1]
      simp

/-- The endpoint repair space is closed under one partial derivative. -/
theorem concreteWEndpointSpan_pderiv_mem
    (n : ℕ) (hn4 : n ≥ 4) (i : Fin n)
    {p : MvPolynomial (Fin n) ℚ}
    (hp : p ∈ concreteWEndpointSpan n hn4) :
    MvPolynomial.pderiv (R := ℚ) i p ∈ concreteWEndpointSpan n hn4 := by
  unfold concreteWEndpointSpan at hp ⊢
  refine Submodule.span_induction
    (s := ({(1 : MvPolynomial (Fin n) ℚ),
      MvPolynomial.X (concreteWEndpoint0 n hn4),
      MvPolynomial.X (concreteWEndpoint1 n hn4)} :
        Set (MvPolynomial (Fin n) ℚ)))
    (p := fun q _ =>
      MvPolynomial.pderiv (R := ℚ) i q ∈
        Submodule.span ℚ
          ({(1 : MvPolynomial (Fin n) ℚ),
            MvPolynomial.X (concreteWEndpoint0 n hn4),
            MvPolynomial.X (concreteWEndpoint1 n hn4)} :
              Set (MvPolynomial (Fin n) ℚ)))
    ?_ ?_ ?_ ?_ hp
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · simp
    · simpa [concreteWEndpointSpan] using
        pderiv_endpoint0_mem_concreteWEndpointSpan n hn4 i
    · simpa [concreteWEndpointSpan] using
        pderiv_endpoint1_mem_concreteWEndpointSpan n hn4 i
  · simp
  · intro p q _ _ hp hq
    simpa [map_add] using Submodule.add_mem _ hp hq
  · intro a p _ hp
    simpa using Submodule.smul_mem _ a hp

private theorem pderiv_rename_mem_concreteWEndpointSpan_of_source_mem
    (n : ℕ) (hn4 : n ≥ 4) (τ : ConstraintType) (i : Fin n)
    {p : MvPolynomial (Fin 4) ℚ}
    (hp : p ∈ perTypeInterfaceSpace τ) :
    MvPolynomial.pderiv (R := ℚ) i
        (MvPolynomial.rename
          ((Fin.castLEEmb hn4 : Fin 4 ↪ Fin n).toFun) p) ∈
      concreteWEndpointSpan n hn4 := by
  cases τ with
  | booleanity =>
      unfold perTypeInterfaceSpace at hp
      refine Submodule.span_induction
        (s := ({(1 : MvPolynomial (Fin 4) ℚ),
          MvPolynomial.X (0 : Fin 4),
          (MvPolynomial.X (0 : Fin 4)) ^ 2} :
            Set (MvPolynomial (Fin 4) ℚ)))
        (p := fun q _ =>
          MvPolynomial.pderiv (R := ℚ) i
              (MvPolynomial.rename
                ((Fin.castLEEmb hn4 : Fin 4 ↪ Fin n).toFun) q) ∈
            concreteWEndpointSpan n hn4)
        ?_ ?_ ?_ ?_ hp
      · intro q hq
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
        rcases hq with rfl | rfl | rfl
        · simp
        · simpa [concreteWEndpoint0] using
            pderiv_endpoint0_mem_concreteWEndpointSpan n hn4 i
        · simpa [concreteWEndpoint0] using
            pderiv_endpoint0_sq_mem_concreteWEndpointSpan n hn4 i
      · simp
      · intro p q _ _ hp hq
        simpa [map_add] using Submodule.add_mem _ hp hq
      · intro a p _ hp
        simpa using Submodule.smul_mem _ a hp
  | adjacency =>
      unfold perTypeInterfaceSpace at hp
      refine Submodule.span_induction
        (s := ({(1 : MvPolynomial (Fin 4) ℚ),
          MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (1 : Fin 4)} :
            Set (MvPolynomial (Fin 4) ℚ)))
        (p := fun q _ =>
          MvPolynomial.pderiv (R := ℚ) i
              (MvPolynomial.rename
                ((Fin.castLEEmb hn4 : Fin 4 ↪ Fin n).toFun) q) ∈
            concreteWEndpointSpan n hn4)
        ?_ ?_ ?_ ?_ hp
      · intro q hq
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
        rcases hq with rfl | rfl
        · simp
        · simpa [concreteWEndpoint0, concreteWEndpoint1] using
            pderiv_endpoint0_mul_endpoint1_mem_concreteWEndpointSpan n hn4 i
      · simp
      · intro p q _ _ hp hq
        simpa [map_add] using Submodule.add_mem _ hp hq
      · intro a p _ hp
        simpa using Submodule.smul_mem _ a hp
  | transitionLeft =>
      unfold perTypeInterfaceSpace at hp
      refine Submodule.span_induction
        (s := ({(1 : MvPolynomial (Fin 4) ℚ),
          MvPolynomial.X (0 : Fin 4)} :
            Set (MvPolynomial (Fin 4) ℚ)))
        (p := fun q _ =>
          MvPolynomial.pderiv (R := ℚ) i
              (MvPolynomial.rename
                ((Fin.castLEEmb hn4 : Fin 4 ↪ Fin n).toFun) q) ∈
            concreteWEndpointSpan n hn4)
        ?_ ?_ ?_ ?_ hp
      · intro q hq
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
        rcases hq with rfl | rfl
        · simp
        · simpa [concreteWEndpoint0] using
            pderiv_endpoint0_mem_concreteWEndpointSpan n hn4 i
      · simp
      · intro p q _ _ hp hq
        simpa [map_add] using Submodule.add_mem _ hp hq
      · intro a p _ hp
        simpa using Submodule.smul_mem _ a hp
  | transitionRight =>
      unfold perTypeInterfaceSpace at hp
      have hp0 : p = 0 := by
        simpa using hp
      subst p
      simp

/-- One-step derivative closure for the endpoint-augmented canonical concreteW
family. -/
theorem endpointAugmentedConcreteW_pderiv_mem
    (n : ℕ) (hn4 : n ≥ 4) (τ : ConstraintType) (i : Fin n)
    {p : MvPolynomial (Fin n) ℚ}
    (hp : p ∈ endpointAugmentedConcreteW n hn4 τ) :
    MvPolynomial.pderiv (R := ℚ) i p ∈ endpointAugmentedConcreteW n hn4 τ := by
  classical
  rw [endpointAugmentedConcreteW, Submodule.mem_sup] at hp
  obtain ⟨pc, hpc, pe, hpe, hp_eq⟩ := hp
  rw [← hp_eq, map_add]
  refine Submodule.add_mem _ ?_ ?_
  · have hpc' :
        MvPolynomial.pderiv (R := ℚ) i pc ∈
          concreteWEndpointSpan n hn4 := by
      unfold concreteWCanonical concreteW at hpc
      unfold ambientPerTypeSpace at hpc
      rw [Submodule.mem_map] at hpc
      obtain ⟨q, hq, hqeq⟩ := hpc
      rw [← hqeq]
      exact pderiv_rename_mem_concreteWEndpointSpan_of_source_mem
        n hn4 τ i hq
    exact Submodule.mem_sup_right hpc'
  · exact Submodule.mem_sup_right
      (concreteWEndpointSpan_pderiv_mem n hn4 i hpe)

private theorem iterDerivList_mem_of_pderiv_mem
    {n : ℕ}
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hstep :
      ∀ (τ : ConstraintType) (i : Fin n) {p : MvPolynomial (Fin n) ℚ},
        p ∈ W τ → MvPolynomial.pderiv (R := ℚ) i p ∈ W τ)
    (τ : ConstraintType) (S : List (Fin n))
    {p : MvPolynomial (Fin n) ℚ}
    (hp : p ∈ W τ) :
    SPDP.iterDerivList S p ∈ W τ := by
  induction S generalizing p with
  | nil =>
      simpa [SPDP.iterDerivList] using hp
  | cons i rest ih =>
      simpa [SPDP.iterDerivList] using
        ih (hstep τ i hp)

/-- Generic conversion from one-step closure to the H4 interface used by H5. -/
theorem derivClosurePerType_of_pderiv_mem
    {n : ℕ}
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hstep :
      ∀ (τ : ConstraintType) (i : Fin n) {p : MvPolynomial (Fin n) ℚ},
        p ∈ W τ → MvPolynomial.pderiv (R := ℚ) i p ∈ W τ) :
    DerivClosurePerType (n := n) W := by
  intro τ S _hS
  refine Submodule.span_le.mpr ?_
  rintro q ⟨p, hp, rfl⟩
  exact iterDerivList_mem_of_pderiv_mem W hstep τ S hp

/-- H4 for the endpoint-augmented canonical concreteW family. -/
theorem endpointAugmentedConcreteW_derivClosurePerType
    (n : ℕ) (hn4 : n ≥ 4) :
    DerivClosurePerType (n := n) (endpointAugmentedConcreteW n hn4) :=
  derivClosurePerType_of_pderiv_mem (endpointAugmentedConcreteW n hn4)
    (fun τ i {p} hp =>
      endpointAugmentedConcreteW_pderiv_mem n hn4 τ i (p := p) hp)

#print axioms concreteWEndpointSpan_pderiv_mem
#print axioms endpointAugmentedConcreteW_pderiv_mem
#print axioms derivClosurePerType_of_pderiv_mem
#print axioms endpointAugmentedConcreteW_derivClosurePerType

end PallLean.Paper93.DeepMath.PathB
