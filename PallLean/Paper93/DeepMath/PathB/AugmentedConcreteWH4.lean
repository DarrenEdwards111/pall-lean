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

private theorem endpoint_triple_card_le_three
    {α : Type*} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Finset α).card ≤ 3 := by
  have h1 :
      (insert a (insert b ({c} : Finset α))).card
        ≤ (insert b ({c} : Finset α)).card + 1 :=
    Finset.card_insert_le _ _
  have h2 :
      (insert b ({c} : Finset α)).card
        ≤ ({c} : Finset α).card + 1 :=
    Finset.card_insert_le _ _
  have h3 : ({c} : Finset α).card = 1 := Finset.card_singleton _
  have hEq :
      ({a, b, c} : Finset α) = insert a (insert b ({c} : Finset α)) :=
    rfl
  rw [hEq]
  calc (insert a (insert b ({c} : Finset α))).card
      ≤ (insert b ({c} : Finset α)).card + 1 := h1
    _ ≤ (({c} : Finset α).card + 1) + 1 := Nat.add_le_add_right h2 1
    _ = (1 + 1) + 1 := by rw [h3]
    _ = 3 := by norm_num

/-- The endpoint repair span is finite-dimensional. -/
theorem concreteWEndpointSpan_finite
    (n : ℕ) (hn4 : n ≥ 4) :
    Module.Finite ℚ ↥(concreteWEndpointSpan n hn4) := by
  unfold concreteWEndpointSpan
  exact Module.Finite.span_of_finite ℚ
    (Set.Finite.insert _
      (Set.Finite.insert _ (Set.finite_singleton _)))

/-- The endpoint repair span has dimension at most three. -/
theorem concreteWEndpointSpan_finrank_le_three
    (n : ℕ) (hn4 : n ≥ 4) :
    Module.finrank ℚ ↥(concreteWEndpointSpan n hn4) ≤ 3 := by
  unfold concreteWEndpointSpan
  calc
    Module.finrank ℚ
        ↥(Submodule.span ℚ
          ({(1 : MvPolynomial (Fin n) ℚ),
            MvPolynomial.X (concreteWEndpoint0 n hn4),
            MvPolynomial.X (concreteWEndpoint1 n hn4)} :
              Set (MvPolynomial (Fin n) ℚ)))
        ≤ ({(1 : MvPolynomial (Fin n) ℚ),
              MvPolynomial.X (concreteWEndpoint0 n hn4),
              MvPolynomial.X (concreteWEndpoint1 n hn4)} :
              Finset (MvPolynomial (Fin n) ℚ)).card := by
          simpa using
            finrank_span_le_card (R := ℚ)
              (s := ({(1 : MvPolynomial (Fin n) ℚ),
                MvPolynomial.X (concreteWEndpoint0 n hn4),
                MvPolynomial.X (concreteWEndpoint1 n hn4)} :
                  Set (MvPolynomial (Fin n) ℚ)))
    _ ≤ 3 :=
      endpoint_triple_card_le_three
        (1 : MvPolynomial (Fin n) ℚ)
        (MvPolynomial.X (concreteWEndpoint0 n hn4))
        (MvPolynomial.X (concreteWEndpoint1 n hn4))

/-- The endpoint-augmented family is finite-dimensional, but not through the
old dimension-`≤ 3` template route. -/
theorem endpointAugmentedConcreteW_finite
    (n : ℕ) (hn4 : n ≥ 4) (τ : ConstraintType) :
    Module.Finite ℚ ↥(endpointAugmentedConcreteW n hn4 τ) := by
  haveI hcanon :
      Module.Finite ℚ ↥(concreteWCanonical n hn4 τ) := by
    unfold concreteWCanonical
    exact PallLean.Paper93.Wiring.concreteW_finite
      n hn4 (Fin.castLEEmb hn4) τ
  haveI hendpoint :
      Module.Finite ℚ ↥(concreteWEndpointSpan n hn4) :=
    concreteWEndpointSpan_finite n hn4
  unfold endpointAugmentedConcreteW
  exact
    Submodule.finite_sup
      (concreteWCanonical n hn4 τ)
      (concreteWEndpointSpan n hn4)

/-- The literal endpoint augmentation has a six-dimensional upper bound:
canonical concreteW contributes at most three dimensions and the endpoint
repair span contributes at most three more.  This is intentionally weaker
than the paper's profile-template budget and records why the old `≤ 3`
budget route does not close automatically after endpoint augmentation. -/
theorem endpointAugmentedConcreteW_finrank_le_six
    (n : ℕ) (hn4 : n ≥ 4) (τ : ConstraintType) :
    Module.finrank ℚ ↥(endpointAugmentedConcreteW n hn4 τ) ≤ 6 := by
  haveI hcanon :
      Module.Finite ℚ ↥(concreteWCanonical n hn4 τ) := by
    unfold concreteWCanonical
    exact PallLean.Paper93.Wiring.concreteW_finite
      n hn4 (Fin.castLEEmb hn4) τ
  haveI hendpoint :
      Module.Finite ℚ ↥(concreteWEndpointSpan n hn4) :=
    concreteWEndpointSpan_finite n hn4
  have hcanon_le :
      Module.finrank ℚ ↥(concreteWCanonical n hn4 τ) ≤ 3 := by
    unfold concreteWCanonical
    exact PallLean.Paper93.Wiring.concreteW_finrank_le_three
      n hn4 (Fin.castLEEmb hn4) τ
  have hendpoint_le :
      Module.finrank ℚ ↥(concreteWEndpointSpan n hn4) ≤ 3 :=
    concreteWEndpointSpan_finrank_le_three n hn4
  have hsup :=
    Submodule.finrank_sup_add_finrank_inf_eq
      (concreteWCanonical n hn4 τ)
      (concreteWEndpointSpan n hn4)
  unfold endpointAugmentedConcreteW
  omega

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

/-! ## Fixed-row endpoint-augmentation obstruction for arbitrary branches -/

private lemma single_one_ne_single_two_of_ne
    {n : ℕ} {v w : Fin n} (h : v ≠ w) :
    Finsupp.single w 1 ≠ Finsupp.single v 2 := by
  intro heq
  have hw := congrArg (fun f : Fin n →₀ ℕ => f w) heq
  simp [h.symm] at hw

private lemma single_two_ne_single_two_of_ne
    {n : ℕ} {v w : Fin n} (h : v ≠ w) :
    Finsupp.single w 2 ≠ Finsupp.single v 2 := by
  intro heq
  have hw := congrArg (fun f : Fin n →₀ ℕ => f w) heq
  simp [h.symm] at hw

private lemma zero_ne_single_two
    {n : ℕ} (v : Fin n) :
    (0 : Fin n →₀ ℕ) ≠ Finsupp.single v 2 := by
  intro heq
  have hv := congrArg (fun f : Fin n →₀ ℕ => f v) heq
  simp at hv

/-- Endpoint-span elements have no square monomial away from the two fixed
endpoint variables. -/
theorem concreteWEndpointSpan_coeff_square_eq_zero_of_ne_endpoints
    {n : ℕ} {hn4 : n ≥ 4} {v : Fin n}
    (hv0 : v ≠ concreteWEndpoint0 n hn4)
    (hv1 : v ≠ concreteWEndpoint1 n hn4)
    {p : MvPolynomial (Fin n) ℚ}
    (hp : p ∈ concreteWEndpointSpan n hn4) :
    MvPolynomial.coeff (Finsupp.single v 2) p = 0 := by
  unfold concreteWEndpointSpan at hp
  refine Submodule.span_induction
    (p := fun q _ => MvPolynomial.coeff (Finsupp.single v 2) q = 0)
    ?_ ?_ ?_ ?_ hp
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · simp [MvPolynomial.coeff_one, zero_ne_single_two]
    · simp [MvPolynomial.coeff_X',
        single_one_ne_single_two_of_ne hv0]
    · simp [MvPolynomial.coeff_X',
        single_one_ne_single_two_of_ne hv1]
  · simp
  · intro p q _ _ hp hq
    simp [hp, hq]
  · intro a p _ hp
    simp [hp]

private theorem concreteWCanonical_booleanity_coeff_square_eq_zero_of_ne_endpoint0
    {n : ℕ} {hn4 : n ≥ 4} {v : Fin n}
    (hv0 : v ≠ concreteWEndpoint0 n hn4)
    {p : MvPolynomial (Fin n) ℚ}
    (hp : p ∈ concreteWCanonical n hn4 ConstraintType.booleanity) :
    MvPolynomial.coeff (Finsupp.single v 2) p = 0 := by
  unfold concreteWCanonical concreteW at hp
  unfold ambientPerTypeSpace at hp
  rw [Submodule.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  unfold perTypeInterfaceSpace at hq
  refine Submodule.span_induction
    (p := fun q _ =>
      MvPolynomial.coeff (Finsupp.single v 2)
          (MvPolynomial.rename
            (Fin.castLE hn4) q) = 0)
    ?_ ?_ ?_ ?_ hq
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · simp [MvPolynomial.coeff_one, zero_ne_single_two]
    · have hrename :
          MvPolynomial.rename (Fin.castLE hn4)
              (MvPolynomial.X (0 : Fin 4)) =
            (MvPolynomial.X (concreteWEndpoint0 n hn4) :
              MvPolynomial (Fin n) ℚ) := by
        simp [concreteWEndpoint0]
      rw [hrename]
      simp [MvPolynomial.coeff_X',
        single_one_ne_single_two_of_ne hv0]
    · have hrename :
          MvPolynomial.rename (Fin.castLE hn4)
              ((MvPolynomial.X (0 : Fin 4)) ^ 2) =
            ((MvPolynomial.X (concreteWEndpoint0 n hn4) :
              MvPolynomial (Fin n) ℚ) ^ 2) := by
        simp [concreteWEndpoint0]
      rw [hrename]
      simp [MvPolynomial.X_pow_eq_monomial,
        single_two_ne_single_two_of_ne hv0]
  · simp
  · intro p q _ _ hp hq
    simp [map_add, hp, hq]
  · intro a p _ hp
    simp [hp]

/-- The fixed endpoint-augmented booleanity space cannot contain an
`X_v^2` coefficient away from the canonical boolean endpoint and the added
second endpoint. -/
theorem endpointAugmentedConcreteW_booleanity_coeff_square_eq_zero_of_ne_endpoints
    {n : ℕ} {hn4 : n ≥ 4} {v : Fin n}
    (hv0 : v ≠ concreteWEndpoint0 n hn4)
    (hv1 : v ≠ concreteWEndpoint1 n hn4)
    {p : MvPolynomial (Fin n) ℚ}
    (hp : p ∈ endpointAugmentedConcreteW n hn4 ConstraintType.booleanity) :
    MvPolynomial.coeff (Finsupp.single v 2) p = 0 := by
  rw [endpointAugmentedConcreteW, Submodule.mem_sup] at hp
  obtain ⟨pc, hpc, pe, hpe, hp_eq⟩ := hp
  rw [← hp_eq]
  simp
    [concreteWCanonical_booleanity_coeff_square_eq_zero_of_ne_endpoint0
      hv0 hpc,
     concreteWEndpointSpan_coeff_square_eq_zero_of_ne_endpoints
      hv0 hv1 hpe]

private lemma single_one_ne_single_two
    {n : ℕ} (v : Fin n) :
    Finsupp.single v 1 ≠ Finsupp.single v 2 := by
  intro heq
  have hv := congrArg (fun f : Fin n →₀ ℕ => f v) heq
  simp at hv

/-- Concrete obstruction to using arbitrary direct booleanity branch shapes
with the fixed endpoint-augmented target: a booleanity factor at a variable
outside the two endpoint coordinates has a nonzero `X_v^2` coefficient, while
the target space has zero such coefficient. -/
theorem booleanity_directBranchFactor_not_mem_endpointAugmentedConcreteW_of_ne_endpoints
    {n : ℕ} {hn4 : n ≥ 4} {v : Fin n}
    (hv0 : v ≠ concreteWEndpoint0 n hn4)
    (hv1 : v ≠ concreteWEndpoint1 n hn4) :
    (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
        MvPolynomial (Fin n) ℚ)
      ∉ endpointAugmentedConcreteW n hn4 ConstraintType.booleanity := by
  intro hp
  have hzero :=
    endpointAugmentedConcreteW_booleanity_coeff_square_eq_zero_of_ne_endpoints
      hv0 hv1 hp
  have hone :
      MvPolynomial.coeff (Finsupp.single v 2)
        (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
          MvPolynomial (Fin n) ℚ) = 1 := by
    simp [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_X',
      MvPolynomial.coeff_one, single_one_ne_single_two, zero_ne_single_two]
  rw [hone] at hzero
  norm_num at hzero

#print axioms concreteWEndpointSpan_finite
#print axioms concreteWEndpointSpan_finrank_le_three
#print axioms endpointAugmentedConcreteW_finite
#print axioms endpointAugmentedConcreteW_finrank_le_six
#print axioms concreteWEndpointSpan_coeff_square_eq_zero_of_ne_endpoints
#print axioms endpointAugmentedConcreteW_booleanity_coeff_square_eq_zero_of_ne_endpoints
#print axioms booleanity_directBranchFactor_not_mem_endpointAugmentedConcreteW_of_ne_endpoints

#print axioms concreteWEndpointSpan_pderiv_mem
#print axioms endpointAugmentedConcreteW_pderiv_mem
#print axioms derivClosurePerType_of_pderiv_mem
#print axioms endpointAugmentedConcreteW_derivClosurePerType

end PallLean.Paper93.DeepMath.PathB
