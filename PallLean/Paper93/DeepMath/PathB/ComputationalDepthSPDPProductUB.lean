import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSPDPDynamic

/-!
# The upper-bound half of the SPDP wall: products have small shifted-partial-derivative rank

The lower-bound half (`ComputationalDepthBlockPermRank{LB,Exp}.lean`) showed the permanent has *large* SPDP rank
(`C(k,κ)²`, exponential).  The separation method also needs the **upper bound**: polynomials from a restricted circuit
class have *small* SPDP rank.  This file proves the core upper bound — the mathematical heart of the method:

  `spdpSubspace_prod_le` — for `f = ∏_{j=1}^m Q_j` with each `deg Q_j ≤ t`, the order-`κ` SPDP subspace satisfies
        `spdpSubspace κ 0 f ≤ prodDerivSpace Q t κ`, where
        `prodDerivSpace Q t κ = span{ (∏_{j∉J} Q_j)·M : |J| ≤ κ, deg M ≤ κt }`.
  `spdpRank_prod_le` — hence `spdpRank κ 0 (∏ Q_j) ≤ finrank (prodDerivSpace Q t κ)`, and that space is spanned by
        `(#{J : |J|≤κ}) · (#monomials of degree ≤ κt)` generators — **small** when `m`, `κ`, `t` are small.
  `spdpRank_sum_le` — subadditivity over a sum: a depth-`4` circuit `∑_{i=1}^s ∏_j Q_{ij}` has
        `spdpRank κ 0 ≤ ∑_i spdpRank κ 0 (∏_j Q_{ij})`, i.e. `≤ s · (single-product bound)`.

## Why this is the *restricted* wall, not `P ≠ NP`

The key structural fact: each derivative of a product touches at most `κ` of the `m` factors (`κ` derivatives, one
factor each), so `∂_S(∏Q_j)` lies in `span{(∏_{j∉J}Q_j)·M : |J|≤κ}` with `M` of controlled degree — a space far
smaller than the ambient when the circuit is shallow.  Combined with the exponential lower bound, this gives a genuine
**restricted separation**: the permanent has no small depth-`4` circuit with bounded bottom fan-in (the GKKS-style
lower bounds).  It is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`: the *full* wall would need "every poly-size circuit ⟹ small
SPDP rank", which is false / `P`-vs-`NP`-strength — SPDP rank does not upper-bound general circuits.  This file proves
exactly the honest, provable half: the upper bound for the shallow/product model.
-/

namespace PallLean.Paper93.DeepMath.PathB.SPDPUpperBound

open MvPolynomial Finset

variable {n m t : ℕ} {F : Type*} [Field F]

/-- Product rule for `pderiv` over a finset (proved by induction). -/
theorem pderiv_prod {ι : Type*} [DecidableEq ι] (i : Fin n) (s : Finset ι)
    (g : ι → MvPolynomial (Fin n) F) :
    pderiv i (∏ j ∈ s, g j) = ∑ j ∈ s, (pderiv i (g j)) * ∏ j' ∈ s.erase j, g j' := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, pderiv_mul, ih, Finset.sum_insert ha, Finset.erase_insert ha]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.erase_insert_of_ne (by rintro rfl; exact ha hj), Finset.prod_insert
      (fun h => ha (Finset.mem_of_mem_erase h)), ← mul_assoc, mul_comm (g a), mul_assoc]

/-- The low-complexity space containing the shifted partial derivatives of a product:
`span{ (∏_{j∉J} Q_j)·M : |J| ≤ κ, deg M ≤ κt }`. -/
noncomputable def prodDerivSpace (Q : Fin m → MvPolynomial (Fin n) F) (t κ : ℕ) :
    Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F { p | ∃ (J : Finset (Fin m)) (M : MvPolynomial (Fin n) F),
    J.card ≤ κ ∧ M.totalDegree ≤ κ * t ∧ p = (∏ j ∈ Jᶜ, Q j) * M }

/-- A generator is in the space. -/
theorem gen_mem_prodDerivSpace (Q : Fin m → MvPolynomial (Fin n) F) (t κ : ℕ)
    (J : Finset (Fin m)) (M : MvPolynomial (Fin n) F) (hJ : J.card ≤ κ) (hM : M.totalDegree ≤ κ * t) :
    (∏ j ∈ Jᶜ, Q j) * M ∈ prodDerivSpace Q t κ :=
  Submodule.subset_span ⟨J, M, hJ, hM, rfl⟩

/-- **L1**: the product itself is a level-`0` element. -/
theorem prod_mem_prodDerivSpace_zero (Q : Fin m → MvPolynomial (Fin n) F) (t : ℕ) :
    (∏ j, Q j) ∈ prodDerivSpace Q t 0 := by
  have := gen_mem_prodDerivSpace Q t 0 ∅ 1 (by simp) (by simp)
  simpa using this

/-- **L2**: one derivative raises the level by one — `pderiv i` maps `prodDerivSpace κ` into `prodDerivSpace (κ+1)`. -/
theorem pderiv_mem_prodDerivSpace (Q : Fin m → MvPolynomial (Fin n) F)
    (ht : ∀ j, (Q j).totalDegree ≤ t) (κ : ℕ) (i : Fin n) (p : MvPolynomial (Fin n) F)
    (hp : p ∈ prodDerivSpace Q t κ) : pderiv i p ∈ prodDerivSpace Q t (κ + 1) := by
  classical
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨J, M, hJ, hM, rfl⟩ := hx
    -- pderiv i ((∏_{Jᶜ} Q) * M) = (pderiv i ∏_{Jᶜ} Q) * M + (∏_{Jᶜ} Q) * pderiv i M
    rw [pderiv_mul, pderiv_prod, Finset.sum_mul]
    refine Submodule.add_mem _ (Submodule.sum_mem _ (fun a ha => ?_)) ?_
    · -- term for factor a ∈ Jᶜ : (∏_{(insert a J)ᶜ} Q) * (pderiv i (Q a) * M)
      have hcompl : Jᶜ.erase a = (insert a J)ᶜ := by rw [Finset.compl_insert]
      have hdeg : (pderiv i (Q a) * M).totalDegree ≤ (κ + 1) * t := by
        calc (pderiv i (Q a) * M).totalDegree
            ≤ (pderiv i (Q a)).totalDegree + M.totalDegree := MvPolynomial.totalDegree_mul _ _
          _ ≤ t + κ * t := Nat.add_le_add (le_trans (NFrameSPDPBridge.pderiv_totalDegree_le i (Q a)) (ht a)) hM
          _ = (κ + 1) * t := by ring
      have hcard : (insert a J).card ≤ κ + 1 :=
        le_trans (Finset.card_insert_le a J) (Nat.add_le_add_right hJ 1)
      have hmem := gen_mem_prodDerivSpace Q t (κ + 1) (insert a J) (pderiv i (Q a) * M) hcard hdeg
      rw [← hcompl] at hmem
      rw [show ((pderiv i (Q a)) * (∏ j' ∈ Jᶜ.erase a, Q j')) * M
            = (∏ j' ∈ Jᶜ.erase a, Q j') * (pderiv i (Q a) * M) by ring]
      exact hmem
    · -- term (∏_{Jᶜ} Q) * pderiv i M
      exact gen_mem_prodDerivSpace Q t (κ + 1) J (pderiv i M) (le_trans hJ (Nat.le_succ κ))
        (le_trans (NFrameSPDPBridge.pderiv_totalDegree_le i M) (le_trans hM
          (Nat.mul_le_mul_right t (Nat.le_succ κ))))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add,
      ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

/-- **L3**: iterating `κ` derivatives lands in level `κ` (from a level-`0` start). -/
theorem iterDerivList_mem_prodDerivSpace (Q : Fin m → MvPolynomial (Fin n) F)
    (ht : ∀ j, (Q j).totalDegree ≤ t) (S : List (Fin n)) (κ : ℕ) (p : MvPolynomial (Fin n) F)
    (hp : p ∈ prodDerivSpace Q t κ) : SPDP.iterDerivList S p ∈ prodDerivSpace Q t (κ + S.length) := by
  induction S generalizing p κ with
  | nil => simpa using hp
  | cons i S' ih =>
    have hstep : SPDP.iterDerivList (i :: S') p = SPDP.iterDerivList S' (pderiv i p) := rfl
    rw [hstep]
    have hstep2 := ih (κ + 1) (pderiv i p) (pderiv_mem_prodDerivSpace Q ht κ i p hp)
    rwa [show κ + 1 + S'.length = κ + (i :: S').length by rw [List.length_cons]; ring] at hstep2

/-- **The core upper bound (proved)**: the order-`κ` SPDP subspace of a product is contained in the low-complexity
space `prodDerivSpace Q t κ`. -/
theorem spdpSubspace_prod_le (Q : Fin m → MvPolynomial (Fin n) F) (ht : ∀ j, (Q j).totalDegree ≤ t) (κ : ℕ) :
    SPDP.spdpSubspace κ 0 (∏ j, Q j) ≤ prodDerivSpace Q t κ := by
  classical
  rw [SPDP.spdpSubspace, Submodule.span_le]
  rintro _ ⟨S, M, hSlen, hMdeg, rfl⟩
  rw [SetLike.mem_coe]
  -- M has degree ≤ 0, so M = C c is a scalar; the derivative is in prodDerivSpace κ
  have hderiv : SPDP.iterDerivList S (∏ j, Q j) ∈ prodDerivSpace Q t κ := by
    have := iterDerivList_mem_prodDerivSpace Q ht S 0 _ (prod_mem_prodDerivSpace_zero Q t)
    rwa [Nat.zero_add, hSlen] at this
  obtain ⟨c, rfl⟩ : ∃ c : F, M = C c :=
    ⟨M.coeff 0, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hMdeg)⟩
  rw [MvPolynomial.C_mul']
  exact Submodule.smul_mem _ _ hderiv

/-- `prodDerivSpace` sits inside a fixed bounded-degree space, hence is finite-dimensional. -/
theorem prodDerivSpace_le_restrict (Q : Fin m → MvPolynomial (Fin n) F) (ht : ∀ j, (Q j).totalDegree ≤ t) (κ : ℕ) :
    prodDerivSpace Q t κ ≤ MvPolynomial.restrictTotalDegree (Fin n) F (m * t + κ * t) := by
  classical
  rw [prodDerivSpace, Submodule.span_le]
  rintro _ ⟨J, M, _, hM, rfl⟩
  rw [SetLike.mem_coe, MvPolynomial.mem_restrictTotalDegree]
  refine le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add ?_ hM)
  refine le_trans (MvPolynomial.totalDegree_finset_prod _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun j _ => ht j)) ?_
  rw [Finset.sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right t (le_trans (Finset.card_le_card (Finset.subset_univ _))
    (by rw [Finset.card_univ, Fintype.card_fin]))

/-- **The single-product SPDP-rank upper bound (proved)**: `spdpRank κ 0 (∏ Q_j) ≤ finrank (prodDerivSpace Q t κ)` —
the derivative rank of a product of `m` factors of degree `≤ t` is bounded by the (small) dimension of the space
spanned by the `≤ κ`-factor-deletions times degree-`≤ κt` shifts. -/
theorem spdpRank_prod_le (Q : Fin m → MvPolynomial (Fin n) F) (ht : ∀ j, (Q j).totalDegree ≤ t) (κ : ℕ) :
    SPDP.spdpRank κ 0 (∏ j, Q j) ≤ Module.finrank F (prodDerivSpace Q t κ) := by
  haveI : FiniteDimensional F (prodDerivSpace Q t κ) :=
    Submodule.finiteDimensional_of_le (prodDerivSpace_le_restrict Q ht κ)
  exact Submodule.finrank_mono (spdpSubspace_prod_le Q ht κ)

/-- **Subadditivity over a finite sum (proved)**: `spdpRank κ ℓ (∑_{i∈s} f i) ≤ ∑_{i∈s} spdpRank κ ℓ (f i)` — the
depth-`4` sum layer.  With `spdpRank_prod_le` this bounds a depth-`4` circuit `∑_i ∏_j Q_{ij}` by
`s · (single-product bound)`. -/
theorem spdpRank_sum_le {ι : Type*} (κ ℓ : ℕ) (s : Finset ι) (f : ι → MvPolynomial (Fin n) F) :
    SPDP.spdpRank κ ℓ (∑ i ∈ s, f i) ≤ ∑ i ∈ s, SPDP.spdpRank κ ℓ (f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    have hbot : SPDP.spdpSubspace κ ℓ (0 : MvPolynomial (Fin n) F) = ⊥ := by
      rw [SPDP.spdpSubspace, Submodule.span_eq_bot]
      rintro x ⟨S, mm, -, -, rfl⟩
      rw [SPDPLowerBound.iterDerivList_zero, mul_zero]
    exact le_of_eq (by rw [SPDP.spdpRank, hbot, finrank_bot])
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (SPDPLowerBound.spdpRank_add_le κ ℓ (f a) (∑ i ∈ s, f i)) (Nat.add_le_add_left ih _)

/-! ### Concrete dimension bound: `finrank(prodDerivSpace) ≤ (#{J:|J|≤κ}) · (#degree-≤κt monomials)` -/

/-- `finrank` of a `Finset.sup` of submodules (all inside a fixed finite-dimensional `W0`) is bounded by the sum of
their `finrank`s. -/
theorem finrank_finset_sup_le {ι : Type*} (s : Finset ι)
    (p : ι → Submodule F (MvPolynomial (Fin n) F))
    (W0 : Submodule F (MvPolynomial (Fin n) F)) [FiniteDimensional F ↥W0] (hle : ∀ i ∈ s, p i ≤ W0) :
    Module.finrank F ↥(s.sup p) ≤ ∑ i ∈ s, Module.finrank F ↥(p i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sup_empty, Finset.sum_empty]; exact le_of_eq (finrank_bot F _)
  | insert a s ha ih =>
    have hsub : s.sup p ≤ W0 := Finset.sup_le (fun i hi => hle i (Finset.mem_insert_of_mem hi))
    haveI : FiniteDimensional F ↥(s.sup p) := Submodule.finiteDimensional_of_le hsub
    haveI : FiniteDimensional F ↥(p a) :=
      Submodule.finiteDimensional_of_le (hle a (Finset.mem_insert_self a s))
    rw [Finset.sup_insert, Finset.sum_insert ha]
    exact le_trans (Submodule.finrank_add_le_finrank_add_finrank _ _)
      (Nat.add_le_add_left (ih (fun i hi => hle i (Finset.mem_insert_of_mem hi))) _)

/-- The `J`-th piece of the decomposition: `(∏_{j∉J} Q_j) · (degree ≤ κt space)`. -/
noncomputable def prodPiece (Q : Fin m → MvPolynomial (Fin n) F) (t κ : ℕ) (J : Finset (Fin m)) :
    Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.map (LinearMap.mulLeft F (∏ j ∈ Jᶜ, Q j)) (MvPolynomial.restrictTotalDegree (Fin n) F (κ * t))

theorem prodPiece_le_restrict (Q : Fin m → MvPolynomial (Fin n) F) (ht : ∀ j, (Q j).totalDegree ≤ t) (κ : ℕ)
    (J : Finset (Fin m)) : prodPiece Q t κ J ≤ MvPolynomial.restrictTotalDegree (Fin n) F (m * t + κ * t) := by
  rw [prodPiece, Submodule.map_le_iff_le_comap]
  intro M hM
  rw [MvPolynomial.mem_restrictTotalDegree] at hM
  rw [Submodule.mem_comap, LinearMap.mulLeft_apply, MvPolynomial.mem_restrictTotalDegree]
  refine le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add ?_ hM)
  refine le_trans (MvPolynomial.totalDegree_finset_prod _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun j _ => ht j)) ?_
  rw [Finset.sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right t (le_trans (Finset.card_le_card (Finset.subset_univ _))
    (by rw [Finset.card_univ, Fintype.card_fin]))

theorem prodDerivSpace_le_sup (Q : Fin m → MvPolynomial (Fin n) F) (t κ : ℕ) :
    prodDerivSpace Q t κ ≤ (Finset.univ.filter (fun J : Finset (Fin m) => J.card ≤ κ)).sup (prodPiece Q t κ) := by
  classical
  rw [prodDerivSpace, Submodule.span_le]
  rintro _ ⟨J, M, hJ, hM, rfl⟩
  have hpiece : (∏ j ∈ Jᶜ, Q j) * M ∈ prodPiece Q t κ J := by
    rw [prodPiece]
    refine Submodule.mem_map_of_mem ?_
    rw [MvPolynomial.mem_restrictTotalDegree]; exact hM
  have hJmem : J ∈ Finset.univ.filter (fun J : Finset (Fin m) => J.card ≤ κ) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ J, hJ⟩
  exact Finset.le_sup (f := prodPiece Q t κ) hJmem hpiece

/-- **The concrete single-product SPDP-rank bound (proved)**: `spdpRank κ 0 (∏_{j=1}^m Q_j)` is at most the number of
`≤ κ`-subsets of the `m` factors times the number of monomials of degree `≤ κt` — an explicit, *small* bound for
shallow circuits. -/
theorem spdpRank_prod_le_card (Q : Fin m → MvPolynomial (Fin n) F) (ht : ∀ j, (Q j).totalDegree ≤ t) (κ : ℕ) :
    SPDP.spdpRank κ 0 (∏ j, Q j)
      ≤ (Finset.univ.filter (fun J : Finset (Fin m) => J.card ≤ κ)).card
          * Module.finrank F ↥(MvPolynomial.restrictTotalDegree (Fin n) F (κ * t)) := by
  classical
  haveI : FiniteDimensional F ↥(MvPolynomial.restrictTotalDegree (Fin n) F (κ * t)) := inferInstance
  haveI : FiniteDimensional F ↥((Finset.univ.filter (fun J : Finset (Fin m) => J.card ≤ κ)).sup (prodPiece Q t κ)) :=
    Submodule.finiteDimensional_of_le (Finset.sup_le (fun J _ => prodPiece_le_restrict Q ht κ J))
  calc SPDP.spdpRank κ 0 (∏ j, Q j)
      ≤ Module.finrank F ↥(prodDerivSpace Q t κ) := spdpRank_prod_le Q ht κ
    _ ≤ Module.finrank F ↥((Finset.univ.filter (fun J : Finset (Fin m) => J.card ≤ κ)).sup (prodPiece Q t κ)) :=
        Submodule.finrank_mono (prodDerivSpace_le_sup Q t κ)
    _ ≤ ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) => J.card ≤ κ), Module.finrank F ↥(prodPiece Q t κ J) :=
        finrank_finset_sup_le _ (prodPiece Q t κ) (MvPolynomial.restrictTotalDegree (Fin n) F (m * t + κ * t))
          (fun J _ => prodPiece_le_restrict Q ht κ J)
    _ ≤ ∑ _J ∈ Finset.univ.filter (fun J : Finset (Fin m) => J.card ≤ κ),
          Module.finrank F ↥(MvPolynomial.restrictTotalDegree (Fin n) F (κ * t)) := by
        refine Finset.sum_le_sum (fun J _ => ?_)
        rw [prodPiece]; exact Submodule.finrank_map_le _ _
    _ = _ := by rw [Finset.sum_const, smul_eq_mul]

end PallLean.Paper93.DeepMath.PathB.SPDPUpperBound

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPUpperBound.spdpSubspace_prod_le
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPUpperBound.spdpRank_prod_le
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPUpperBound.spdpRank_prod_le_card
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPUpperBound.spdpRank_sum_le
