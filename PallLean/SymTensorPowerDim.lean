/-
  SymTensorPowerDim.lean — Symmetric tensor power dimension bound (Paper §9 Lemma 31)

  The stars-and-bars bound `dim Sym^k(W) = C(k + dim(W) - 1, k)` for `dim W ≤ 3`.

  Target theorem: for a finite-dimensional ℚ-submodule W of MvPolynomial N ℚ
  with `finrank ℚ W ≤ 3`, the k-th symmetric power (defined as the submodule
  spanned by k-fold products of elements of W) has finrank ≤ C(k+2, 2).

  Proof strategy:
  1. W is finite-dimensional over ℚ (division ring ⇒ Module.Free), so has a basis
     `b : Basis (Fin d) ℚ W` with `d = finrank ℚ W ≤ 3`.
  2. Every k-fold product of W-elements expands multilinearly as a ℚ-linear
     combination of k-fold products of basis elements `∏ (b (σ i))` for some
     `σ : Fin k → Fin d`.
  3. By commutativity, `∏ (b (σ i))` only depends on the multiset of values of σ,
     i.e. on an element of `Sym (Fin d) k`.
  4. `|Sym (Fin d) k| = multichoose d k = C(d+k-1, k) ≤ C(k+2, 2)` for `d ≤ 3`.
  5. `finrank (symPower k W) ≤ |spanning set| ≤ C(k+2, 2)`.
-/
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic

open Module

namespace PallLean.SymTensorPowerDim

open MvPolynomial

/-! ## Definition of the k-fold symmetric power of a submodule

The "symmetric power" `symPower R k W ⊆ MvPolynomial N R` is the submodule
spanned by k-fold products `∏ (f i)` where `f i ∈ W` for each `i : Fin k`.
This matches the paper's usage in §9 Lemma 31: `Sym^k(W_τ)` for the interface
space `W_τ`. -/

/-- The k-fold symmetric power as a submodule of `MvPolynomial N R`. -/
noncomputable def symPower (R : Type*) [CommSemiring R] {N : Type*}
    (k : ℕ) (W : Submodule R (MvPolynomial N R)) :
    Submodule R (MvPolynomial N R) :=
  Submodule.span R
    { p : MvPolynomial N R |
      ∃ f : Fin k → MvPolynomial N R, (∀ i, f i ∈ W) ∧ p = ∏ i, f i }

/-! ## Stars-and-bars combinatorial bound

`C(k + d - 1, k) ≤ C(k + 2, 2)` when `d ≤ 3`. -/

/-- `C(m + d, d) ≤ C(m + 2, 2)` when `d ≤ 2`. (i.e. `d - 1 ≤ 2` for `d ≤ 3`.) -/
theorem stars_and_bars_pad_le (m d : ℕ) (hd : d ≤ 2) :
    Nat.choose (m + d) d ≤ Nat.choose (m + 2) 2 := by
  -- Monotonicity of `Nat.choose (m + d) d` in `d`:
  -- C(m+0,0) = 1, C(m+1,1) = m+1, C(m+2,2) = (m+2)(m+1)/2.
  -- For d ≤ 2 we just case-split.
  interval_cases d
  · -- d = 0: C(m, 0) = 1 ≤ C(m+2, 2)
    have hcm0 : Nat.choose (m + 0) 0 = 1 := by
      simp
    rw [hcm0]
    -- 1 ≤ C(m+2, 2): since (m+2 choose 2) ≥ (2 choose 2) = 1 by monotonicity.
    have hbase : Nat.choose (0 + 2) 2 = 1 := by decide
    calc 1 = Nat.choose (0 + 2) 2 := hbase.symm
      _ ≤ Nat.choose (m + 2) 2 := Nat.choose_mono 2 (by omega)
  · -- d = 1: C(m+1, 1) = m+1 ≤ C(m+2, 2)
    have hc1 : Nat.choose (m + 1) 1 = m + 1 := by
      simp [Nat.choose_one_right]
    rw [hc1]
    -- C(m+2, 2) = (m+1)(m+2)/2. We want m+1 ≤ (m+2)(m+1)/2.
    -- 2*(m+1) = (m+1) + (m+1) ≤ (m+1) + (m+1)*(m+1) = (m+1)*(m+2). So
    -- (m+1) ≤ (m+1)*(m+2)/2 = C(m+2,2).
    have hkey : 2 * (m + 1) ≤ (m + 1) * (m + 2) := by nlinarith
    -- C(m+2, 2) = (m+2) choose 2 = (m+1)*(m+2)/2 via Nat.choose_two_right
    rw [Nat.choose_two_right]
    -- goal: m + 1 ≤ (m + 2) * (m + 2 - 1) / 2
    have hms : (m + 2) - 1 = m + 1 := by omega
    rw [hms]
    -- goal: m + 1 ≤ (m + 2) * (m + 1) / 2
    -- Use Nat.le_div_iff_mul_le requiring divisor > 0
    refine Nat.le_div_iff_mul_le (by omega) |>.mpr ?_
    -- (m + 1) * 2 ≤ (m + 2) * (m + 1)
    nlinarith
  · -- d = 2: equality
    exact le_refl _

/-- `C(k + d - 1, k) ≤ C(k + 2, 2)` when `d ≤ 3`, i.e. `dim W ≤ 3`.
    (Requires d ≥ 1; for d = 0 the symmetric power is zero.) -/
theorem stars_and_bars_dim3 (k d : ℕ) (hd_pos : 1 ≤ d) (hd : d ≤ 3) :
    Nat.choose (k + d - 1) k ≤ Nat.choose (k + 2) 2 := by
  -- Use C(n, k) = C(n, n - k) to rewrite: let e := d - 1, then k + e = n and n - k = e.
  -- So C(k + d - 1, k) = C(k + e, k) = C(k + e, e) ≤ C(k + 2, 2) since e ≤ 2.
  have he_le : d - 1 ≤ 2 := by omega
  have hadd : k + d - 1 = k + (d - 1) := by omega
  rw [hadd]
  -- C(k + e, k) = C(k + e, e):
  have hsym : Nat.choose (k + (d - 1)) k = Nat.choose (k + (d - 1)) (d - 1) := by
    have hle : k ≤ k + (d - 1) := Nat.le_add_right k (d - 1)
    have := Nat.choose_symm hle
    rw [Nat.add_sub_cancel_left] at this
    exact this.symm
  rw [hsym]
  exact stars_and_bars_pad_le k (d - 1) he_le

/-! ## Main lemma: spanning via multiset products

Given a basis `b : Basis (Fin d) ℚ W`, every k-fold product of elements of W
lies in the ℚ-span of "symmetric products" `∏ᵢ (b (σ i)).val` indexed by
multisets of size k over `Fin d`. -/

variable {N : Type*}

/-- For any `f : Fin k → MvPolynomial N ℚ` with each `f i ∈ W`, the product
    `∏ᵢ f i` lies in the ℚ-span of the ordered basis products
    `{ ∏ᵢ (b (σ i)).val | σ : Fin k → Fin d }`.

    This is multilinear expansion of the product. -/
theorem prod_in_span_ordered_basis_products
    {k d : ℕ} (W : Submodule ℚ (MvPolynomial N ℚ))
    (b : Module.Basis (Fin d) ℚ W)
    (f : Fin k → MvPolynomial N ℚ) (hf : ∀ i, f i ∈ W) :
    (∏ i, f i) ∈
      Submodule.span ℚ
        { p : MvPolynomial N ℚ |
          ∃ σ : Fin k → Fin d, p = ∏ i, ((b (σ i)) : MvPolynomial N ℚ) } := by
  classical
  -- Write each f i = Σⱼ c i j * (b j).val using basis coordinates.
  -- Let f' : Fin k → W be f lifted to W.
  set f' : Fin k → W := fun i => ⟨f i, hf i⟩ with hf'_def
  -- The Basis.sum_repr gives f' i = Σⱼ b.repr (f' i) j • b j.
  have hrepr : ∀ i, (f' i : MvPolynomial N ℚ) = ∑ j, b.repr (f' i) j • ((b j) : MvPolynomial N ℚ) := by
    intro i
    -- b.sum_repr (f' i) gives : ∑ j, b.repr (f' i) j • b j = f' i
    have h := b.sum_repr (f' i)
    -- Push the Submodule subtype → MvPolynomial equality
    have h' : ((∑ j, b.repr (f' i) j • (b j)) : W) = f' i := h
    have hval := congrArg (fun (x : W) => (x : MvPolynomial N ℚ)) h'
    simp only [Submodule.coe_sum, SetLike.val_smul] at hval
    exact hval.symm
  -- Substitute in the product, and expand the product of sums.
  have hexpand : (∏ i, f i) =
      ∑ σ : (Fin k → Fin d),
        (∏ i, b.repr (f' i) (σ i)) • (∏ i, ((b (σ i)) : MvPolynomial N ℚ)) := by
    -- ∏ᵢ (Σⱼ c_{i,j} * v_j) = Σ_{σ : Fin k → Fin d} ∏ᵢ (c_{i,σ(i)} * v_{σ(i)})
    -- = Σ_σ (∏ᵢ c_{i,σ(i)}) * ∏ᵢ v_{σ(i)}
    calc (∏ i, f i)
        = (∏ i, (f' i : MvPolynomial N ℚ)) := by rfl
      _ = ∏ i, ∑ j, b.repr (f' i) j • ((b j) : MvPolynomial N ℚ) := by
          refine Finset.prod_congr rfl ?_; intro i _; exact hrepr i
      _ = ∑ σ ∈ Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset (Fin d))),
            ∏ i, (b.repr (f' i) (σ i) • ((b (σ i)) : MvPolynomial N ℚ)) := by
          rw [Finset.prod_univ_sum]
      _ = ∑ σ : (Fin k → Fin d),
            ∏ i, (b.repr (f' i) (σ i) • ((b (σ i)) : MvPolynomial N ℚ)) := by
          rw [show (Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset (Fin d))) :
                  Finset (Fin k → Fin d))
                = (Finset.univ : Finset (Fin k → Fin d)) from Fintype.piFinset_univ]
      _ = ∑ σ : (Fin k → Fin d),
            (∏ i, b.repr (f' i) (σ i)) • (∏ i, ((b (σ i)) : MvPolynomial N ℚ)) := by
          refine Finset.sum_congr rfl ?_; intro σ _
          rw [Finset.prod_smul]
  rw [hexpand]
  -- The RHS is a finite ℚ-linear combination of ordered basis products.
  apply Submodule.sum_mem
  intro σ _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨σ, rfl⟩

/-! The ordered basis products `∏ᵢ (b (σ i)).val` for `σ : Fin k → Fin d`,
    modulo the equivalence "same multiset of image values", are counted by
    `Sym (Fin d) k`. By commutativity, `∏ᵢ (b (σ i)).val` only depends on the
    multiset `(Finset.univ.val.map σ : Multiset (Fin d))`. -/

/-- The map from `Fin k → Fin d` to `Sym (Fin d) k` via the multiset image. -/
def orderedToSym {k d : ℕ} (σ : Fin k → Fin d) : Sym (Fin d) k :=
  ⟨Multiset.map σ Finset.univ.val, by
    rw [Multiset.card_map]
    exact Finset.card_univ.trans (Fintype.card_fin k)⟩

/-- The basis products, viewed as a function of the multiset, are well-defined. -/
noncomputable def symProd {k d : ℕ} (W : Submodule ℚ (MvPolynomial N ℚ))
    (b : Module.Basis (Fin d) ℚ W) (m : Sym (Fin d) k) : MvPolynomial N ℚ :=
  ((m : Multiset (Fin d)).map (fun j => ((b j) : MvPolynomial N ℚ))).prod

/-- `∏ᵢ (b (σ i)).val = symProd W b (orderedToSym σ)` — ordered product depends
    only on the multiset image. -/
theorem ordered_prod_eq_symProd
    {k d : ℕ} (W : Submodule ℚ (MvPolynomial N ℚ))
    (b : Module.Basis (Fin d) ℚ W) (σ : Fin k → Fin d) :
    (∏ i, ((b (σ i)) : MvPolynomial N ℚ)) = symProd W b (orderedToSym σ) := by
  classical
  -- RHS unfolded: ((Multiset.map σ univ.val).map (fun j => (b j).val)).prod
  --            = (univ.val.map (fun i => (b (σ i)).val)).prod by Multiset.map_map
  -- LHS: ∏ i : Fin k, (b (σ i)).val = (univ.val.map (fun i => (b (σ i)).val)).prod
  show (∏ i, ((b (σ i)) : MvPolynomial N ℚ))
      = ((Multiset.map σ Finset.univ.val).map
          (fun j => ((b j) : MvPolynomial N ℚ))).prod
  rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

/-- The span of ordered basis products equals the span of the (finite) set of
    symmetric products indexed by `Sym (Fin d) k`. -/
theorem ordered_span_le_sym_span
    {k d : ℕ} (W : Submodule ℚ (MvPolynomial N ℚ))
    (b : Module.Basis (Fin d) ℚ W) :
    Submodule.span ℚ
      { p : MvPolynomial N ℚ |
        ∃ σ : Fin k → Fin d, p = ∏ i, ((b (σ i)) : MvPolynomial N ℚ) } ≤
    Submodule.span ℚ (Set.range (symProd W b : Sym (Fin d) k → _)) := by
  apply Submodule.span_le.mpr
  intro p hp
  rcases hp with ⟨σ, rfl⟩
  rw [ordered_prod_eq_symProd]
  exact Submodule.subset_span ⟨orderedToSym σ, rfl⟩

/-! ## Finrank bound ingredient: span of a finite image -/

/-- The finrank of the span of `Set.range g` for `g : α → M` with `α` finite is
    at most `Fintype.card α`. -/
theorem finrank_span_range_le {R M : Type*} [DivisionRing R] [AddCommGroup M] [Module R M]
    {α : Type*} [Fintype α] (g : α → M) :
    Module.finrank R (Submodule.span R (Set.range g)) ≤ Fintype.card α := by
  classical
  -- `range g = Finset.image g Finset.univ` as sets.
  have hrange : (Set.range g) = (↑(Finset.univ.image g) : Set M) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
    · intro hx
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hx) with ⟨a, _, rfl⟩
      exact ⟨a, rfl⟩
  rw [hrange]
  calc Module.finrank R (Submodule.span R (↑(Finset.univ.image g) : Set M))
      ≤ (Finset.univ.image g).card := finrank_span_finset_le_card _
    _ ≤ (Finset.univ : Finset α).card := Finset.card_image_le
    _ = Fintype.card α := Finset.card_univ

/-! ## Main theorem: dim Sym^k(W) ≤ C(k+2, 2) for dim W ≤ 3 -/

/-- Main target: `dim (symPower k W) ≤ C(k+2, 2)` when `dim W ≤ 3`.

    This is the paper's §9 Lemma 31 dimension bound (stars-and-bars). -/
theorem sym_tensor_power_dim_bound {k : ℕ}
    (W : Submodule ℚ (MvPolynomial N ℚ))
    (hW_fin : Module.Finite ℚ ↥W)
    (hW_dim : Module.finrank ℚ ↥W ≤ 3) :
    Module.finrank ℚ (symPower ℚ k W) ≤ Nat.choose (k + 2) 2 := by
  classical
  -- Abbreviate d = finrank ℚ W ≤ 3.
  set d := Module.finrank ℚ ↥W with hd_def
  -- W is free (over a division ring ℚ).
  have hfree : Module.Free ℚ ↥W := inferInstance
  -- W has a basis indexed by Fin d.
  let b : Module.Basis (Fin d) ℚ ↥W := Module.finBasis ℚ ↥W
  -- symPower k W ⊆ span { ∏ᵢ (b (σ i)).val | σ : Fin k → Fin d }
  have h1 : symPower ℚ k W ≤
      Submodule.span ℚ
        { p : MvPolynomial N ℚ |
          ∃ σ : Fin k → Fin d, p = ∏ i, ((b (σ i)) : MvPolynomial N ℚ) } := by
    unfold symPower
    apply Submodule.span_le.mpr
    intro p hp
    rcases hp with ⟨f, hf, rfl⟩
    exact prod_in_span_ordered_basis_products W b f hf
  -- span of ordered basis products ≤ span of symmetric products indexed by Sym (Fin d) k
  have h2 : Submodule.span ℚ
        { p : MvPolynomial N ℚ |
          ∃ σ : Fin k → Fin d, p = ∏ i, ((b (σ i)) : MvPolynomial N ℚ) } ≤
      Submodule.span ℚ (Set.range (symProd W b : Sym (Fin d) k → _)) :=
    ordered_span_le_sym_span W b
  -- Combined: symPower k W ≤ span (range symProd)
  have hsub : symPower ℚ k W ≤
      Submodule.span ℚ (Set.range (symProd W b : Sym (Fin d) k → _)) :=
    le_trans h1 h2
  -- finrank symPower ≤ finrank span ≤ |Sym (Fin d) k| = multichoose d k = C(d+k-1, k)
  -- Finiteness of the bigger space
  have hfin_big : Module.Finite ℚ ↥(Submodule.span ℚ
      (Set.range (symProd W b : Sym (Fin d) k → _))) := by
    apply Module.Finite.span_of_finite
    exact Set.finite_range _
  -- Monotonicity of finrank on inclusion of submodules within the same ambient
  have hfinrank_le :
      Module.finrank ℚ (symPower ℚ k W) ≤
      Module.finrank ℚ (Submodule.span ℚ (Set.range (symProd W b : Sym (Fin d) k → _))) :=
    Submodule.finrank_mono hsub
  -- The larger span has finrank ≤ |Sym (Fin d) k| = multichoose d k
  have hcard_bound :
      Module.finrank ℚ (Submodule.span ℚ (Set.range (symProd W b : Sym (Fin d) k → _))) ≤
      Fintype.card (Sym (Fin d) k) := finrank_span_range_le _
  have hsymcard : Fintype.card (Sym (Fin d) k) = Nat.multichoose d k :=
    Sym.card_sym_fin_eq_multichoose d k
  have hmc_eq : Nat.multichoose d k = Nat.choose (d + k - 1) k := Nat.multichoose_eq d k
  -- Combine and use d ≤ 3
  rcases Nat.eq_zero_or_pos d with hd0 | hd_pos
  · -- d = 0: W = 0, so symPower k W = ⊥ when k ≥ 1.
    -- For k = 0: symPower 0 W is spanned by the empty product = 1, finrank ≤ 1 ≤ C(2,2)=1.
    -- We can still close this via the bound: multichoose 0 k = if k = 0 then 1 else 0.
    have : Fintype.card (Sym (Fin 0) k) ≤ Nat.choose (k + 2) 2 := by
      by_cases hk0 : k = 0
      · subst hk0
        -- Sym (Fin 0) 0 has exactly one element (the empty multiset)
        have : Fintype.card (Sym (Fin 0) 0) = Nat.multichoose 0 0 :=
          Sym.card_sym_fin_eq_multichoose 0 0
        rw [this, Nat.multichoose_zero_right]
        decide
      · -- Sym (Fin 0) k for k ≥ 1 is empty
        have : Fintype.card (Sym (Fin 0) k) = Nat.multichoose 0 k :=
          Sym.card_sym_fin_eq_multichoose 0 k
        rw [this]
        have : Nat.multichoose 0 k = 0 := by
          cases k with
          | zero => exact absurd rfl hk0
          | succ k' =>
            -- multichoose 0 (k'+1) = 0 for k' ≥ 0
            simp
        rw [this]
        exact Nat.zero_le _
    calc Module.finrank ℚ (symPower ℚ k W)
        ≤ Fintype.card (Sym (Fin d) k) := le_trans hfinrank_le hcard_bound
      _ ≤ Nat.choose (k + 2) 2 := by rw [hd0] at *; exact this
  · -- d ≥ 1: use stars_and_bars_dim3
    have hd_pos' : 1 ≤ d := hd_pos
    have hd_le : d ≤ 3 := hW_dim
    calc Module.finrank ℚ (symPower ℚ k W)
        ≤ Module.finrank ℚ
            (Submodule.span ℚ (Set.range (symProd W b : Sym (Fin d) k → _))) := hfinrank_le
      _ ≤ Fintype.card (Sym (Fin d) k) := hcard_bound
      _ = Nat.multichoose d k := hsymcard
      _ = Nat.choose (d + k - 1) k := hmc_eq
      _ = Nat.choose (k + d - 1) k := by
          congr 1; omega
      _ ≤ Nat.choose (k + 2) 2 := stars_and_bars_dim3 k d hd_pos' hd_le

#print axioms sym_tensor_power_dim_bound

end PallLean.SymTensorPowerDim
