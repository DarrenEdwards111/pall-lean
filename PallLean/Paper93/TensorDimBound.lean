/-
  TensorDimBound.lean — Profile subspace tensor dimension bound (Paper §9 Lemma 31)

  Composition layer (Agent 9 of 10):
  given per-interface spaces `W_σ ⊆ MvPolynomial (Fin N) ℚ` with
  `finrank ℚ (W σ) ≤ 3` (Agent 8's construction) and a profile
  `h : Σ → ℕ` (Agent 4's profile), the paper's §9 Lemma 31 produces a
  "profile subspace"

  ```
  V_h ⊆ ⊗_{σ ∈ Σ} Sym^{h σ}(W_σ)
  ```

  whose dimension is bounded by

  ```
  dim V_h ≤ ∏_σ C(h σ + d_0 - 1, h σ) = ∏_σ C(h σ + 2, 2)   (at d_0 = 3).
  ```

  Since everything lives inside the commutative polynomial ring
  `MvPolynomial (Fin N) ℚ`, the paper's abstract tensor product
  `⊗_σ Sym^{h σ}(W_σ)` is realised concretely by the submodule of
  polynomial products `∏_σ f σ` with each `f σ ∈ Sym^{h σ}(W σ)`.

  Proof strategy (composition of Agent 1's single-interface lemma with
  a Finset-level multilinear expansion over the finite alphabet `Σ`):

  1. For each `σ`, fix a basis `b σ : Basis (Fin (d σ)) ℚ (W σ)` with
     `d σ := finrank ℚ (W σ) ≤ 3` (provided by `Module.finBasis` since
     ℚ is a field).
  2. By Agent 1's spanning lemmas, every `f σ ∈ Sym^{h σ}(W σ)` lies in
     the ℚ-span of the symmetric basis products
     `symProd (W σ) (b σ) m` for `m : Sym (Fin (d σ)) (h σ)`.
  3. Expand `∏_σ f σ` as a finite ℚ-linear combination of products
     `∏_σ symProd (W σ) (b σ) (m σ)` indexed by
     `m : ∀ σ, Sym (Fin (d σ)) (h σ)`, via `Finset.prod_univ_sum`.
  4. Hence `V_h` lies in the span of this finite family, whose
     cardinality is `∏_σ |Sym (Fin (d σ)) (h σ)| = ∏_σ multichoose (d σ) (h σ)`,
     bounded by `∏_σ C(h σ + 2, 2)` via Agent 1's
     `stars_and_bars_dim3` lemma.

  This file imports and composes `PallLean.SymTensorPowerDim` (Agent 1),
  and is parameterised over a generic finite alphabet `Σ` (called `Iface`
  below to avoid shadowing the `Finset.sum` binder `Σ`) so that Agent 8's
  `InterfaceType` can be plugged in without edits here.
-/
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Tactic

import PallLean.SymTensorPowerDim

open Module
open scoped BigOperators

namespace PallLean
namespace Paper93

open MvPolynomial
open PallLean.SymTensorPowerDim

/-! ## Definition of the profile subspace

Given per-interface subspaces `W : Iface → Submodule ℚ (MvPolynomial (Fin N) ℚ)`
and a profile `h : Iface → ℕ`, the paper's profile subspace

  V_h  ⊆  ⊗_σ Sym^{h σ}(W σ)

is realised concretely as the submodule of `MvPolynomial (Fin N) ℚ`
spanned by all products `∏_σ f σ` where `f σ ∈ Sym^{h σ}(W σ)` for
each `σ`. This matches the paper's description "V_h is contained in
∏_σ Sym^{h(σ)}(W_σ)" in the commutative polynomial setting. -/

/-- Paper §9 Lemma 31 profile subspace: the submodule spanned by all
    products `∏_σ f σ` with `f σ ∈ Sym^{h σ}(W σ)`.

    In the tensor-algebra formulation, this is the image of
    `⊗_σ Sym^{h σ}(W σ)` under the canonical tensor-to-polynomial
    product map. -/
noncomputable def profileSubspace {N : ℕ} {Iface : Type*} [Fintype Iface]
    (h : Iface → ℕ)
    (W : Iface → Submodule ℚ (MvPolynomial (Fin N) ℚ)) :
    Submodule ℚ (MvPolynomial (Fin N) ℚ) :=
  Submodule.span ℚ
    { p : MvPolynomial (Fin N) ℚ |
      ∃ f : Iface → MvPolynomial (Fin N) ℚ,
        (∀ σ : Iface, f σ ∈ symPower ℚ (h σ) (W σ)) ∧
        p = ∏ σ : Iface, f σ }

/-- **Lemma 31 membership constructor.**

If a row/product has profile `h` in the literal sense that, for each interface
type `σ`, it contributes exactly `h σ` slots and every one of those slots lies
in the corresponding local space `W σ`, then the full typed product lands in
the profile subspace `profileSubspace h W`.

This is the non-dimensional half of Lemma 31: it proves membership
`row/product with profile h ∈ V_h` directly from the defining symmetric-power
generators, before any finrank/template-count argument is used. -/
theorem profileProduct_mem_profileSubspace {N : ℕ} {Iface : Type*}
    [Fintype Iface]
    (h : Iface → ℕ)
    (W : Iface → Submodule ℚ (MvPolynomial (Fin N) ℚ))
    (slot : ∀ σ : Iface, Fin (h σ) → MvPolynomial (Fin N) ℚ)
    (hslot : ∀ σ j, slot σ j ∈ W σ) :
    (∏ σ : Iface, ∏ j : Fin (h σ), slot σ j) ∈
      profileSubspace h W := by
  classical
  apply Submodule.subset_span
  refine ⟨(fun σ : Iface => ∏ j : Fin (h σ), slot σ j), ?_, rfl⟩
  intro σ
  unfold symPower
  apply Submodule.subset_span
  exact ⟨slot σ, hslot σ, rfl⟩

/-! ## Multilinear expansion over the finite alphabet

The key step: given bases `b σ : Basis (Fin (d σ)) ℚ (W σ)` for each
`σ`, every product `∏_σ f σ` with `f σ ∈ Sym^{h σ}(W σ)` lies in the
span of the finite family of "per-interface symmetric basis products"
indexed by `m : ∀ σ, Sym (Fin (d σ)) (h σ)`. -/

/-- Finite index set for ordered multi-interface basis products:
    a choice of a symmetric multiset per interface. -/
abbrev ProfileIndex {Iface : Type*} [Fintype Iface]
    (h : Iface → ℕ) (d : Iface → ℕ) : Type _ :=
  ∀ σ : Iface, Sym (Fin (d σ)) (h σ)

/-- `ProfileIndex h d` is a fintype (each factor `Sym (Fin (d σ)) (h σ)` is a
    fintype, and `Iface` is a fintype). -/
instance profileIndex_fintype {Iface : Type*} [Fintype Iface] [DecidableEq Iface]
    (h d : Iface → ℕ) : Fintype (ProfileIndex h d) :=
  Pi.instFintype

/-- The canonical multi-interface symmetric product associated to a
    profile index: the polynomial product `∏_σ symProd (W σ) (b σ) (m σ)`. -/
noncomputable def profileSymProd {N : ℕ} {Iface : Type*} [Fintype Iface]
    {h : Iface → ℕ} {d : Iface → ℕ}
    (W : Iface → Submodule ℚ (MvPolynomial (Fin N) ℚ))
    (b : ∀ σ, Module.Basis (Fin (d σ)) ℚ ↥(W σ))
    (m : ProfileIndex h d) : MvPolynomial (Fin N) ℚ :=
  ∏ σ : Iface, symProd (W σ) (b σ) (m σ)

/-- Multilinear expansion step: any product `∏_σ f σ` with each
    `f σ ∈ Sym^{h σ}(W σ)` lies in the span of the profile symmetric
    products. -/
theorem prod_in_span_profileSymProd
    {N : ℕ} {Iface : Type*} [Fintype Iface] [DecidableEq Iface]
    {h : Iface → ℕ} {d : Iface → ℕ}
    (W : Iface → Submodule ℚ (MvPolynomial (Fin N) ℚ))
    (b : ∀ σ, Module.Basis (Fin (d σ)) ℚ ↥(W σ))
    (f : Iface → MvPolynomial (Fin N) ℚ)
    (hf : ∀ σ, f σ ∈ symPower ℚ (h σ) (W σ)) :
    (∏ σ : Iface, f σ) ∈
      Submodule.span ℚ (Set.range (profileSymProd W b : ProfileIndex h d → _)) := by
  classical
  -- For each σ, `f σ` lies in span of `Set.range (symProd (W σ) (b σ))`.
  -- This is the content of Agent 1's `ordered_span_le_sym_span` combined
  -- with `prod_in_span_ordered_basis_products`.
  have hf_sym : ∀ σ, f σ ∈
      Submodule.span ℚ (Set.range (symProd (W σ) (b σ) : Sym (Fin (d σ)) (h σ) → _)) := by
    intro σ
    -- Start from `f σ ∈ symPower ℚ (h σ) (W σ)` and unfold.
    have hfσ := hf σ
    unfold symPower at hfσ
    -- Reduce to showing `symPower` sits inside the sym-range span.
    -- `symPower ℚ k W ≤ span (range (symProd W b))` via Agent 1's lemmas.
    have h1 : symPower ℚ (h σ) (W σ) ≤
        Submodule.span ℚ
          { p : MvPolynomial (Fin N) ℚ |
            ∃ τ : Fin (h σ) → Fin (d σ),
              p = ∏ i, ((b σ (τ i)) : MvPolynomial (Fin N) ℚ) } := by
      unfold symPower
      refine Submodule.span_le.mpr ?_
      intro p hp
      rcases hp with ⟨g, hg, rfl⟩
      exact prod_in_span_ordered_basis_products (W σ) (b σ) g hg
    have h2 : Submodule.span ℚ
          { p : MvPolynomial (Fin N) ℚ |
            ∃ τ : Fin (h σ) → Fin (d σ),
              p = ∏ i, ((b σ (τ i)) : MvPolynomial (Fin N) ℚ) } ≤
        Submodule.span ℚ (Set.range (symProd (W σ) (b σ) : Sym (Fin (d σ)) (h σ) → _)) :=
      ordered_span_le_sym_span (W σ) (b σ)
    have : symPower ℚ (h σ) (W σ) ≤
        Submodule.span ℚ (Set.range (symProd (W σ) (b σ) : Sym (Fin (d σ)) (h σ) → _)) :=
      le_trans h1 h2
    exact this (hf σ)
  -- Now express each `f σ` in terms of the range using `mem_span_range_iff_exists_fun`.
  -- Instead, use the spanning formulation via `Finset.prod_univ_sum`.
  -- We pass through a choice of coefficient function per σ.
  -- Use `Submodule.mem_span_range_iff_exists_fun` from Mathlib
  --   (or equivalently: since `Sym (Fin (d σ)) (h σ)` is a fintype,
  --    spanning means finite linear combination).
  --
  -- Let `c σ : Sym (Fin (d σ)) (h σ) → ℚ` be coefficients with
  --   f σ = ∑ m, c σ m • symProd (W σ) (b σ) m.
  have hsum : ∀ σ, ∃ c : Sym (Fin (d σ)) (h σ) → ℚ,
      f σ = ∑ m, c m • symProd (W σ) (b σ) m := by
    intro σ
    -- `mem_span_range_iff_exists_fun` is the standard form.
    -- On a fintype index, `mem_span_range_iff_exists_fun` gives a total function c.
    have := (Submodule.mem_span_range_iff_exists_fun ℚ (v := symProd (W σ) (b σ))
        (x := f σ)).mp (hf_sym σ)
    rcases this with ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  -- Pull out the coefficient functions with `Classical.choice`.
  choose c hc using hsum
  -- Substitute into the product and expand via `Finset.prod_univ_sum`.
  have hprod_eq :
      (∏ σ : Iface, f σ) =
        ∑ m : ProfileIndex h d,
          (∏ σ : Iface, c σ (m σ)) • profileSymProd W b m := by
    calc (∏ σ : Iface, f σ)
        = ∏ σ : Iface, ∑ j, c σ j • symProd (W σ) (b σ) j := by
            refine Finset.prod_congr rfl ?_
            intro σ _
            exact hc σ
      _ = ∑ m ∈ Fintype.piFinset (fun σ : Iface => (Finset.univ : Finset (Sym (Fin (d σ)) (h σ)))),
            ∏ σ : Iface, c σ (m σ) • symProd (W σ) (b σ) (m σ) := by
            rw [Finset.prod_univ_sum]
      _ = ∑ m : ProfileIndex h d,
            ∏ σ : Iface, c σ (m σ) • symProd (W σ) (b σ) (m σ) := by
            -- `Fintype.piFinset (fun σ => univ) = univ` by `Fintype.piFinset_univ`;
            -- and `ProfileIndex h d` reduces to `∀ σ, Sym (Fin (d σ)) (h σ)` by definition.
            rfl
      _ = ∑ m : ProfileIndex h d,
            (∏ σ : Iface, c σ (m σ)) • ∏ σ : Iface, symProd (W σ) (b σ) (m σ) := by
            refine Finset.sum_congr rfl ?_
            intro m _
            rw [Finset.prod_smul]
      _ = ∑ m : ProfileIndex h d,
            (∏ σ : Iface, c σ (m σ)) • profileSymProd W b m := by
            rfl
  rw [hprod_eq]
  refine Submodule.sum_mem _ ?_
  intro m _
  refine Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨m, rfl⟩

/-! ## Containment: profileSubspace ⊆ span of profile sym products -/

theorem profileSubspace_le_profileSymProd_span
    {N : ℕ} {Iface : Type*} [Fintype Iface] [DecidableEq Iface]
    {h : Iface → ℕ} {d : Iface → ℕ}
    (W : Iface → Submodule ℚ (MvPolynomial (Fin N) ℚ))
    (b : ∀ σ, Module.Basis (Fin (d σ)) ℚ ↥(W σ)) :
    profileSubspace h W ≤
      Submodule.span ℚ (Set.range (profileSymProd W b : ProfileIndex h d → _)) := by
  unfold profileSubspace
  refine Submodule.span_le.mpr ?_
  intro p hp
  rcases hp with ⟨f, hf, rfl⟩
  exact prod_in_span_profileSymProd W b f hf

/-! ## Cardinality of the profile index set

`|ProfileIndex h d| = ∏_σ |Sym (Fin (d σ)) (h σ)| = ∏_σ multichoose (d σ) (h σ)`. -/

theorem profileIndex_card
    {Iface : Type*} [Fintype Iface] [DecidableEq Iface]
    (h d : Iface → ℕ) :
    Fintype.card (ProfileIndex h d) = ∏ σ : Iface, Nat.multichoose (d σ) (h σ) := by
  classical
  -- `ProfileIndex h d` unfolds to `∀ σ, Sym (Fin (d σ)) (h σ)` by definition.
  have hcard : Fintype.card (∀ σ : Iface, Sym (Fin (d σ)) (h σ))
      = ∏ σ : Iface, Fintype.card (Sym (Fin (d σ)) (h σ)) := Fintype.card_pi
  calc Fintype.card (ProfileIndex h d)
      = Fintype.card (∀ σ : Iface, Sym (Fin (d σ)) (h σ)) := rfl
    _ = ∏ σ : Iface, Fintype.card (Sym (Fin (d σ)) (h σ)) := hcard
    _ = ∏ σ : Iface, Nat.multichoose (d σ) (h σ) := by
          refine Finset.prod_congr rfl ?_
          intro σ _
          exact Sym.card_sym_fin_eq_multichoose (d σ) (h σ)

/-! ## Finrank bound: combining Agent 1's stars-and-bars with a product over Σ -/

/-- Arithmetic lemma: `multichoose d k ≤ C(k + 2, 2)` when `d ≤ 3`. -/
theorem multichoose_le_choose_of_dim_le_three (d k : ℕ) (hd : d ≤ 3) :
    Nat.multichoose d k ≤ Nat.choose (k + 2) 2 := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd_pos
  · -- d = 0: multichoose 0 k = 0 for k > 0, = 1 for k = 0. Both ≤ C(k+2,2).
    subst hd0
    by_cases hk0 : k = 0
    · subst hk0
      -- multichoose 0 0 = 1 ≤ C(2, 2) = 1
      have h1 : Nat.multichoose 0 0 = 1 := by
        rw [Nat.multichoose_eq]
        simp
      have h2 : Nat.choose (0 + 2) 2 = 1 := by decide
      rw [h1, h2]
    · -- multichoose 0 (succ k) = 0
      cases k with
      | zero => exact absurd rfl hk0
      | succ k' =>
        have h1 : Nat.multichoose 0 (k' + 1) = 0 := by
          rw [Nat.multichoose_eq]
          -- C(0 + (k' + 1) - 1, k' + 1) = C(k', k' + 1) = 0
          simp
        rw [h1]
        exact Nat.zero_le _
  · -- d ≥ 1, d ≤ 3: use Agent 1's stars_and_bars_dim3.
    have := stars_and_bars_dim3 k d hd_pos hd
    have hmc := Nat.multichoose_eq d k
    calc Nat.multichoose d k
        = Nat.choose (d + k - 1) k := hmc
      _ = Nat.choose (k + d - 1) k := by congr 1; omega
      _ ≤ Nat.choose (k + 2) 2 := this

/-- Monotonicity of ∏ on ℕ. -/
private theorem prod_le_prod_of_le
    {Iface : Type*} [Fintype Iface]
    (f g : Iface → ℕ) (hfg : ∀ σ, f σ ≤ g σ) :
    (∏ σ : Iface, f σ) ≤ ∏ σ : Iface, g σ :=
  Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun σ _ => hfg σ)

/-! ## Main theorem: Paper §9 Lemma 31 dimension bound -/

/-- Paper §9 Lemma 31 profile subspace dimension bound.

    Given per-interface subspaces `W σ ⊆ MvPolynomial (Fin N) ℚ` with
    `finrank ℚ (W σ) ≤ 3` and a profile `h : Iface → ℕ`, the profile
    subspace `V_h = span { ∏_σ f σ | f σ ∈ Sym^{h σ}(W σ) }` has finrank
    bounded by the product `∏_σ C(h σ + 2, 2)`.

    This is the direct composition of Agent 1's single-interface
    `sym_tensor_power_dim_bound` (via its underlying `stars_and_bars_dim3`)
    with a Finset-level multilinear expansion over the finite alphabet. -/
theorem profileSubspace_finrank_bound
    {N : ℕ} {Iface : Type*} [Fintype Iface] [DecidableEq Iface]
    (h : Iface → ℕ)
    (W : Iface → Submodule ℚ (MvPolynomial (Fin N) ℚ))
    (hW_fin : ∀ σ, Module.Finite ℚ ↥(W σ))
    (hW_dim : ∀ σ, Module.finrank ℚ ↥(W σ) ≤ 3) :
    Module.finrank ℚ (profileSubspace h W) ≤
      ∏ σ : Iface, Nat.choose (h σ + 2) 2 := by
  classical
  -- For each σ, let `d σ := finrank ℚ (W σ)` and pick a basis `b σ`.
  set d : Iface → ℕ := fun σ => Module.finrank ℚ ↥(W σ) with hd_def
  have hd_le : ∀ σ, d σ ≤ 3 := hW_dim
  let b : ∀ σ, Module.Basis (Fin (d σ)) ℚ ↥(W σ) :=
    fun σ => Module.finBasis ℚ ↥(W σ)
  -- profileSubspace h W ≤ span (range (profileSymProd W b))
  have hsub : profileSubspace h W ≤
      Submodule.span ℚ
        (Set.range (profileSymProd W b : ProfileIndex h d → _)) :=
    profileSubspace_le_profileSymProd_span W b
  -- The RHS is finite-dimensional (span of a finite family).
  haveI hfin_big : Module.Finite ℚ
      ↥(Submodule.span ℚ (Set.range (profileSymProd W b : ProfileIndex h d → _))) := by
    apply Module.Finite.span_of_finite
    exact Set.finite_range _
  -- Finrank monotonicity: finrank V_h ≤ finrank (span of finite family).
  have hmono :
      Module.finrank ℚ (profileSubspace h W) ≤
      Module.finrank ℚ
        (Submodule.span ℚ (Set.range (profileSymProd W b : ProfileIndex h d → _))) :=
    Submodule.finrank_mono hsub
  -- Finrank of the span is ≤ card of the (fintype) profile index.
  have hcard :
      Module.finrank ℚ
        (Submodule.span ℚ (Set.range (profileSymProd W b : ProfileIndex h d → _))) ≤
      Fintype.card (ProfileIndex h d) := finrank_span_range_le _
  -- |ProfileIndex h d| = ∏ σ, multichoose (d σ) (h σ).
  have hcard_eq : Fintype.card (ProfileIndex h d) = ∏ σ : Iface, Nat.multichoose (d σ) (h σ) :=
    profileIndex_card h d
  -- Each factor multichoose (d σ) (h σ) ≤ C(h σ + 2, 2) by stars-and-bars.
  have hfac_le : ∀ σ, Nat.multichoose (d σ) (h σ) ≤ Nat.choose (h σ + 2) 2 :=
    fun σ => multichoose_le_choose_of_dim_le_three (d σ) (h σ) (hd_le σ)
  -- Chain: finrank V_h ≤ |Profile| ≤ ∏ multichoose ≤ ∏ C(h+2,2).
  calc Module.finrank ℚ (profileSubspace h W)
      ≤ Module.finrank ℚ
          (Submodule.span ℚ (Set.range (profileSymProd W b : ProfileIndex h d → _))) := hmono
    _ ≤ Fintype.card (ProfileIndex h d) := hcard
    _ = ∏ σ : Iface, Nat.multichoose (d σ) (h σ) := hcard_eq
    _ ≤ ∏ σ : Iface, Nat.choose (h σ + 2) 2 :=
        prod_le_prod_of_le
          (fun σ => Nat.multichoose (d σ) (h σ))
          (fun σ => Nat.choose (h σ + 2) 2)
          hfac_le

#print axioms profileProduct_mem_profileSubspace
#print axioms profileSubspace_finrank_bound

end Paper93
end PallLean
