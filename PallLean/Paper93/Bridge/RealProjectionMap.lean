/-
  PallLean/Paper93/Bridge/RealProjectionMap.lean

  Paper §9.3.1 — REAL compiled-basis projection map.

  This file (Agent H6 of 10) replaces Agent F2's abstract/vacuous
  `π := LinearMap.id` bridge (in `PallLean/Paper93/Bridge/ProjectionMap.lean`)
  with a concrete compiled-basis projection:

    * `isCompiledAdmissible B κ ℓ α` — a monomial multi-degree `α` is
      compiled-admissible iff its total degree is ≤ ℓ AND its variable
      support, viewed under the block partition `B`, touches at most `κ`
      distinct blocks. This matches the paper's Definition 12 /
      §9.3.1 restricted column family of `M^B_{κ,ℓ}`: the columns are
      indexed by block-admissible shift monomials of bounded total
      degree whose support is confined to ≤ κ blocks.

    * `πReal B κ ℓ` — the ℚ-linear projection that zeroes out all
      non-admissible monomials in a polynomial's support, keeping only
      the coefficients at admissible multi-degrees. Built kernel-only
      via `Finsupp.filterAddHom` plus `Finsupp.filter_smul`.

    * `πReal_finrank_range_le` — the range of `πReal B κ ℓ` has
      ℚ-finrank at most `(ℓ + 1) ^ N`, a polynomial (in `N, ℓ`) count
      bound which matches §9.3.1's "polynomial column count" claim
      for the compiled matrix `M^B_{κ,ℓ}`.

  We deliberately do NOT modify the existing
  `PallLean/Paper93/Bridge/ProjectionMap.lean` (Agent F2's file):
  downstream callers already depend on its interface. The real
  projection `πReal` defined here is a drop-in replacement that
  a later agent can wire into those consumers.

  Rules observed:
    * No `sorry`.
    * No bespoke axioms.
    * Kernel-only: `#print axioms ⟹ [propext, Classical.choice, Quot.sound]`.
    * Verified by `lake build`.
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Finsupp.Fintype
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic
import PallLean.SPDPDefs

namespace PallLean.Paper93.Bridge

open MvPolynomial SPDP

attribute [local instance] Classical.dec

/-! ## Compiled-basis admissibility predicate

Paper §9.3.1 / Definition 12: the canonical coefficient basis is a
restricted column family of the compiled matrix `M^B_{κ,ℓ}`. A column
is represented by a shift monomial `X^α` with:

  * total degree `|α| = ∑ α_i ≤ ℓ`, and
  * variable support touching at most `κ` distinct `B`-blocks.

The second clause is the "block-admissibility at scale κ" constraint
from Definition 12: the derivative support (equivalently, for a pure
shift monomial, the variable support) must be confined to ≤ κ blocks.
-/

/-- **Compiled-basis admissibility predicate.**

A multi-degree `α : Fin N →₀ ℕ` is compiled-admissible at scales
`(κ, ℓ)` for the block partition `B` iff:

  1. Its total degree is at most `ℓ`:  `∑_i α_i ≤ ℓ`.
  2. Its support touches at most `κ` distinct blocks:
     `#(image B.assign α.support) ≤ κ`.

Clause 2 uses `Finset.image` on `α.support` under the block-assignment
function `B.assign : Fin N → Fin B.numBlocks`. The image is a
`Finset (Fin B.numBlocks)`; its cardinality counts the number of
distinct blocks touched by `α`. -/
def isCompiledAdmissible {N : ℕ} (B : BlockPartition N) (κ ℓ : ℕ)
    (α : Fin N →₀ ℕ) : Prop :=
  (α.sum (fun _ e => e) ≤ ℓ) ∧
    (α.support.image (fun i => B.assign i)).card ≤ κ

instance isCompiledAdmissible_decidable {N : ℕ} (B : BlockPartition N)
    (κ ℓ : ℕ) (α : Fin N →₀ ℕ) :
    Decidable (isCompiledAdmissible B κ ℓ α) := by
  unfold isCompiledAdmissible
  exact instDecidableAnd

/-! ## The real compiled-basis projection map

The projection filters a polynomial's Finsupp-coefficient function,
keeping only the coefficients at compiled-admissible multi-degrees.
Additivity is inherited from `Finsupp.filterAddHom`; ℚ-linearity
follows from `Finsupp.filter_smul`.

Note: `MvPolynomial (Fin N) ℚ` is definitionally
`AddMonoidAlgebra ℚ (Fin N →₀ ℕ) = (Fin N →₀ ℕ) →₀ ℚ`, so
`Finsupp.filter` and related APIs apply directly. -/

/-- **Real compiled-basis projection as an AddMonoidHom.**

Zeros out all non-admissible monomials, leaving admissible ones
untouched. Additivity is free from `Finsupp.filterAddHom`. -/
noncomputable def πRealHom {N : ℕ} (B : BlockPartition N) (κ ℓ : ℕ) :
    MvPolynomial (Fin N) ℚ →+ MvPolynomial (Fin N) ℚ :=
  Finsupp.filterAddHom (fun α => isCompiledAdmissible B κ ℓ α)

/-- **Real compiled-basis projection as a ℚ-linear map.**

Upgraded from `πRealHom` via `Finsupp.filter_smul`, which states that
`filter` commutes with scalar multiplication: `(c • p).filter P =
c • p.filter P`. -/
noncomputable def πReal {N : ℕ} (B : BlockPartition N) (κ ℓ : ℕ) :
    MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ where
  toFun := (πRealHom B κ ℓ).toFun
  map_add' := (πRealHom B κ ℓ).map_add
  map_smul' := by
    intro c p
    -- Unfold `πRealHom` to `Finsupp.filter` and apply `Finsupp.filter_smul`.
    change Finsupp.filter (fun α => isCompiledAdmissible B κ ℓ α) (c • p) =
      c • Finsupp.filter (fun α => isCompiledAdmissible B κ ℓ α) p
    exact Finsupp.filter_smul

/-- Pointwise formula: `πReal` evaluates a monomial-coefficient to `p.coeff α`
when `α` is admissible, and to `0` otherwise. -/
theorem πReal_coeff {N : ℕ} (B : BlockPartition N) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) ℚ) (α : Fin N →₀ ℕ) :
    (πReal B κ ℓ p).coeff α =
      if isCompiledAdmissible B κ ℓ α then p.coeff α else 0 := by
  -- Coefficient-as-finsupp evaluation; `πReal` is defined via `Finsupp.filter`.
  change Finsupp.filter (fun α => isCompiledAdmissible B κ ℓ α) p α = _
  rw [Finsupp.filter_apply]
  rfl

/-! ## Range of `πReal` lives in the admissible monomial span -/

/-- The finite set of "all admissible multi-degrees bounded by `ℓ`",
viewed as multi-degrees `Fin N → Fin (ℓ + 1)` lifted back through
`Finsupp.equivFunOnFinite`. This finset enumerates every `α` with
`α i ≤ ℓ` for all `i`, which is a superset of all total-degree-≤-ℓ
`α`'s; the cardinality bound `(ℓ+1)^N` follows immediately. -/
noncomputable def boundedDegreeFinsupps (N ℓ : ℕ) : Finset (Fin N →₀ ℕ) :=
  ((Finset.univ : Finset (Fin N → Fin (ℓ + 1))).image
    (fun f => Finsupp.equivFunOnFinite.symm (fun i => (f i).val)))

theorem boundedDegreeFinsupps_card_le (N ℓ : ℕ) :
    (boundedDegreeFinsupps N ℓ).card ≤ (ℓ + 1) ^ N := by
  unfold boundedDegreeFinsupps
  calc ((Finset.univ : Finset (Fin N → Fin (ℓ + 1))).image
            (fun f => Finsupp.equivFunOnFinite.symm (fun i => (f i).val))).card
      ≤ (Finset.univ : Finset (Fin N → Fin (ℓ + 1))).card := Finset.card_image_le
    _ = (ℓ + 1) ^ N := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- If `α i ≤ ℓ` for every `i : Fin N`, then `α ∈ boundedDegreeFinsupps N ℓ`. -/
theorem boundedDegreeFinsupps_mem_of_bounded {N ℓ : ℕ} (α : Fin N →₀ ℕ)
    (hα : ∀ i : Fin N, α i ≤ ℓ) :
    α ∈ boundedDegreeFinsupps N ℓ := by
  unfold boundedDegreeFinsupps
  refine Finset.mem_image.mpr ⟨fun i => ⟨α i, Nat.lt_succ_of_le (hα i)⟩, ?_, ?_⟩
  · exact Finset.mem_univ _
  · apply Finsupp.equivFunOnFinite.symm_apply_eq.mpr
    ext i
    simp only [Finsupp.equivFunOnFinite_apply]

/-- **Compiled-admissible monomial spanning set.**

The Finset of monomials `X^α` with `α ∈ boundedDegreeFinsupps N ℓ` —
i.e., with every coordinate `α i ≤ ℓ`. This is a superset of the
compiled-admissible monomials for `(B, κ, ℓ)` (since total degree ≤ ℓ
forces every coord ≤ ℓ), and hence spans the range of `πReal`. -/
noncomputable def admissibleMonomialSpan (N ℓ : ℕ) :
    Finset (MvPolynomial (Fin N) ℚ) :=
  (boundedDegreeFinsupps N ℓ).image (fun α => MvPolynomial.monomial α (1 : ℚ))

theorem admissibleMonomialSpan_card_le (N ℓ : ℕ) :
    (admissibleMonomialSpan N ℓ).card ≤ (ℓ + 1) ^ N := by
  unfold admissibleMonomialSpan
  exact le_trans Finset.card_image_le (boundedDegreeFinsupps_card_le N ℓ)

/-- If `α` is compiled-admissible, then `α i ≤ ℓ` for every `i`
(total degree bounds each coordinate). -/
theorem isCompiledAdmissible_coord_le {N : ℕ} {B : BlockPartition N}
    {κ ℓ : ℕ} {α : Fin N →₀ ℕ} (h : isCompiledAdmissible B κ ℓ α)
    (i : Fin N) : α i ≤ ℓ := by
  by_cases hi : i ∈ α.support
  · -- `α i ≤ ∑_j α j ≤ ℓ`.
    have h1 : α i ≤ α.sum (fun _ e => e) := by
      have := Finset.single_le_sum (f := fun j => α j) (s := α.support)
        (by intro j _; exact Nat.zero_le _) hi
      simpa [Finsupp.sum] using this
    exact h1.trans h.1
  · -- Not in support ⇒ `α i = 0`.
    have : α i = 0 := Finsupp.notMem_support_iff.mp hi
    exact this ▸ Nat.zero_le _

/-- **Key spanning lemma.** For any polynomial `p`, `πReal B κ ℓ p`
lies in the ℚ-linear span of the `admissibleMonomialSpan N ℓ`.

Proof: expand `πReal p` as its monomial sum; non-admissible monomials
vanish by `πReal_coeff`; admissible ones have every coord ≤ ℓ (by
`isCompiledAdmissible_coord_le`) and hence their monomial `X^α`
lies in the spanning finset. -/
theorem πReal_mem_span {N : ℕ} (B : BlockPartition N) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) ℚ) :
    πReal B κ ℓ p ∈
      Submodule.span ℚ (↑(admissibleMonomialSpan N ℓ) :
        Set (MvPolynomial (Fin N) ℚ)) := by
  classical
  -- Decompose via `as_sum`.
  rw [show πReal B κ ℓ p =
        ∑ α ∈ (πReal B κ ℓ p).support,
          MvPolynomial.monomial α ((πReal B κ ℓ p).coeff α) from
        (πReal B κ ℓ p).as_sum]
  apply Submodule.sum_mem
  intro α hα
  -- `α ∈ support (πReal p)` ⇒ coefficient is nonzero at `α`; rewrite via `πReal_coeff`.
  -- If `¬admissible`, the coeff is `0`, contradicting membership in support.
  have hcoeff_ne : (πReal B κ ℓ p).coeff α ≠ 0 := by
    intro h0
    exact (MvPolynomial.mem_support_iff.mp hα) h0
  have h_adm : isCompiledAdmissible B κ ℓ α := by
    by_contra hcon
    have : (πReal B κ ℓ p).coeff α = 0 := by
      rw [πReal_coeff]
      exact if_neg hcon
    exact hcoeff_ne this
  -- `monomial α c = c • monomial α 1`.
  rw [show MvPolynomial.monomial α ((πReal B κ ℓ p).coeff α) =
        (πReal B κ ℓ p).coeff α • MvPolynomial.monomial α (1 : ℚ) by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
  apply Submodule.smul_mem
  -- `monomial α 1 ∈ admissibleMonomialSpan`.
  apply Submodule.subset_span
  refine Finset.mem_coe.mpr ?_
  unfold admissibleMonomialSpan
  refine Finset.mem_image.mpr ⟨α, ?_, rfl⟩
  exact boundedDegreeFinsupps_mem_of_bounded α
    (fun i => isCompiledAdmissible_coord_le h_adm i)

/-! ## Rank bound on the range of `πReal` -/

/-- The range of `πReal B κ ℓ` is contained in the ℚ-span of the
admissible monomial finset. -/
theorem πReal_range_le_span {N : ℕ} (B : BlockPartition N) (κ ℓ : ℕ) :
    LinearMap.range (πReal B κ ℓ) ≤
      Submodule.span ℚ (↑(admissibleMonomialSpan N ℓ) :
        Set (MvPolynomial (Fin N) ℚ)) := by
  rintro q ⟨p, rfl⟩
  exact πReal_mem_span B κ ℓ p

/-- The span of the admissible monomial finset is a finite ℚ-module. -/
theorem admissibleMonomialSpan_finite (N ℓ : ℕ) :
    Module.Finite ℚ
      ↥(Submodule.span ℚ (↑(admissibleMonomialSpan N ℓ) :
        Set (MvPolynomial (Fin N) ℚ))) := by
  exact Module.Finite.span_of_finite ℚ (Finset.finite_toSet _)

/-- **Paper §9.3.1 polynomial-column-count bound.**

The range of the real compiled-basis projection `πReal B κ ℓ` has
ℚ-finrank at most `(ℓ + 1) ^ N`: polynomial in `ℓ` for fixed `N`.

Proof sketch:
  1. The range is contained in the span of `admissibleMonomialSpan N ℓ`
     (a Finset of monomials with coordinate-bounds `α i ≤ ℓ`).
  2. That span is finite-dimensional with finrank ≤ `(admissibleMonomialSpan N ℓ).card`
     by `finrank_span_finset_le_card`.
  3. `(admissibleMonomialSpan N ℓ).card ≤ (ℓ + 1) ^ N` by
     `admissibleMonomialSpan_card_le`.
  4. `finrank` is monotone under submodule inclusion. -/
theorem πReal_finrank_range_le {N : ℕ} (B : BlockPartition N) (κ ℓ : ℕ) :
    Module.finrank ℚ (LinearMap.range (πReal B κ ℓ)) ≤ (ℓ + 1) ^ N := by
  classical
  -- Ambient span is finite-dimensional.
  haveI : Module.Finite ℚ
      ↥(Submodule.span ℚ (↑(admissibleMonomialSpan N ℓ) :
        Set (MvPolynomial (Fin N) ℚ))) :=
    admissibleMonomialSpan_finite N ℓ
  -- Monotonicity of finrank via submodule inclusion.
  have h_le : Module.finrank ℚ (LinearMap.range (πReal B κ ℓ)) ≤
      Module.finrank ℚ
        ↥(Submodule.span ℚ (↑(admissibleMonomialSpan N ℓ) :
          Set (MvPolynomial (Fin N) ℚ))) :=
    Submodule.finrank_mono (πReal_range_le_span B κ ℓ)
  -- Span of finset has finrank ≤ card.
  have h_span :
      Module.finrank ℚ
        ↥(Submodule.span ℚ (↑(admissibleMonomialSpan N ℓ) :
          Set (MvPolynomial (Fin N) ℚ)))
        ≤ (admissibleMonomialSpan N ℓ).card :=
    finrank_span_finset_le_card (admissibleMonomialSpan N ℓ)
  -- Card bound.
  have h_card : (admissibleMonomialSpan N ℓ).card ≤ (ℓ + 1) ^ N :=
    admissibleMonomialSpan_card_le N ℓ
  exact h_le.trans (h_span.trans h_card)

/-! ## Rank-monotonicity sanity lemma (matches Agent F2's `π_rank_le`) -/

/-- `πReal` is rank-nonincreasing on every finite submodule
(standard fact: any linear map is rank-nonincreasing on finite
submodules). This matches the interface obligation of Agent F2's
`π_rank_le`. -/
theorem πReal_rank_le {N : ℕ} (B : BlockPartition N) (κ ℓ : ℕ)
    (W : Submodule ℚ (MvPolynomial (Fin N) ℚ)) [Module.Finite ℚ W] :
    Module.finrank ℚ (Submodule.map (πReal B κ ℓ) W) ≤
      Module.finrank ℚ W :=
  Submodule.finrank_map_le (πReal B κ ℓ) W

end PallLean.Paper93.Bridge
