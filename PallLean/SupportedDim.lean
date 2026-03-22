/-
  SupportedDim.lean — Dimension of variable-restricted polynomial spaces

  Key lemma: for polynomials on a k-element variable set of degree ≤ d,
  the dimension is C(k+d, k) ≤ (k+d)^k.
-/
import PallLean.CompiledPoly
import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic

namespace SupportedDim

open MvPolynomial

/-- The set of Finsupp with support in s and sum ≤ d. -/
def boundedSupp {σ : Type*} [DecidableEq σ] (s : Finset σ) (d : ℕ) :
    Set (σ →₀ ℕ) :=
  { n | n.sum (fun _ e => e) ≤ d ∧ ↑n.support ⊆ ↑s }

/-- restrictSupport on boundedSupp gives the degree-bounded variable-restricted space. -/
def restrictSupportDeg {σ : Type*} [DecidableEq σ] (R : Type*) [CommSemiring R]
    (s : Finset σ) (d : ℕ) : Submodule R (MvPolynomial σ R) :=
  restrictSupport R (boundedSupp s d)

/-- A polynomial is in restrictSupportDeg iff its vars ⊆ s and totalDegree ≤ d. -/
theorem mem_restrictSupportDeg {σ : Type*} [DecidableEq σ] {R : Type*} [CommSemiring R]
    {s : Finset σ} {d : ℕ} {p : MvPolynomial σ R} :
    p ∈ restrictSupportDeg R s d ↔ p.totalDegree ≤ d ∧ ↑p.vars ⊆ ↑s := by
  sorry

/-- The SPDP span of V with vars.card ≤ k and deg ≤ d, under S-coupling,
    lies inside restrictSupportDeg on a (3k)-element set of degree ≤ ℓ+d. -/
theorem spdp_span_in_restrictSupportDeg {N : ℕ}
    (κ ℓ : ℕ) (V : MvPolynomial (Fin N) ℚ)
    (bp : CompiledPoly.BlockPartition N)
    (hV_deg : V.totalDegree ≤ 6)
    (s : Finset (Fin N)) (hs : ↑V.vars ⊆ ↑s) (hs_card : s.card ≤ 24) :
    Submodule.span ℚ
      { q | ∃ (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ),
        S.length ≤ κ ∧ m.totalDegree ≤ ℓ ∧
        (S.toFinset.image bp.blockOf).card = S.toFinset.card ∧
        (∀ v ∈ m.vars, bp.blockOf v ∈ S.toFinset.image bp.blockOf) ∧
        q = m * SPDP.iterDerivList S V }
    ≤ restrictSupportDeg ℚ s (ℓ + 6) := by
  sorry

/-- finrank of restrictSupportDeg ≤ (card s + d)^(card s). -/
theorem finrank_restrictSupportDeg_le {σ : Type*} [DecidableEq σ] [Fintype σ]
    (s : Finset σ) (d : ℕ) :
    Module.finrank ℚ (restrictSupportDeg ℚ s d) ≤ (s.card + d) ^ s.card := by
  -- restrictSupportDeg ≤ restrictTotalDegree, so finrank ≤ finrank(restrictTotalDegree)
  -- But that depends on |σ|. We need the tighter bound.
  --
  -- finrank(restrictSupportDeg) = |boundedSupp s d| (from basisRestrictSupport)
  -- |boundedSupp s d| = number of Finsupp n with n.sum id ≤ d and n.support ⊆ s
  -- = number of multisets of size ≤ d from s = C(|s|+d, |s|) ≤ (|s|+d)^|s|
  --
  -- finrank(restrictSupportDeg s d) ≤ finrank(restrictTotalDegree d)
  -- ≤ C(|σ|+d, |σ|) ≤ (|σ|+d)^|σ|
  -- This is too weak (depends on |σ| not |s|).
  -- For the tight bound: finrank = |boundedSupp s d| = C(|s|+d, |s|) ≤ (|s|+d)^|s|.
  -- Needs Fintype instance for boundedSupp and card counting.
  sorry

/-- Module.Finite for restrictSupportDeg (subset of restrictTotalDegree). -/
instance instFinite_restrictSupportDeg {σ : Type*} [DecidableEq σ] [Fintype σ]
    (s : Finset σ) (d : ℕ) : Module.Finite ℚ (restrictSupportDeg ℚ s d) := by
  unfold restrictSupportDeg
  have h_le : restrictSupport ℚ (boundedSupp s d) ≤ restrictTotalDegree σ ℚ d := by
    apply restrictSupport_mono
    intro n hn; exact hn.1
  exact Module.Finite.of_injective (Submodule.inclusion h_le) (Submodule.inclusion_injective _)

end SupportedDim
