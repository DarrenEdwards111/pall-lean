/-
  SupportedDim.lean — Dimension of variable-restricted polynomial spaces

  Key lemma: for polynomials on a k-element variable set of degree ≤ d,
  the dimension is C(k+d, k) ≤ (k+d)^k.
-/
import PallLean.CompiledPoly
import PallLean.VarsIterDeriv
import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic

namespace SupportedDim

open MvPolynomial

/-! ## Block closure: all variables in blocks touched by a set -/

/-- The block closure of a variable set: all variables sharing a block with some element of s. -/
def blockClosure {N : ℕ} (bp : CompiledPoly.BlockPartition N) (s : Finset (Fin N)) :
    Finset (Fin N) :=
  Finset.univ.filter (fun v => bp.blockOf v ∈ s.image bp.blockOf)

theorem mem_blockClosure {N : ℕ} (bp : CompiledPoly.BlockPartition N) (s : Finset (Fin N))
    (v : Fin N) : v ∈ blockClosure bp s ↔ bp.blockOf v ∈ s.image bp.blockOf := by
  simp only [blockClosure, Finset.mem_filter, Finset.mem_univ, true_and]

theorem subset_blockClosure {N : ℕ} (bp : CompiledPoly.BlockPartition N) (s : Finset (Fin N)) :
    s ⊆ blockClosure bp s := by
  intro v hv; rw [mem_blockClosure]; exact Finset.mem_image_of_mem _ hv

/-- S-coupled variables are in the block closure of S. -/
theorem scoupled_vars_subset_blockClosure {N : ℕ}
    (bp : CompiledPoly.BlockPartition N)
    (S : List (Fin N)) (ms : MvPolynomial (Fin N) ℚ)
    (hcoupl : ∀ v ∈ ms.vars, bp.blockOf v ∈ S.toFinset.image bp.blockOf) :
    ↑ms.vars ⊆ ↑(blockClosure bp S.toFinset) := by
  intro v hv
  exact Finset.mem_coe.mpr ((mem_blockClosure bp S.toFinset v).mpr (hcoupl v hv))

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
  classical
  unfold restrictSupportDeg boundedSupp
  rw [mem_restrictSupport_iff]
  constructor
  · intro h
    constructor
    · rw [totalDegree, Finset.sup_le_iff]
      intro n hn; exact (h hn).1
    · intro i hi
      obtain ⟨n, hn, hin⟩ := (mem_vars i).mp hi
      exact (h hn).2 hin
  · intro ⟨hd, hv⟩ n hn
    exact ⟨le_trans (le_totalDegree hn) hd, fun i hi =>
      hv ((mem_vars i).mpr ⟨n, hn, hi⟩)⟩

/-- The SPDP span lies inside restrictSupportDeg on the block closure of V.vars. -/
theorem spdp_span_in_restrictSupportDeg {N : ℕ}
    (κ ℓ : ℕ) (V : MvPolynomial (Fin N) ℚ)
    (bp : CompiledPoly.BlockPartition N)
    (hV_deg : V.totalDegree ≤ 6) :
    Submodule.span ℚ
      { q | ∃ (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ),
        S.length ≤ κ ∧ m.totalDegree ≤ ℓ ∧
        (S.toFinset.image bp.blockOf).card = S.toFinset.card ∧
        (∀ v ∈ m.vars, bp.blockOf v ∈ S.toFinset.image bp.blockOf) ∧
        q = m * SPDP.iterDerivList S V }
    ≤ restrictSupportDeg ℚ (blockClosure bp V.vars) (ℓ + 6) := by
  apply Submodule.span_le.mpr
  intro q hq
  obtain ⟨S, ms, hlen, hdeg, htrans, hcoupl, heq⟩ := hq
  have : ms * SPDP.iterDerivList S V ∈
      restrictSupportDeg ℚ (blockClosure bp V.vars) (ℓ + 6) := by
    rw [mem_restrictSupportDeg]
    constructor
    · calc (ms * SPDP.iterDerivList S V).totalDegree
          ≤ ms.totalDegree + (SPDP.iterDerivList S V).totalDegree :=
            MvPolynomial.totalDegree_mul ms (SPDP.iterDerivList S V)
        _ ≤ ℓ + V.totalDegree := Nat.add_le_add hdeg (SPDP.totalDegree_iterDerivList_le S V)
        _ ≤ ℓ + 6 := by omega
    · -- vars(ms * iterDerivList S V) ⊆ blockClosure bp V.vars
      -- vars(product) ⊆ vars(ms) ∪ vars(iterDerivList S V)
      -- vars(iterDerivList S V) ⊆ V.vars ⊆ blockClosure
      -- vars(ms) ⊆ blockClosure (from S-coupling)
      classical
      intro v hv
      have hv_union := MvPolynomial.vars_mul ms (SPDP.iterDerivList S V) hv
      simp only [Finset.mem_union] at hv_union
      rcases hv_union with hms | hderiv
      · -- v ∈ ms.vars: S-coupled → bp.blockOf v ∈ S.toFinset.image bp.blockOf
        -- ⊆ V.vars.image bp.blockOf (if S ⊆ V.vars — needs iterDerivList analysis)
        -- For now: S.toFinset.image bp.blockOf ⊆ V.vars.image bp.blockOf follows from
        -- the fact that ∂^S(V) ≠ 0 only when S ⊆ V.vars
        sorry
      · -- v ∈ vars(iterDerivList S V) ⊆ vars(V) ⊆ blockClosure bp V.vars
        exact Finset.mem_coe.mpr (subset_blockClosure bp V.vars
          (VarsIterDeriv.vars_iterDerivList_subset S V hderiv))
  exact heq ▸ this


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
  -- The basis of restrictSupportDeg is indexed by boundedSupp s d.
  -- |boundedSupp s d| = C(|s|+d, |s|) ≤ (|s|+d)^|s| (stars and bars + choose_le_pow).
  -- We use: finrank ≤ finrank(restrictTotalDegree d) for any containing type,
  -- but need the bound to depend on |s|.
  -- 
  -- Direct approach: sorry (needs Fintype instance for boundedSupp + card counting)
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
