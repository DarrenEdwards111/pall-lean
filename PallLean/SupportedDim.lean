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
  by_cases hzero : SPDP.iterDerivList S V = 0
  · rw [heq, hzero, mul_zero]; exact zero_mem _
  · have hS_sub : S.toFinset ⊆ V.vars := by
      by_contra h; apply hzero
      exact VarsIterDeriv.iterDerivList_eq_zero_of_not_subset_vars S V h
    have hmem : ms * SPDP.iterDerivList S V ∈
        restrictSupportDeg ℚ (blockClosure bp V.vars) (ℓ + 6) := by
      rw [mem_restrictSupportDeg]
      constructor
      · calc (ms * SPDP.iterDerivList S V).totalDegree
            ≤ ms.totalDegree + (SPDP.iterDerivList S V).totalDegree :=
              MvPolynomial.totalDegree_mul ms (SPDP.iterDerivList S V)
          _ ≤ ℓ + V.totalDegree := Nat.add_le_add hdeg (SPDP.totalDegree_iterDerivList_le S V)
          _ ≤ ℓ + 6 := by omega
      · classical
        intro v hv
        rcases Finset.mem_union.mp (MvPolynomial.vars_mul ms (SPDP.iterDerivList S V) hv) with
          hms | hderiv
        · rw [Finset.mem_coe, mem_blockClosure]
          exact Finset.image_subset_image hS_sub (hcoupl v hms)
        · exact Finset.mem_coe.mpr (subset_blockClosure bp V.vars
            (VarsIterDeriv.vars_iterDerivList_subset S V hderiv))
    exact heq ▸ hmem


/-- finrank of restrictSupportDeg ≤ (card s + d)^(card s). -/
theorem finrank_restrictSupportDeg_le {σ : Type*} [DecidableEq σ] [Fintype σ]
    (s : Finset σ) (d : ℕ) :
    Module.finrank ℚ (restrictSupportDeg ℚ s d) ≤ (s.card + d) ^ s.card := by
  -- Step 1: restrictSupportDeg ⊆ span of monomial image
  have h_span : restrictSupportDeg ℚ s d ≤ Submodule.span ℚ
      ((fun m => MvPolynomial.monomial m (1 : ℚ)) '' (boundedSupp s d)) := by
    intro p hp
    rw [mem_restrictSupport_iff] at hp
    rw [← p.as_sum]
    apply Submodule.sum_mem
    intro m hm
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨m, hp hm, rfl⟩
  -- Step 2: boundedSupp s d is finite
  have h_finite : Set.Finite (boundedSupp s d) := by
    apply Set.Finite.subset (Set.Finite.pi (fun _ : σ => Set.finite_le_nat d))
    intro n ⟨hsum, hsupp⟩
    simp only [Set.mem_pi, Set.mem_Iic]
    intro i
    by_cases hi : n i = 0
    · omega
    · exact le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finsupp.mem_support_iff.mpr (by omega))) hsum
  -- Step 3: finrank chain
  have h_fin_image := h_finite.image (fun m => MvPolynomial.monomial m (1 : ℚ))
  calc Module.finrank ℚ (restrictSupportDeg ℚ s d)
      ≤ Module.finrank ℚ (Submodule.span ℚ
          ((fun m => MvPolynomial.monomial m (1 : ℚ)) '' boundedSupp s d)) :=
        Submodule.finrank_mono h_span
    _ ≤ h_fin_image.toFinset.card := finrank_span_le_card _
    _ ≤ h_finite.toFinset.card := Finset.card_image_le
    _ ≤ (s.card + d) ^ s.card := by
        -- Inject boundedSupp into (↥s → Fin (d+1)) via restriction
        -- Helper: n x ≤ n.sum id for x ∈ n.support
        have val_le_sum : ∀ (n : σ →₀ ℕ), ∀ x, n x ≤ n.sum (fun _ a => a) := by
          intro n x
          by_cases hx : n x = 0
          · omega
          · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
              (Finsupp.mem_support_iff.mpr (by omega))
        -- Define the encoding
        let encode : boundedSupp s d → (↥s → Fin (d + 1)) :=
          fun ⟨n, hsum, hsupp⟩ i => ⟨n ↑i, Nat.lt_succ_of_le (le_trans (val_le_sum n ↑i) hsum)⟩
        -- Prove injectivity
        have h_inj : Function.Injective encode := by
          intro ⟨a, ha_sum, ha_supp⟩ ⟨b, hb_sum, hb_supp⟩ h
          simp only [encode, Subtype.mk.injEq] at h ⊢
          ext x
          by_cases hx : x ∈ s
          · have := congr_fun h ⟨x, hx⟩
            exact Fin.ext_iff.mp this
          · have ha0 : a x = 0 := by
              by_contra hne
              exact hx (Finset.mem_coe.mp (ha_supp (Finsupp.mem_support_iff.mpr (by omega))))
            have hb0 : b x = 0 := by
              by_contra hne
              exact hx (Finset.mem_coe.mp (hb_supp (Finsupp.mem_support_iff.mpr (by omega))))
            simp [ha0, hb0]
        -- Card bound
        have h_type_card : Fintype.card (↥s → Fin (d + 1)) = (d + 1) ^ s.card := by
          simp [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
        -- Use Set.Finite.toFinset_card_le via injection
        calc h_finite.toFinset.card
            ≤ Fintype.card (↥s → Fin (d + 1)) := by
              rw [← h_finite.toFinset_card]
              exact Fintype.card_le_of_injective encode h_inj
          _ = (d + 1) ^ s.card := h_type_card
          _ ≤ (s.card + d) ^ s.card := Nat.pow_le_pow_left (by omega) _


/-- Module.Finite for restrictSupportDeg (subset of restrictTotalDegree). -/
instance instFinite_restrictSupportDeg {σ : Type*} [DecidableEq σ] [Fintype σ]
    (s : Finset σ) (d : ℕ) : Module.Finite ℚ (restrictSupportDeg ℚ s d) := by
  unfold restrictSupportDeg
  have h_le : restrictSupport ℚ (boundedSupp s d) ≤ restrictTotalDegree σ ℚ d := by
    apply restrictSupport_mono
    intro n hn; exact hn.1
  exact Module.Finite.of_injective (Submodule.inclusion h_le) (Submodule.inclusion_injective _)

end SupportedDim
