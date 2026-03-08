/-
  ProfileDecomp.lean — Progressive proof of profile_decomposition

  Decomposes the blocked SPDP subspace by gate: since p = Σ gate(i),
  linearity of derivatives gives blockedSpdpSubspace ≤ ⨆ gateSubspace(i).

  Each per-gate subspace has bounded dimension (via containment in
  restrictTotalDegree), and the number of pieces ≤ numGates * width.
-/
import PallLean.SPDPDefs
import Mathlib.Tactic

namespace ProfileDecomp

open MvPolynomial SPDP

variable {v : ℕ} {F : Type*} [Field F]

/-! ## iterDerivList linearity -/

theorem iterDerivList_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin v) F)
    (S : List (Fin v)) :
    iterDerivList S (∑ i ∈ s, f i) = ∑ i ∈ s, iterDerivList S (f i) := by
  induction S generalizing f with
  | nil => simp [iterDerivList]
  | cons j rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    have h1 : ∀ g : ι → MvPolynomial (Fin v) F,
        List.foldl (fun q i => pderiv i q) (pderiv j (∑ i ∈ s, g i)) rest =
        iterDerivList rest (pderiv j (∑ i ∈ s, g i)) := fun _ => rfl
    rw [h1, map_sum, ih]
    rfl

/-! ## Per-gate subspace -/

noncomputable def gateSubspace
    (B : BlockPartition v) (κ ℓ : ℕ)
    (gate : MvPolynomial (Fin v) F) :
    Submodule F (MvPolynomial (Fin v) F) :=
  Submodule.span F
    { q | ∃ (S : List (Fin v)) (m : MvPolynomial (Fin v) F),
        S.length = κ ∧ m.totalDegree ≤ ℓ ∧
        isBlockAdmissible B S ∧
        q = m * iterDerivList S gate }

/-- The gate subspace is contained in restrictTotalDegree. -/
theorem gateSubspace_le_restrictTotalDegree
    (B : BlockPartition v) (κ ℓ : ℕ)
    (gate : MvPolynomial (Fin v) F) :
    gateSubspace B κ ℓ gate ≤
    restrictTotalDegree (Fin v) F (ℓ + gate.totalDegree) := by
  apply Submodule.span_le.mpr
  intro q ⟨S, m, _, hdeg, _, hq⟩
  show q ∈ restrictTotalDegree (Fin v) F (ℓ + gate.totalDegree)
  rw [MvPolynomial.mem_restrictTotalDegree, hq]
  exact le_trans (totalDegree_mul m _)
    (Nat.add_le_add hdeg (SPDP.totalDegree_iterDerivList_le S gate))

instance gateSubspace_finite
    (B : BlockPartition v) (κ ℓ : ℕ)
    (gate : MvPolynomial (Fin v) F) :
    Module.Finite F (gateSubspace B κ ℓ gate) := by
  have hle := gateSubspace_le_restrictTotalDegree B κ ℓ gate
  exact Module.Finite.of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)

/-- Per-gate finrank bound via containment in restrictTotalDegree. -/
theorem gateSubspace_finrank_le
    (B : BlockPartition v) (κ ℓ : ℕ)
    (gate : MvPolynomial (Fin v) F) :
    Module.finrank F (gateSubspace B κ ℓ gate) ≤
    Module.finrank F (MvPolynomial.restrictTotalDegree (Fin v) F (ℓ + gate.totalDegree)) :=
  Submodule.finrank_mono (gateSubspace_le_restrictTotalDegree B κ ℓ gate)

/-! ## Gate decomposition -/

theorem gate_decomposition
    (B : BlockPartition v) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin v) F)
    (h : HasLocalityStructure p) :
    blockedSpdpSubspace B κ ℓ p ≤
    ⨆ i : Fin h.numGates, gateSubspace B κ ℓ (h.gate i) := by
  apply Submodule.span_le.mpr
  intro q ⟨S, m, hlen, hdeg, hadm, _, _, hq⟩
  have hsum : iterDerivList S p = ∑ i : Fin h.numGates, iterDerivList S (h.gate i) := by
    conv_lhs => rw [h.sum_eq]
    exact iterDerivList_sum Finset.univ h.gate S
  rw [hq, hsum, Finset.mul_sum]
  apply Submodule.sum_mem
  intro i _
  exact (le_iSup (fun i => gateSubspace B κ ℓ (h.gate i)) i)
    (Submodule.subset_span ⟨S, m, hlen, hdeg, hadm, rfl⟩)

/-! ## Full profile decomposition -/

/-- Profile decomposition: the blocked SPDP subspace decomposes into
    at most numGates * width finite-dimensional pieces (gate subspaces).
    Requires width > 0 to ensure Fin R is nonempty enough to cover all gates.
    (When width = 0 and κ = 0, gate subspaces can be nonzero but Fin 0 is empty.) -/
theorem profile_decomposition_from_gates
    (B : BlockPartition v) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin v) F)
    (h : HasLocalityStructure p)
    (hw : 0 < h.width) :
    ∃ (m : ℕ) (U : Fin m → Submodule F (MvPolynomial (Fin v) F))
      (_ : ∀ i, Module.Finite F ↥(U i)),
      blockedSpdpSubspace B κ ℓ p ≤ ⨆ i, U i ∧
      m ≤ h.numGates * h.width := by
  let R := h.numGates * h.width
  let U : Fin R → Submodule F (MvPolynomial (Fin v) F) :=
    fun j => if hj : j.val < h.numGates then gateSubspace B κ ℓ (h.gate ⟨j.val, hj⟩) else ⊥
  have hfin : ∀ j : Fin R, Module.Finite F ↥(U j) := by
    intro j; simp only [U]; by_cases hj : j.val < h.numGates
    · rw [dif_pos hj]; infer_instance
    · rw [dif_neg hj]; infer_instance
  refine ⟨R, U, hfin, ?_, le_refl _⟩
  -- Cover: blockedSpdpSubspace ≤ ⨆ U
  apply le_trans (gate_decomposition B κ ℓ p h)
  apply iSup_le; intro i
  have hiR : i.val < R := lt_of_lt_of_le i.isLt (Nat.le_mul_of_pos_right _ hw)
  apply le_iSup_of_le ⟨i.val, hiR⟩
  show gateSubspace B κ ℓ (h.gate i) ≤ U ⟨i.val, hiR⟩
  change gateSubspace B κ ℓ (h.gate i) ≤
    (if hj : i.val < h.numGates then gateSubspace B κ ℓ (h.gate ⟨i.val, hj⟩) else ⊥)
  rw [dif_pos i.isLt]

end ProfileDecomp
