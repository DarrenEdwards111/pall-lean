import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA5a

/-!
# Shrinkage brick A5b: THE TELESCOPE

The one-step iterated over all restriction sequences — with NO explicit
sequence space: `resSum` recursively sums the restricted measures over every
extension, and the telescope bounds it by the shrink product:

* `shrinkP s r = Π_{j<r} (2(s−j) − 3)` and `bigN s r = Π_{j<r} 2(s−j)`;
* `resSum r R f` — the sum of `dmsizeC` over all `r`-step restriction
  sequences with distinct variables from `R`;
* **`resSum_le` (proved)** — for any tree witness supported on `R` with
  `r + 2 ≤ |R|`:
  `resSum r R (eval t) ≤ shrinkP |R| r · L₀(t) + r · bigN |R| r`.
  Each step re-normalizes via `normalize'` (count-tracking) and applies
  `onestep_core`; the `+1`s accumulate into the `r · bigN` error, absorbed
  because each shrink factor is below its `bigN` factor.

The ratio `shrinkP/bigN ≈ ((s−r)/s)^{3/2}` is the Γ = 3/2 recovery.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-! ### The shrink products -/

def shrinkP : ℕ → ℕ → ℕ
  | _, 0 => 1
  | s, r + 1 => (2 * s - 3) * shrinkP (s - 1) r

def bigN : ℕ → ℕ → ℕ
  | _, 0 => 1
  | s, r + 1 => (2 * s) * bigN (s - 1) r

theorem shrinkP_le_bigN : ∀ (r s : ℕ), shrinkP s r ≤ bigN s r := by
  intro r
  induction r with
  | zero => intro s; exact le_refl _
  | succ r ih =>
    intro s
    show (2 * s - 3) * shrinkP (s - 1) r ≤ (2 * s) * bigN (s - 1) r
    exact Nat.mul_le_mul (by omega) (ih (s - 1))

theorem litInd_le_one {n : ℕ} (t : DMTreeC n) : litInd t ≤ 1 := by
  cases t with
  | lit i b => exact le_refl _
  | cst v => exact Nat.zero_le _
  | and l r => exact Nat.zero_le _
  | or l r => exact Nat.zero_le _

/-! ### The recursive restriction sum -/

/-- Sum of restricted measures over all `r`-step sequences from `R`. -/
noncomputable def resSum {n : ℕ} :
    ℕ → Finset (Fin n) → ((Fin n → Bool) → Bool) → ℕ
  | 0, _, f => dmsizeC f
  | r + 1, R, f => ∑ i ∈ R,
      (resSum r (R.erase i) (restrictF1 i false f)
        + resSum r (R.erase i) (restrictF1 i true f))

/-- **THE TELESCOPE (proved)**: iterated Subbotovskaya shrinkage. -/
theorem resSum_le {n : ℕ} : ∀ (r : ℕ) (R : Finset (Fin n)) (t : DMTreeC n),
    r + 2 ≤ R.card → (∀ i, cntC i t ≠ 0 → i ∈ R) →
    resSum r R (fun x => t.eval x)
      ≤ shrinkP R.card r * t.lsize0 + r * bigN R.card r := by
  intro r
  induction r with
  | zero =>
    intro R t _ _
    show dmsizeC (fun x => t.eval x) ≤ 1 * t.lsize0 + 0 * 1
    have h := dmsizeC_leC (fun x => t.eval x) t (fun _ => rfl)
    omega
  | succ r ih =>
    intro R t hcard hsupp
    classical
    obtain ⟨t', ht'e, ht's, hcase, ht'c⟩ := normalize' t
    have hsupp' : ∀ i, cntC i t' ≠ 0 → i ∈ R := by
      intro i hi
      refine hsupp i ?_
      intro h0
      have := ht'c i
      omega
    have hfe : (fun x => t.eval x) = (fun x => t'.eval x) :=
      funext (fun x => (ht'e x).symm)
    show (∑ i ∈ R,
        (resSum r (R.erase i) (restrictF1 i false (fun x => t.eval x))
          + resSum r (R.erase i) (restrictF1 i true (fun x => t.eval x))))
      ≤ shrinkP R.card (r + 1) * t.lsize0 + (r + 1) * bigN R.card (r + 1)
    have hpt : ∀ i ∈ R,
        (resSum r (R.erase i) (restrictF1 i false (fun x => t.eval x))
          + resSum r (R.erase i) (restrictF1 i true (fun x => t.eval x)))
        ≤ shrinkP (R.card - 1) r
            * ((simpC (subst1 i false t')).lsize0
              + (simpC (subst1 i true t')).lsize0)
          + 2 * (r * bigN (R.card - 1) r) := by
      intro i hiR
      have hcarde : r + 2 ≤ (R.erase i).card := by
        rw [Finset.card_erase_of_mem hiR]
        omega
      have hsupp_ib : ∀ b : Bool, ∀ j,
          cntC j (simpC (subst1 i b t')) ≠ 0 → j ∈ R.erase i := by
        intro b j hj
        have h1 : cntC j (simpC (subst1 i b t')) ≤ cntC j (subst1 i b t') :=
          cntC_simpC_le _ _
        have h2 : cntC j (subst1 i b t') ≤ cntC j t' :=
          cntC_subst1_le _ _ _ _
        refine Finset.mem_erase.mpr ⟨?_, hsupp' j (by omega)⟩
        intro hji
        subst hji
        have h3 := cntC_subst1_self j b t'
        omega
      have hIH : ∀ b : Bool,
          resSum r (R.erase i) (restrictF1 i b (fun x => t.eval x))
          ≤ shrinkP (R.card - 1) r * (simpC (subst1 i b t')).lsize0
            + r * bigN (R.card - 1) r := by
        intro b
        have hfeq : restrictF1 i b (fun x => t.eval x)
            = (fun x => (simpC (subst1 i b t')).eval x) := by
          have h1 : restrictF1 i b (fun x => t.eval x)
              = restrictF1 i b (fun x => t'.eval x) := by rw [hfe]
          rw [h1]
          exact (funext (restricted_tree_computes i b t'
            (fun x => t'.eval x) (fun _ => rfl))).symm
        rw [hfeq]
        have h := ih (R.erase i) (simpC (subst1 i b t')) hcarde (hsupp_ib b)
        rw [Finset.card_erase_of_mem hiR] at h
        exact h
      have hf := hIH false
      have ht2 := hIH true
      have hd : shrinkP (R.card - 1) r
          * ((simpC (subst1 i false t')).lsize0
            + (simpC (subst1 i true t')).lsize0)
          = shrinkP (R.card - 1) r * (simpC (subst1 i false t')).lsize0
            + shrinkP (R.card - 1) r * (simpC (subst1 i true t')).lsize0 :=
        Nat.mul_add _ _ _
      omega
    have hsum := Finset.sum_le_sum hpt
    have hsplitR : (∑ i ∈ R, (shrinkP (R.card - 1) r
        * ((simpC (subst1 i false t')).lsize0
          + (simpC (subst1 i true t')).lsize0)
        + 2 * (r * bigN (R.card - 1) r)))
        = (∑ i ∈ R, shrinkP (R.card - 1) r
            * ((simpC (subst1 i false t')).lsize0
              + (simpC (subst1 i true t')).lsize0))
          + R.card * (2 * (r * bigN (R.card - 1) r)) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
    have hmulsum : (∑ i ∈ R, shrinkP (R.card - 1) r
        * ((simpC (subst1 i false t')).lsize0
          + (simpC (subst1 i true t')).lsize0))
        = shrinkP (R.card - 1) r * (∑ i ∈ R,
            ((simpC (subst1 i false t')).lsize0
              + (simpC (subst1 i true t')).lsize0)) := by
      rw [Finset.mul_sum]
    have hPs : shrinkP R.card (r + 1)
        = (2 * R.card - 3) * shrinkP (R.card - 1) r := rfl
    have hNs : bigN R.card (r + 1) = (2 * R.card) * bigN (R.card - 1) r := rfl
    have hcomm : R.card * (2 * (r * bigN (R.card - 1) r))
        = r * (2 * R.card * bigN (R.card - 1) r) := by ring
    rcases hcase with ⟨v, hv⟩ | ⟨hcf', hnorm'⟩
    · subst hv
      have hzero : (∑ i ∈ R,
          ((simpC (subst1 i false (.cst v : DMTreeC n))).lsize0
            + (simpC (subst1 i true (.cst v : DMTreeC n))).lsize0)) = 0 :=
        Finset.sum_eq_zero (fun i _ => rfl)
      have hz2 : shrinkP (R.card - 1) r * (∑ i ∈ R,
          ((simpC (subst1 i false (.cst v : DMTreeC n))).lsize0
            + (simpC (subst1 i true (.cst v : DMTreeC n))).lsize0)) = 0 := by
        rw [hzero, Nat.mul_zero]
      rw [hPs, hNs]
      have hexp : (r + 1) * (2 * R.card * bigN (R.card - 1) r)
          = r * (2 * R.card * bigN (R.card - 1) r)
            + 2 * R.card * bigN (R.card - 1) r := Nat.succ_mul _ _
      omega
    · have hos := onestep_core R t' hcf' hnorm' hsupp'
      have hli1 := litInd_le_one t'
      have hSstep : (∑ i ∈ R,
          ((simpC (subst1 i false t')).lsize0
            + (simpC (subst1 i true t')).lsize0))
          ≤ (2 * R.card - 3) * t'.lsize0 + 1 := by
        have h3 : (2 * R.card - 3) * t'.lsize0 + 3 * t'.lsize0
            = 2 * R.card * t'.lsize0 := by
          rw [← Nat.add_mul]
          congr 1
          omega
        omega
      have hm1 : shrinkP (R.card - 1) r * (∑ i ∈ R,
          ((simpC (subst1 i false t')).lsize0
            + (simpC (subst1 i true t')).lsize0))
          ≤ shrinkP (R.card - 1) r * ((2 * R.card - 3) * t'.lsize0 + 1) :=
        Nat.mul_le_mul_left _ hSstep
      have hm2 : shrinkP (R.card - 1) r * ((2 * R.card - 3) * t'.lsize0 + 1)
          = (2 * R.card - 3) * shrinkP (R.card - 1) r * t'.lsize0
            + shrinkP (R.card - 1) r := by
        rw [Nat.mul_add, Nat.mul_one]
        congr 1
        rw [← Nat.mul_assoc, Nat.mul_comm (shrinkP (R.card - 1) r)
          (2 * R.card - 3)]
      have hm3 : (2 * R.card - 3) * shrinkP (R.card - 1) r * t'.lsize0
          ≤ (2 * R.card - 3) * shrinkP (R.card - 1) r * t.lsize0 :=
        Nat.mul_le_mul_left _ ht's

      have hm4 : shrinkP (R.card - 1) r
          ≤ 2 * R.card * bigN (R.card - 1) r := by
        have h1 := shrinkP_le_bigN r (R.card - 1)
        have h2 : bigN (R.card - 1) r
            ≤ 2 * R.card * bigN (R.card - 1) r := by
          have h3 : 1 * bigN (R.card - 1) r
              ≤ (2 * R.card) * bigN (R.card - 1) r :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        omega
      have hexp : (r + 1) * (2 * R.card * bigN (R.card - 1) r)
          = r * (2 * R.card * bigN (R.card - 1) r)
            + 2 * R.card * bigN (R.card - 1) r := Nat.succ_mul _ _
      rw [hPs, hNs]
      omega

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.resSum_le
