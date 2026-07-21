import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGeneralExtract

/-!
# Brick C of the ∀m `SlackComposes` campaign: the slot-multiplicity counting identity

The excess budget, counted with slot multiplicity (a gate reading the same wire
in both slots creates multiplicity just as two distinct readers do):

* `slotCnt` / `slotReads` — how many gate-slots of the cone read a wire;
* **`slotReads_pos` (proved)** — every non-root cone wire is read;
* **`cone_ge_slot` (proved)** — `2·|coneVars| + X ≤ |cone| + 1` where
  `X = Σ (slotReads − 1)` is the total excess;
* **`reconvR_card_le` (proved)** — the reconvergence wires (`slotReads ≥ 2`)
  number at most `X`;
* **`readers_unique_of_not_reconv` (proved)** — away from the reconvergence
  set, cone readers are unique (chain determinism for brick D);
* **`AEm_coneVars_ge` (proved)** — `3m ≤ |coneVars|` for circuits computing
  `AEm m`.

With the pillars (`B ≤ t`, `D ≤ v`) this yields
`|cone| + 1 ≥ 2V + X = 6m + 2v + X ≥ 7m`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- Slot-multiplicity count of reads of wire `q` by a single gate. -/
def slotCnt {n : ℕ} (g : CGate n) (q : ℕ) : ℕ :=
  match g with
  | .var _ => 0
  | .cst _ => 0
  | .un _ j => if j = q then 1 else 0
  | .bin _ j k => (if j = q then 1 else 0) + (if k = q then 1 else 0)

/-- Slot-multiplicity count of cone reads of wire `q`. -/
noncomputable def slotReads (c : List (CGate n)) (q : ℕ) : ℕ :=
  ∑ w ∈ cone c, slotCnt (c.getD w (.cst false)) q

/-- Total excess over the non-root cone wires. -/
noncomputable def excessX (c : List (CGate n)) : ℕ :=
  ∑ q ∈ (cone c).erase (c.length - 1), (slotReads c q - 1)

/-- The reconvergence wires: non-root cone wires with slot-multiplicity ≥ 2. -/
noncomputable def reconvR (c : List (CGate n)) : Finset ℕ :=
  ((cone c).erase (c.length - 1)).filter (fun q => 2 ≤ slotReads c q)

theorem slotCnt_le_inSlots_sum {n : ℕ} (g : CGate n) (S : Finset ℕ) :
    ∑ q ∈ S, slotCnt g q ≤ inSlots g := by
  cases g with
  | var i => simp [slotCnt, inSlots]
  | cst b => simp [slotCnt, inSlots]
  | un op j =>
    show ∑ q ∈ S, (if j = q then 1 else 0) ≤ 1
    rw [Finset.sum_ite_eq S j (fun _ => 1)]
    split <;> omega
  | bin op j k =>
    show ∑ q ∈ S, ((if j = q then 1 else 0) + (if k = q then 1 else 0)) ≤ 2
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq S j (fun _ => 1),
      Finset.sum_ite_eq S k (fun _ => 1)]
    split <;> split <;> omega

theorem slotCnt_pos_of_reads {n : ℕ} (g : CGate n) (q : ℕ)
    (h : q ∈ gateReads g) : 1 ≤ slotCnt g q := by
  cases g with
  | var i => exact absurd h (by simp [gateReads])
  | cst b => exact absurd h (by simp [gateReads])
  | un op j =>
    have hj : j = q := (Finset.mem_singleton.mp h).symm
    show 1 ≤ if j = q then 1 else 0
    rw [if_pos hj]
  | bin op j k =>
    show 1 ≤ (if j = q then 1 else 0) + (if k = q then 1 else 0)
    rcases Finset.mem_insert.mp h with hj | hk
    · rw [if_pos hj.symm]
      omega
    · rw [if_pos (Finset.mem_singleton.mp hk).symm]
      omega

/-- **Every non-root cone wire is read (proved, slot form).** -/
theorem slotReads_pos {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length)
    {q : ℕ} (hq : q ∈ (cone c).erase (c.length - 1)) : 1 ≤ slotReads c q := by
  obtain ⟨hqne, hqc⟩ := Finset.mem_erase.mp hq
  obtain ⟨hqlt, hqcone⟩ := mem_cone.mp hqc
  cases hqcone with
  | root => exact absurd rfl hqne
  | step hw hjm hjw =>
    rename_i w'
    have hwc : w' ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hw, hw⟩
    calc (1 : ℕ) ≤ slotCnt (c.getD w' (.cst false)) q :=
          slotCnt_pos_of_reads _ q hjm
      _ ≤ slotReads c q := by
          rw [slotReads]
          exact Finset.single_le_sum
            (f := fun w => slotCnt (c.getD w (.cst false)) q)
            (fun w _ => Nat.zero_le _) hwc

/-- **THE SLOT IDENTITY (proved)**: `2·|coneVars| + X ≤ |cone| + 1`. -/
theorem cone_ge_slot {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length) :
    2 * (coneVars c).card + excessX c ≤ (cone c).card + 1 := by
  classical
  have hroot : c.length - 1 ∈ cone c := mem_cone.mpr ⟨by omega, InCone.root⟩
  -- Σ slotReads over non-root wires = (|cone| − 1) + X
  have hsum1 : ∑ q ∈ (cone c).erase (c.length - 1), slotReads c q
      = ((cone c).card - 1) + excessX c := by
    have hcong : ∑ q ∈ (cone c).erase (c.length - 1), slotReads c q
        = ∑ q ∈ (cone c).erase (c.length - 1), ((slotReads c q - 1) + 1) := by
      refine Finset.sum_congr rfl (fun q hq => ?_)
      have := slotReads_pos c hs hq
      omega
    rw [hcong, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_one,
      Finset.card_erase_of_mem hroot]
    rw [excessX]
    omega
  -- Σ slotReads ≤ Σ inSlots over cone gates (double count)
  have hsum2 : ∑ q ∈ (cone c).erase (c.length - 1), slotReads c q
      ≤ ∑ w ∈ cone c, inSlots (c.getD w (.cst false)) := by
    show ∑ q ∈ (cone c).erase (c.length - 1), ∑ w ∈ cone c,
        slotCnt (c.getD w (.cst false)) q ≤ _
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun w _ => slotCnt_le_inSlots_sum _ _)
  -- Σ inSlots ≤ 2 (|cone| − |coneVars|)
  have hsplit : ∑ w ∈ coneVars c, inSlots (c.getD w (.cst false))
      + ∑ w ∈ (cone c).filter
          (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
          inSlots (c.getD w (.cst false))
      = ∑ w ∈ cone c, inSlots (c.getD w (.cst false)) := by
    rw [coneVars]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hvar0 : ∑ w ∈ coneVars c, inSlots (c.getD w (.cst false)) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    rw [coneVars, Finset.mem_filter] at hw
    obtain ⟨-, i', hi'⟩ := hw
    rw [hi']
    rfl
  have hrest : ∑ w ∈ (cone c).filter
      (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
      inSlots (c.getD w (.cst false))
      ≤ 2 * ((cone c).filter
        (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')).card := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ 2 (fun w _ => inSlots_le_two _)) ?_
    rw [smul_eq_mul]
    omega
  have hpart : (coneVars c).card
      + ((cone c).filter
        (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')).card
      = (cone c).card := by
    rw [coneVars]
    exact Finset.card_filter_add_card_filter_not (s := cone c)
      (p := fun w => ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')
  have hcpos : 1 ≤ (cone c).card := Finset.card_pos.mpr ⟨_, hroot⟩
  omega

/-- **The reconvergence wires number at most the excess (proved).** -/
theorem reconvR_card_le {n : ℕ} (c : List (CGate n)) :
    (reconvR c).card ≤ excessX c := by
  classical
  calc (reconvR c).card
      = ∑ _q ∈ reconvR c, 1 := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
    _ ≤ ∑ q ∈ reconvR c, (slotReads c q - 1) := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        rw [reconvR, Finset.mem_filter] at hq
        omega
    _ ≤ excessX c := by
        rw [excessX]
        exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- **Chain determinism away from the reconvergence set (proved)**: a non-root
non-reconvergence cone wire has a unique cone reader. -/
theorem readers_unique_of_not_reconv {n : ℕ} (c : List (CGate n))
    (hs : 0 < c.length) {q : ℕ} (hq : q ∈ (cone c).erase (c.length - 1))
    (hqr : q ∉ reconvR c) {w₁ w₂ : ℕ} (h₁ : w₁ ∈ cone c) (h₂ : w₂ ∈ cone c)
    (hr₁ : q ∈ gateReads (c.getD w₁ (.cst false)))
    (hr₂ : q ∈ gateReads (c.getD w₂ (.cst false))) : w₁ = w₂ := by
  classical
  by_contra hne
  have h2le : 2 ≤ slotReads c q := by
    calc (2 : ℕ) ≤ slotCnt (c.getD w₁ (.cst false)) q
          + slotCnt (c.getD w₂ (.cst false)) q := by
          have hp₁ := slotCnt_pos_of_reads (c.getD w₁ (.cst false)) q hr₁
          have hp₂ := slotCnt_pos_of_reads (c.getD w₂ (.cst false)) q hr₂
          omega
      _ = ∑ w ∈ ({w₁, w₂} : Finset ℕ), slotCnt (c.getD w (.cst false)) q := by
          rw [Finset.sum_pair hne]
      _ ≤ slotReads c q := by
          refine Finset.sum_le_sum_of_subset ?_
          intro w hw
          rcases Finset.mem_insert.mp hw with h | h
          · rw [h]; exact h₁
          · rw [Finset.mem_singleton.mp h]; exact h₂
  exact hqr (Finset.mem_filter.mpr ⟨hq, h2le⟩)

/-- `3m ≤ |coneVars|` for circuits computing `AEm m`. -/
theorem AEm_coneVars_ge (m : ℕ) (c : List (CGate (3 * m)))
    (hcomp : computes c (AEm m)) (hs : 0 < c.length) :
    3 * m ≤ (coneVars c).card := by
  have h := depSet_card_le_coneVars (AEm m) c hcomp hs
  have hd : (depSet (AEm m)).card = 3 * m := by
    rw [depSet_AEm, Finset.card_univ, Fintype.card_fin]
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cone_ge_slot
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.reconvR_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.readers_unique_of_not_reconv
