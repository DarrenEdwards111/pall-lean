import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSharingSensitiveMCSP

/-!
# Canonical Hamming paths through the sharing-sensitive MCSP threshold

The one-bit repair theorem extends along a canonical coordinate-by-coordinate
path between truth tables.  This file proves:

* a `k`-step DAG-size Lipschitz bound along that path;
* a discrete crossing lemma for arbitrary Boolean paths;
* every easy-to-hard truth-table path contains an MCSP boundary edge, and that
  edge lies in the `3n+3` inner-size band.

This proves boundary *existence* from any hard endpoint.  It deliberately does
not claim boundary abundance: collisions between paths at their first crossing
are the remaining expansion problem required by hardness magnification.
-/

namespace PallLean.Paper93.DeepMath.PathB.SharingSensitiveMCSP

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound

/-- Replace the first `k` coordinates of `z` by their values in `w`. -/
def tablePath {n : ℕ} (z w : Fin (2 ^ n) → Bool) (k : ℕ) :
    Fin (2 ^ n) → Bool :=
  fun i => if i.val < k then w i else z i

@[simp] theorem tablePath_zero {n : ℕ} (z w : Fin (2 ^ n) → Bool) :
    tablePath z w 0 = z := by
  funext i
  simp [tablePath]

@[simp] theorem tablePath_full {n : ℕ} (z w : Fin (2 ^ n) → Bool) :
    tablePath z w (2 ^ n) = w := by
  funext i
  simp [tablePath, i.isLt]

theorem tablePath_succ {n k : ℕ} (z w : Fin (2 ^ n) → Bool)
    (hk : k < 2 ^ n) :
    tablePath z w (k + 1) =
      Function.update (tablePath z w k) (⟨k, hk⟩ : Fin (2 ^ n)) (w ⟨k, hk⟩) := by
  funext i
  by_cases hi : i = (⟨k, hk⟩ : Fin (2 ^ n))
  · subst i
    simp [tablePath]
  · have hne : i.val ≠ k := by
      intro h
      apply hi
      exact Fin.ext h
    have hiff : i.val < k + 1 ↔ i.val < k := by omega
    rw [Function.update_of_ne hi]
    simp only [tablePath, hiff]

/-- One canonical path step has the same `3n+3` sharing-preserving cost as a
single arbitrary truth-table update. -/
theorem cbudget_tablePath_step {n k : ℕ} (z w : Fin (2 ^ n) → Bool)
    (hk : k < 2 ^ n) :
    cbudget (fnOfTable (tablePath z w (k + 1))) ≤
      cbudget (fnOfTable (tablePath z w k)) + (3 * n + 3) := by
  rw [tablePath_succ z w hk]
  exact cbudget_fnOfTable_update_le _ _ _

/-- **Multibit sharing-sensitive Lipschitz bound.**  After `k` canonical
truth-table changes, minimum DAG size has increased by at most
`k * (3n+3)`. -/
theorem cbudget_tablePath_le {n k : ℕ} (z w : Fin (2 ^ n) → Bool)
    (hk : k ≤ 2 ^ n) :
    cbudget (fnOfTable (tablePath z w k)) ≤
      cbudget (fnOfTable z) + k * (3 * n + 3) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hlt : k < 2 ^ n := Nat.lt_of_succ_le hk
      calc
        cbudget (fnOfTable (tablePath z w (k + 1))) ≤
            cbudget (fnOfTable (tablePath z w k)) + (3 * n + 3) :=
          cbudget_tablePath_step z w hlt
        _ ≤ (cbudget (fnOfTable z) + k * (3 * n + 3)) + (3 * n + 3) :=
          Nat.add_le_add_right (ih (Nat.le_of_succ_le hk)) _
        _ = cbudget (fnOfTable z) + (k + 1) * (3 * n + 3) := by
          simp [Nat.add_mul, Nat.add_assoc]

theorem cbudget_table_le_of_path {n : ℕ} (z w : Fin (2 ^ n) → Bool) :
    cbudget (fnOfTable w) ≤
      cbudget (fnOfTable z) + (2 ^ n) * (3 * n + 3) := by
  rw [← tablePath_full z w]
  exact cbudget_tablePath_le z w (le_rfl : 2 ^ n ≤ 2 ^ n)

/-! ## A discrete intermediate-value theorem -/

/-- Any finite Boolean path starting at `true` and ending at `false` has a
consecutive `true`-to-`false` transition. -/
theorem bool_path_crossing (P : ℕ → Bool) (N : ℕ)
    (hzero : P 0 = true) (hend : P N = false) :
    ∃ k, k < N ∧ P k = true ∧ P (k + 1) = false := by
  induction N with
  | zero => simp_all
  | succ N ih =>
      by_cases hprev : P N = true
      · exact ⟨N, Nat.lt_succ_self N, hprev, hend⟩
      · have hprevFalse : P N = false := Bool.eq_false_of_not_eq_true hprev
        obtain ⟨k, hk, hkt, hkf⟩ := ih hprevFalse
        exact ⟨k, hk.trans (Nat.lt_succ_self N), hkt, hkf⟩

/-! ## Easy-to-hard paths meet the narrow MCSP boundary -/

/-- Every canonical path from an accepted truth table to a rejected one has a
YES-to-NO edge.  The inner minimum circuit sizes at that edge straddle `s`
inside the already-proved band of width `3n+3`.

This is the exact point where the local theory stops: turning the existence of
one crossing per endpoint into many *distinct* crossings requires a congestion
or expansion theorem. -/
theorem circuitMCSP_path_crossing {n s : ℕ}
    (z w : Fin (2 ^ n) → Bool)
    (hyes : circuitMCSP n s z = true)
    (hno : circuitMCSP n s w = false) :
    ∃ k, k < 2 ^ n ∧
      circuitMCSP n s (tablePath z w k) = true ∧
      circuitMCSP n s (tablePath z w (k + 1)) = false ∧
      cbudget (fnOfTable (tablePath z w k)) ≤ s ∧
      s < cbudget (fnOfTable (tablePath z w (k + 1))) ∧
      cbudget (fnOfTable (tablePath z w (k + 1))) ≤ s + (3 * n + 3) := by
  have hstart : circuitMCSP n s (tablePath z w 0) = true := by simpa using hyes
  have hend : circuitMCSP n s (tablePath z w (2 ^ n)) = false := by simpa using hno
  obtain ⟨k, hk, hkt, hkf⟩ := bool_path_crossing
    (fun j => circuitMCSP n s (tablePath z w j)) (2 ^ n) hstart hend
  have hstep := tablePath_succ z w hk
  have hkf' : circuitMCSP n s
      (Function.update (tablePath z w k) (⟨k, hk⟩ : Fin (2 ^ n)) (w ⟨k, hk⟩)) = false := by
    rw [← hstep]
    exact hkf
  have hband := circuitMCSP_boundary_edge_band
    (tablePath z w k) (⟨k, hk⟩ : Fin (2 ^ n)) (w ⟨k, hk⟩) hkt hkf'
  rw [← hstep] at hband
  exact ⟨k, hk, hkt, hkf, hband.1, hband.2.1, hband.2.2⟩

/-! ## A canonical easy endpoint -/

def zeroTable (N : ℕ) : Fin N → Bool := fun _ => false

@[simp] theorem fnOfTable_zeroTable {n : ℕ} :
    fnOfTable (zeroTable (2 ^ n)) = fun _ => false := by
  rfl

theorem cbudget_fnOfTable_zeroTable {n : ℕ} :
    cbudget (fnOfTable (zeroTable (2 ^ n))) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Nat.sInf_le
  exact ⟨[], by intro x; rfl, rfl⟩

@[simp] theorem circuitMCSP_zeroTable {n s : ℕ} :
    circuitMCSP n s (zeroTable (2 ^ n)) = true := by
  rw [circuitMCSP_eq_true_iff, cbudget_fnOfTable_zeroTable]
  exact Nat.zero_le s

/-- Any truth table genuinely above threshold supplies a concrete narrow-band
boundary edge on the canonical path from the zero function.  This removes the
easy-endpoint premise from `circuitMCSP_path_crossing`. -/
theorem circuitMCSP_boundary_of_hard {n s : ℕ}
    (w : Fin (2 ^ n) → Bool) (hhard : s < cbudget (fnOfTable w)) :
    ∃ k, k < 2 ^ n ∧
      circuitMCSP n s (tablePath (zeroTable (2 ^ n)) w k) = true ∧
      circuitMCSP n s (tablePath (zeroTable (2 ^ n)) w (k + 1)) = false ∧
      cbudget (fnOfTable (tablePath (zeroTable (2 ^ n)) w k)) ≤ s ∧
      s < cbudget (fnOfTable (tablePath (zeroTable (2 ^ n)) w (k + 1))) ∧
      cbudget (fnOfTable (tablePath (zeroTable (2 ^ n)) w (k + 1))) ≤
        s + (3 * n + 3) := by
  have hno : circuitMCSP n s w = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    exact (Nat.not_le_of_gt hhard) ((circuitMCSP_eq_true_iff w).mp ht)
  exact circuitMCSP_path_crossing (zeroTable (2 ^ n)) w
    circuitMCSP_zeroTable hno

end PallLean.Paper93.DeepMath.PathB.SharingSensitiveMCSP

#print axioms PallLean.Paper93.DeepMath.PathB.SharingSensitiveMCSP.cbudget_tablePath_le
#print axioms PallLean.Paper93.DeepMath.PathB.SharingSensitiveMCSP.bool_path_crossing
#print axioms PallLean.Paper93.DeepMath.PathB.SharingSensitiveMCSP.circuitMCSP_path_crossing
#print axioms PallLean.Paper93.DeepMath.PathB.SharingSensitiveMCSP.circuitMCSP_boundary_of_hard
