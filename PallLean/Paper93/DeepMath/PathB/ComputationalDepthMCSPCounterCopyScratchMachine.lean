import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitCounterCopy

/-!
# MCSP verifier: suffix-preserving counter copy into reserved scratch

The generic unary copy machine was originally proved on a counter occupying
the complete live tape.  Comparator staging needs the stronger operational
form: a counter followed by exactly one counter-sized zero scratch region and
then an arbitrary live suffix.

This file proves that the *same fixed finite-control machine* fills only the
reserved scratch, restores its source counter, writes the copied `01`
terminator, and preserves the suffix byte-for-byte:

    unaryD n ++ 0^(2n+2) ++ suffix
      ↦ unaryD n ++ unaryD n ++ suffix.

No input-dependent transition table and no initialization shortcut is used.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPCounterCopyScratchMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy

private theorem writeAt_boundary (P R : List Bool) (b w : Bool) :
    writeAt (P ++ b :: R) P.length w = P ++ w :: R := by
  rw [writeAt_of_lt w (by simp)]
  simp

/-- Copy-round tape with the unused part of the reserved target kept zero. -/
def cpyS (n jA jC : ℕ) (suffix : List Bool) : List Bool :=
  cpyT n jA jC ++
    (List.replicate (2 * (n - jC) + 2) false ++ suffix)

/-- Restore tape with two reserved cells left for the copied terminator. -/
def resS (n i : ℕ) (suffix : List Bool) : List Bool :=
  resT n i ++ ([false, false] ++ suffix)

theorem cpyS_zero (n : ℕ) (suffix : List Bool) :
    cpyS n 0 0 suffix =
      unaryD n ++ List.replicate (2 * n + 2) false ++ suffix := by
  simp [cpyS, cpyT_zero]

theorem cpyS_length (n jA jC : ℕ) (suffix : List Bool)
    (hA : jA ≤ n) (hC : jC ≤ n) :
    (cpyS n jA jC suffix).length = 4 * n + 4 + suffix.length := by
  simp [cpyS, cpyT_length n jA jC hA]
  omega

private theorem getD_cpyT {n jA jC p : ℕ} {suffix : List Bool}
    (hA : jA ≤ n) (hp : p < (cpyT n jA jC).length) :
    (cpyS n jA jC suffix).getD p false =
      (cpyT n jA jC).getD p false := by
  rw [cpyS, List.getD_append (h := hp)]

theorem cpyS_getD_Amark_lo (n jA jC i : ℕ) (suffix : List Bool)
    (hA : jA ≤ n) (hC : jC ≤ n) (h : i < jA) :
    (cpyS n jA jC suffix).getD (2 * i) false = true := by
  rw [getD_cpyT hA (by rw [cpyT_length n jA jC hA]; omega)]
  exact cpyT_getD_Amark_lo n jA jC i h

theorem cpyS_getD_Amark_hi (n jA jC i : ℕ) (suffix : List Bool)
    (hA : jA ≤ n) (hC : jC ≤ n) (h : i < jA) :
    (cpyS n jA jC suffix).getD (2 * i + 1) false = false := by
  rw [getD_cpyT hA (by rw [cpyT_length n jA jC hA]; omega)]
  exact cpyT_getD_Amark_hi n jA jC i h

theorem cpyS_getD_Adata (n jA jC c : ℕ) (suffix : List Bool)
    (hA : jA ≤ n) (hC : jC ≤ n)
    (h1 : 2 * jA ≤ c) (h2 : c < 2 * n) :
    (cpyS n jA jC suffix).getD c false = true := by
  rw [getD_cpyT hA (by rw [cpyT_length n jA jC hA]; omega)]
  exact cpyT_getD_Adata n jA jC c hA h1 h2

theorem cpyS_getD_marker_lo (n jA jC : ℕ) (suffix : List Bool)
    (hA : jA ≤ n) (hC : jC ≤ n) :
    (cpyS n jA jC suffix).getD (2 * n) false = false := by
  rw [getD_cpyT hA (by rw [cpyT_length n jA jC hA]; omega)]
  exact cpyT_getD_marker_lo n jA jC hA

theorem cpyS_getD_marker_hi (n jA jC : ℕ) (suffix : List Bool)
    (hA : jA ≤ n) (hC : jC ≤ n) :
    (cpyS n jA jC suffix).getD (2 * n + 1) false = true := by
  rw [getD_cpyT hA (by rw [cpyT_length n jA jC hA]; omega)]
  exact cpyT_getD_marker_hi n jA jC hA

theorem cpyS_getD_C (n jA jC c : ℕ) (suffix : List Bool)
    (hA : jA ≤ n) (hC : jC ≤ n)
    (h1 : 2 * n + 2 ≤ c) (h2 : c < 2 * n + 2 + 2 * jC) :
    (cpyS n jA jC suffix).getD c false = true := by
  rw [getD_cpyT hA (by rw [cpyT_length n jA jC hA]; omega)]
  exact cpyT_getD_C n jA jC c hA h1 h2

theorem cpyS_getD_blank_lo (n jA jC : ℕ) (suffix : List Bool)
    (hA : jA ≤ n) (hC : jC ≤ n) :
    (cpyS n jA jC suffix).getD (2 * n + 2 * jC + 2) false = false := by
  rw [cpyS, show 2 * n + 2 * jC + 2 =
      (cpyT n jA jC).length by rw [cpyT_length n jA jC hA]; omega,
    List.getD_append_right (h := le_refl _), Nat.sub_self]
  simp

theorem cpyS_getD_blank_hi (n jA jC : ℕ) (suffix : List Bool)
    (hA : jA ≤ n) (hC : jC ≤ n) :
    (cpyS n jA jC suffix).getD (2 * n + 2 * jC + 3) false = false := by
  rw [cpyS, show 2 * n + 2 * jC + 3 =
      (cpyT n jA jC).length + 1 by
        rw [cpyT_length n jA jC hA]; omega,
    List.getD_append_right (h := by omega)]
  rw [List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (by omega)

theorem cpyS_mark (n j : ℕ) (suffix : List Bool) (hj : j < n) :
    writeAt (cpyS n j j suffix) (2 * j + 1) false =
      cpyS n (j + 1) j suffix := by
  unfold cpyS
  rw [writeAt_of_lt false (by
    simp [cpyT_length n j j (by omega)]; omega)]
  rw [List.set_append_left _ _ (by
    rw [cpyT_length n j j (by omega)]; omega)]
  rw [← writeAt_of_lt false
      (by rw [cpyT_length n j j (by omega)]; omega),
    cpyT_mark n j hj]

theorem cpyS_grow (n j : ℕ) (suffix : List Bool) (hj : j < n) :
    writeAt
        (writeAt (cpyS n (j + 1) j suffix)
          (2 * n + 2 * j + 2) true)
        (2 * n + 2 * j + 3) true =
      cpyS n (j + 1) (j + 1) suffix := by
  let A := cpyT n (j + 1) j
  let tail := List.replicate (2 * (n - (j + 1)) + 2) false ++ suffix
  have hlen : A.length = 2 * n + 2 * j + 2 := by
    dsimp [A]
    rw [cpyT_length n (j + 1) j (by omega)]
    omega
  have hshape : cpyS n (j + 1) j suffix =
      A ++ false :: false :: tail := by
    simp only [cpyS, A, tail]
    rw [show 2 * (n - j) + 2 =
      2 + (2 * (n - (j + 1)) + 2) by omega,
      List.replicate_add]
    rfl
  rw [hshape, ← hlen, writeAt_boundary]
  rw [show A ++ true :: false :: tail =
      (A ++ [true]) ++ false :: tail by simp,
    show 2 * n + 2 * j + 3 = (A ++ [true]).length by
      simp [hlen],
    writeAt_boundary]
  simp [cpyS, A, tail, cpyT, List.append_assoc,
    show 2 * (j + 1) = 2 * j + 2 by omega, List.replicate_add]

theorem resS_zero (n : ℕ) (suffix : List Bool) :
    resS n 0 suffix = cpyS n n n suffix := by
  simp [resS, cpyS, resT_zero]

theorem resS_length (n i : ℕ) (suffix : List Bool) (hi : i ≤ n) :
    (resS n i suffix).length = 4 * n + 4 + suffix.length := by
  simp [resS, resT_length n i hi]
  omega

private theorem getD_resT {n i p : ℕ} {suffix : List Bool}
    (hi : i ≤ n) (hp : p < (resT n i).length) :
    (resS n i suffix).getD p false = (resT n i).getD p false := by
  rw [resS, List.getD_append (h := hp)]

theorem resS_getD_pair_lo (n i : ℕ) (suffix : List Bool) (h : i < n) :
    (resS n i suffix).getD (2 * i) false = true := by
  rw [getD_resT (by omega)
    (by rw [resT_length n i (by omega)]; omega)]
  exact resT_getD_pair_lo n i h

theorem resS_getD_pair_hi (n i : ℕ) (suffix : List Bool) (h : i < n) :
    (resS n i suffix).getD (2 * i + 1) false = false := by
  rw [getD_resT (by omega)
    (by rw [resT_length n i (by omega)]; omega)]
  exact resT_getD_pair_hi n i h

theorem resS_getD_marker_lo (n : ℕ) (suffix : List Bool) :
    (resS n n suffix).getD (2 * n) false = false := by
  rw [getD_resT (le_refl n)
    (by rw [resT_length n n (le_refl n)]; omega)]
  exact resT_getD_marker_lo n

theorem resS_getD_marker_hi (n : ℕ) (suffix : List Bool) :
    (resS n n suffix).getD (2 * n + 1) false = true := by
  rw [getD_resT (le_refl n)
    (by rw [resT_length n n (le_refl n)]; omega)]
  exact resT_getD_marker_hi n

theorem resS_getD_C (n c : ℕ) (suffix : List Bool)
    (h1 : 2 * n + 2 ≤ c) (h2 : c < 4 * n + 2) :
    (resS n n suffix).getD c false = true := by
  rw [getD_resT (le_refl n)
    (by rw [resT_length n n (le_refl n)]; omega)]
  exact resT_getD_C n c h1 h2

theorem resS_getD_blank_lo (n : ℕ) (suffix : List Bool) :
    (resS n n suffix).getD (4 * n + 2) false = false := by
  rw [resS, show 4 * n + 2 = (resT n n).length by
      exact (resT_length n n (le_refl n)).symm,
    List.getD_append_right (h := le_refl _), Nat.sub_self]
  rfl

theorem resS_getD_blank_hi (n : ℕ) (suffix : List Bool) :
    (resS n n suffix).getD (4 * n + 3) false = false := by
  rw [resS, show 4 * n + 3 = (resT n n).length + 1 by
      rw [resT_length n n (le_refl n)],
    List.getD_append_right (h := by omega)]
  simp

theorem resS_heal (n i : ℕ) (suffix : List Bool) (hi : i < n) :
    writeAt (resS n i suffix) (2 * i + 1) true =
      resS n (i + 1) suffix := by
  unfold resS
  rw [writeAt_of_lt true (by
    simp [resT_length n i (by omega)]; omega)]
  rw [List.set_append_left _ _ (by
    rw [resT_length n i (by omega)]; omega)]
  rw [← writeAt_of_lt true
      (by rw [resT_length n i (by omega)]; omega),
    resT_heal n i hi]

theorem resS_finish (n : ℕ) (suffix : List Bool) :
    writeAt (resS n n suffix) (4 * n + 3) true =
      unaryD n ++ unaryD n ++ suffix := by
  unfold resS
  rw [show 4 * n + 3 = (resT n n ++ [false]).length by
      simp [resT_length n n (le_refl n)]]
  rw [show resT n n ++ ([false, false] ++ suffix) =
      (resT n n ++ [false]) ++ false :: suffix by simp,
    writeAt_boundary]
  have h := resT_finish n
  rw [show 4 * n + 3 = (resT n n).length + 1 by
      rw [resT_length n n (le_refl n)],
    writeAt_append_end1] at h
  simpa [List.append_assoc] using congrArg (fun x => x ++ suffix) h

/-! ## Scratch-preserving run -/

theorem run_copy_round_scratch (n j : ℕ) (suffix : List Bool)
    (hj : j < n) (s : Bool) :
    run copyMachine (2 * n + 2 * j + 6)
      ⟨(0, s), 0, cpyS n j j suffix⟩ =
      ⟨(0, false), 0, cpyS n (j + 1) (j + 1) suffix⟩ := by
  have st1 := run_findSkip (cpyS n j j suffix) 0 j s (fun i hi =>
    ⟨by simpa using cpyS_getD_Amark_lo n j j i suffix (by omega) (by omega) hi,
     by simpa using cpyS_getD_Amark_hi n j j i suffix (by omega) (by omega) hi⟩)
  simp only [Nat.zero_add] at st1
  have st2 := run_two_mark (s := if j = 0 then s else true)
    (p := 2 * j) (T := cpyS n j j suffix)
    (cpyS_getD_Adata n j j (2 * j) suffix (by omega) (by omega)
      (by omega) (by omega))
    (cpyS_getD_Adata n j j (2 * j + 1) suffix (by omega) (by omega)
      (by omega) (by omega))
  rw [cpyS_mark n j suffix hj] at st2
  have st3 := run_seekE (cpyS n (j + 1) j suffix)
    (2 * j + 2) n true (fun i hi => by
      rcases Nat.lt_trichotomy i (n - j - 1) with h | h | h
      · exact cpyS_getD_Adata n (j + 1) j
          (2 * j + 2 + 2 * i + 1) suffix (by omega) (by omega)
          (by omega) (by omega)
      · rw [show 2 * j + 2 + 2 * i + 1 = 2 * n + 1 from by omega]
        exact cpyS_getD_marker_hi n (j + 1) j suffix (by omega) (by omega)
      · exact cpyS_getD_C n (j + 1) j
          (2 * j + 2 + 2 * i + 1) suffix (by omega) (by omega)
          (by omega) (by omega))
  rw [show 2 * j + 2 + 2 * n = 2 * n + 2 * j + 2 by ring] at st3
  simp only [ite_self] at st3
  have st4 := run_four_grow (s := true) (p := 2 * n + 2 * j + 2)
    (T := cpyS n (j + 1) j suffix)
    (cpyS_getD_blank_lo n (j + 1) j suffix (by omega) (by omega))
    (cpyS_getD_blank_hi n (j + 1) j suffix (by omega) (by omega))
  rw [show 2 * n + 2 * j + 2 + 1 = 2 * n + 2 * j + 3 by omega,
    cpyS_grow n j suffix hj] at st4
  rw [show 2 * n + 2 * j + 6 =
      2 * j + (2 + (2 * n + 4)) by omega,
    run_add, st1, run_add, st2, run_add, st3, st4]

theorem run_copy_rounds_scratch (n k : ℕ) (suffix : List Bool)
    (hk : k ≤ n) (s : Bool) :
    run copyMachine (cpyRounds n k)
      ⟨(0, s), 0, cpyS n 0 0 suffix⟩ =
      ⟨(0, if k = 0 then s else false), 0, cpyS n k k suffix⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show cpyRounds n (k + 1) =
          cpyRounds n k + (2 * n + 2 * k + 6) from rfl,
        run_add, ih (by omega),
        run_copy_round_scratch n k suffix (by omega),
        if_neg (by omega)]

theorem run_restore_scratch (n : ℕ) (suffix : List Bool)
    (s : Bool) (i : ℕ) (hi : i ≤ n) :
    run copyMachine (2 * i) ⟨(6, s), 0, resS n 0 suffix⟩ =
      ⟨(6, if i = 0 then s else true), 2 * i, resS n i suffix⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [show 2 * (i + 1) = 2 * i + 2 by ring, run_add,
        ih (by omega),
        run_two_heal (resS_getD_pair_lo n i suffix (by omega))
          (resS_getD_pair_hi n i suffix (by omega)),
        resS_heal n i suffix (by omega)]
      rfl

/-- The existing fixed copy machine fills the reserved scratch and preserves
an arbitrary following suffix exactly. -/
theorem copy_run_scratch (n : ℕ) (suffix : List Bool) :
    run copyMachine (cpyClock n)
      (init copyMachine
        (unaryD n ++ List.replicate (2 * n + 2) false ++ suffix)) =
      ⟨(10, false), 4 * n + 3,
        unaryD n ++ unaryD n ++ suffix⟩ := by
  rw [init_cpy, ← cpyS_zero, cpyClock, run_add,
    run_copy_rounds_scratch n n suffix (le_refl n) false, ite_self]
  have st1 := run_findSkip (cpyS n n n suffix) 0 n false (fun i hi =>
    ⟨by simpa using (cpyS_getD_Amark_lo n n n i suffix
        (le_refl n) (le_refl n) hi),
     by simpa using (cpyS_getD_Amark_hi n n n i suffix
        (le_refl n) (le_refl n) hi)⟩)
  simp only [Nat.zero_add] at st1
  have st2 := run_two_toRestore (s := if n = 0 then false else true)
    (p := 2 * n) (T := cpyS n n n suffix)
    (cpyS_getD_marker_lo n n n suffix (le_refl n) (le_refl n))
    (cpyS_getD_marker_hi n n n suffix (le_refl n) (le_refl n))
  have st3 := run_restore_scratch n suffix false n (le_refl n)
  have st4 := run_two_cross67 (s := if n = 0 then false else true)
    (p := 2 * n) (T := resS n n suffix)
    (resS_getD_marker_lo n suffix) (resS_getD_marker_hi n suffix)
  have st5 := run_seekCs (resS n n suffix) (2 * n + 2) n false
    (fun i hi =>
      ⟨resS_getD_C n (2 * n + 2 + 2 * i) suffix (by omega) (by omega),
       resS_getD_C n (2 * n + 2 + 2 * i + 1) suffix (by omega) (by omega)⟩)
  rw [show 2 * n + 2 + 2 * n = 4 * n + 2 by ring] at st5
  have st6 := run_two_finish (s := if n = 0 then false else true)
    (p := 4 * n + 2) (T := resS n n suffix)
    (resS_getD_blank_lo n suffix) (resS_getD_blank_hi n suffix)
  rw [show 4 * n + 2 + 1 = 4 * n + 3 by omega,
    resS_finish n suffix] at st6
  rw [run_add, st1, run_add, st2, ← resS_zero, run_add, st3,
    run_add, st4, run_add, st5, st6]

theorem copy_halts_scratch (n : ℕ) (suffix : List Bool) :
    HaltsBy copyMachine
      (unaryD n ++ List.replicate (2 * n + 2) false ++ suffix)
      (cpyClock n) := by
  unfold HaltsBy
  rw [copy_run_scratch]
  rfl

end PallLean.Paper93.DeepMath.PathB.MCSPCounterCopyScratchMachine

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterCopyScratchMachine.copy_run_scratch
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterCopyScratchMachine.copy_halts_scratch
