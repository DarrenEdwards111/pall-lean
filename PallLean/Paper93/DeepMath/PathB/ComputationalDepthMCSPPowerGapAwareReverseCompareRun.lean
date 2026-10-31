import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPPowerGapAwareReverseCompareRound

/-!
# MCSP verifier: complete physical reverse comparison

This file inducts the physical reverse round and proves both endgames of the
fixed `reverseCompareMachine`.  It genuinely halts and decides `a ≤ b` on the
live retained-gap tape; the final tape is exactly the descriptor consumed by
the local-home adapter.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareRun

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCompareHomeMachine
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareMachine
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareRound

def reverseRounds (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => reverseRounds a k + reverseRoundClock a k

theorem reverseRounds_eq (a k : ℕ) :
    reverseRounds a k = cmpRounds a k + 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [reverseRounds, cmpRounds, reverseRoundClock]
      rw [ih]
      ring

theorem run_reverse_rounds (a b k : ℕ) (rest : List Bool)
    (hka : k ≤ a) (hkb : k ≤ b) (s : Bool) :
    run reverseCompareMachine (reverseRounds a k)
      ⟨.cmp 0 s, 0, reversePhysicalTape a b 0 0 rest⟩ =
      ⟨.cmp 0 (if k = 0 then s else true), 0,
        reversePhysicalTape a b k k rest⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show reverseRounds a (k + 1) =
          reverseRounds a k + reverseRoundClock a k from rfl,
        run_add, ih (by omega) (by omega),
        run_reverse_round a b k rest (by omega) (by omega),
        if_neg (by omega)]

theorem run_reverse_two_accept {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run reverseCompareMachine 2 ⟨.cmp 0 s, p, T⟩ =
      ⟨.cmp 6 false, p + 1, T⟩ := by
  rw [show 2 = 1 + 1 by omega, run_add]
  change step reverseCompareMachine
    (step reverseCompareMachine ⟨.cmp 0 s, p, T⟩) = _
  rw [step_reverse_c0, h1, step_reverse_c1_accept h2]

theorem run_reverse_two_reject {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run reverseCompareMachine 2 ⟨.cmp 4 s, p, T⟩ =
      ⟨.cmp 7 false, p + 1, T⟩ := by
  rw [show 2 = 1 + 1 by omega, run_add]
  change step reverseCompareMachine
    (step reverseCompareMachine ⟨.cmp 4 s, p, T⟩) = _
  rw [step_reverse_c4, h1, step_reverse_c5_reject h2]

/-- Accept endgame: after `a` rounds, scan the fully marked first counter and
halt before touching the retained gap. -/
theorem reverseCompare_run_le (a b : ℕ) (rest : List Bool)
    (hab : a ≤ b) :
    run reverseCompareMachine (reverseRounds a a + (2 * a + 2))
      (init reverseCompareMachine (reversePhysicalTape a b 0 0 rest)) =
      ⟨.cmp 6 false, 2 * a + 1,
        reversePhysicalTape a b a a rest⟩ := by
  rw [init_reverseCompare]
  change run reverseCompareMachine (reverseRounds a a + (2 * a + 2))
    ⟨.cmp 0 false, 0, reversePhysicalTape a b 0 0 rest⟩ = _
  rw [run_add, run_reverse_rounds a b a rest (le_refl a) hab false]
  have st1 := run_reverse_skipA (reversePhysicalTape a b a a rest)
    0 a (if a = 0 then false else true) (fun i hi =>
      ⟨by simpa using reverseT_getD_Amark_lo a b a a i rest hi,
       by simpa using reverseT_getD_Amark_hi a b a a i rest hi⟩)
  simp only [Nat.zero_add] at st1
  have st2 := run_reverse_two_accept
    (s := if a = 0 then (if a = 0 then false else true) else true)
    (p := 2 * a) (T := reversePhysicalTape a b a a rest)
    (reverseT_getD_Aend_lo a b a a rest (le_refl a))
    (reverseT_getD_Aend_hi a b a a rest (le_refl a))
  rw [show 2 * a + 2 = 2 * a + 2 by rfl, run_add, st1, st2]

/-- Reject endgame: after `b` rounds, mark the next `A` pair, cross the gap,
and find the exhausted `B` boundary. -/
theorem reverseCompare_run_gt (a b : ℕ) (rest : List Bool)
    (hab : b < a) :
    run reverseCompareMachine (reverseRounds a (b + 1))
      (init reverseCompareMachine (reversePhysicalTape a b 0 0 rest)) =
      ⟨.cmp 7 false, 2 * a + 4 + 2 * b + 1,
        reversePhysicalTape a b (b + 1) b rest⟩ := by
  rw [init_reverseCompare]
  change run reverseCompareMachine (reverseRounds a (b + 1))
    ⟨.cmp 0 false, 0, reversePhysicalTape a b 0 0 rest⟩ = _
  rw [show reverseRounds a (b + 1) =
      reverseRounds a b + reverseRoundClock a b from rfl,
    run_add, run_reverse_rounds a b b rest (by omega) (le_refl b) false]
  have st1 := run_reverse_skipA (reversePhysicalTape a b b b rest)
    0 b (if b = 0 then false else true) (fun i hi =>
      ⟨by simpa using reverseT_getD_Amark_lo a b b b i rest hi,
       by simpa using reverseT_getD_Amark_hi a b b b i rest hi⟩)
  simp only [Nat.zero_add] at st1
  have st2 := run_reverse_two_markA
    (s := if b = 0 then (if b = 0 then false else true) else true)
    (p := 2 * b) (T := reversePhysicalTape a b b b rest)
    (reverseT_getD_Adata a b b b (2 * b) rest
      (by omega) (by omega) (by omega))
    (reverseT_getD_Adata a b b b (2 * b + 1) rest
      (by omega) (by omega) (by omega))
  rw [reverseT_markA a b b b rest hab (le_refl b)] at st2
  have st3 := run_reverse_seek
    (reversePhysicalTape a b (b + 1) b rest)
    (2 * b + 2) (a - b - 1) true (fun i hi =>
      ⟨reverseT_getD_Adata a b (b + 1) b
          (2 * b + 2 + 2 * i) rest (by omega) (by omega) (by omega),
       reverseT_getD_Adata a b (b + 1) b
          (2 * b + 2 + 2 * i + 1) rest (by omega) (by omega) (by omega)⟩)
  rw [show 2 * b + 2 + 2 * (a - b - 1) = 2 * a from by omega] at st3
  simp only [ite_self] at st3
  let Apre : List Bool :=
    markedD (b + 1) ++ List.replicate (2 * (a - (b + 1))) true
  have hApre : Apre.length = 2 * a := by
    simp [Apre, markedD_length]
    omega
  have st4raw := run_reverse_four_cross Apre (workD b b ++ rest)
  have st4 : run reverseCompareMachine 4
      ⟨.cmp 2 true, 2 * a,
        reversePhysicalTape a b (b + 1) b rest⟩ =
      ⟨.cmp 4 false, 2 * a + 4,
        reversePhysicalTape a b (b + 1) b rest⟩ := by
    convert st4raw using 1 <;>
      simp [Apre, reversePhysicalTape, compareHomeTape, workD,
        List.append_assoc, hApre] <;> omega
  have st5 := run_reverse_skipB
    (reversePhysicalTape a b (b + 1) b rest)
    (2 * a + 4) b false (fun i hi =>
      ⟨reverseT_getD_Bmark_lo a b (b + 1) b i rest (by omega) hi,
       reverseT_getD_Bmark_hi a b (b + 1) b i rest (by omega) hi⟩)
  have st6 := run_reverse_two_reject
    (s := if b = 0 then false else true)
    (p := 2 * a + 4 + 2 * b)
    (T := reversePhysicalTape a b (b + 1) b rest)
    (reverseT_getD_Bend_lo a b (b + 1) b rest (by omega) (le_refl b))
    (reverseT_getD_Bend_hi a b (b + 1) b rest (by omega) (le_refl b))
  unfold reverseRoundClock
  rw [show 2 * a + 2 * b + 6 =
      2 * b + (2 + (2 * (a - b - 1) + (4 + (2 * b + 2))))
        from by omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4,
    run_add, st5, st6]

def reverseCompareClock (a b : ℕ) : ℕ :=
  if a ≤ b then reverseRounds a a + (2 * a + 2)
  else reverseRounds a (b + 1)

theorem reverseCompare_halts (a b : ℕ) (rest : List Bool) :
    HaltsBy reverseCompareMachine (reversePhysicalTape a b 0 0 rest)
      (reverseCompareClock a b) := by
  unfold HaltsBy reverseCompareClock
  rcases le_or_gt a b with hab | hab
  · rw [if_pos hab, reverseCompare_run_le a b rest hab]
    rfl
  · rw [if_neg (by omega), reverseCompare_run_gt a b rest hab]
    rfl

theorem reverseCompare_decides (a b : ℕ) (rest : List Bool) :
    decideOut reverseCompareMachine (reversePhysicalTape a b 0 0 rest)
      (reverseCompareClock a b) = decide (a ≤ b) := by
  unfold decideOut reverseCompareClock
  rcases le_or_gt a b with hab | hab
  · rw [if_pos hab, reverseCompare_run_le a b rest hab]
    simp [reverseCompareMachine, hab]
  · rw [if_neg (by omega), reverseCompare_run_gt a b rest hab]
    simp [reverseCompareMachine]
    omega

end PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareRun

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareRun.run_reverse_rounds
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareRun.reverseCompare_run_le
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareRun.reverseCompare_run_gt
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareRun.reverseCompare_halts
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareRun.reverseCompare_decides
