import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimePhysicalWorkspace

/-!
# The deterministic post-lookup REND corridor

`RoundInv` intentionally says nothing after its live `REND`.  For the actual
`rsTape` evolution, however, the two pair shifts do not create arbitrary
garbage: every deleted round duplicates the old `REND` pair twice.  This file
records that stronger reachable-state fact.  It turns the formerly stale
workspace interval into a fixed-controller-readable corridor of `10` pairs.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRendCorridor

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinMasterRound
open PallLean.Paper93.DeepMath.PathB.CookLevinRendShift
open PallLean.Paper93.DeepMath.PathB.CookLevinRoundInvariant
open PallLean.Paper93.DeepMath.PathB.CookLevinWholeRun
open PallLean.Paper93.DeepMath.PathB.CookLevinInP
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact

/-- `m` consecutive doubled `REND = 10` pairs beginning at cell `q`. -/
def RendCorridor (T : List Bool) (q m : Nat) : Prop :=
  ∀ i, i < m →
    T.getD (q + 2 * i) false = true ∧
    T.getD (q + 2 * i + 1) false = false

/-- One concrete lookup round extends the reachable REND corridor by exactly
two pairs: the final source pair of each of the two shifts is a REND pair. -/
theorem roundInv_round_rendCorridor (T : List Bool) (k D m : Nat)
    (hk : 1 ≤ k) (hD : 1 ≤ D) (hinv : RoundInv T k D)
    (hcorr : RendCorridor T (2 * k + 4 + 2 * D) m) :
    let T' := rsTape (rsTape T (2 * k + 4) D) (2 * k) (D + 1)
    RendCorridor T' (2 * (k - 1) + 4 + 2 * (D - 1)) (m + 2) := by
  dsimp only
  let TA := rsTape T (2 * k + 4) D
  let TB := rsTape TA (2 * k) (D + 1)
  have hinv' : RoundInv TB (k - 1) (D - 1) := by
    simpa [TA, TB] using roundInv_preserved T k D hk hD hinv
  change RendCorridor TB (2 * (k - 1) + 4 + 2 * (D - 1)) (m + 2)
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · refine ⟨hinv'.rendlo, ?_⟩
    rw [show 2 * (k - 1) + 4 + 2 * (D - 1) + 1 =
      2 * (k - 1) + 5 + 2 * (D - 1) by omega]
    exact hinv'.rendhi
  by_cases hi1 : i = 1
  · subst i
    have hloTA : TA.getD (2 * k + 2 * D + 2) false = true := by
      change (rsTape T (2 * k + 4) D).getD
        (2 * k + 2 * D + 2) false = true
      rw [show 2 * k + 2 * D + 2 = (2 * k + 4) + 2 * (D - 1) by omega]
      rw [rsTape_getD_lt T (2 * k + 4) D
        (2 * k + 4 + 2 * (D - 1)) (by omega) (by omega)]
      rw [show 2 * k + 4 + 2 * (D - 1) + 2 =
        2 * k + 4 + 2 * D by omega]
      exact hinv.rendlo
    have hhiTA : TA.getD (2 * k + 2 * D + 3) false = false := by
      change (rsTape T (2 * k + 4) D).getD
        (2 * k + 2 * D + 3) false = false
      rw [show 2 * k + 2 * D + 3 = (2 * k + 4) + 2 * (D - 1) + 1 by omega]
      rw [rsTape_getD_lt T (2 * k + 4) D
        (2 * k + 4 + 2 * (D - 1) + 1) (by omega) (by omega)]
      rw [show 2 * k + 4 + 2 * (D - 1) + 1 + 2 =
        2 * k + 5 + 2 * D by omega]
      exact hinv.rendhi
    have hloTB : TB.getD (2 * k + 2 * D + 2) false = true := by
      change (rsTape TA (2 * k) (D + 1)).getD
        (2 * k + 2 * D + 2) false = true
      rw [rsTape_getD_ge TA (2 * k) (2 * k + 2 * D + 2)
        (D + 1) (by omega)]
      exact hloTA
    have hhiTB : TB.getD (2 * k + 2 * D + 3) false = false := by
      change (rsTape TA (2 * k) (D + 1)).getD
        (2 * k + 2 * D + 3) false = false
      rw [rsTape_getD_ge TA (2 * k) (2 * k + 2 * D + 3)
        (D + 1) (by omega)]
      exact hhiTA
    constructor
    · rw [show 2 * (k - 1) + 4 + 2 * (D - 1) + 2 =
        2 * k + 2 * D + 2 by omega]
      exact hloTB
    · rw [show 2 * (k - 1) + 4 + 2 * (D - 1) + 2 + 1 =
        2 * k + 2 * D + 3 by omega]
      exact hhiTB
  · have hi2 : 2 ≤ i := by omega
    let j := i - 2
    have hj : j < m := by dsimp [j]; omega
    obtain ⟨hlo, hhi⟩ := hcorr j hj
    have hposlo :
        2 * (k - 1) + 4 + 2 * (D - 1) + 2 * i =
          2 * k + 4 + 2 * D + 2 * j := by
      dsimp [j]
      omega
    have hposhi :
        2 * (k - 1) + 4 + 2 * (D - 1) + 2 * i + 1 =
          2 * k + 4 + 2 * D + 2 * j + 1 := by
      dsimp [j]
      omega
    have hloTA : TA.getD (2 * k + 4 + 2 * D + 2 * j) false = true := by
      change (rsTape T (2 * k + 4) D).getD
        (2 * k + 4 + 2 * D + 2 * j) false = true
      rw [rsTape_getD_ge T (2 * k + 4)
        (2 * k + 4 + 2 * D + 2 * j) D (by omega)]
      exact hlo
    have hhiTA : TA.getD (2 * k + 4 + 2 * D + 2 * j + 1) false = false := by
      change (rsTape T (2 * k + 4) D).getD
        (2 * k + 4 + 2 * D + 2 * j + 1) false = false
      rw [rsTape_getD_ge T (2 * k + 4)
        (2 * k + 4 + 2 * D + 2 * j + 1) D (by omega)]
      exact hhi
    have hloTB : TB.getD (2 * k + 4 + 2 * D + 2 * j) false = true := by
      change (rsTape TA (2 * k) (D + 1)).getD
        (2 * k + 4 + 2 * D + 2 * j) false = true
      rw [rsTape_getD_ge TA (2 * k)
        (2 * k + 4 + 2 * D + 2 * j) (D + 1) (by omega)]
      exact hloTA
    have hhiTB : TB.getD (2 * k + 4 + 2 * D + 2 * j + 1) false = false := by
      change (rsTape TA (2 * k) (D + 1)).getD
        (2 * k + 4 + 2 * D + 2 * j + 1) false = false
      rw [rsTape_getD_ge TA (2 * k)
        (2 * k + 4 + 2 * D + 2 * j + 1) (D + 1) (by omega)]
      exact hhiTA
    constructor
    · rw [hposlo]
      exact hloTB
    · rw [hposhi]
      exact hhiTB

/-- Iterating `v` concrete rounds extends the input corridor by `2v` pairs. -/
theorem rounds_rendCorridor (v : Nat) : ∀ (T : List Bool) (D m : Nat),
    v ≤ D → RoundInv T v D →
    RendCorridor T (2 * v + 4 + 2 * D) m →
    ∃ T', run masterM (clockSum v D)
        ⟨(1, 0, false, false), 2 * v + 2, T⟩ =
        ⟨(1, 0, false, false), 2, T'⟩ ∧
      RoundInv T' 0 (D - v) ∧
      RendCorridor T' (4 + 2 * (D - v)) (m + 2 * v) := by
  induction v with
  | zero =>
      intro T D m _ hinv hcorr
      refine ⟨T, ?_, by simpa using hinv, ?_⟩
      · simp [clockSum]
      · simpa using hcorr
  | succ v ih =>
      intro T D m hv hinv hcorr
      let T1 := rsTape (rsTape T (2 * (v + 1) + 4) D)
        (2 * (v + 1)) (D + 1)
      have hrun1 : run masterM (roundClock D)
          ⟨(1, 0, false, false), 2 * (v + 1) + 2, T⟩ =
          ⟨(1, 0, false, false), 2 * v + 2, T1⟩ := by
        simpa [roundClock, T1] using
          roundInv_step T (v + 1) D (by omega) (by omega) hinv
      have hinv1 : RoundInv T1 v (D - 1) := by
        simpa [T1] using
          roundInv_preserved T (v + 1) D (by omega) (by omega) hinv
      have hcorr1 : RendCorridor T1 (2 * v + 4 + 2 * (D - 1)) (m + 2) := by
        simpa [T1] using roundInv_round_rendCorridor T (v + 1) D m
          (by omega) (by omega) hinv hcorr
      obtain ⟨T', hrun2, hinv2, hcorr2⟩ :=
        ih T1 (D - 1) (m + 2) (by omega) hinv1 hcorr1
      refine ⟨T', ?_, ?_, ?_⟩
      · simp only [clockSum]
        rw [run_add, hrun1]
        exact hrun2
      · simpa [show D - (v + 1) = D - 1 - v by omega] using hinv2
      · convert hcorr2 using 1 <;> omega

/-- The terminal read performs no writes, so the corridor survives the full
lookup clock. -/
theorem wholeRun_rendCorridor (v : Nat) (T : List Bool) (D m : Nat)
    (hv : v ≤ D) (hinv : RoundInv T v D)
    (hcorr : RendCorridor T (2 * v + 4 + 2 * D) m) :
    ∃ T', run masterM (clockSum v D + 7)
        ⟨(1, 0, false, false), 2 * v + 2, T⟩ =
        ⟨(9, 0, T.getD (2 * v + 4 + 2 * v) false, false), 4, T'⟩ ∧
      RendCorridor T' (4 + 2 * (D - v)) (m + 2 * v) := by
  obtain ⟨T1, hrounds, hinv1, hcorr1⟩ :=
    rounds_rendCorridor v T D m hv hinv hcorr
  have htail : run masterM 7
      ⟨(1, 0, false, false), 2, T1⟩ =
      ⟨(9, 0, T1.getD 4 false, false), 4, T1⟩ :=
    tail_read (s := 2) (tape := T1) (by omega) (by simpa using hinv1.lsent)
  obtain ⟨T2, hrounds2, _, htrack⟩ := rounds v T D hv hinv
  have hT2 : T2 = T1 := by
    rw [hrounds2] at hrounds
    exact congrArg Cfg.tp hrounds
  subst T2
  refine ⟨T1, ?_, hcorr1⟩
  rw [run_add, hrounds, htail, htrack]

/-- On the real canonical literal input, the complete master run leaves a
reachable corridor of exactly `2v+2` REND pairs starting at cell six.  Thus
the interval between the shortened live workspace and the preserved trailer
is structured, rather than arbitrary. -/
theorem masterM_literal_rendCorridor (w : List Bool) (l : Lit)
    (tail : List Bool) :
    let bits := literalLookupTape w l
    let trailer := [true, false, false, true] ++ tail
    let cf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    RendCorridor cf.tp 6 (2 * l.1 + 2) := by
  dsimp only
  let bits := literalLookupTape w l
  let trailer := [true, false, false, true] ++ tail
  let A := signedLookupAssignment w l.1 l.2
  let T := bits ++ trailer
  have hv : l.1 ≤ A.length := by
    dsimp [A]
    rw [signedLookupAssignment_length]
    omega
  have hinv : RoundInv T l.1 A.length := by
    dsimp [T, bits, A]
    exact literalLookupTape_append_roundInv w l trailer
  have hbitslen : bits.length = 4 * l.1 + 8 := by
    simp [bits, literalLookupTape, CookLevinInP.encode,
      signedLookupAssignment_length, CookLevinInP.double_length]
    ring
  have hcorr0 : RendCorridor T
      (2 * l.1 + 4 + 2 * A.length) 2 := by
    intro i hi
    interval_cases i
    · refine ⟨hinv.rendlo, ?_⟩
      rw [show 2 * l.1 + 4 + 2 * A.length + 2 * 0 + 1 =
        2 * l.1 + 5 + 2 * A.length by omega]
      exact hinv.rendhi
    · have hq : 2 * l.1 + 4 + 2 * A.length + 2 = bits.length := by
        dsimp [A]
        rw [signedLookupAssignment_length, hbitslen]
        omega
      constructor
      · rw [hq]
        simp [T, trailer]
      · rw [show 2 * l.1 + 4 + 2 * A.length + 2 * 1 + 1 =
          bits.length + 1 by omega]
        simp [T, trailer]
  obtain ⟨T', hwhole, hcorr⟩ :=
    wholeRun_rendCorridor l.1 T A.length 2 hv hinv hcorr0
  have hinit := init_phase T l.1 A.length hinv
  have hfull : run masterM (literalLookupClock w l)
      (init masterM T) =
      ⟨(9, 0, T.getD (2 * l.1 + 4 + 2 * l.1) false, false), 4, T'⟩ := by
    rw [literalLookupClock, master_forced_init, run_add, hinit]
    exact hwhole
  rw [show run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer)) =
      ⟨(9, 0, T.getD (2 * l.1 + 4 + 2 * l.1) false, false), 4, T'⟩ by
        simpa [T] using hfull]
  have hAlen : A.length = l.1 + 1 := by
    simp [A, signedLookupAssignment_length]
  rw [hAlen] at hcorr
  convert hcorr using 1 <;> omega

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRendCorridor

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRendCorridor.roundInv_round_rendCorridor
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRendCorridor.rounds_rendCorridor
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRendCorridor.wholeRun_rendCorridor
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRendCorridor.masterM_literal_rendCorridor
