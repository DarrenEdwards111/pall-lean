import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupLeftBoundaryRound

/-!
# Charged local lookup: invariant-level live-round boundary safety

The raw geometry required by `round_full_leftSafe` is discharged once from
`RoundInv`, exactly as for the existing execution theorem `roundInv_step`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryRoundInvariant

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinRendShift
open PallLean.Paper93.DeepMath.PathB.CookLevinRoundInvariant
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryRound

/-- One live round is boundary-safe directly from the packaged doubled-tape
invariant. -/
theorem roundInv_step_leftSafe (T : List Bool) (k D : Nat)
    (hk : 1 ≤ k) (hD : 1 ≤ D) (h : RoundInv T k D) :
    LeftSafeRun masterM ⟨(1, 0, false, false), 2 * k + 2, T⟩
      ((2 + 1 + 2 + (8 * (D - 1) + 8) + 1) +
        ((2 * (D - 1 + 1) + 2) + 1 + 1 + (8 * D + 8) + 1 + (2 * D + 2) + 1)) := by
  set TA := rsTape T (2 * k + 4) D with hTAdef
  set TB := rsTape TA (2 * k) (D + 1) with hTBdef
  have bns : ∀ b : Bool, (!b && b) = false := by
    intro b
    cases b <;> rfl
  have bnr : ∀ b : Bool, (b && !b) = false := by
    intro b
    cases b <;> rfl
  have TAbef : ∀ p, p < 2 * k + 4 → TA.getD p false = T.getD p false :=
    fun p hp => by
      rw [hTAdef]
      exact rsTape_getD_before T (2 * k + 4) D p hp
  have TAwin : ∀ p, 2 * k + 4 ≤ p → p < 2 * k + 4 + 2 * D →
      TA.getD p false = T.getD (p + 2) false :=
    fun p h1 h2 => by
      rw [hTAdef]
      exact rsTape_getD_lt T (2 * k + 4) D p h1 h2
  have TBsep : ∀ p, 2 * k ≤ p → p ≤ 2 * k + 1 →
      TB.getD p false = T.getD (p + 2) false := by
    intro p h1 h2
    rw [hTBdef, rsTape_getD_lt TA (2 * k) (D + 1) p h1 (by omega),
      hTAdef, rsTape_getD_before T (2 * k + 4) D (p + 2) (by omega)]
  have TBdata : ∀ p, 2 * k + 2 ≤ p → p < 2 * k + 2 * D + 2 →
      TB.getD p false = T.getD (p + 4) false := by
    intro p h1 h2
    rw [hTBdef, rsTape_getD_lt TA (2 * k) (D + 1) p (by omega) (by omega),
      hTAdef, rsTape_getD_lt T (2 * k + 4) D (p + 2) (by omega) (by omega),
      show p + 2 + 2 = p + 4 from by omega]
  have hcnt : T.getD (2 * k + 2 - 1) false = true := by
    rw [show 2 * k + 2 - 1 = 2 * k + 1 from by omega]
    exact (h.ctr k hk (le_refl k)).2
  have hnr : ∀ i, i < D - 1 →
      (T.getD (2 * k + 2 + 2 + 2 * i + 2) false &&
        !(T.getD (2 * k + 2 + 2 + 2 * i + 3) false)) = false := by
    intro i hi
    rw [show 2 * k + 2 + 2 + 2 * i + 2 = 2 * k + 4 + 2 * (i + 1) from by omega,
      show 2 * k + 2 + 2 + 2 * i + 3 = 2 * k + 5 + 2 * (i + 1) from by omega,
      h.dat (i + 1) (by omega)]
    exact bnr _
  have hrend : (T.getD (2 * k + 2 + 2 + 2 * (D - 1) + 2) false &&
      !(T.getD (2 * k + 2 + 2 + 2 * (D - 1) + 3) false)) = true := by
    rw [show 2 * k + 2 + 2 + 2 * (D - 1) + 2 = 2 * k + 4 + 2 * D from by omega,
      show 2 * k + 2 + 2 + 2 * (D - 1) + 3 = 2 * k + 5 + 2 * D from by omega,
      h.rendlo, h.rendhi]
    decide
  have hTA : TA = rsTape T (2 * k + 2 + 2) (D - 1 + 1) := by
    rw [hTAdef, show 2 * k + 2 + 2 = 2 * k + 4 from by omega,
      show D - 1 + 1 = D from by omega]
  have hns1 : ∀ i, i < D - 1 + 1 →
      (!(TA.getD (2 * k + 2 + 2 + 2 * (D - 1) + 1 - 2 * i - 1) false) &&
        TA.getD (2 * k + 2 + 2 + 2 * (D - 1) + 1 - 2 * i) false) = false := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [show 2 * k + 2 + 2 + 2 * (D - 1) + 1 - 2 * 0 - 1 =
          2 * k + 2 * D + 2 from by omega,
        TAwin (2 * k + 2 * D + 2) (by omega) (by omega),
        show 2 * k + 2 * D + 2 + 2 = 2 * k + 4 + 2 * D from by omega,
        h.rendlo]
      simp
    · rw [show 2 * k + 2 + 2 + 2 * (D - 1) + 1 - 2 * i - 1 =
          2 * k + 2 * D + 2 - 2 * i from by omega,
        show 2 * k + 2 + 2 + 2 * (D - 1) + 1 - 2 * i =
          2 * k + 2 * D + 3 - 2 * i from by omega,
        TAwin (2 * k + 2 * D + 2 - 2 * i) (by omega) (by omega),
        TAwin (2 * k + 2 * D + 3 - 2 * i) (by omega) (by omega),
        show 2 * k + 2 * D + 2 - 2 * i + 2 = 2 * k + 4 + 2 * (D - i) from by omega,
        show 2 * k + 2 * D + 3 - 2 * i + 2 = 2 * k + 5 + 2 * (D - i) from by omega,
        h.dat (D - i) (by omega)]
      exact bns _
  have hsep1 :
      (!(TA.getD (2 * k + 2 + 2 + 2 * (D - 1) + 1 - 2 * (D - 1 + 1) - 1) false) &&
        TA.getD (2 * k + 2 + 2 + 2 * (D - 1) + 1 - 2 * (D - 1 + 1)) false) = true := by
    rw [show 2 * k + 2 + 2 + 2 * (D - 1) + 1 - 2 * (D - 1 + 1) - 1 =
          2 * k + 2 from by omega,
      show 2 * k + 2 + 2 + 2 * (D - 1) + 1 - 2 * (D - 1 + 1) =
          2 * k + 3 from by omega,
      TAbef (2 * k + 2) (by omega), TAbef (2 * k + 3) (by omega),
      h.seplo, h.sephi]
    decide
  have hnrB : ∀ i, i < D →
      (TA.getD (2 * k + 2 - 2 + 2 * i + 2) false &&
        !(TA.getD (2 * k + 2 - 2 + 2 * i + 3) false)) = false := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [show 2 * k + 2 - 2 + 2 * 0 + 2 = 2 * k + 2 from by omega,
        TAbef (2 * k + 2) (by omega), h.seplo]
      simp
    · rw [show 2 * k + 2 - 2 + 2 * i + 2 = 2 * k + 2 * i + 2 from by omega,
        show 2 * k + 2 - 2 + 2 * i + 3 = 2 * k + 2 * i + 3 from by omega,
        TAwin (2 * k + 2 * i + 2) (by omega) (by omega),
        TAwin (2 * k + 2 * i + 3) (by omega) (by omega),
        show 2 * k + 2 * i + 2 + 2 = 2 * k + 4 + 2 * i from by omega,
        show 2 * k + 2 * i + 3 + 2 = 2 * k + 5 + 2 * i from by omega,
        h.dat i (by omega)]
      exact bnr _
  have hrendB : (TA.getD (2 * k + 2 - 2 + 2 * D + 2) false &&
      !(TA.getD (2 * k + 2 - 2 + 2 * D + 3) false)) = true := by
    rw [show 2 * k + 2 - 2 + 2 * D + 2 = 2 * k + 2 * D + 2 from by omega,
      show 2 * k + 2 - 2 + 2 * D + 3 = 2 * k + 2 * D + 3 from by omega,
      TAwin (2 * k + 2 * D + 2) (by omega) (by omega),
      TAwin (2 * k + 2 * D + 3) (by omega) (by omega),
      show 2 * k + 2 * D + 2 + 2 = 2 * k + 4 + 2 * D from by omega,
      show 2 * k + 2 * D + 3 + 2 = 2 * k + 5 + 2 * D from by omega,
      h.rendlo, h.rendhi]
    decide
  have hTB : TB = rsTape TA (2 * k + 2 - 2) (D + 1) := by
    rw [hTBdef, show 2 * k + 2 - 2 = 2 * k from by omega]
  have hP2 : (2 * k + 2 * D + 1 : Nat) = 2 * k + 2 - 2 + 2 * D + 1 := by
    omega
  have hns2 : ∀ i, i < D →
      (!(TB.getD (2 * k + 2 * D + 1 - 2 * i - 1) false) &&
        TB.getD (2 * k + 2 * D + 1 - 2 * i) false) = false := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [show 2 * k + 2 * D + 1 - 2 * 0 - 1 = 2 * k + 2 * D from by omega,
        TBdata (2 * k + 2 * D) (by omega) (by omega),
        show 2 * k + 2 * D + 4 = 2 * k + 4 + 2 * D from by omega,
        h.rendlo]
      simp
    · rw [show 2 * k + 2 * D + 1 - 2 * i - 1 = 2 * k + 2 * D - 2 * i from by omega,
        TBdata (2 * k + 2 * D - 2 * i) (by omega) (by omega),
        TBdata (2 * k + 2 * D + 1 - 2 * i) (by omega) (by omega),
        show 2 * k + 2 * D - 2 * i + 4 = 2 * k + 4 + 2 * (D - i) from by omega,
        show 2 * k + 2 * D + 1 - 2 * i + 4 = 2 * k + 5 + 2 * (D - i) from by omega,
        h.dat (D - i) (by omega)]
      exact bns _
  have hsep2 :
      (!(TB.getD (2 * k + 2 * D + 1 - 2 * D - 1) false) &&
        TB.getD (2 * k + 2 * D + 1 - 2 * D) false) = true := by
    rw [show 2 * k + 2 * D + 1 - 2 * D - 1 = 2 * k from by omega,
      show 2 * k + 2 * D + 1 - 2 * D = 2 * k + 1 from by omega,
      TBsep (2 * k) (by omega) (by omega),
      TBsep (2 * k + 1) (by omega) (by omega),
      show 2 * k + 1 + 2 = 2 * k + 3 from by omega,
      h.seplo, h.sephi]
    decide
  exact round_full_leftSafe (s := 2 * k + 2) (K := D - 1) (KB := D)
    (P2 := 2 * k + 2 * D + 1) (T := T) (TA := TA) (TB := TB)
    (by omega) hcnt hnr hrend hTA hns1 hsep1 hnrB hrendB hTB hP2 hns2 hsep2

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryRoundInvariant

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryRoundInvariant.roundInv_step_leftSafe
