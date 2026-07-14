import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinRoundBody

/-!
# Cook–Levin M1 — the doubled-tape round-start invariant and its preservation

`round_full` (CookLevinRoundBody) takes the round body from a round-start config with `k` counters to the
round-start config with `k-1` counters, but its hypotheses are raw `getD` facts about the tape and its two evolved
copies.  This file packages those facts into a single **round-start invariant** `RoundInv T k D` (the doubled
`LSENT counterᵏ SEP a₀…a_{D-1} REND` structure, with the region past `REND` left free) and proves the invariant is
**preserved**: one loop iteration maps `RoundInv T k D` to `RoundInv TB (k-1) (D-1)` — `a₀` and one counter deleted.

The heart is the `getD` behaviour of `rsTape` (the shift-delete of `rendShift`): it copies the window one pair to
the left and leaves everything outside untouched.  With the existing `rsTape_getD_ge` (past the window), the two
missing cases below (`rsTape_getD_before`, `rsTape_getD_lt`) fully characterise it.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinRoundInvariant

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinRendShift
open PallLean.Paper93.DeepMath.PathB.CookLevinRoundBody
open PallLean.Paper93.DeepMath.PathB.CookLevinShiftLoop (writeAt_getD_ne writeAt_getD_self)

/-! ## `rsTape` `getD` characterisation -/

/-- Before the shifted window (`p < q`), `rsTape` leaves the cell unchanged. -/
theorem rsTape_getD_before (x : List Bool) (q : ℕ) :
    ∀ (m p : ℕ), p < q → (rsTape x q m).getD p false = x.getD p false := by
  intro m
  induction m with
  | zero => intro p _; rfl
  | succ m ih =>
    intro p hp
    simp only [rsTape]
    rw [writeAt_getD_ne (show p ≠ q + 2 * m + 1 by omega), writeAt_getD_ne (show p ≠ q + 2 * m by omega)]
    exact ih p hp

/-- Inside the shifted window (`q ≤ p < q + 2m`), `rsTape` reads the cell two to the right (left-shift by one pair). -/
theorem rsTape_getD_lt (x : List Bool) (q : ℕ) :
    ∀ (m p : ℕ), q ≤ p → p < q + 2 * m → (rsTape x q m).getD p false = x.getD (p + 2) false := by
  intro m
  induction m with
  | zero => intro p _ hp; omega
  | succ m ih =>
    intro p hq hp
    simp only [rsTape]
    rcases Nat.lt_or_ge p (q + 2 * m) with hlt | hge
    · rw [writeAt_getD_ne (show p ≠ q + 2 * m + 1 by omega), writeAt_getD_ne (show p ≠ q + 2 * m by omega)]
      exact ih p hq hlt
    · have : p = q + 2 * m ∨ p = q + 2 * m + 1 := by omega
      rcases this with rfl | rfl
      · rw [writeAt_getD_ne (show q + 2 * m ≠ q + 2 * m + 1 by omega), writeAt_getD_self]
      · rw [writeAt_getD_self]

/-! ## The round-start invariant and its preservation -/

/-- **Round-start invariant.**  With `k ≥ 1` counters and `D` data pairs, the doubled tape reads
`LSENT counterᵏ SEP a₀…a_{D-1} REND` and is unconstrained past `REND`.  `SEP` low is at `2k+2`.  A counter pair is
`11`, `SEP` is `01`, `REND` is `10`, and each data pair has equal cells (so it is neither `SEP` nor `REND`). -/
structure RoundInv (T : List Bool) (k D : ℕ) : Prop where
  /-- Every counter pair `[2i, 2i+1]` (`i = 1…k`) is `11`. -/
  ctr : ∀ i, 1 ≤ i → i ≤ k → T.getD (2 * i) false = true ∧ T.getD (2 * i + 1) false = true
  /-- `SEP` low cell is `0`. -/
  seplo : T.getD (2 * k + 2) false = false
  /-- `SEP` high cell is `1`. -/
  sephi : T.getD (2 * k + 3) false = true
  /-- Each data pair `[2k+4+2j, 2k+5+2j]` (`j < D`) has equal cells. -/
  dat : ∀ j, j < D → T.getD (2 * k + 4 + 2 * j) false = T.getD (2 * k + 5 + 2 * j) false
  /-- `REND` low cell is `1`. -/
  rendlo : T.getD (2 * k + 4 + 2 * D) false = true
  /-- `REND` high cell is `0`. -/
  rendhi : T.getD (2 * k + 5 + 2 * D) false = false

/-- **Invariant preservation.**  The doubled-tape transform of one loop iteration — delete the `a₀` pair
(`rsTape … (2k+4) D`, the `SHA` shift) then the counter pair (`rsTape … (2k) (D+1)`, the `SHB` shift) — carries a
round-start tape with `k` counters and `D` data pairs to a round-start tape with `k-1` counters and `D-1` data
pairs (`a₀` and one counter deleted).  This is exactly `round_full`'s output tape (with `K = D-1`, `KB = D`). -/
theorem roundInv_preserved (T : List Bool) (k D : ℕ) (hk : 1 ≤ k) (hD : 1 ≤ D) (h : RoundInv T k D) :
    RoundInv (rsTape (rsTape T (2 * k + 4) D) (2 * k) (D + 1)) (k - 1) (D - 1) := by
  set TA := rsTape T (2 * k + 4) D with hTA
  set TB := rsTape TA (2 * k) (D + 1) with hTB
  -- counter region (before both windows): TB p = TA p = T p
  have cnt : ∀ p, p < 2 * k → TB.getD p false = T.getD p false := by
    intro p hp
    rw [hTB, rsTape_getD_before TA (2 * k) (D + 1) p hp, hTA, rsTape_getD_before T (2 * k + 4) D p (by omega)]
  -- SEP region (TB window, then before TA window): TB p = TA (p+2) = T (p+2)   for p ∈ {2k, 2k+1}
  have sep : ∀ p, 2 * k ≤ p → p ≤ 2 * k + 1 → TB.getD p false = T.getD (p + 2) false := by
    intro p hp1 hp2
    rw [hTB, rsTape_getD_lt TA (2 * k) (D + 1) p hp1 (by omega), hTA,
      rsTape_getD_before T (2 * k + 4) D (p + 2) (by omega)]
  -- data/REND region (both windows): TB p = TA (p+2) = T (p+4)   for p ∈ [2k+2, 2k+2D+1]
  have dta : ∀ p, 2 * k + 2 ≤ p → p < 2 * k + 2 * D + 2 → TB.getD p false = T.getD (p + 2 + 2) false := by
    intro p hp1 hp2
    rw [hTB, rsTape_getD_lt TA (2 * k) (D + 1) p (by omega) (by omega), hTA,
      rsTape_getD_lt T (2 * k + 4) D (p + 2) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- counters 1 … k-1 survive
    intro i hi1 hik
    obtain ⟨hc, hc1⟩ := h.ctr i hi1 (by omega)
    exact ⟨by rw [cnt (2 * i) (by omega), hc], by rw [cnt (2 * i + 1) (by omega), hc1]⟩
  · -- new SEP low at 2(k-1)+2 = 2k
    rw [show 2 * (k - 1) + 2 = 2 * k from by omega, sep (2 * k) (by omega) (by omega),
      show 2 * k + 2 = 2 * k + 2 from rfl, h.seplo]
  · -- new SEP high at 2(k-1)+3 = 2k+1
    rw [show 2 * (k - 1) + 3 = 2 * k + 1 from by omega, sep (2 * k + 1) (by omega) (by omega),
      show 2 * k + 1 + 2 = 2 * k + 3 from by omega, h.sephi]
  · -- new data pair j = old data pair j+1
    intro j hj
    rw [show 2 * (k - 1) + 4 + 2 * j = 2 * k + 2 + 2 * j from by omega,
      show 2 * (k - 1) + 5 + 2 * j = 2 * k + 3 + 2 * j from by omega,
      dta (2 * k + 2 + 2 * j) (by omega) (by omega), dta (2 * k + 3 + 2 * j) (by omega) (by omega),
      show 2 * k + 2 + 2 * j + 2 + 2 = 2 * k + 4 + 2 * (j + 1) from by omega,
      show 2 * k + 3 + 2 * j + 2 + 2 = 2 * k + 5 + 2 * (j + 1) from by omega]
    exact h.dat (j + 1) (by omega)
  · -- new REND low at 2(k-1)+4+2(D-1) = 2k+2D
    rw [show 2 * (k - 1) + 4 + 2 * (D - 1) = 2 * k + 2 * D from by omega,
      dta (2 * k + 2 * D) (by omega) (by omega),
      show 2 * k + 2 * D + 2 + 2 = 2 * k + 4 + 2 * D from by omega, h.rendlo]
  · -- new REND high at 2(k-1)+5+2(D-1) = 2k+2D+1
    rw [show 2 * (k - 1) + 5 + 2 * (D - 1) = 2 * k + 2 * D + 1 from by omega,
      dta (2 * k + 2 * D + 1) (by omega) (by omega),
      show 2 * k + 2 * D + 1 + 2 + 2 = 2 * k + 5 + 2 * D from by omega, h.rendhi]

/-! ## Applying `round_full` from the invariant -/

/-- **One invariant-level round step.**  From `RoundInv T k D` (`k, D ≥ 1`) the master runs one full loop iteration
from the round-start config (loop head at `SEP` low `2k+2`) to the round-start config for `k-1` counters (head at
the new `SEP` low `2k`), with the `a₀`-and-counter-deleted tape.  All nine of `round_full`'s doubled-tape
preconditions are discharged from the six `RoundInv` fields via the `rsTape` `getD` lemmas: the scans hit a marker
pair (`i = 0`) then equal-celled data pairs (both markers fail, `!b && b = b && !b = false`). -/
theorem roundInv_step (T : List Bool) (k D : ℕ) (hk : 1 ≤ k) (hD : 1 ≤ D) (h : RoundInv T k D) :
    run masterM ((2 + 1 + 2 + (8 * (D - 1) + 8) + 1)
        + ((2 * (D - 1 + 1) + 2) + 1 + 1 + (8 * D + 8) + 1 + (2 * D + 2) + 1))
        ⟨(1, 0, false, false), 2 * k + 2, T⟩
      = ⟨(1, 0, false, false), 2 * k, rsTape (rsTape T (2 * k + 4) D) (2 * k) (D + 1)⟩ := by
  set TA := rsTape T (2 * k + 4) D with hTAdef
  set TB := rsTape TA (2 * k) (D + 1) with hTBdef
  have bns : ∀ b : Bool, (!b && b) = false := by intro b; cases b <;> rfl
  have bnr : ∀ b : Bool, (b && !b) = false := by intro b; cases b <;> rfl
  -- `getD` transfer facts for TA and TB
  have TAbef : ∀ p, p < 2 * k + 4 → TA.getD p false = T.getD p false :=
    fun p hp => by rw [hTAdef]; exact rsTape_getD_before T (2 * k + 4) D p hp
  have TAwin : ∀ p, 2 * k + 4 ≤ p → p < 2 * k + 4 + 2 * D → TA.getD p false = T.getD (p + 2) false :=
    fun p h1 h2 => by rw [hTAdef]; exact rsTape_getD_lt T (2 * k + 4) D p h1 h2
  have TBsep : ∀ p, 2 * k ≤ p → p ≤ 2 * k + 1 → TB.getD p false = T.getD (p + 2) false := by
    intro p h1 h2
    rw [hTBdef, rsTape_getD_lt TA (2 * k) (D + 1) p h1 (by omega), hTAdef,
      rsTape_getD_before T (2 * k + 4) D (p + 2) (by omega)]
  have TBdata : ∀ p, 2 * k + 2 ≤ p → p < 2 * k + 2 * D + 2 → TB.getD p false = T.getD (p + 4) false := by
    intro p h1 h2
    rw [hTBdef, rsTape_getD_lt TA (2 * k) (D + 1) p (by omega) (by omega), hTAdef,
      rsTape_getD_lt T (2 * k + 4) D (p + 2) (by omega) (by omega), show p + 2 + 2 = p + 4 from by omega]
  -- discharge round_full's preconditions
  have hs2 : 2 ≤ 2 * k + 2 := by omega
  have hcnt : T.getD (2 * k + 2 - 1) false = true := by
    rw [show 2 * k + 2 - 1 = 2 * k + 1 from by omega]; exact (h.ctr k hk (le_refl k)).2
  have hnr : ∀ i, i < D - 1 →
      (T.getD (2 * k + 2 + 2 + 2 * i + 2) false && !(T.getD (2 * k + 2 + 2 + 2 * i + 3) false)) = false := by
    intro i hi
    rw [show 2 * k + 2 + 2 + 2 * i + 2 = 2 * k + 4 + 2 * (i + 1) from by omega,
      show 2 * k + 2 + 2 + 2 * i + 3 = 2 * k + 5 + 2 * (i + 1) from by omega, h.dat (i + 1) (by omega)]
    exact bnr _
  have hrend : (T.getD (2 * k + 2 + 2 + 2 * (D - 1) + 2) false
      && !(T.getD (2 * k + 2 + 2 + 2 * (D - 1) + 3) false)) = true := by
    rw [show 2 * k + 2 + 2 + 2 * (D - 1) + 2 = 2 * k + 4 + 2 * D from by omega,
      show 2 * k + 2 + 2 + 2 * (D - 1) + 3 = 2 * k + 5 + 2 * D from by omega, h.rendlo, h.rendhi]
    decide
  have hTA : TA = rsTape T (2 * k + 2 + 2) (D - 1 + 1) := by
    rw [hTAdef, show 2 * k + 2 + 2 = 2 * k + 4 from by omega, show D - 1 + 1 = D from by omega]
  have hns1 : ∀ i, i < D - 1 + 1 →
      (!(TA.getD (2 * k + 2 + 2 + 2 * (D - 1) + 1 - 2 * i - 1) false)
        && TA.getD (2 * k + 2 + 2 + 2 * (D - 1) + 1 - 2 * i) false) = false := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [show 2 * k + 2 + 2 + 2 * (D - 1) + 1 - 2 * 0 - 1 = 2 * k + 2 * D + 2 from by omega,
        TAwin (2 * k + 2 * D + 2) (by omega) (by omega),
        show 2 * k + 2 * D + 2 + 2 = 2 * k + 4 + 2 * D from by omega, h.rendlo]
      simp
    · rw [show 2 * k + 2 + 2 + 2 * (D - 1) + 1 - 2 * i - 1 = 2 * k + 2 * D + 2 - 2 * i from by omega,
        show 2 * k + 2 + 2 + 2 * (D - 1) + 1 - 2 * i = 2 * k + 2 * D + 3 - 2 * i from by omega,
        TAwin (2 * k + 2 * D + 2 - 2 * i) (by omega) (by omega),
        TAwin (2 * k + 2 * D + 3 - 2 * i) (by omega) (by omega),
        show 2 * k + 2 * D + 2 - 2 * i + 2 = 2 * k + 4 + 2 * (D - i) from by omega,
        show 2 * k + 2 * D + 3 - 2 * i + 2 = 2 * k + 5 + 2 * (D - i) from by omega, h.dat (D - i) (by omega)]
      exact bns _
  have hsep1 : (!(TA.getD (2 * k + 2 + 2 + 2 * (D - 1) + 1 - 2 * (D - 1 + 1) - 1) false)
      && TA.getD (2 * k + 2 + 2 + 2 * (D - 1) + 1 - 2 * (D - 1 + 1)) false) = true := by
    rw [show 2 * k + 2 + 2 + 2 * (D - 1) + 1 - 2 * (D - 1 + 1) - 1 = 2 * k + 2 from by omega,
      show 2 * k + 2 + 2 + 2 * (D - 1) + 1 - 2 * (D - 1 + 1) = 2 * k + 3 from by omega,
      TAbef (2 * k + 2) (by omega), TAbef (2 * k + 3) (by omega), h.seplo, h.sephi]
    decide
  have hnrB : ∀ i, i < D →
      (TA.getD (2 * k + 2 - 2 + 2 * i + 2) false && !(TA.getD (2 * k + 2 - 2 + 2 * i + 3) false)) = false := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [show 2 * k + 2 - 2 + 2 * 0 + 2 = 2 * k + 2 from by omega, TAbef (2 * k + 2) (by omega), h.seplo]
      simp
    · rw [show 2 * k + 2 - 2 + 2 * i + 2 = 2 * k + 2 * i + 2 from by omega,
        show 2 * k + 2 - 2 + 2 * i + 3 = 2 * k + 2 * i + 3 from by omega,
        TAwin (2 * k + 2 * i + 2) (by omega) (by omega), TAwin (2 * k + 2 * i + 3) (by omega) (by omega),
        show 2 * k + 2 * i + 2 + 2 = 2 * k + 4 + 2 * i from by omega,
        show 2 * k + 2 * i + 3 + 2 = 2 * k + 5 + 2 * i from by omega, h.dat i (by omega)]
      exact bnr _
  have hrendB : (TA.getD (2 * k + 2 - 2 + 2 * D + 2) false
      && !(TA.getD (2 * k + 2 - 2 + 2 * D + 3) false)) = true := by
    rw [show 2 * k + 2 - 2 + 2 * D + 2 = 2 * k + 2 * D + 2 from by omega,
      show 2 * k + 2 - 2 + 2 * D + 3 = 2 * k + 2 * D + 3 from by omega,
      TAwin (2 * k + 2 * D + 2) (by omega) (by omega), TAwin (2 * k + 2 * D + 3) (by omega) (by omega),
      show 2 * k + 2 * D + 2 + 2 = 2 * k + 4 + 2 * D from by omega,
      show 2 * k + 2 * D + 3 + 2 = 2 * k + 5 + 2 * D from by omega, h.rendlo, h.rendhi]
    decide
  have hTB : TB = rsTape TA (2 * k + 2 - 2) (D + 1) := by
    rw [hTBdef, show 2 * k + 2 - 2 = 2 * k from by omega]
  have hP2 : (2 * k + 2 * D + 1 : ℕ) = 2 * k + 2 - 2 + 2 * D + 1 := by omega
  have hns2 : ∀ i, i < D →
      (!(TB.getD (2 * k + 2 * D + 1 - 2 * i - 1) false) && TB.getD (2 * k + 2 * D + 1 - 2 * i) false) = false := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [show 2 * k + 2 * D + 1 - 2 * 0 - 1 = 2 * k + 2 * D from by omega,
        TBdata (2 * k + 2 * D) (by omega) (by omega),
        show 2 * k + 2 * D + 4 = 2 * k + 4 + 2 * D from by omega, h.rendlo]
      simp
    · rw [show 2 * k + 2 * D + 1 - 2 * i - 1 = 2 * k + 2 * D - 2 * i from by omega,
        show 2 * k + 2 * D + 1 - 2 * i = 2 * k + 2 * D + 1 - 2 * i from rfl,
        TBdata (2 * k + 2 * D - 2 * i) (by omega) (by omega),
        TBdata (2 * k + 2 * D + 1 - 2 * i) (by omega) (by omega),
        show 2 * k + 2 * D - 2 * i + 4 = 2 * k + 4 + 2 * (D - i) from by omega,
        show 2 * k + 2 * D + 1 - 2 * i + 4 = 2 * k + 5 + 2 * (D - i) from by omega, h.dat (D - i) (by omega)]
      exact bns _
  have hsep2 : (!(TB.getD (2 * k + 2 * D + 1 - 2 * D - 1) false)
      && TB.getD (2 * k + 2 * D + 1 - 2 * D) false) = true := by
    rw [show 2 * k + 2 * D + 1 - 2 * D - 1 = 2 * k from by omega,
      show 2 * k + 2 * D + 1 - 2 * D = 2 * k + 1 from by omega,
      TBsep (2 * k) (by omega) (by omega), TBsep (2 * k + 1) (by omega) (by omega),
      show 2 * k + 2 = 2 * k + 2 from rfl, show 2 * k + 1 + 2 = 2 * k + 3 from by omega, h.seplo, h.sephi]
    decide
  have key := round_full (s := 2 * k + 2) (K := D - 1) (KB := D) (P2 := 2 * k + 2 * D + 1)
    (T := T) (TA := TA) (TB := TB) hs2 hcnt hnr hrend hTA hns1 hsep1 hnrB hrendB hTB hP2 hns2 hsep2
  rw [show (2 * k + 2 - 2 : ℕ) = 2 * k from by omega] at key
  exact key

/-- **Iterable per-round step.**  Combines application (`roundInv_step`) with preservation (`roundInv_preserved`):
from a round-start config satisfying `RoundInv T k D`, one master loop iteration lands at the round-start config
for `k-1` counters (head at the new `SEP` low `2(k-1)+2`) on a tape `T'` that again satisfies the invariant
`RoundInv T' (k-1) (D-1)`.  This is the building block the whole-run induction on the counter `v` iterates. -/
theorem roundInv_round (T : List Bool) (k D : ℕ) (hk : 1 ≤ k) (hD : 1 ≤ D) (h : RoundInv T k D) :
    ∃ T', run masterM ((2 + 1 + 2 + (8 * (D - 1) + 8) + 1)
          + ((2 * (D - 1 + 1) + 2) + 1 + 1 + (8 * D + 8) + 1 + (2 * D + 2) + 1))
          ⟨(1, 0, false, false), 2 * k + 2, T⟩
        = ⟨(1, 0, false, false), 2 * (k - 1) + 2, T'⟩ ∧ RoundInv T' (k - 1) (D - 1) := by
  refine ⟨rsTape (rsTape T (2 * k + 4) D) (2 * k) (D + 1), ?_, roundInv_preserved T k D hk hD h⟩
  rw [show 2 * (k - 1) + 2 = 2 * k from by omega]
  exact roundInv_step T k D hk hD h

end PallLean.Paper93.DeepMath.PathB.CookLevinRoundInvariant
