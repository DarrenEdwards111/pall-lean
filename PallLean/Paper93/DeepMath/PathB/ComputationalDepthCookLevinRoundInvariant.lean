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
open PallLean.Paper93.DeepMath.PathB.CookLevinRendShift
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

end PallLean.Paper93.DeepMath.PathB.CookLevinRoundInvariant
