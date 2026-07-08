import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameConeAmplify

/-!
# N-Frame → KRW: formula-depth composition for a special family (the monotone route)

The general-circuit route hit the direct-sum / tensor-subadditivity wall.  Pivot: FORMULAS have fan-out
`≤ 1`, so the sharing/amortization mechanism is absent (`formula_freshness`), and the difficulty moves to
FORMULA DEPTH = Karchmer–Wigderson communication complexity.  There the relevant conjecture is KRW
composition, `CC(KW_{f ⋄ g}) ≈ CC(KW_f) + CC(KW_g)`, whose truth gives `P ⊄ NC¹`.  This file sets up the
depth-composition framework and freezes the provable pieces; the special family where the KRW LOWER bound
is a THEOREM is the MONOTONE one.

## The framework

Formula depth `D(f)` equals the communication complexity `CC(KW_f)` of the Karchmer–Wigderson game.  For
a composition tower `F_{k+1} = Mix ⋄ F_k` (block composition), write `D k := D(F_k)`.
  • COMPOSITION UPPER BOUND (protocols compose): `D(f ⋄ g) ≤ D(f) + D(g)` — play `KW_f` to find a differing
    block, then `KW_g` within it.  Provable; the "naive" upper bound KRW conjectures is near-optimal.
  • KRW LOWER BOUND (the conjecture): `D(F_{k+1}) ≥ D(F_k) + Δ` for a per-level increment `Δ = Δ(Mix)`.
    General: OPEN (⟹ `P ⊄ NC¹`).  MONOTONE inner function liftable via query-to-communication: PROVED.
    Universal relation / strong composition: PROVED.  Best general bound: Håstad `(3−o(1)) log n`.

## The theorems (amplification is genuine; the KRW increment is the contract)

  `krw_amplifies` — **PROVED (induction)**: if composition adds depth `Δ` at every level
        (`∀ k, D k + Δ ≤ D (k+1)` — the KRW lower bound), then `D 0 + d·Δ ≤ D d`.  Depth accumulates
        LINEARLY in the number of composition levels.
  `krw_beats_log_depth` — **PROVED**: with `D d ≥ d·Δ`, block size giving `log n = d·L`, and a per-level
        increment beating the log block size (`c·L < Δ`), the depth exceeds `c·log n`
        (`c·(d·L) < D d`) — SUPER-`c·log n`.  So a KRW increment `Δ > L` (larger than the log of the
        composed block) at every level yields super-logarithmic depth, i.e. a function outside
        `NC¹`-depth `c·log n`.

## Honest scope — framework + amplification proved; the KRW increment is the frontier

The amplification and the super-log criterion are proved arithmetic.  The load-bearing input is the
per-level KRW lower bound `D(F_{k+1}) ≥ D(F_k) + Δ`.  For GENERAL functions it is the open KRW conjecture
(equivalent to `P ⊄ NC¹`), and even the best unconditional single bound is `(3−o(1)) log n` (Håstad,
25+ yrs).  For the MONOTONE model it is a THEOREM (KRW composition holds for monotone inner functions via
query-to-communication lifting), so `krw_amplifies` runs UNCONDITIONALLY there — combined with the
monotone-Freshness route (`no_cancellation_freshness`), the monotone recursive family is where these
depth bounds are actually provable.  This is the stepping stone; general super-log depth needs the KRW
conjecture, unmoved.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameKRW

/-- **KRW AMPLIFICATION (proved)**: if every composition level adds at least `Δ` to the formula depth
(the KRW lower bound `D k + Δ ≤ D (k+1)`), then after `d` levels `D 0 + d·Δ ≤ D d` — depth accumulates
linearly in the number of composed blocks. -/
theorem krw_amplifies (D : ℕ → ℕ) (Δ : ℕ)
    (hstep : ∀ k, D k + Δ ≤ D (k + 1)) :
    ∀ d, D 0 + d * Δ ≤ D d := by
  intro d
  induction d with
  | zero => simp
  | succ n ih =>
    have hs := hstep n
    have e : D 0 + (n + 1) * Δ = (D 0 + n * Δ) + Δ := by ring
    omega

/-- **SUPER-LOG DEPTH CRITERION (proved)**: with the amplified depth `d·Δ ≤ D d`, a block size giving
`log n = d·L`, and a per-level KRW increment beating the log block size (`c·L < Δ`), the depth exceeds
`c·log n`: `c·(d·L) < D d`.  So `Δ > L` per level yields super-`c·log n` depth — outside `NC¹`-depth. -/
theorem krw_beats_log_depth (Dd d Δ L c : ℕ) (hd : 1 ≤ d)
    (hamp : d * Δ ≤ Dd) (hincrement : c * L < Δ) :
    c * (d * L) < Dd := by
  have hkey : c * (d * L) = d * (c * L) := by ring
  have hlt : d * (c * L) < d * Δ := by
    exact Nat.mul_lt_mul_of_pos_left hincrement (by omega)
  omega

/-- **KRW LOWER ⟹ SUPER-LOG, PACKAGED (proved)**: per-level KRW increment `Δ` (from `krw_amplifies`,
`D 0 = 0`), `log n = d·L`, and `Δ` beating `c·L` give `c·log n < D d`. -/
theorem krw_composition_forces_superlog
    (D : ℕ → ℕ) (Δ L c d : ℕ) (hd : 1 ≤ d) (hD0 : D 0 = 0)
    (hstep : ∀ k, D k + Δ ≤ D (k + 1)) (hincrement : c * L < Δ) :
    c * (d * L) < D d := by
  have hamp := krw_amplifies D Δ hstep d
  rw [hD0] at hamp
  exact krw_beats_log_depth (D d) d Δ L c hd (by omega) hincrement

end PallLean.Paper93.DeepMath.PathB.NFrameKRW

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameKRW.krw_amplifies
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameKRW.krw_beats_log_depth
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameKRW.krw_composition_forces_superlog
