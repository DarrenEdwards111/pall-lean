import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NisanWigdersonGenerator
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NisanWigdersonLowIntersection

/-!
# The Nisan–Wigderson hybrid argument — the telescoping heart (proved) + the reduction sockets

Entry 190 left `NWGeneratorFromDesign` (design + hard function ⇒ a generator fooling `ACC⁰`) as a named socket; entry 191
proved the efficient low-intersection design.  This file opens up the **hybrid argument** — the proof that a design plus
a hard function yields a derandomisation — and *proves its genuine analytic/combinatorial heart*: the **hybrid
telescoping lemma**.

The NW hybrid argument runs: a distinguisher with global advantage `ε` between the generator output (hybrid `0`) and
uniform (hybrid `m`) ⟹ by telescoping, some *adjacent* hybrid pair is distinguished with advantage `≥ ε/m` ⟹ (Yao) a
next-bit predictor for the hard function `f` on the active block ⟹ (reconstruction, using the low-intersection design to
hardwire the other `m−1` blocks as small tables) a small circuit for `f` ⟹ contradiction with hardness.  Hence no
distinguisher exists — the generator fools `ACC⁰`.

## What is proved (clean axioms, no `sorry`)

* **`hybrid_advantage`** — the telescoping heart, fully proved: if the distinguisher's acceptance probabilities
  `f 0, …, f m` over the `m+1` hybrids satisfy a global advantage `ε ≤ |f m − f 0|` (with `ε > 0`), then some adjacent
  pair has advantage `ε/m ≤ |f (i+1) − f i|`.  Proof: telescoping `∑ (f(i+1) − f i) = f m − f 0`
  (`Finset.sum_range_sub`), `|∑| ≤ ∑|·|` (`Finset.abs_sum_le_sum_abs`), and if *every* adjacent gap were `< ε/m` the
  sum would be `< m·(ε/m) = ε ≤ |f m − f 0|`, a contradiction.
* **`low_intersection_table_card`** — the quantitative payoff of entry 191: a block sharing `r < k` seed bits with the
  active block is a Boolean function of `r` bits, so its truth table has `2^r ≤ 2^k` entries — the per-block hardwiring
  cost in the reconstruction.  This is *why* the low-intersection design (intersection `< k`) makes reconstruction
  efficient.
* **`nw_hybrid_no_distinguisher`** — the composition glue (proved): the telescoping lemma + the three reduction sockets
  + hardness + a design ⇒ a global advantage is contradictory.
* **`nwGeneratorFromDesign_via_hybrid`** — discharges the **entry-190 `NWGeneratorFromDesign` socket** under the three
  named sub-sockets: a design and a hard function give the derandomisation `¬ GlobalAdvantage` (no `ε`-distinguisher).

## Honest scope

This proves the **telescoping heart** of the NW hybrid argument (`hybrid_advantage`) completely and from first
principles, and the **quantitative low-intersection payoff** (`low_intersection_table_card`), and the **composition
glue** discharging entry 190's `NWGeneratorFromDesign` socket.  What remain named sub-sockets are the two steps that need
the computational model: **`YaoPredictor`** (adjacent-hybrid advantage ⇒ next-bit predictor — Yao's distinguisher↔
predictor theorem) and **`Reconstruction`** (next-bit predictor + low-intersection design ⇒ small circuit for `f` — the
hardwiring argument), plus **`HardnessExcludesCircuit`** (the hard function has no small circuit).  Each is a proven
classical fact (Nisan–Wigderson 1994, Yao) requiring circuit-complexity / probability infrastructure absent here.  This
proves the hybrid argument's *combinatorial engine* and its *decomposition*, not the full generator.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonHybrid

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonGenerator (NWGeneratorFromDesign)

/-- **Global distinguishing advantage.**  `f i` is the distinguisher's acceptance probability on hybrid `i`; hybrid `0`
is the generator's output and hybrid `m` is uniform.  A global advantage of `ε` means `ε ≤ |f m − f 0|`. -/
def GlobalAdvantage (f : ℕ → ℝ) (m : ℕ) (ε : ℝ) : Prop := ε ≤ |f m - f 0|

/-- **Adjacent (per-step) distinguishing advantage.**  Some neighbouring hybrid pair `i, i+1` (`i < m`) is distinguished
with advantage `≥ ε/m`. -/
def AdjacentAdvantage (f : ℕ → ℝ) (m : ℕ) (ε : ℝ) : Prop := ∃ i, i < m ∧ ε / m ≤ |f (i + 1) - f i|

/-- **The hybrid telescoping lemma (PROVED) — the analytic heart of the NW hybrid argument.**  A global advantage `ε`
(with `ε > 0`) across the `m+1` hybrids forces an adjacent pair with advantage `≥ ε/m`.  Proof: telescoping
`∑_{i<m} (f(i+1) − f i) = f m − f 0`, so `|f m − f 0| ≤ ∑ |f(i+1) − f i|`; were every gap `< ε/m`, the sum would be
`< m·(ε/m) = ε ≤ |f m − f 0|`, contradiction.  (The case `m = 0` is impossible: it forces `|f 0 − f 0| = 0 < ε`.) -/
theorem hybrid_advantage (f : ℕ → ℝ) (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hglob : GlobalAdvantage f m ε) : AdjacentAdvantage f m ε := by
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp only [GlobalAdvantage, sub_self, abs_zero] at hglob; linarith
    · exact hpos
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm0.ne'
  by_contra h
  simp only [AdjacentAdvantage, not_exists, not_and, not_le] at h
  have hsum : ∑ i ∈ Finset.range m, |f (i + 1) - f i| < ε := by
    calc ∑ i ∈ Finset.range m, |f (i + 1) - f i|
        < ∑ _i ∈ Finset.range m, (ε / m) := by
          apply Finset.sum_lt_sum_of_nonempty
          · rw [Finset.nonempty_range_iff]; exact hm0.ne'
          · intro i hi; rw [Finset.mem_range] at hi; exact h i hi
      _ = m * (ε / m) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ε := by field_simp
  have hle : |f m - f 0| ≤ ∑ i ∈ Finset.range m, |f (i + 1) - f i| := by
    rw [← Finset.sum_range_sub f m]; exact Finset.abs_sum_le_sum_abs _ _
  unfold GlobalAdvantage at hglob; linarith

/-- **The low-intersection hardwiring cost (PROVED) — the quantitative payoff of entry 191.**  In the reconstruction
step, each of the other `m−1` blocks shares only `r < k` seed bits with the active block (the low-intersection
property), so it is a Boolean function of `r` bits and its truth table has `2^r ≤ 2^k` entries.  Thus the
low-intersection design (`nw_low_intersection_design`, intersection `< k`) bounds the per-block hardwiring cost by
`2^k`, which is what keeps the reconstructed circuit small. -/
theorem low_intersection_table_card (r k : ℕ) (hrk : r < k) :
    Fintype.card (Fin r → Bool) ≤ 2 ^ k := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  exact Nat.pow_le_pow_right (by norm_num) (le_of_lt hrk)

/-- **Yao's distinguisher ↔ predictor socket.**  An adjacent-hybrid distinguishing advantage yields a next-bit predictor
for the hard function on the active block (Yao 1982).  Stated, not proved. -/
def YaoPredictor (AdjAdv NextBitPredictor : Prop) : Prop := AdjAdv → NextBitPredictor

/-- **The reconstruction socket.**  A next-bit predictor, together with the low-intersection design (which lets the
other `m−1` blocks be hardwired as tables of size `≤ 2^k`, cf. `low_intersection_table_card`), yields a small circuit
computing the hard function `f`.  Stated, not proved. -/
def Reconstruction (NextBitPredictor LowIntersectionDesign SmallCircuitForF : Prop) : Prop :=
  NextBitPredictor → LowIntersectionDesign → SmallCircuitForF

/-- **The hardness socket.**  A hard function has no small circuit. -/
def HardnessExcludesCircuit (HardFunction SmallCircuitForF : Prop) : Prop :=
  HardFunction → SmallCircuitForF → False

/-- **Composition glue (PROVED): no distinguisher survives.**  The telescoping lemma turns a global advantage into an
adjacent one; Yao turns that into a next-bit predictor; reconstruction (with the design) turns that into a small circuit
for `f`; hardness forbids it.  Hence a global `ε`-advantage is contradictory. -/
theorem nw_hybrid_no_distinguisher
    (f : ℕ → ℝ) (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (NextBitPredictor LowIntersectionDesign SmallCircuitForF HardFunction : Prop)
    (yao : YaoPredictor (AdjacentAdvantage f m ε) NextBitPredictor)
    (recon : Reconstruction NextBitPredictor LowIntersectionDesign SmallCircuitForF)
    (hard : HardnessExcludesCircuit HardFunction SmallCircuitForF)
    (hdesign : LowIntersectionDesign) (hHard : HardFunction)
    (hglob : GlobalAdvantage f m ε) : False :=
  hard hHard (recon (yao (hybrid_advantage f m ε hε hglob)) hdesign)

/-- **Discharging the entry-190 `NWGeneratorFromDesign` socket via the hybrid argument (PROVED glue).**  Under the three
named sub-sockets (Yao, reconstruction, hardness), a low-intersection design and a hard function give the
derandomisation `¬ GlobalAdvantage f m ε` — i.e. no `ACC⁰` distinguisher achieves advantage `ε`, so the generator fools
`ACC⁰`.  The telescoping engine `hybrid_advantage` is the proved core; the remaining sub-sockets are the classical
Yao/reconstruction/hardness steps. -/
theorem nwGeneratorFromDesign_via_hybrid
    (f : ℕ → ℝ) (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (NextBitPredictor LowIntersectionDesign SmallCircuitForF HardFunction : Prop)
    (yao : YaoPredictor (AdjacentAdvantage f m ε) NextBitPredictor)
    (recon : Reconstruction NextBitPredictor LowIntersectionDesign SmallCircuitForF)
    (hard : HardnessExcludesCircuit HardFunction SmallCircuitForF) :
    NWGeneratorFromDesign LowIntersectionDesign HardFunction (¬ GlobalAdvantage f m ε) :=
  fun hdesign hHard hglob =>
    nw_hybrid_no_distinguisher f m ε hε NextBitPredictor LowIntersectionDesign SmallCircuitForF
      HardFunction yao recon hard hdesign hHard hglob

end PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonHybrid

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonHybrid.hybrid_advantage
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonHybrid.low_intersection_table_card
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonHybrid.nwGeneratorFromDesign_via_hybrid
