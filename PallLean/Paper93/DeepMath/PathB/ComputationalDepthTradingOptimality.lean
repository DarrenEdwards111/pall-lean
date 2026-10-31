import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAlternationTrading

/-!
# Trading optimality: the potential-function method (universal `c ≤ 2` cap) + the tight threshold's algebraic home

The user asked for the **full Buss–Williams optimality meta-theorem** (no alternation-trading proof establishes
`SAT ∉ TISP(n^c)` for `c ≥ 2cos(π/7) ≈ 1.8019`).  Honest status: the *tight* constant is Buss–Williams' result,
obtained by **LP duality with a computer search** over the unbounded space of proof-tree shapes — a numerical,
partly machine-found optimum that this file does not reproduce (doing so faithfully is a research-scale
formalization; asserting it without the LP/search would be a fabrication).

What IS proved here is the **method** behind it, universally, with an explicit closed-form dual certificate:

* `Phi` — the potential `Φ(L) = base(L) + Σ (quantifier exponents)`, the uniform LP-dual certificate;
* `phi_steps_mono` — `Φ` is non-decreasing along **every** derivation when `c ≥ 2` (speedup preserves it exactly;
  slowdown pays `r + x ≤ c·max(x,r)` since `c·max ≥ 2·max ≥ x+r`; weaken/complement are monotone);
* `trading_optimality_two` — **the universal cap**: for `c ≥ 2`, NO derivation (any proof shape) takes
  `DTISP(n^r)` to `DTISP(n^{r'})` with `r' < r`.  So alternation trading proves nothing for `c ≥ 2`.

The gap `[2cos(π/7), 2)` is exactly where the *uniform* dual weights are loose: closing it to the tight
`2cos(π/7)` needs depth-dependent (LP-optimal) weights — the Buss–Williams contribution.  The tight threshold's
algebraic home is pinned:

* `bwPoly` — the Buss–Williams characteristic polynomial `x³ − x² − 2x + 1`;
* `trading_threshold_root` — it has a root in `(1.8, 1.81)` (`= 2cos(π/7)`), strictly below the potential cap `2`,
  localizing the loose region.

So: the trading proof system (`AlternationTrading`), its endpoints (speedup necessary; a working derivation), a
universal potential cap at `2`, and the tight constant's algebraic location — all machine-checked.  The tight
optimality itself remains the honestly-fenced computer-assisted result.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TradingOptimality

open PallLean.Paper93.DeepMath.PathB.AlternationTrading

/-- The uniform LP-dual potential: base plus total quantifier exponent. -/
def Phi (L : Line) : ℚ := L.base + (L.quants.map Prod.snd).sum

variable {c : ℚ}

/-- **Every move is `Φ`-non-decreasing when `c ≥ 2`.** -/
theorem phi_step_mono (hc : 2 ≤ c) {L L' : Line} (h : Step c L L') : Phi L ≤ Phi L' := by
  cases h with
  | speedup qs r x hx hxr =>
    simp only [Phi, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    linarith
  | slowdown qs Q x r hx =>
    simp only [Phi, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    have hmx : x ≤ max x r := le_max_left x r
    have hmr : r ≤ max x r := le_max_right x r
    have hm0 : (0 : ℚ) ≤ max x r := le_trans hx hmx
    nlinarith [hmx, hmr, hm0, hc, mul_nonneg (by linarith : (0:ℚ) ≤ c - 2) hm0]
  | weaken qs r r' hle =>
    simp only [Phi]
    linarith
  | complement qs r =>
    have heq : (qs.map (fun p : Bool × ℚ => (!p.1, p.2))).map Prod.snd = qs.map Prod.snd := by
      simp [List.map_map, Function.comp]
    exact le_of_eq (by simp only [Phi, heq])

/-- **`Φ` is non-decreasing along every derivation when `c ≥ 2`.** -/
theorem phi_steps_mono (hc : 2 ≤ c) {L L' : Line} (h : Steps c L L') : Phi L ≤ Phi L' := by
  induction h with
  | refl => exact le_refl _
  | tail _ step ih => exact le_trans ih (phi_step_mono hc step)

/-- **The universal potential cap.**  For `c ≥ 2`, no alternation-trading derivation — of any proof shape — takes
`DTISP(n^r)` to `DTISP(n^{r'})` with `r' < r`.  Hence trading proves `SAT ∉ TISP(n^c)` for NO `c ≥ 2`: the
proof-system optimum is `< 2`.  (The tight optimum `2cos(π/7)` needs depth-dependent LP weights; see below.) -/
theorem trading_optimality_two (hc : 2 ≤ c) {r r' : ℚ}
    (h : Steps c ⟨[], r⟩ ⟨[], r'⟩) : r ≤ r' := by
  have := phi_steps_mono hc h
  simpa [Phi] using this

/-! ## The tight threshold's algebraic home -/

/-- The Buss–Williams characteristic polynomial; its root in `(1,2)` is `2cos(π/7)`. -/
def bwPoly (x : ℝ) : ℝ := x ^ 3 - x ^ 2 - 2 * x + 1

/-- **The tight trading threshold** `2cos(π/7)` is the root of `bwPoly` in `(1.8, 1.81)` — strictly below the
universal potential cap `2`, localizing exactly where the uniform dual weights are loose. -/
theorem trading_threshold_root :
    ∃ x : ℝ, x ∈ Set.Ioo (1.8 : ℝ) 1.81 ∧ bwPoly x = 0 ∧ x < 2 := by
  have hcont : ContinuousOn bwPoly (Set.Icc (1.8 : ℝ) 1.81) := by
    unfold bwPoly; fun_prop
  have h1 : bwPoly 1.8 < 0 := by unfold bwPoly; norm_num
  have h2 : (0 : ℝ) < bwPoly 1.81 := by unfold bwPoly; norm_num
  have hsub := intermediate_value_Ioo (by norm_num : (1.8 : ℝ) ≤ 1.81) hcont
  obtain ⟨x, hx, hfx⟩ := hsub ⟨h1, h2⟩
  exact ⟨x, hx, hfx, by have := hx.2; linarith⟩

end PallLean.Paper93.DeepMath.PathB.TradingOptimality

#print axioms PallLean.Paper93.DeepMath.PathB.TradingOptimality.trading_optimality_two
#print axioms PallLean.Paper93.DeepMath.PathB.TradingOptimality.trading_threshold_root
