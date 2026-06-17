import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ThresholdBTClosure

/-!
# The fan-in depth recurrence — `FanInStaysPolylog` reduced to one per-layer merge

Entry 167 split the Beigel–Tarui closure into two proved size-factors (linear `SYM` top, quasipoly bounded-fan-in
feature layer) held together by the socket `FanInStaysPolylog` — that the bottom AND fan-in stays polylog under `ACC⁰`
depth composition.  This file does the **depth induction** (the user's "induct over circuit depth" step): it proves
that *if* each `ACC⁰` layer multiplies the fan-in by at most a factor `≤ L`, *then* after `d ≤ D` layers from a base
fan-in `≤ b` the fan-in is `≤ L^D · b` — which is polylog for constant depth `D` and polylog `L, b`.  This reduces
`FanInStaysPolylog` to the **single per-layer merge lemma** (the genuine Beigel–Tarui mixed-radix content), and chains it
to the quasipoly feature-count bound of entry 167.

## What is proved (clean axioms, no `sorry`)

* **`fanInAtDepth`** + **`fanInAtDepth_succ`** — the fan-in recurrence `fanInAtDepth b factor (d+1) = factor ·
  fanInAtDepth b factor d` (each layer multiplies by `factor`).
* **`fanin_bounded_by_recurrence`** — the depth induction: if `layerFanIn 0 ≤ b` and each layer satisfies
  `layerFanIn (d+1) ≤ factor · layerFanIn d` (the per-layer merge), then `layerFanIn d ≤ fanInAtDepth b factor d`.
* **`fanInAtDepth_le`** — for constant depth: `factor ≤ L`, `d ≤ D`, `1 ≤ L` ⇒ `fanInAtDepth b factor d ≤ L^D · b`
  (polylog when `L, b` polylog and `D` constant).
* **`quasipoly_feature_count_of_layer_merge`** — the chain to entry 167: the per-layer merge + constant depth ⇒ the
  bottom AND-feature count is `≤ (n+1)^{L^D·b}` (quasipoly).

## Honest scope

The depth induction and the constant-depth arithmetic are proved: *given* the per-layer merge bound, the fan-in stays
polylog and the feature count stays quasipoly.  The one remaining ingredient is the **per-layer merge** itself
(`layerFanIn (d+1) ≤ factor · layerFanIn d`, supplied as a hypothesis here) — that composing the `SYM∘AND` forms of a
gate's children into the gate's own `SYM∘AND` form multiplies the bottom fan-in by only a polylog factor.  That is the
genuine Beigel–Tarui mixed-radix merge — a *theorem*, not an open problem (`NEXP ⊄ ACC⁰`, Williams 2011, and the BT
representation are proven classically), but its full Lean proof over a concrete `ACC⁰` gate datatype is the substantial
remaining formalisation.  We reduce `FanInStaysPolylog` to exactly that one lemma; we do **not** prove it, and nothing
here is a new separation or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0FanInRecurrence

open PallLean.Paper93.DeepMath.PathB

/-- The AND fan-in after `d` composition layers from base fan-in `b`, each layer multiplying by `factor`. -/
def fanInAtDepth (b factor d : ℕ) : ℕ := factor ^ d * b

@[simp] theorem fanInAtDepth_zero (b factor : ℕ) : fanInAtDepth b factor 0 = b := by
  simp [fanInAtDepth]

/-- **The fan-in recurrence (proved): each layer multiplies the fan-in by `factor`.** -/
theorem fanInAtDepth_succ (b factor d : ℕ) :
    fanInAtDepth b factor (d + 1) = factor * fanInAtDepth b factor d := by
  simp only [fanInAtDepth, pow_succ]; ring

/-- **The depth induction (proved): per-layer merge ⇒ fan-in bounded by the recurrence.**  If the bottom fan-in starts
`≤ b` and each `ACC⁰` layer multiplies it by at most `factor` (`hstep`, the per-layer merge), then after `d` layers the
fan-in is `≤ fanInAtDepth b factor d = factor^d · b`.  This is the "induct over circuit depth" step: the per-layer
bound iterates to a depth bound. -/
theorem fanin_bounded_by_recurrence (b factor : ℕ) (layerFanIn : ℕ → ℕ)
    (h0 : layerFanIn 0 ≤ b) (hstep : ∀ d, layerFanIn (d + 1) ≤ factor * layerFanIn d) :
    ∀ d, layerFanIn d ≤ fanInAtDepth b factor d := by
  intro d
  induction d with
  | zero => simpa using h0
  | succ d ih =>
    rw [fanInAtDepth_succ]
    exact le_trans (hstep d) (Nat.mul_le_mul_left factor ih)

/-- **Constant depth keeps the fan-in polylog (proved): `factor ≤ L`, `d ≤ D` ⇒ `fanInAtDepth b factor d ≤ L^D · b`.**
For a polylog per-layer factor `L`, constant depth `D`, and polylog base `b`, the bound `L^D · b` is polylog — this is
*why* the Beigel–Tarui bottom fan-in stays polylog (constant depth is essential). -/
theorem fanInAtDepth_le (b factor d L D : ℕ) (hL : 1 ≤ L) (hf : factor ≤ L) (hd : d ≤ D) :
    fanInAtDepth b factor d ≤ L ^ D * b := by
  refine Nat.mul_le_mul_right b ?_
  exact le_trans (Nat.pow_le_pow_left hf d) (Nat.pow_le_pow_right hL hd)

/-- **The chain to entry 167 (proved): per-layer merge + constant depth ⇒ quasipoly AND-feature count.**  Combining the
depth induction with the constant-depth bound, the actual bottom fan-in `layerFanIn d` is `≤ L^D · b`; feeding that into
`…ACC0ThresholdBTClosure.quasipoly_BT_observer_of_fanin_preservation`, the bottom AND-feature count is `≤ (n+1)^{L^D·b}`
— quasipolynomial when `L, b` are polylog and `D` is constant.  The only socketed premise is `hstep` (the per-layer
Beigel–Tarui merge). -/
theorem quasipoly_feature_count_of_layer_merge
    (n b factor L D d : ℕ) (layerFanIn : ℕ → ℕ)
    (hL : 1 ≤ L) (hf : factor ≤ L) (hd : d ≤ D)
    (h0 : layerFanIn 0 ≤ b)
    (hstep : ∀ k, layerFanIn (k + 1) ≤ factor * layerFanIn k) :
    (Layer3.lowDegMonomials n (layerFanIn d)).card ≤ (n + 1) ^ (L ^ D * b) := by
  have hw : layerFanIn d ≤ L ^ D * b :=
    le_trans (fanin_bounded_by_recurrence b factor layerFanIn h0 hstep d)
      (fanInAtDepth_le b factor d L D hL hf hd)
  exact ACC0ThresholdBTClosure.quasipoly_BT_observer_of_fanin_preservation n (L ^ D * b)
    (layerFanIn d) hw

end PallLean.Paper93.DeepMath.PathB.ACC0FanInRecurrence

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FanInRecurrence.fanInAtDepth_succ
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FanInRecurrence.fanin_bounded_by_recurrence
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FanInRecurrence.fanInAtDepth_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FanInRecurrence.quasipoly_feature_count_of_layer_merge
