import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PolynomialMethodApproximation

/-!
# The quantitative depth bound — the clean per-layer step (roadmap (A))

Roadmap step (A): make the depth bound *quantitative*.  The committed `or_step`/`and_step` give the per-layer
degree growth `D ↦ t·D` and the error split `E ↦ k·E + Eg`, but they leave the gate-boosting error `Eg` in the
awkward form `(2^k)^t · Eg ≤ 2ⁿ · (2^{k-1})^t`.  This file extracts the **clean** per-gate bound `2^t · Eg ≤ 2ⁿ`
(error `≤ 2^{-t}` of the inputs) and repackages the per-layer step with it — the quantitative ingredient the depth
induction consumes.  Built *on top of* the committed circuit arc (`or_step`/`and_step`), not modifying it.

**The extraction.**  `(2^k)^t · Eg ≤ 2ⁿ · (2^{k-1})^t` ⟺ (cancelling `2^{(k-1)t}`) `2^t · Eg ≤ 2ⁿ`.  So each
`OR`/`AND` gate's boosting error is at most a `2^{-t}` fraction of the input space — independent of the fan-in `k`.

**The per-layer step (clean).**  An `OR` (resp. `AND`) of `k` approximants of degree `≤ D`, error `≤ E`, yields an
approximant of degree `≤ t·D` and error `≤ k·E + Eg` with `2^t · Eg ≤ 2ⁿ`.  Iterating over a depth-`d` circuit gives
degree `≤ t^d · D₀` and error `≤ size · 2ⁿ · 2^{-t}` (the structural iteration is the committed depth induction).

## What is proved (clean axioms, no `sorry`)

* **`gate_error_le`** (PROVED) — the clean extraction: `(card (Finset (Fin k)))^t · Eg ≤ N · (2^{k-1})^t` (with
  `1 ≤ k`) ⇒ `2^t · Eg ≤ N`.  Turns the awkward `or_step` gate bound into the clean `2^{-t}` fraction.
* **`card_input`** (PROVED) — `Fintype.card (Fin n → Bool) = 2^n`.
* **`or_layer_quant`** / **`and_layer_quant`** (PROVED) — the clean per-layer quantitative step: `or_step`/`and_step`
  repackaged with the clean gate error `2^t · Eg ≤ 2ⁿ`.
* **`pow_depth_degree`** (PROVED) — the closed-form degree recurrence: `t·` applied `d` times to `D₀` is `t^d · D₀`,
  so a depth-`d` circuit's approximant has degree `≤ t^d · D₀`.

## Honest scope

This assembles the *clean quantitative per-layer step* — the gate error is now a transparent `2^{-t}` fraction
(`gate_error_le`), and the layer step (`or_layer_quant`/`and_layer_quant`) and degree recurrence (`pow_depth_degree`)
are proved.  The remaining piece of `QuantitativeDepthBound` is the *structural iteration* over the committed `Circ`
datatype (apply the layer step at each gate, accumulate degree `t^d` and error `size·2ⁿ·2^{-t}`) — this lives in the
committed circuit arc (the quantitative refinement of `approximable_exists`) and is left to it.  This is **not**
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0QuantitativeDepthBound

open PallLean.Paper93.DeepMath.PathB.ACC0OrStep (perr or_step and_step andTarget)
open PallLean.Paper93.DeepMath.PathB.ACC0SmallErrorForm (orTarget)

/-- **The clean per-gate error extraction (PROVED).**  From the `or_step`/`and_step` gate bound
`(card (Finset (Fin k)))^t · Eg ≤ N · (2^{k-1})^t` (with `1 ≤ k`), cancelling the common factor `2^{(k-1)t}` gives
the clean `2^t · Eg ≤ N`: the gate boosting error is a `2^{-t}` fraction, independent of fan-in. -/
theorem gate_error_le {k t Eg N : ℕ} (hk : 1 ≤ k)
    (hgate : (Fintype.card (Finset (Fin k))) ^ t * Eg ≤ N * (2 ^ (k - 1)) ^ t) :
    2 ^ t * Eg ≤ N := by
  rw [Fintype.card_finset, Fintype.card_fin, ← pow_mul, ← pow_mul] at hgate
  have hle : t ≤ k * t := le_mul_of_one_le_left (Nat.zero_le t) hk
  have hsplit : k * t = (k - 1) * t + t := by rw [Nat.sub_one_mul]; omega
  rw [hsplit, pow_add] at hgate
  have key : 2 ^ ((k - 1) * t) * (2 ^ t * Eg) ≤ 2 ^ ((k - 1) * t) * N := by
    calc 2 ^ ((k - 1) * t) * (2 ^ t * Eg)
        = 2 ^ ((k - 1) * t) * 2 ^ t * Eg := by ring
      _ ≤ N * 2 ^ ((k - 1) * t) := hgate
      _ = 2 ^ ((k - 1) * t) * N := by ring
  exact Nat.le_of_mul_le_mul_left key (pow_pos (by norm_num) _)

/-- **The input space has `2^n` elements (PROVED).** -/
theorem card_input (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **The clean per-layer `OR` step (PROVED).**  An `OR` of `k ≥ 1` approximants of degree `≤ D`, error `≤ E` yields an
approximant of degree `≤ t·D` and error `≤ k·E + Eg`, where the gate error is the clean `2^t · Eg ≤ 2ⁿ`. -/
theorem or_layer_quant {n k t : ℕ} (hk : 1 ≤ k) (h : Fin k → (Fin n → Bool) → Bool)
    (P : Fin k → MvPolynomial (Fin n) (ZMod 2)) (D E : ℕ)
    (hdeg : ∀ i, (P i).totalDegree ≤ D) (herr : ∀ i, (perr (P i) (h i)).card ≤ E) :
    ∃ (Q : MvPolynomial (Fin n) (ZMod 2)) (Eg : ℕ),
      Q.totalDegree ≤ t * D
        ∧ (perr Q (fun x => orTarget (fun i => h i x))).card ≤ k * E + Eg
        ∧ 2 ^ t * Eg ≤ 2 ^ n := by
  obtain ⟨Q, Eg, hd, he, hg⟩ := or_step (t := t) h P D E hdeg herr
  refine ⟨Q, Eg, hd, he, ?_⟩
  rw [← card_input n]
  exact gate_error_le hk hg

/-- **The clean per-layer `AND` step (PROVED).**  Same as `or_layer_quant` for `AND`. -/
theorem and_layer_quant {n k t : ℕ} (hk : 1 ≤ k) (h : Fin k → (Fin n → Bool) → Bool)
    (P : Fin k → MvPolynomial (Fin n) (ZMod 2)) (D E : ℕ)
    (hdeg : ∀ i, (P i).totalDegree ≤ D) (herr : ∀ i, (perr (P i) (h i)).card ≤ E) :
    ∃ (Q : MvPolynomial (Fin n) (ZMod 2)) (Eg : ℕ),
      Q.totalDegree ≤ t * D
        ∧ (perr Q (fun x => andTarget (fun i => h i x))).card ≤ k * E + Eg
        ∧ 2 ^ t * Eg ≤ 2 ^ n := by
  obtain ⟨Q, Eg, hd, he, hg⟩ := and_step (t := t) h P D E hdeg herr
  refine ⟨Q, Eg, hd, he, ?_⟩
  rw [← card_input n]
  exact gate_error_le hk hg

/-- **The closed-form degree recurrence (PROVED).**  Applying the per-layer degree growth `D ↦ t·D` exactly `d` times
to a base degree `D₀` gives `t^d · D₀`.  So a depth-`d` circuit's polynomial-method approximant has total degree
`≤ t^d · D₀` (the degree half of `QuantitativeDepthBound`, in closed form). -/
theorem pow_depth_degree (t D₀ : ℕ) : ∀ d : ℕ, (fun D => t * D)^[d] D₀ = t ^ d * D₀
  | 0 => by simp
  | d + 1 => by
      rw [Function.iterate_succ_apply', pow_depth_degree t D₀ d, pow_succ]
      ring

/-!
**The rung.**  The quantitative per-layer step is assembled cleanly: the gate boosting error is now the transparent
`2^t · Eg ≤ 2ⁿ` (`gate_error_le`) — a `2^{-t}` fraction, fan-in-independent — and the `OR`/`AND` layer steps
(`or_layer_quant`/`and_layer_quant`) carry it, while the degree closed form `t^d · D₀` is proved (`pow_depth_degree`).
What remains of `QuantitativeDepthBound` is the structural iteration over the committed `Circ` datatype (apply the layer
step gate-by-gate, accumulating degree `t^d` and error `size · 2ⁿ · 2^{-t}`) — the quantitative refinement of the
committed `approximable_exists`, left to the circuit arc.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0QuantitativeDepthBound

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0QuantitativeDepthBound.gate_error_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0QuantitativeDepthBound.or_layer_quant
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0QuantitativeDepthBound.and_layer_quant
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0QuantitativeDepthBound.pow_depth_degree
