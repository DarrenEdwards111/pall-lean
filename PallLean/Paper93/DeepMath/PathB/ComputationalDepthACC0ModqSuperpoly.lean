import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModqExp

/-!
# Bridge (super-polynomial) — `MOD_q ∉` polynomial-size `AC⁰[p]` (proved)

The cleanest statement of the Razborov–Smolensky lower bound: `MOD_q` is **not polynomially bounded** in `AC⁰[p]`.  Using the
explicit blow-up `modq_size_blowup` (size reaches `p^t` by an arity `≤ G(t)` polynomial in `t`) together with
exponential-beats-polynomial (`exp_beats_poly`), we conclude: for *every* exponent `c`, some arity `N` has subcircuit-list
length exceeding `N^c` — i.e. the size grows faster than any polynomial in the number of inputs.

## What is proved (clean axioms, no `sorry`)

* **`exp_beats_poly`** (PROVED) — for `p ≥ 2` and any `a, B`, there is `t ≥ 1` with `a·t^B < p^t` (exponential beats
  polynomial, via `tendsto_pow_const_mul_const_pow_of_abs_lt_one`).
* **`modq_superpoly`** (PROVED) — for any uniform `AC⁰[p]` family computing `MOD_q` at constant depth, and every `c`, some
  arity `N` has `N^c < 4q·(subcircuits (toBoolSyntax (D N))).length`.

## Honest scope

This is the super-polynomial size lower bound — `MOD_q ∉` polynomial-size constant-depth `AC⁰[p]`, the definitive form of the
polynomial-method separation.  The **Williams cash-out** (`NEXP ⊄ ACC⁰`) is a different, P≠NP-strength theorem and remains
**open** / not faked.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0Superpoly

open Finset Filter Topology
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (ModpOnly)
open PallLean.Paper93.DeepMath.PathB.ACC0ToBoolSyntax (toBoolSyntax)
open PallLean.Paper93.DeepMath.PathB.Layer3 (subcircuits)
open PallLean.Paper93.DeepMath.PathB.ACC0ModqExp (modq_size_blowup)

/-- **Exponential beats polynomial (PROVED).**  For `p ≥ 2`, every `a·t^B` is eventually below `p^t`. -/
theorem exp_beats_poly (a B p : ℕ) (hp : 2 ≤ p) : ∃ t : ℕ, 1 ≤ t ∧ a * t ^ B < p ^ t := by
  have h1p : (1 : ℕ) < p := by omega
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast h1p
  have hr : |(1 / (p : ℝ))| < 1 := by
    rw [abs_of_nonneg (by positivity), div_lt_one (by linarith)]; linarith
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one B hr
  have hev : ∀ᶠ t : ℕ in Filter.atTop, (t : ℝ) ^ B * (1 / (p : ℝ)) ^ t < 1 / ((a : ℝ) + 1) :=
    ht.eventually_lt_const (by positivity)
  obtain ⟨t, htlt, ht1⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
  refine ⟨t, ht1, ?_⟩
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpt : (0 : ℝ) < (p : ℝ) ^ t := by positivity
  have key : ((a : ℝ) + 1) * ((t : ℝ) ^ B * (1 / (p : ℝ)) ^ t) < 1 := by
    have h := mul_lt_mul_of_pos_left htlt (show (0 : ℝ) < (a : ℝ) + 1 by positivity)
    rwa [mul_one_div_cancel (by positivity : (a : ℝ) + 1 ≠ 0)] at h
  have hreal : (a : ℝ) * (t : ℝ) ^ B < (p : ℝ) ^ t := by
    have h2 := mul_lt_mul_of_pos_right key hpt
    rw [one_mul] at h2
    have heq : ((a : ℝ) + 1) * ((t : ℝ) ^ B * (1 / (p : ℝ)) ^ t) * (p : ℝ) ^ t
        = ((a : ℝ) + 1) * (t : ℝ) ^ B := by
      rw [one_div, inv_pow, mul_assoc, mul_assoc ((t : ℝ) ^ B),
        inv_mul_cancel₀ (pow_ne_zero t (ne_of_gt hp0)), mul_one]
    rw [heq] at h2
    nlinarith [pow_nonneg (Nat.cast_nonneg t : (0 : ℝ) ≤ t) B]
  exact_mod_cast hreal

/-- **`MOD_q ∉` polynomial-size `AC⁰[p]` (PROVED).**  For any uniform `AC⁰[p]` family computing `MOD_q` at depth `d` and every
exponent `c`, some arity `N` has `N^c < 4q·(subcircuits (toBoolSyntax (D N))).length` — the size beats every polynomial. -/
theorem modq_superpoly (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p)
    {d : ℕ} (D : (N : ℕ) → ACC0Circuit N)
    (hDind : ∀ N, ∀ y : Fin N → Bool,
      ACC0CircuitModel.eval (D N) y = decide ((Finset.univ.filter (fun i => y i = true)).card % q = 0))
    (hDmod : ∀ N, ModpOnly p (D N))
    (hDdepth : ∀ N, BoolCircuitSyntax.depth (toBoolSyntax (D N)) ≤ d)
    (c : ℕ) :
    ∃ N, N ^ c < 4 * q * (subcircuits (toBoolSyntax (D N))).length := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨t, ht1, hexp⟩ :=
    exp_beats_poly ((16 * (p - 1) ^ (2 * d) + 1 + q) ^ c) (2 * d * c) p hp2
  have hpt1 : 1 ≤ (p - 1) * t := Nat.mul_pos (by omega) ht1
  obtain ⟨N, hNle, hN⟩ := modq_size_blowup p q hpq D hDind hDmod hDdepth t ht1 hpt1
  refine ⟨N, ?_⟩
  have ht2d : 1 ≤ t ^ (2 * d) := Nat.one_le_pow _ _ (by omega)
  have hGK : 16 * (((p - 1) * t) ^ d) ^ 2 + 1 + q
      ≤ (16 * (p - 1) ^ (2 * d) + 1 + q) * t ^ (2 * d) := by
    have hexpand : (((p - 1) * t) ^ d) ^ 2 = (p - 1) ^ (2 * d) * t ^ (2 * d) := by
      rw [← pow_mul, Nat.mul_comm d 2, mul_pow]
    have h1q : 1 + q ≤ (1 + q) * t ^ (2 * d) := Nat.le_mul_of_pos_right (1 + q) (by omega)
    rw [hexpand, add_mul, add_mul]
    nlinarith [h1q, ht2d, Nat.zero_le ((p - 1) ^ (2 * d) * t ^ (2 * d))]
  calc N ^ c
      ≤ (16 * (((p - 1) * t) ^ d) ^ 2 + 1 + q) ^ c := Nat.pow_le_pow_left hNle c
    _ ≤ ((16 * (p - 1) ^ (2 * d) + 1 + q) * t ^ (2 * d)) ^ c := Nat.pow_le_pow_left hGK c
    _ = (16 * (p - 1) ^ (2 * d) + 1 + q) ^ c * t ^ (2 * d * c) := by rw [mul_pow, ← pow_mul]
    _ < p ^ t := hexp
    _ < 4 * q * (subcircuits (toBoolSyntax (D N))).length := hN

/-!
**`MOD_q ∉` polynomial-size `AC⁰[p]`, proved.**  The polynomial-method separation in its definitive super-polynomial form.
Remaining (open, not faked): the Williams cash-out to `NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0Superpoly

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Superpoly.exp_beats_poly
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Superpoly.modq_superpoly
