import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer7CircuitFamily
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Smolensky
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Assembly
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Layer 7 (open frontier) — PARITY is not in nonuniform `AC⁰[p]` (circuit-family level)

The honest **Route-B / level-2** corollary of `SCOPE_LAYER7_COMPLEXITY_CLASS_BRIDGE.md`: lifting the
per-length single-circuit `parity_function_lower_bound` (Layer 3) to a **circuit-family language**
statement.

* `exists_poly_lt_pow` — the one genuinely-arithmetic ingredient: **exponential beats polynomial**, i.e.
  for `p ≥ 2` and any `A, C, B`, some `t ≥ 1` has `A·t^C + B < p^t` (via Mathlib's
  `isLittleO_pow_const_const_pow_of_one_lt`).
* `parity_not_in_nonuniform_AC0p` — **no constant-depth, polynomially-size-bounded `AC⁰[p]` circuit
  family computes the PARITY language.**  Proof: instantiate `parity_function_lower_bound` at length
  `2m+1` with `m = 8·((p-1)t)^{2d}`, giving `p^t < 4·#subcircuits ≤ 4·sizeBound(2m+1)`; the right side is
  polynomial in `t` while `p^t` is exponential, so `exists_poly_lt_pow` supplies a `t` that breaks it.

## Honest framing (must travel with this theorem)

This is a **nonuniform circuit-family** lower bound for an **explicit, easy (P-computable)** language.
It is **NOT** `P ≠ NP`, **NOT** `NP ⊄ AC⁰[p]` in any deep sense, and **NOT** a statement about hard `NP`
functions (PARITY ∈ P ⊆ NP, so any "language in NP outside `AC⁰[p]`" reading is Razborov–Smolensky
repackaged, and the uniform-`NP` framing additionally needs the off-limits TM `NP` of `Step4Compiler` plus
encoding/uniformity bridges — see the scope docs). What is genuinely new here vs. Layer 3 is only the
*family/asymptotic packaging*, not any new separation.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer7

open PallLean.Paper93.DeepMath.PathB Asymptotics Filter

/-- **Exponential beats polynomial.**  For `p ≥ 2` and any `A, C, B`, there is `t ≥ 1` with
`A·t^C + B < p^t`.  (From `isLittleO_pow_const_const_pow_of_one_lt`: `(A+B)·t^C = o(p^t)`, so eventually
`(A+B)·t^C ≤ ½·p^t`, and `A·t^C + B ≤ (A+B)·t^C` for `t ≥ 1`.) -/
theorem exists_poly_lt_pow (p : ℕ) (hp : 2 ≤ p) (A C B : ℕ) :
    ∃ t : ℕ, 1 ≤ t ∧ A * t ^ C + B < p ^ t := by
  have hr : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlo : (fun n : ℕ => ((A + B : ℕ) : ℝ) * (n : ℝ) ^ C) =o[atTop] (fun n : ℕ => (p : ℝ) ^ n) :=
    (isLittleO_pow_const_const_pow_of_one_lt C hr).const_mul_left _
  have hev : ∀ᶠ n : ℕ in atTop,
      ((A + B : ℕ) : ℝ) * (n : ℝ) ^ C ≤ (1 / 2) * (p : ℝ) ^ n := by
    have h := (isLittleO_iff.mp hlo) (show (0 : ℝ) < 1 / 2 by norm_num)
    refine h.mono (fun n hn => ?_)
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)] at hn
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N + 1, Nat.le_add_left 1 N, ?_⟩
  have hb := hN (N + 1) (Nat.le_succ N)
  have hcastpos : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 N
  have hpow1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ C := one_le_pow₀ hcastpos
  have hppos : (0 : ℝ) < (p : ℝ) ^ (N + 1) := by positivity
  have hBle : (B : ℝ) ≤ (B : ℝ) * ((N + 1 : ℕ) : ℝ) ^ C := le_mul_of_one_le_right (by positivity) hpow1
  have hstep1 : (A : ℝ) * ((N + 1 : ℕ) : ℝ) ^ C + (B : ℝ)
      ≤ ((A + B : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) ^ C := by
    have hd : ((A + B : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) ^ C
        = (A : ℝ) * ((N + 1 : ℕ) : ℝ) ^ C + (B : ℝ) * ((N + 1 : ℕ) : ℝ) ^ C := by push_cast; ring
    rw [hd]; linarith [hBle]
  have hreal : ((A * (N + 1) ^ C + B : ℕ) : ℝ) < ((p ^ (N + 1) : ℕ) : ℝ) := by
    push_cast at hb hstep1 hppos ⊢; linarith
  exact_mod_cast hreal

open Classical in
/-- **PARITY is not in nonuniform `AC⁰[p]`.**  No constant-depth, polynomially-size-bounded `AC⁰[p]`
circuit family computes the PARITY language.  (Honest level-2 corollary — *not* `P ≠ NP`, *not* a
hard-`NP`-function separation; see the module docstring.) -/
theorem parity_not_in_nonuniform_AC0p (p : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (F : AC0pFamily p) (hpoly : IsPolyBounded F.sizeBound) :
    ¬ F.Computes parityLang := by
  intro hComp
  obtain ⟨a, c, b, hsz⟩ := hpoly
  set d := F.depthBound with hd_def
  set q := p - 1 with hq_def
  obtain ⟨t, ht1, htlt⟩ := exists_poly_lt_pow p (Fact.out (p := p.Prime)).two_le
      (4 * a * (16 * q ^ (d * 2) + 1) ^ c) (d * 2 * c) (4 * b)
  set m := 8 * ((q * t) ^ d) ^ 2 with hm_def
  set n := 2 * m + 1 with hn_def
  -- Per-length Razborov–Smolensky bound at length `n = 2m+1`.
  have hLB : p ^ t < 4 * (Layer3.subcircuits (F.circ n)).toFinset.card :=
    Layer3.parity_function_lower_bound p hp2 (F.circ n) (F.hdepth n) t ht1
      (fun x => by rw [hComp n x]; rfl)
      (fun a' r cs h => Layer4.hmod_of_isAC0p (F.circ n) (F.isAC0p n) a' r cs h)
      (by rw [hm_def])
  -- The family size at length `n` is polynomial in `t`: `n ≤ (16·q^{2d}+1)·t^{2d}`.
  have hn_le : n ≤ (16 * q ^ (d * 2) + 1) * t ^ (d * 2) := by
    have e1 : n = 16 * ((q * t) ^ d) ^ 2 + 1 := by rw [hn_def, hm_def]; ring
    have e2 : ((q * t) ^ d) ^ 2 = q ^ (d * 2) * t ^ (d * 2) := by rw [← pow_mul, mul_pow]
    have hone : 1 ≤ t ^ (d * 2) := Nat.one_le_pow _ _ (by omega)
    rw [e1, e2]; nlinarith [hone, Nat.zero_le (q ^ (d * 2))]
  have hnc : n ^ c ≤ (16 * q ^ (d * 2) + 1) ^ c * t ^ (d * 2 * c) := by
    calc n ^ c ≤ ((16 * q ^ (d * 2) + 1) * t ^ (d * 2)) ^ c := Nat.pow_le_pow_left hn_le c
      _ = (16 * q ^ (d * 2) + 1) ^ c * (t ^ (d * 2)) ^ c := mul_pow _ _ _
      _ = (16 * q ^ (d * 2) + 1) ^ c * t ^ (d * 2 * c) := by rw [← pow_mul]
  have hchain : 4 * (Layer3.subcircuits (F.circ n)).toFinset.card
      ≤ (4 * a * (16 * q ^ (d * 2) + 1) ^ c) * t ^ (d * 2 * c) + 4 * b := by
    have h1 : (Layer3.subcircuits (F.circ n)).toFinset.card ≤ a * n ^ c + b :=
      le_trans (F.hsize n) (hsz n)
    have h2 : a * n ^ c ≤ a * ((16 * q ^ (d * 2) + 1) ^ c * t ^ (d * 2 * c)) :=
      Nat.mul_le_mul_left a hnc
    nlinarith [h1, h2]
  omega

end PallLean.Paper93.DeepMath.PathB.Layer7

#print axioms PallLean.Paper93.DeepMath.PathB.Layer7.exists_poly_lt_pow
#print axioms PallLean.Paper93.DeepMath.PathB.Layer7.parity_not_in_nonuniform_AC0p
