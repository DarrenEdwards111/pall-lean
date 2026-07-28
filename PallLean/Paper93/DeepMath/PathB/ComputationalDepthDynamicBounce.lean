import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCircuitLBGrowth

/-!
# Dynamic SPDP + the per-step string bounce: the incompressibility compounds — but the bounce count is the wall

Dynamic SPDP (the `DynamicRestriction` shrinkage engine) is a rank measure evolving through a *restriction
sequence*.  Darren's "string bounce for each step": under each restriction the string bounces back carrying
*retained incompressibility* — a per-step hardness factor.  The honest question is whether those per-step
bounces compound into a lower bound.  This file proves they do, and locates exactly where it stops.

**The compounding is real (proved).**  If each restriction step retains a factor `s` of the measure —
`s · Hᵢ ≤ Hᵢ₊₁`, the incompressible bounce — then after `k` steps the measure is at least `s^k · H₀`
(`compounds_geometrically`, by induction).  Per-step incompressibility *multiplies*; that is the dynamic-SPDP
amplification, and it is exactly the geometric compounding of the string bounce.

**Sustained bounces give a superpolynomial bound (proved).**  If the bounce holds at rate `2` at *every* step
(`2 · Hᵢ ≤ Hᵢ₊₁`) from a nonzero base, then `2^n ≤ Hₙ`, so the measure is **not polynomially bounded**
(`sustained_bounce_superpoly`, via the `two_pow_not_polyBounded` growth fact).  A string that bounces
incompressibly at every step is, provably, superpolynomially hard.

**Where it caps — the honest wall.**  The lower bound is `2^k` where `k` is the number of *sustained*
incompressible bounces.  For **formulas** this is the shrinkage engine: Håstad's exponent gives a per-step
rate, but the variable budget exhausts the bounce after `k = O(log n)` steps, so `2^k = n^{O(1)}` — the
polynomial `n^{5/2}`/`n³` Andreev ceiling, real and already in the corpus.  Superpolynomial needs `k = ω(log
n)` sustained bounces, and sustaining an incompressible bounce at *every* step for a SAT-specific *general*
circuit target is precisely the open per-step shrinkage rate at general depth — `cost_super`.

## What is proved

* **`compounds_geometrically`** — per-step retention `s` compounds: `s^k · H₀ ≤ Hₖ`.
* **`dominates_not_polyBounded`** — anything dominating `2^n` is not polynomially bounded.
* **`sustained_bounce_superpoly`** — a rate-`2` bounce sustained at every step forces a superpolynomial
  (non-poly-bounded) measure.

## Honest verdict — the mechanism works; the number of bounces is the wall

The dynamic-SPDP / string-bounce idea is *correct as a mechanism*: per-step incompressibility genuinely
compounds geometrically (`compounds_geometrically`), and a sustained bounce genuinely yields a superpolynomial
bound (`sustained_bounce_superpoly`) — both machine-checked.  It is even *instantiated and working* for
formulas, where the shrinkage exponent is known but the bounce exhausts at `O(log n)` steps, giving the real
polynomial Andreev ceiling.  What it does not cross is the number of sustained bounces: superpolynomial needs
the incompressible bounce to hold at *every* step for a general-circuit SAT target, and proving that is the
open per-step shrinkage rate at general depth — `cost_super`, in dynamic-SPDP/string-bounce language.  The
compounding is real; sustaining the bounce is the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DynamicBounce

open PallLean.Paper93.DeepMath.PathB.CircuitLBGrowth

/-! ### The per-step bounce compounds geometrically -/

/-- **The bounce compounds (proved).**  If each restriction step retains a factor `s` of the measure
(`s · Hᵢ ≤ Hᵢ₊₁` — the incompressible string bounce), then after `k` steps the measure is at least
`s^k · H₀`.  Per-step incompressibility multiplies: the dynamic-SPDP amplification. -/
theorem compounds_geometrically (H : ℕ → ℕ) (s : ℕ) (hstep : ∀ i, s * H i ≤ H (i + 1)) (k : ℕ) :
    s ^ k * H 0 ≤ H k := by
  induction k with
  | zero => simp
  | succ n ih =>
    calc s ^ (n + 1) * H 0 = s * (s ^ n * H 0) := by rw [pow_succ]; ring
      _ ≤ s * H n := Nat.mul_le_mul (Nat.le_refl s) ih
      _ ≤ H (n + 1) := hstep n

/-! ### Sustained bounces ⟹ superpolynomial -/

/-- **Domination gives non-poly-boundedness (proved).**  If a measure dominates `2^n` everywhere, it is not
polynomially bounded — otherwise `2^n` would be, contradicting `two_pow_not_polyBounded`. -/
theorem dominates_not_polyBounded (H : ℕ → ℕ) (hdom : ∀ n, 2 ^ n ≤ H n) :
    ¬ PolyBounded H := by
  intro hpoly
  obtain ⟨c, d, hcd⟩ := hpoly
  exact two_pow_not_polyBounded ⟨c, d, fun n => le_trans (hdom n) (hcd n)⟩

/-- **A sustained incompressible bounce forces superpolynomial hardness (proved).**  If the string bounces at
rate `2` at every step (`2 · Hᵢ ≤ Hᵢ₊₁`) from a nonzero base, then `2^n ≤ Hₙ` for all `n`, so the measure is
not polynomially bounded.  Incompressibility at every step ⟹ superpolynomial. -/
theorem sustained_bounce_superpoly (H : ℕ → ℕ) (hstep : ∀ i, 2 * H i ≤ H (i + 1)) (h0 : 1 ≤ H 0) :
    ¬ PolyBounded H := by
  apply dominates_not_polyBounded
  intro n
  calc 2 ^ n = 2 ^ n * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ n * H 0 := Nat.mul_le_mul (Nat.le_refl _) h0
    _ ≤ H n := compounds_geometrically H 2 hstep n

end PallLean.Paper93.DeepMath.PathB.DynamicBounce

#print axioms PallLean.Paper93.DeepMath.PathB.DynamicBounce.compounds_geometrically
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicBounce.dominates_not_polyBounded
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicBounce.sustained_bounce_superpoly
