import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaIterate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaDegree

/-!
# Toda iterate, glued: the polylog-degree exact-mod-`p^{2^k}` indicator (PROVED)

The capstone of the Toda integer-route ladder.  `ACC0TodaIterate` gave the modulus side
(`p^{2^k} ∣ A^{[k]}(value) − b` on `ℤ`) and `ACC0TodaDegree` gave the degree side
(`totalDegree (A^{[k]} q) ≤ 3^k · deg q`).  This file links them through the evaluation homomorphism and
combines them into one statement.

  `todaAmpIterP_eval` — `eval x (A^{[k]} q) = A^{[k]}(eval x q)` (the polynomial iterate evaluates to the
  value iterate; `eval` is a ring hom and `A` is a polynomial).
  `todaIterate_indicator` — **the indicator**: from a degree-`d` polynomial `q` whose values are
  `≡ b(x) (mod p)` with `b(x) ∈ {0,1}`, the iterate `A^{[k]} q` is a polynomial of degree `≤ 3^k · d`
  whose values are `≡ b(x) (mod p^{2^k})` for **every** `x`.

Applied to a single `MOD_p` gate (start `q = ∑ xᵢ`-style degree-1 mod-`p` indicator, `d = 1`), this is a
degree-`3^k` polynomial computing the gate's `{0,1}` value mod `p^{2^k}`.  Choosing `2^k` past the count
range (`p^{2^k} > fan-in`) makes it the **exact** integer `{0,1}` indicator; for `k ≈ log log` the degree
`3^k` is **polylog** — the integer route's exact low-degree representation of an *unbounded-fan-in* `MOD`
gate.

## What is proved (clean axioms, no `sorry`)

* `todaAmpP_eval`, `todaAmpIterP_eval` — the polynomial iterate evaluates to the `ℤ`-value iterate.
* `todaIterate_indicator` — degree `≤ 3^k·d` ∧ values `≡ b (mod p^{2^k})`, for a mod-`p` start `q`.

## Honest scope

This is the exact-mod-`p^{2^k}` indicator at degree `3^k·d`, for any start polynomial `q` that is a
mod-`p` `{0,1}` representation.  The remaining wall: supplying the start `q` as the actual bottom-`AND`
count of a depth-`d` ACC⁰ circuit and assembling the per-gate indicators into one exact quasipoly
`SYM∘AND` across depth (with `p^{2^k}` chosen against the global count).  That assembly is the
Beigel–Tarui integer construction body, not built here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TodaIndicator

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0TodaAmplify (todaAmp)
open PallLean.Paper93.DeepMath.PathB.ACC0TodaIterate (todaAmpIter todaAmpIter_amplifies)
open PallLean.Paper93.DeepMath.PathB.ACC0TodaDegree (todaAmpP todaAmpIterP todaAmpIterP_totalDegree_le)

variable {σ : Type*}

/-- **One polynomial step evaluates to the `ℤ`-value step (proved).** -/
theorem todaAmpP_eval (x : σ → ℤ) (q : MvPolynomial σ ℤ) :
    eval x (todaAmpP q) = todaAmp (eval x q) := by
  simp only [todaAmpP, todaAmp, map_sub, map_mul, map_pow, map_ofNat]

/-- **The `k`-fold polynomial iterate evaluates to the `k`-fold `ℤ`-value iterate (proved).** -/
theorem todaAmpIterP_eval (x : σ → ℤ) (k : ℕ) (q : MvPolynomial σ ℤ) :
    eval x (todaAmpIterP k q) = todaAmpIter k (eval x q) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [todaAmpIterP, todaAmpP_eval, ih, todaAmpIter]

/-- **The Toda indicator (proved).**  If `q` is a degree-`d` polynomial whose values represent a `{0,1}`
function `b` mod `p` (`p ∣ eval x q − b x`, `b x ∈ {0,1}`), then `A^{[k]} q` has total degree `≤ 3^k·d`
and its values represent `b` mod `p^{2^k}` for every `x`.  Degree `3^k` (polylog for `k ≈ log log`),
modulus `p^{2^k}` (exact once it passes the count range). -/
theorem todaIterate_indicator (q : MvPolynomial σ ℤ) (p : ℤ) (k : ℕ)
    (b : (σ → ℤ) → ℤ) (hb : ∀ x, b x = 0 ∨ b x = 1)
    (hq : ∀ x, p ∣ (eval x q - b x)) :
    (todaAmpIterP k q).totalDegree ≤ 3 ^ k * q.totalDegree
      ∧ ∀ x, p ^ (2 ^ k) ∣ (eval x (todaAmpIterP k q) - b x) := by
  refine ⟨todaAmpIterP_totalDegree_le k q, fun x => ?_⟩
  rw [todaAmpIterP_eval]
  exact todaAmpIter_amplifies (hb x) (hq x) k

/-!
**Toda indicator proved.**  `A^{[k]} q` is a degree-`≤ 3^k·d` polynomial whose values are `≡ b (mod
p^{2^k})` — the polylog-degree exact-mod-`p^{2^k}` `{0,1}` indicator of the integer route.  Supplying `q`
as a real bottom-`AND` count and assembling across depth (the exact quasipoly `SYM∘AND` for unbounded
fan-in) is the remaining wall.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0TodaIndicator

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TodaIndicator.todaIterate_indicator
