import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRSAssembly
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoostingFinal
import Mathlib

/-!
# Hardness instantiation skeleton (PROVED shape + mechanism; deep core fenced)

`ACC0.Circuit.no_acp_circuit` turns a *hardness* fact about a function `f` into a circuit lower bound.  This file
makes the instantiation concrete and **honest**: it proves the separation *shape* and the boosting *mechanism*, and
fences — precisely, as documented gaps, not as silent sockets — what genuinely remains to reach `MOD_q ∉ AC⁰[p]`.

  `no_computing_circuit` — **the separation shape (PROVED).**  Repackages `no_acp_circuit`: if `f` is hard (no
        degree-`d` Walsh polynomial agrees with `f` on more than `B` points), then *no* well-formed AC⁰[p] circuit
        of degree `≤ d` with `size·2^(n-t) + B < 2ⁿ` computes `f`.

  `hard_of_walshFn_univ` — **the boosting mechanism is real (PROVED).**  `boosting_surjection` directly supplies a
        hardness predicate for the full parity `walshFn univ`, with bound `B = 2ⁿ − 1`.  So the hardness side of
        `no_acp_circuit` is genuinely inhabited, not hypothetical.

## The three gaps to a non-vacuous `MOD_q ∉ AC⁰[p]` (honestly fenced)

`hard_of_walshFn_univ` + `no_computing_circuit` do **not** yet give a real separation.  Three concrete gaps remain,
each a genuine piece of mathematics, none of them faked here:

1. **Range / affine bridge — CLOSED.**  `cf p C` is `{0,1}`-valued; `walshFn univ` is `{−1,+1}`-valued, so
   `cf p C = walshFn univ` is *unsatisfiable* (instantiating with `f = walshFn univ` is vacuous).  This is now
   resolved by `hard_of_affine`: any `{0,1}` function `f` with `walshFn univ = 1 − 2·f` inherits the parity
   hardness at the *same* degree and bound (a degree-`d` approximator of `f` becomes one of `walshFn univ` via
   `aCoef ↦ δ_∅ − 2·aCoef`).  What remains to a *concrete* `{0,1}` target is the arithmetic identity
   `walshFn univ x = 1 − 2·(0/1 parity)` — a packaging detail, not a barrier.

2. **Sharp dimension bound — CLOSED.**  `hard_of_walshFn_univ` exposes only `B = 2ⁿ − 1` (because
   `boosting_surjection`'s stated conclusion is `< 2ⁿ`), which makes `no_computing_circuit`'s
   `size·2^(n-t) + B < 2ⁿ` force `size·2^(n-t) < 1`, impossible.  This is now resolved:
   `WalshSpan.boosting_surjection_sharp` (via `RazborovSmolensky.dimension_argument_sharp`) keeps the exact bound
   `|G| ≤ Σ_{i ≤ n/2+d} C(n,i)`, and `hard_of_walshFn_univ_sharp` is the corresponding hardness predicate — a
   genuinely non-vacuous `B` (`< 2ⁿ` when `n/2+d < n`).

3. **The `MOD_q` reduction (the barriered core).**  Boosting handles `walshFn univ` (the full product = parity).
   `MOD_q` (`q ≠ 2`) is *not* the full product; reducing its non-approximability to parity's is the genuine,
   `MOD_q`-specific Razborov–Smolensky lower bound — the part subject to natural-proofs/algebrization barriers.
   It is **not** attempted here.

So this file is a skeleton: a compiled separation shape and a real hardness mechanism, with the deep core (3) and
the two quantitative bridges (1), (2) named as the precise remaining obligations.
-/

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.WalshSpan

namespace PallLean.Paper93.DeepMath.PathB.ACC0.Circuit

variable {n : ℕ}

/-- **The separation shape (PROVED).**  If `f` is hard (no degree-`d` Walsh polynomial agrees with `f` on more than
`B` points), then no well-formed AC⁰[p] circuit of degree `≤ d` and bad-set budget `size·2^(n-t) + B < 2ⁿ` computes
`f`.  A direct repackaging of `no_acp_circuit` as a non-existence statement. -/
theorem no_computing_circuit {p t : ℕ} [Fact p.Prime] (ht : 1 ≤ t) (htn : t ≤ n) (h2 : (2 : ZMod p) ≠ 0)
    (d B : ℕ) (f : (Fin n → Bool) → ZMod p)
    (hard : ∀ (aCoef : Finset (Fin n) → ZMod p) (G : Finset (Fin n → Bool)),
              (∀ T, d < T.card → aCoef T = 0) → (∀ x ∈ G, f x = evalW aCoef x) → G.card ≤ B) :
    ¬ ∃ C : Circuit n,
      WF p C ∧ (t * (p - 1)) ^ depth C ≤ d ∧ size C * 2 ^ (n - t) + B < 2 ^ n ∧ (∀ x, cf p C x = f x) := by
  rintro ⟨C, hC, hdeg, hsmall, hCf⟩
  exact no_acp_circuit ht htn h2 d B f hard C hC hdeg hCf hsmall

/-- **The boosting mechanism is real (PROVED).**  `boosting_surjection` directly yields a hardness predicate for the
full parity `walshFn univ`: any degree-`d` Walsh polynomial agreeing with `walshFn univ` on `G` (with `n/2+d < n`)
has `|G| ≤ 2ⁿ − 1`.  This inhabits the `hard` hypothesis of `no_computing_circuit` — the mechanism is not
hypothetical.  (The bound `2ⁿ − 1` is the *weak* one; see gap 2.) -/
theorem hard_of_walshFn_univ {p : ℕ} [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (d : ℕ) (hmn : n / 2 + d < n) :
    ∀ (aCoef : Finset (Fin n) → ZMod p) (G : Finset (Fin n → Bool)),
      (∀ T, d < T.card → aCoef T = 0) →
      (∀ x ∈ G, walshFn Finset.univ x = evalW aCoef x) → G.card ≤ 2 ^ n - 1 := by
  intro aCoef G hsupp hagree
  have h := boosting_surjection h2 aCoef hsupp G (fun b hb => (hagree b hb).symm) hmn
  omega

/-- **Sharp hardness for parity — gap (2) CLOSED.**  `boosting_surjection_sharp` gives the exact dimension bound:
any degree-`d` Walsh polynomial agreeing with `walshFn univ` on `G` has `|G| ≤ Σ_{i ≤ n/2+d} C(n,i)`.  This is the
non-vacuous bound (`< 2ⁿ` when `n/2+d < n`), so plugged into `no_computing_circuit` with
`B = Σ_{i ≤ n/2+d} C(n,i)` the budget `size·2^(n-t) + B < 2ⁿ` is genuinely satisfiable.  Gaps (1) range/affine and
(3) the `MOD_q` reduction remain. -/
theorem hard_of_walshFn_univ_sharp {p : ℕ} [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (d : ℕ) :
    ∀ (aCoef : Finset (Fin n) → ZMod p) (G : Finset (Fin n → Bool)),
      (∀ T, d < T.card → aCoef T = 0) →
      (∀ x ∈ G, walshFn Finset.univ x = evalW aCoef x) →
      G.card ≤ ∑ i ∈ Finset.range (n / 2 + d + 1), n.choose i := by
  intro aCoef G hsupp hagree
  exact boosting_surjection_sharp h2 aCoef hsupp G (fun b hb => (hagree b hb).symm)

/-- **The affine `0/1 ↔ ±1` bridge — gap (1) CLOSED.**  If a `{−1,+1}` function `h` is hard and a `{0,1}` function
`f` is its affine image `h = 1 − 2·f`, then `f` is hard with the *same* degree `d` and bound `B`.  A degree-`d`
Walsh approximator `aCoef` of `f` on `G` is turned into a degree-`d` approximator `δ_∅ − 2·aCoef` of `h` (the
constant `1 = walshFn ∅` adds only the degree-`0` term `∅`), so `h`'s hardness applies.  This is what lets the
`{−1,+1}` parity lower bound (`hard_of_walshFn_univ_sharp`) be transported to a genuine `{0,1}`-valued target — the
range mismatch in `no_computing_circuit`'s `cf p C = f`. -/
theorem hard_of_affine {p : ℕ} [Fact p.Prime] (h f : (Fin n → Bool) → ZMod p)
    (haff : ∀ x, h x = 1 - 2 * f x) (d B : ℕ)
    (hh : ∀ (aCoef : Finset (Fin n) → ZMod p) (G : Finset (Fin n → Bool)),
            (∀ T, d < T.card → aCoef T = 0) → (∀ x ∈ G, h x = evalW aCoef x) → G.card ≤ B) :
    ∀ (aCoef : Finset (Fin n) → ZMod p) (G : Finset (Fin n → Bool)),
      (∀ T, d < T.card → aCoef T = 0) → (∀ x ∈ G, f x = evalW aCoef x) → G.card ≤ B := by
  intro aCoef G hsupp hagree
  refine hh (fun T => (if T = ∅ then 1 else 0) - 2 * aCoef T) G ?_ ?_
  · intro T hT
    have hT0 : T ≠ ∅ := fun h0 => by rw [h0] at hT; simp at hT
    show (if T = ∅ then (1 : ZMod p) else 0) - 2 * aCoef T = 0
    rw [if_neg hT0, hsupp T hT]; ring
  · intro x hx
    have key : evalW (fun T => (if T = ∅ then (1 : ZMod p) else 0) - 2 * aCoef T) x
             = 1 - 2 * evalW aCoef x := by
      simp only [evalW, sub_mul, Finset.sum_sub_distrib]
      congr 1
      · simp [ite_mul, Finset.sum_ite_eq', walshFn]
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun S _ => by ring)
    rw [haff x, hagree x hx, key]

end PallLean.Paper93.DeepMath.PathB.ACC0.Circuit

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.no_computing_circuit
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.hard_of_walshFn_univ
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.hard_of_walshFn_univ_sharp
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.hard_of_affine
