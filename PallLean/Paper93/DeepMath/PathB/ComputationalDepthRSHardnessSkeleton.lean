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

1. **Range / affine bridge.**  `cf p C` is `{0,1}`-valued; `walshFn univ` is `{−1,+1}`-valued.  So `cf p C =
   walshFn univ` is *unsatisfiable* — instantiating `no_computing_circuit` with `f = walshFn univ` is vacuous.  A
   real target must be a `{0,1}` function (e.g. the `0/1` `MOD_q` indicator), with an affine `0/1 ↔ ±1` bridge
   relating its Walsh-approximability to that of `walshFn univ`.

2. **Sharp dimension bound.**  `hard_of_walshFn_univ` exposes only `B = 2ⁿ − 1` (because `boosting_surjection`'s
   stated conclusion is `< 2ⁿ`).  But `no_computing_circuit`'s `size·2^(n-t) + B < 2ⁿ` then forces
   `size·2^(n-t) < 1`, impossible.  A non-vacuous separation needs the *sharp* `B = Σ_{i ≤ n/2+d} C(n,i)` (the
   coefficient-space size — `card_le_of_surjective` already gives it, but `dimension_argument`/`boosting_surjection`
   discard it for `< 2ⁿ`).  Re-proving boosting with the sharp bound is the quantitative work.

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

end PallLean.Paper93.DeepMath.PathB.ACC0.Circuit

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.no_computing_circuit
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.hard_of_walshFn_univ
