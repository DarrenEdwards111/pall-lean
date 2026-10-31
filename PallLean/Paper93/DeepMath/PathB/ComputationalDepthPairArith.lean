import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATVerifierSpec

/-!
# The pair-assembly arithmetic spec

The evaluator must compute, from a literal's coordinate blocks `(t, p, tag)`, the flat
variable value `v = 3·pair(t,p) + tag` that `decodeVar'` recovers — then look up the
witness bit at `v`.  This file pins that value's arithmetic as the **verified target** the
machine arms must produce, before the tape-surgery integration:

* `pairVal t p tag = 3·Nat.pair t p + tag`, matching `decodeVar'` exactly
  (`decodeVar'_pairVal`);
* `pair_branch` — `Nat.pair` is the branch `if t<p then p²+t else t²+t+p`, so the two
  assembly arms have the concrete targets `pairVal_lt` (`3·(p²+t)+tag`) and `pairVal_ge`
  (`3·(t²+t+p)+tag`);
* the op-chain decomposition each arm realizes — square, add, triple (`×3 = mul 3`), add
  tag — as ℕ identities (`pairVal_lt_ops` / `pairVal_ge_ops`);
* `pairVal_le` — `pairVal ≤ 3·(t+p+1)² + tag`, the clock bound for the arm machines.

The machine arms (built next) consume `t, p, tag` blocks and emit `1^(pairVal …)`; their
run lemmas are verified against these identities.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PairArith

open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec (encodeVar' decodeVar'
  decodeVar'_encodeVar' encodeVar'_coords)
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-- The flat variable value a coordinate-encoded literal decodes to. -/
def pairVal (t p tag : ℕ) : ℕ := 3 * Nat.pair t p + tag

/-- **The branch identity**: `Nat.pair` selects `p²+t` or `t²+t+p`. -/
theorem pair_branch (t p : ℕ) :
    Nat.pair t p = if t < p then p * p + t else t * t + t + p := by
  unfold Nat.pair
  split <;> ring

/-- The `t < p` arm's target. -/
theorem pairVal_lt (t p tag : ℕ) (h : t < p) :
    pairVal t p tag = 3 * (p * p + t) + tag := by
  unfold pairVal
  rw [pair_branch, if_pos h]

/-- The `¬ t < p` arm's target. -/
theorem pairVal_ge (t p tag : ℕ) (h : ¬ t < p) :
    pairVal t p tag = 3 * (t * t + t + p) + tag := by
  unfold pairVal
  rw [pair_branch, if_neg h]

/-- The `t < p` arm's op chain: square `p`, add `t`, triple, add `tag`. -/
theorem pairVal_lt_ops (t p tag : ℕ) (h : t < p) :
    pairVal t p tag = (p * p + t) + (p * p + t) + (p * p + t) + tag := by
  rw [pairVal_lt t p tag h]; ring

/-- The `¬ t < p` arm's op chain. -/
theorem pairVal_ge_ops (t p tag : ℕ) (h : ¬ t < p) :
    pairVal t p tag = (t * t + t + p) + (t * t + t + p) + (t * t + t + p) + tag := by
  rw [pairVal_ge t p tag h]; ring

/-- **`decodeVar'` recovers `pairVal`**: the coordinate blocks for `(t, p, tag)` decode to
`pairVal t p tag` — the machine arm's output `1^(pairVal …)` indexes the
witness exactly as `satVerify` reads it. -/
theorem decodeVar'_pairVal (t p tag : ℕ) (rest : List Bool) :
    decodeVar' (encodeVar' (3 * Nat.pair t p + tag) ++ rest) = (pairVal t p tag, rest) := by
  rw [decodeVar'_encodeVar']
  rfl

/-- `pairVal` is polynomially bounded in `t + p + tag`: `Nat.pair t p ≤ (t+p+1)²`. -/
theorem pairVal_le (t p tag : ℕ) :
    pairVal t p tag ≤ 3 * ((t + p + 1) * (t + p + 1)) + tag := by
  unfold pairVal
  have hpair : Nat.pair t p ≤ (t + p + 1) * (t + p + 1) := by
    rw [pair_branch]
    split
    · next h => nlinarith
    · next h => nlinarith
  omega

end PallLean.Paper93.DeepMath.PathB.PairArith
