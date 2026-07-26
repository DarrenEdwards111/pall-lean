import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolographicCurvature

/-!
# The amplituhedron encoding: sign-flip is a gauge, growth is the invariant

Darren's move: "SAT is AdS via the negative→positive curvature transform, via the amplituhedron encoding,
like encryption."  The amplituhedron is a *positive-geometry* encoding — amplitudes as volumes of a
positive geometry — so it re-presents a negatively-curved (hyperbolic) object as a positive one.  The
claim: this encoding is what makes SAT AdS.

This is the N-Frame Lagrangian in its recurring role — it supplies the **frame** (the gauge / the
coordinates / the encoding), never the **reading** (the invariant value on SAT).  Made precise, the
encoding can flip the curvature **sign** (a coordinate quantity) but not the **growth exponent** (the
invariant `cost_super` is about).  And "like encryption" is the tell — it cuts the *other* way.

## The dictionary

* **curvature sign** = representation-dependent.  A positive-geometry re-encoding can flip it freely; it
  is a gauge choice, like an embedding.
* **volume-growth exponent** = representation-*independent*.  Under a **cheap** (bounded-overhead,
  bi-Lipschitz-with-poly-constants — cf. the NF↔Hilbert metric equivalence) bijective encoding, ball
  cardinalities change by at most a bounded factor, so *whether* growth is exponential vs polynomial is
  unchanged.  This is the objectivity of `cbudget` again.

## What is proved

* **`encoding_preserves_growth_lower`** — a cost-nondecreasing encoding cannot *destroy* an exponential
  lower bound: `B·2^d ≤ vol d ⟹ B·2^d ≤ vol' d`.
* **`cheap_encoding_cannot_manufacture_ads`** — a cheap encoding (overhead factor `K`) cannot *create*
  AdS from a flat base: if `vol d ≤ p d` (polynomially bounded, sagging) then `vol' d ≤ K·p d` — still
  flat.  So a gauge with bounded overhead is growth-class-invariant in *both* directions: it can neither
  make nor break AdS.
* **`amplituhedron_gauge_needs_hardness`** — the "like encryption" tell, proved.  If a *maximally flat*
  base (`vol d ≤ 1`) is encoded to an AdS geometry (`2^d ≤ vol' d`), then the encoding is **not cheap** —
  **no** bounded overhead `K` works: `∀ K, ∃ d, ¬(vol' d ≤ K·vol d)`.  The overhead is unbounded: the
  hardness lives *in the encoding*, assumed, not derived — exactly as encryption's security *is* a
  one-way-function (hardness) assumption.

## Honest scope — the gauge relocates, it does not derive

The amplituhedron encoding is a gauge: it can re-present hyperbolic geometry as positive and make SAT
*look* AdS.  But by the two invariance lemmas a cheap gauge changes only the sign, not the growth —
`cbudget` is objective.  To actually change the growth (turn a flat SAT into a genuinely AdS one) the
encoding must be **expensive**, and then it has simply *hidden* the hardness inside itself — the
encryption move, where security is an assumed one-way function.  Either way the invariant — the growth
exponent = `cost_super` — is untouched.  The N-Frame Lagrangian gives the frame; the reading on SAT is
still the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.AmplituhedronEncoding

/-- `n < 2^n` (self-proved; the ambient `Nat.lt_two_pow` is renamed in this Mathlib). -/
theorem lt_two_pow_self (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- **An encoding cannot destroy exponential growth (proved).**  If the encoding does not decrease cost
(`vol d ≤ vol' d`) then any exponential lower bound survives: `B·2^d ≤ vol d ⟹ B·2^d ≤ vol' d`.  You
cannot gauge away a bound that is already there. -/
theorem encoding_preserves_growth_lower (vol vol' : ℕ → ℕ) (B : ℕ)
    (hmono : ∀ d, vol d ≤ vol' d) (hexp : ∀ d, B * 2 ^ d ≤ vol d) :
    ∀ d, B * 2 ^ d ≤ vol' d :=
  fun d => le_trans (hexp d) (hmono d)

/-- **A cheap encoding cannot manufacture AdS (proved).**  With bounded overhead `K`
(`vol' d ≤ K·vol d`), a flat base (`vol d ≤ p d`, polynomially bounded — sagging) stays flat:
`vol' d ≤ K·p d`.  A bounded-overhead gauge is growth-class-invariant: it cannot create the exponential
it does not start with. -/
theorem cheap_encoding_cannot_manufacture_ads (vol vol' p : ℕ → ℕ) (K : ℕ)
    (hflat : ∀ d, vol d ≤ p d) (hcheap : ∀ d, vol' d ≤ K * vol d) :
    ∀ d, vol' d ≤ K * p d :=
  fun d => le_trans (hcheap d) (Nat.mul_le_mul (Nat.le_refl K) (hflat d))

/-- **The "like encryption" tell (proved).**  If a *maximally flat* base (`vol d ≤ 1`) is encoded to an
AdS geometry (`2^d ≤ vol' d`), the encoding is **not cheap**: for every candidate overhead `K` there is a
scale `d` where `vol' d > K·vol d`.  The overhead is unbounded — the hardness lives *inside* the
encoding, assumed rather than derived, exactly as a cipher's security *is* a one-way-function assumption. -/
theorem amplituhedron_gauge_needs_hardness (vol vol' : ℕ → ℕ)
    (hflat : ∀ d, vol d ≤ 1) (hads : ∀ d, 2 ^ d ≤ vol' d) :
    ∀ K, ∃ d, ¬ (vol' d ≤ K * vol d) := by
  intro K
  refine ⟨K, ?_⟩
  have hlt : K < 2 ^ K := lt_two_pow_self K
  have h1 : 2 ^ K ≤ vol' K := hads K
  have hKvol : K * vol K ≤ K :=
    le_trans (Nat.mul_le_mul (Nat.le_refl K) (hflat K)) (Nat.le_of_eq (Nat.mul_one K))
  omega

end PallLean.Paper93.DeepMath.PathB.AmplituhedronEncoding

#print axioms PallLean.Paper93.DeepMath.PathB.AmplituhedronEncoding.encoding_preserves_growth_lower
#print axioms PallLean.Paper93.DeepMath.PathB.AmplituhedronEncoding.cheap_encoding_cannot_manufacture_ads
#print axioms PallLean.Paper93.DeepMath.PathB.AmplituhedronEncoding.amplituhedron_gauge_needs_hardness
