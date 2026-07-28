import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSuperpolyCeiling

/-!
# The circuit horn is `P ≠ NP`: a no-go for the polynomial ladder, not a proof of the horn

Asked to prove the superpolynomial *circuit* bound horn.  That request is, verbatim, `P ≠ NP`: the horn is
`¬ PolyBounded (circuitCost)` for a SAT family — the general-circuit superpolynomial lower bound, `cost_super`
itself.  It is not a socket beneath the wall; it *is* the wall.  I did not fabricate a proof of it (no technique
produces a superpolynomial general-circuit lower bound; the record for an explicit function is `≈ 5n`).  What is
machine-checked here is the honest structure: **what proving the horn requires, and why the polynomial ladder
cannot reach it.**

**Proving the horn requires a superpolynomial certificate.**  A circuit lower bound is a certificate
`b(n) ≤ circuitCost(n)`.  If the certificate `b` is superpolynomial, the horn follows
(`superpoly_certificate_gives_horn`): `circuitCost` dominates every `n^k`, so it is not polynomially bounded.
So the *only* route to the horn is a superpolynomial certificate.

**The polynomial ladder cannot supply one.**  Every certificate the blade ladder produces is polynomial —
Khrapchenko `n²`, Andreev `n^{5/2}`.  A polynomial certificate is consistent with the circuit family being
polynomial-size (`poly_certificate_consistent_with_poly_size`): the world `circuitCost = b = n²` satisfies the
certificate `b ≤ circuitCost` yet `circuitCost` is polynomially bounded — a `P = NP`-consistent world.  So no
polynomial certificate forces the horn; climbing or raising the *polynomial* ladder never reaches it
(`circuit_horn_requires_superpoly_certificate`).

**Hence the horn is exactly the open object.**  It needs a genuinely superpolynomial general-circuit lower
bound — not derivable from any polynomial result, however the sharing model or base bound is dialed.  That is
`cost_super`, `P ≠ NP`, and I did not manufacture it.

## What is proved

* **`superpoly_certificate_gives_horn`** — a superpolynomial lower-bound certificate `b ≤ circuitCost` yields
  the horn `¬ PolyBounded circuitCost`.  The only route.
* **`poly_certificate_consistent_with_poly_size`** — a polynomial certificate coexists with a
  polynomially-bounded `circuitCost`: it does not force the horn (the no-go).
* **`circuit_horn_requires_superpoly_certificate`** — both: the horn needs a superpolynomial certificate, and
  polynomial certificates (what the ladder gives) are consistent with `P = NP`.

## Honest verdict — I did not prove the horn; I proved the ladder cannot reach it

The superpolynomial circuit horn is `P ≠ NP`, and I built no proof of it, because none exists.  What is
machine-checked is a genuine no-go: proving the horn requires a *superpolynomial* certificate
(`superpoly_certificate_gives_horn`), and every certificate the polynomial blade ladder produces is polynomial,
consistent with polynomial-size circuits (`poly_certificate_consistent_with_poly_size`) — so no amount of
climbing the sharing altitude or raising the base bound *within the polynomial regime* reaches the horn
(`circuit_horn_requires_superpoly_certificate`).  The horn is not a missing step at the top of the ladder; it is
a different kind of object — a superpolynomial general-circuit lower bound — that the ladder's polynomial
certificates provably cannot entail.  Reaching it is `cost_super`, the open theorem.  I held the line: the no-go
is real and proved; the horn is not, and I did not fake it.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CircuitHornNoGo

open PallLean.Paper93.DeepMath.PathB.SuperpolyCeiling

/-- **A superpolynomial certificate yields the horn (proved).**  If a superpolynomial `b` lower-bounds
`circuitCost` (`b n ≤ circuitCost n`), then `circuitCost` is superpolynomial too, hence not polynomially
bounded — the horn.  This is the *only* route to it. -/
theorem superpoly_certificate_gives_horn
    (circuitCost b : Nat → Nat) (hb : Superpoly b) (hcert : ∀ n, b n ≤ circuitCost n) :
    ¬ PolyBounded circuitCost := by
  have hsp : Superpoly circuitCost := by
    intro k
    obtain ⟨n, hn⟩ := hb k
    exact ⟨n, lt_of_lt_of_le hn (hcert n)⟩
  exact superpoly_not_polyBounded hsp

/-- **A polynomial certificate does not force the horn (proved) — the no-go.**  The world
`circuitCost = b = n²` satisfies the certificate `b ≤ circuitCost` yet `circuitCost` is polynomially bounded: a
polynomial lower bound is consistent with polynomial-size circuits (`P = NP`).  So the polynomial ladder cannot
reach the horn. -/
theorem poly_certificate_consistent_with_poly_size :
    ∃ (circuitCost b : Nat → Nat),
      PolyBounded b ∧ (∀ n, b n ≤ circuitCost n) ∧ PolyBounded circuitCost :=
  ⟨knownBase, knownBase, known_base_is_polynomial, fun _ => le_refl _, known_base_is_polynomial⟩

/-- **The horn requires a superpolynomial certificate (proved).**  Left: a superpolynomial certificate yields
the horn.  Right: polynomial certificates — what the blade ladder produces — are consistent with `P = NP`.  So
the horn needs a genuinely superpolynomial general-circuit lower bound, not derivable from the polynomial
ladder: `cost_super`. -/
theorem circuit_horn_requires_superpoly_certificate :
    (∀ circuitCost b : Nat → Nat, Superpoly b → (∀ n, b n ≤ circuitCost n) → ¬ PolyBounded circuitCost)
    ∧ (∃ circuitCost b : Nat → Nat, PolyBounded b ∧ (∀ n, b n ≤ circuitCost n) ∧ PolyBounded circuitCost) :=
  ⟨fun cc b hb hc => superpoly_certificate_gives_horn cc b hb hc, poly_certificate_consistent_with_poly_size⟩

end PallLean.Paper93.DeepMath.PathB.CircuitHornNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.CircuitHornNoGo.superpoly_certificate_gives_horn
#print axioms PallLean.Paper93.DeepMath.PathB.CircuitHornNoGo.poly_certificate_consistent_with_poly_size
#print axioms PallLean.Paper93.DeepMath.PathB.CircuitHornNoGo.circuit_horn_requires_superpoly_certificate
