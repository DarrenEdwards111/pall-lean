# The ACC⁰ frontier for the observer-boundary method

This note isolates **exactly what the observer-boundary ("God Move") method would have to supply to attack
`NP ⊄ ACC⁰`** — the open rung just below `P` vs `NP`.  It does *not* claim the separation.  Its concrete
output is the conditional schema proved in `ComputationalDepthObserverACC0Frontier.lean`.

**Status of the landscape (for calibration, all literature-known unless marked):**
* `NP ⊄ AC⁰[p]` — **known** (Razborov–Smolensky); rederived through the observer invariant in
  `ComputationalDepthObserverAC0pCalibration.lean` (§9 of `SCOPE_OBSERVER_BOUNDARY_ENTROPY.md`).
* `NEXP ⊄ ACC⁰` — **known** (Williams), via algorithmic / non-natural-proof machinery.
* `NP ⊄ ACC⁰` — **OPEN.**  Not a calibration we can knock off; a serious frontier rung.

---

## 1. Recap: why the AC⁰[p] observer calibration works

The AC⁰[p] calibration is the **dimension** instance of the invariant (boundary = feature-space dimension):

* An `AC⁰[p]` circuit's behavior, on a large agreement set `G`, lies in the span of **low-degree polynomials
  over a single field `F_p`** — its feature space, of dimension `≤ #monomials = poly(n)`.  So boundary
  `= finrank(feature) ≤ poly(n)`: ACC⁰[p] is a *low-boundary* observer.
* A hard function (`MOD_q`, `q ≠ p`) forces the feature behaviors on `G` to span the **full** function space
  (`Layer4.sqfSpan_eq_top`), dimension `|G|` — *non-mergeable* behaviors.
* `|G| ≤ #monomials` is impossible in the band-margin window (`Layer4.dim_bound_general`).  Done.

The decisive structural fact: **one field, one low-degree boundary** captures *every* `AC⁰[p]` circuit, and a
`MOD_q` for a *single different* modulus escapes it.

## 2. What ACC⁰ adds — and why §1 breaks

`ACC⁰ = AC⁰` **with `MOD_m` gates for arbitrary (possibly several, composite) moduli `m`**.  The single-field
argument breaks at every step:

* **No single field is faithful.**  `MOD_2` is degree-1 over `F_2` but has *no* low-degree representation
  over `F_3`, and vice-versa.  An ACC⁰ circuit may freely mix `MOD_2` and `MOD_3` gates; no single `F_p`
  low-degree span contains its behavior, so "boundary = dimension over one field" no longer upper-bounds it.
* **Composite moduli have no field at all.**  `MOD_6` lives over `Z/6`, which is not a field; the
  Razborov–Smolensky polynomial/field machinery has no direct analogue (this is the classical reason ACC⁰
  resists the polynomial method).
* **Mixed-modulus cancellation.**  CRT lets an ACC⁰ circuit simulate behavior that is high-degree in every
  *individual* modular component while being cheap overall — exactly the escape route a single-field
  observer cannot see.  This is why Williams needed algorithmic (`#SAT`-algorithm ⇒ lower bound) machinery,
  not a natural-proofs/low-degree boundary, to reach even `NEXP ⊄ ACC⁰`.

So the AC⁰[p] calibration's "low-degree feature boundary over one field" is **not** a valid bridge for ACC⁰:
ACC⁰ circuits are *not* low-boundary in the single-field model.

## 3. The enriched modular-boundary conjecture

To recover a bridge, the observer boundary must be **enriched** to span all the moduli an ACC⁰ circuit can
use.  A candidate (the modelling target — *not yet defined precisely in Lean*):

> **Enriched modular observer boundary** `B_enr(C)` := the dimension of the feature space spanned by
> low-degree polynomials over the **product / CRT structure `∏_m Z/m`** of all moduli `m` appearing in the
> circuit (or over a suitable family of fields covering them), restricted to the agreement set.

Two questions, both open, are the content of any ACC⁰ separation by this method:

* **(Bridge) Low enriched boundary for ACC⁰.**  Does *every* ACC⁰ circuit of size `s` and depth `d` have
  `B_enr ≤ poly(n)` (or `quasipoly`)?  Plausibly yes for bounded depth — but the CRT mixing makes the
  dimension count subtle, and a *clean* bound is not known.
* **(Hardness) High enriched boundary for some NP language.**  Is there an NP language `L` whose behaviors
  force `B_enr ≥ super-poly` under *every* faithful observer?  This is the hard half — and, as
  `equality_decomposition_gap` shows, it must hold under *all* admissible decompositions, not one.

## 4. The conditional schema (proved) and honest status

`ComputationalDepthObserverACC0Frontier.lean` proves the **exact implication** these two questions feed:

```
acc0_separation_of_boundary / not_acc0_of_boundary :
  (g monotone) →
  (∀ ACC⁰ circuit C, boundary C ≤ g (size C))      -- (Bridge) ACC⁰ ⇒ low enriched boundary
  (∀ circuit computing L, lb ≤ boundary C)          -- (Hardness) L forces high enriched boundary
  (g sizeBound < lb)                                 -- the gap
  ⊢ no ACC⁰ circuit of size ≤ sizeBound computes L   -- i.e. NP ⊄ ACC⁰
```

This is the observer schema (`ObserverSchema.observer_resource_lower_bound`, §9–11) specialised to ACC⁰.  The
implication is a one-line `lb ≤ boundary ≤ g(size) ≤ g(sizeBound) < lb`.  The **two hypotheses are the open
mathematics** — stated as explicit Lean hypotheses (the demotion pattern: no custom axiom, nothing faked).

**Honest status.**
* `NP ⊄ ACC⁰` is **open**.  Nothing here proves it.
* The God Move gives a **possible route, not a theorem**: supply the enriched-modular boundary model (§3),
  prove the bridge for ACC⁰, and find a hard NP language for it.  Each is genuine open research.
* The value of this rung: the conditional theorem says *precisely* what must be supplied, and the §2 analysis
  says *precisely* why the AC⁰[p] argument does not transfer — so no effort is wasted re-running the
  single-field method where it provably cannot work.

The concrete next research action is **(3): define the enriched-modular boundary and test the bridge half on
small ACC⁰ circuits** — not to claim the separation.

---

## 5. Bridge test, done — verdict: exact enrichment fails, approximation is mandatory

`ComputationalDepthEnrichedModularBoundary.lean` defines the enriched boundary the note proposed
(`enrichedBoundary M prof = ∑_{m ∈ M} prof m`) and tests the bridge half.  Proved (clean axioms, no `sorry`):

* `enrichedBoundary_mono`, `enrichedBoundary_add` — monotone; additive when profiles add (the shape of AND/OR
  composition, since exact `deg(f·g) ≤ deg f + deg g`).
* `enrichedBoundary_le_card_mul` — **the bridge, conditional**: if every component is low (`prof m ≤ b`),
  enriched boundary `≤ |M|·b`.  The enrichment *does* compose across moduli with dimensions summing.
* `enrichedBoundary_ge_component` / `enrichedBoundary_two_moduli_obstruction` — **the obstruction**: the sum
  is `≥` any single component, so one high component makes the whole boundary high.

**Verdict (honest, and not the hoped-for clean answer).**  The *exact* enriched boundary does **not** model
ACC⁰ as low-boundary:

* A single `MOD_p` gate is degree `≤ p−1` over `F_p` but **full degree** over `F_q` (`q ≠ p`); by
  `enrichedBoundary_ge_component` the `∑` inherits that high term — so `MOD_p` has *high* exact enriched
  boundary.  The naive sum does not make mixed-modulus gates low.
* `AND` of `n` inputs has exact degree `n` over every field, so `enrichedBoundary_add` drives it to `≈ |M|·n`.

This is the same wall RS hit for one field — *exact* low-degree boundary fails under composition — and RS
fixed it with **approximate (probabilistic) polynomials**.  So the enrichment (the `∑` over `M`) is the right
fix for the *moduli*, but the per-modulus boundary must be the **approximate** degree, not the exact one.
A low *approximate* enriched bridge for ACC⁰ over mixed moduli is the open frontier — and it is exactly the
`boundary` to plug into `ObserverACC0.acc0_separation_of_boundary`.  The exact version is ruled out here.

**Next research action:** define the *approximate* per-modulus degree (probabilistic polynomials over each
`F_p`, errors composing across depth), and test whether ACC⁰ circuits have low *approximate* enriched
boundary.  That is the genuine remaining bridge question; the exact one is settled (negatively) above.

---

## 6. Approximate per-modulus bridge — proved for one field, gap pinned for mixed moduli

`ComputationalDepthApproxEnrichedBoundary.lean` does §5's next action.

* **The approximate single-field bridge is already a theorem** (`Layer4.exists_baseChanged_approximant`,
  cited): an `AC⁰[p]` circuit has a polynomial of total degree `≤ ((p−1)·t)^depth` agreeing on `≥ ¾` of
  inputs, with the `K^depth` composition (`Layer3.ApproxDegreeData.approxDegree_le`, `K=(p−1)t`).  So over
  **one** field the *approximate* boundary **does** model `AC⁰[p]` as low-boundary — the property the *exact*
  boundary lacked (§5).  The per-modulus half of the enriched bridge is done.

* **The mixed-moduli gap is pinned (proved obstruction).**  The bridge needs `IsAC0pSyntax p C` — every `MOD`
  gate modulus `= p`.  Proved here:
  * `modGate_not_isAC0p` — a single `MOD_q` gate (`q ≠ p`) is not `AC⁰[p]`;
  * `mixedCircuit_not_isAC0p_left` / `_right` — a circuit using both `MOD_p` and `MOD_q` (`q ≠ p`) is
    **neither** `AC⁰[p]` **nor** `AC⁰[q]`.

  So *neither* single-field approximant applies to a mixed circuit.  The enriched *approximate* bridge for
  ACC⁰ therefore needs a **new joint construction** — approximating polynomials over the combined modular
  structure — that does not reduce to the single-field one.  **That joint construction is the open frontier**
  (and the reason ACC⁰ resists the polynomial method).

**Status after §6.**  Per-modulus approximate bridge: *settled positively*.  Mixed-moduli reduction:
*provably does not apply*.  `NP ⊄ ACC⁰`: still open — now reduced to "build a low-approximate-boundary joint
modular representation for ACC⁰, or find an NP language that forces it high".
