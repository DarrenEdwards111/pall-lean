# SCOPE: attacking the machine-completeness bridge directly

This assesses recommendation #1 from `SCOPE_OBSERVER_BOUNDARY_THREAD.md`: *attack the machine-completeness bridge
head-on — and expect it to fail at a known barrier.* It is a **map of the obstruction**, not an attempt.
**Verdict: don't pursue it — but for a cleaner reason than "it's hard." The decisive, *proved* obstruction is that
the observer measure is polynomially capped (`NeciporukCeilingTotal.neciporuk_ceiling`, `≤ n²`), which kills the
frontier at piece 1 (no function has a super-polynomial boundary) and makes the bridge itself *moot*. The bridge is
also `P ≠ NP`-strength — but that is a *structural* argument (§2), fitting a documented pattern of distinct
load-bearing bridges in this program that each turned out `P ≠ NP`-strength; it is *not* a Lean proof that this
particular bridge equals the separation, and it is not the operative fact. Corrected ranking below.**

> **Correction (post-audit).** An earlier draft led with "this project has already demonstrated *that equivalence*
> several times." That over-identifies: the prior collapses (§2) are *different* bridges/sockets/gaps establishing a
> *pattern*, not proofs that *this* bridge equals the separation. And it over-ranked the bridge: the **cap (§3) is
> decisive and proven**, and it makes the bridge moot; §2 (bridge ⟺ separation) is a secondary structural
> observation; §4 (relativization / natural proofs) is softer still and largely *redundant* with the cap.

## 1. What the bridge is

The frontier (`SCOPE_OBSERVER_BOUNDARY_THREAD.md §3`) needs three pieces; #1 is done (restricted), #3 is the SAT
lower bound, and the decisive middle is:

> **Machine-completeness bridge.** Every polynomial-time machine `M` deciding SAT induces a decomposition `D_M` in
> the structured class such that the observer boundary satisfies `boundary(D_M) ≤ poly(runtime(M))`, and `M` cannot
> evade the hard cuts by encoding, padding, state representation, or a different decomposition.

Combined with structured hardness (`boundary(D) ≥ super-poly` for SAT on every `D` in the class) this gives
`super-poly ≤ poly`, a contradiction, hence `SAT ∉ P`. The bridge is the *universal quantifier over all machines*
made to land inside the class where we have a bound.

**But note where this actually dies.** The cap of §3 (`boundary ≤ n²` for *every* function, now a theorem) makes
the "structured hardness" hypothesis `boundary(D) ≥ super-poly` **false for everything** — no function, SAT
included, has a super-polynomial boundary. So the frontier is dead at *piece 1*, before the bridge is reached; a
perfect bridge would not help, because with `boundary ≤ n²` the inequality `boundary ≤ runtime` is trivially
satisfiable and no contradiction is ever forced. The bridge is therefore *moot*, not merely hard. Sections 2 and 4
explain why it is also `P ≠ NP`-strength and barriered — true, but secondary.

## 2. The bridge is `P ≠ NP`-strength — a structural argument, plus a documented pattern

*(Secondary to §3; the cap already makes the bridge moot. This section says why, if you did reach it, it is also
`P ≠ NP`-strength.)*

**Structural argument (not a Lean proof of this bridge).** Given the other frontier pieces, a proof of the bridge
yields `SAT ∉ P`; and if `SAT ∉ P` the bridge's hypothesis ("a poly-time machine deciding SAT") is vacuous, so the
bridge holds trivially. Hence bridge ⟺ separation *modulo the other pieces* — the "package ⟺ `¬(SAT ∈ P)`" shape.
This is an argument about the shape of the claim, not a machine-checked equivalence for this specific bridge.

**The documented pattern.** It is not a coincidence that this shape keeps recurring: every prior load-bearing
"bridge / socket / gap" in this program — *distinct* objects in *distinct* arcs — was found to be `P ≠ NP`-strength
or vacuous or merely asserted. These establish the *pattern*, not that any of them *is* the machine-completeness
bridge:

* **Theorem-207 (`project_routew_socket_pattern`)** — the "closure glue" was **PROVEN equivalent to the
  separation**: glue ⟺ separation. A publishable negative result: the bridge *is* the theorem.
* **HM socket (same file)** — **proved vacuous**: the package ⟺ `¬(SAT ∈ P)`. Again bridge ⟺ separation.
* **book1 SPDP "P-observer ⇒ low SPDP rank" (`project_tseitin_proofspace_observer`)** — the load-bearing bridge was
  **asserted, not derived**; it is `P ≠ NP`-strength and false in the naive model. The exact PUpper direction of
  the machine-completeness bridge, un-provable as stated.
* **N-Frame load-bearing pivot (`project_nframe_load_bearing`)** — `gap ⟺ separation` proved; the "P/poly-capture"
  conjecture (the coverage half) was **named but not discharged**, explicitly `P ≠ NP`-strength.
* **ACC⁰ Beigel–Tarui collapse socket (`project_acc0_celltree_bt_arc`)** — the collapse socket = `P ≠ NP`-strength;
  refused to fake.

The standing audit rule this produced — *check `#print axioms P_ne_NP_unconditional`, not the leaf lemmas
(`project_routew_socket_pattern`)* — exists precisely because such bridges keep re-appearing as unproved sockets.
So the honest reading: discharging the machine-completeness bridge would (structurally) be the same act as proving
`P ≠ NP`, and it fits a well-documented pattern — but this is a secondary point, because §3's cap already forbids
the bridge from ever helping.

## 3. Handicap 1 — the observer measure is capped below separation strength

Even granting a *complete* bridge, the observer/Nečiporuk boundary cannot separate P from NP, because the measure
has a hard ceiling.

For any function on `n` variables and any partition into disjoint non-empty blocks,
`Σ_blocks log₂(#subfunctions on block) ≤ n²` — **now a machine-checked theorem**
(`NeciporukCeilingTotal.neciporuk_ceiling`, clean-axiom, no `sorry`), with the sharper `Θ(n²/log n)` following
from the per-block cap `min(2^b, n-b)` (`NeciporukCeiling.log_subfunctions_le_min`) under the standard convexity
optimization. Either way the total boundary is **polynomial**, so it can never be super-polynomial: a completed
bridge yields at best a polynomial SAT lower bound, polynomially short of a separation (P permits `n^100`).

To lift the ceiling you would need a measure that is super-polynomial for SAT under *every* decomposition. But
`SCOPE_INTRINSIC_INVARIANT.md` settles that: any such representation-invariant measure is either an intrinsic
function property (poly-bounded — the ceiling is a concrete instance) or an inf over representations (circular).
The crossing-capacity arc also proved the natural way to escape the ceiling — a *crossing bridge to TC⁰/NC¹* — is
**false** (a machine-checked no-go). So Handicap 1 is not a missing lemma; it is a proven cap.

## 4. Handicap 2 — the coverage argument hits the classical barriers (soft, and redundant with §3)

*(This section is weaker than §3 and largely subsumed by it: the cap already kills the route, so these barriers
are not needed. They matter only for the hypothetical "what if the ceiling were lifted." The relativization item
is a plausibility sketch, not a theorem, and the natural-proofs item does not apply to the actual capped boundary
— see the caveat on that bullet.)*

Suppose the ceiling of §3 were somehow lifted. The coverage half — *every poly machine deciding SAT induces a hard
decomposition, with boundary ≤ runtime* — would be a fully general lower-bound argument, and the standard barriers
would then bite:

* **Relativization (Baker–Gill–Solovay), made precise.** The PUpper direction, `boundary ≤ runtime`, is about
  information crossing a cut and holds relative to any oracle `O`: `boundary(M^O, D) ≤ runtime(M^O)`. If the
  hardness half — *SAT hard on every decomposition* — were also proved by the observer boundary (a counting /
  communication measure, oracle-independent), the whole argument would relativize, yielding `SAT^O ∉ P^O` for
  **every** `O`. But there is an oracle `A` with `P^A = NP^A`. Contradiction. Hence the hardness half **cannot** be
  carried by the (relativizing) observer boundary — it must exploit non-relativizing structure of SAT that the
  observer framework does not see. This is exactly the predicted "fail at relativization."
* **Natural proofs (Razborov–Rudich) — caveat.** This bar applies only to a *useful* constructive+large property.
  The **actual** observer boundary is *not* useful (it is capped, §3), so it is not a natural proof at all — it
  simply proves nothing super-polynomial, and the correct reason it fails is the cap, not this barrier. The
  natural-proofs bar bites only in the counterfactual where §3 is lifted to yield a useful measure: *then* a
  constructive+large hardness property would break pseudorandom function generators, so it would have to be either
  SAT-specific (re-opening the machine-completeness gap) or non-constructive (Handicap-1's circular inf). Stated as
  a live barrier against the real measure, it is a category error.
* **Algebrization (Aaronson–Wigderson).** Communication/observer arguments algebrize; algebrizing techniques
  cannot separate P from NP.
* **The rank shadow is Valiant rigidity.** The linear form of the coverage bridge is matrix rigidity
  (`nframe_linear_nonlinear_dilemma`: *linear mixer = Valiant rigidity, open; linear form of the framework ≡
  Valiant's problem*). The N-frame arc already terminated on exactly this wall.

## 5. Verdict and recommendation

Attacking the machine-completeness bridge directly is attacking `P ≠ NP` directly. Beyond that identity — already
proved several times over in this repository — it carries two handicaps specific to the observer route: the measure
is **capped at `n²/log n`** (Handicap 1, a proven no-go, quadratically short of separation), and the coverage
argument **relativizes / is natural / algebrizes**, with **Valiant rigidity** as its linear shadow (Handicap 2).

So the honest expectation the scope doc set — *expect it to fail at a known barrier* — is met on all counts, and
one of them (bridge ⟺ separation) is not a barrier but a proven identity. **Do not pursue the bridge as a route to
`P ≠ NP`.**

The one buildable, honest by-product is a **no-go**, not a bridge: formalizing the **Nečiporuk ceiling** as a
theorem — *for every `n`-variable function and every partition, `Σ log₂(#subfunctions) ≤ C · n²/log n`* — which
proves that the observer/Nečiporuk boundary is quadratically capped and therefore *cannot* separate P from NP.
That is a genuine limitation theorem, the same species as the completed restricted matrix, and it would close the
observer route with a proof rather than a prediction. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
