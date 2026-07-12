# SCOPE: attacking the machine-completeness bridge directly

This assesses recommendation #1 from `SCOPE_OBSERVER_BOUNDARY_THREAD.md`: *attack the machine-completeness bridge
head-on — and expect it to fail at a known barrier.* It is a **map of the obstruction**, not an attempt.
**Verdict: the bridge is provably equivalent in strength to `P ≠ NP` itself — this project has already
demonstrated that equivalence several times — and the observer measure that would carry it is both capped below
separation strength and relativizing. Attacking it directly is attacking `P ≠ NP` directly, with two extra
handicaps.**

## 1. What the bridge is

The frontier (`SCOPE_OBSERVER_BOUNDARY_THREAD.md §3`) needs three pieces; #1 is done (restricted), #3 is the SAT
lower bound, and the decisive middle is:

> **Machine-completeness bridge.** Every polynomial-time machine `M` deciding SAT induces a decomposition `D_M` in
> the structured class such that the observer boundary satisfies `boundary(D_M) ≤ poly(runtime(M))`, and `M` cannot
> evade the hard cuts by encoding, padding, state representation, or a different decomposition.

Combined with structured hardness (`boundary(D) ≥ super-poly` for SAT on every `D` in the class) this gives
`super-poly ≤ poly`, a contradiction, hence `SAT ∉ P`. The bridge is the *universal quantifier over all machines*
made to land inside the class where we have a bound.

## 2. The bridge ⟺ separation — already demonstrated here, repeatedly

This is not a prediction. Every prior attempt in this repository to discharge exactly this bridge (under different
names) was shown to be `P ≠ NP`-strength or to smuggle the conclusion into an unproved socket:

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
(`project_routew_socket_pattern`)* — exists precisely because the bridge keeps re-appearing as an unproved socket.
So the first, decisive finding of this scope is empirical and already in hand: **discharging the bridge and proving
`P ≠ NP` are the same act.** Attacking it "directly" is not a shortcut around the separation; it is the separation.

## 3. Handicap 1 — the observer measure is capped below separation strength

Even granting a *complete* bridge, the observer/Nečiporuk boundary cannot separate P from NP, because the measure
has a hard ceiling.

For any function on `n` variables and any partition into blocks, `Σ_blocks log₂(#subfunctions on block)` is
maximized at balanced blocks and is `Θ(n²/log n)` — the **Nečiporuk ceiling** (`project_neciporuk_crossing_capacity
_arc`: *ceiling n²/log n*). The method provably cannot certify more than quadratic formula size (or `n²/log²n`
branching-program size). So a completed bridge yields at best a **quadratic** SAT lower bound — polynomially short
of a separation, which needs super-polynomial (P permits `n^100`).

To lift the ceiling you would need a measure that is super-polynomial for SAT under *every* decomposition. But
`SCOPE_INTRINSIC_INVARIANT.md` settles that: any such representation-invariant measure is either an intrinsic
function property (poly-bounded — the ceiling is a concrete instance) or an inf over representations (circular).
The crossing-capacity arc also proved the natural way to escape the ceiling — a *crossing bridge to TC⁰/NC¹* — is
**false** (a machine-checked no-go). So Handicap 1 is not a missing lemma; it is a proven cap.

## 4. Handicap 2 — the coverage argument hits the classical barriers

Suppose the ceiling were somehow lifted. The coverage half — *every poly machine deciding SAT induces a hard
decomposition, with boundary ≤ runtime* — is a fully general lower-bound argument and meets all three barriers:

* **Relativization (Baker–Gill–Solovay), made precise.** The PUpper direction, `boundary ≤ runtime`, is about
  information crossing a cut and holds relative to any oracle `O`: `boundary(M^O, D) ≤ runtime(M^O)`. If the
  hardness half — *SAT hard on every decomposition* — were also proved by the observer boundary (a counting /
  communication measure, oracle-independent), the whole argument would relativize, yielding `SAT^O ∉ P^O` for
  **every** `O`. But there is an oracle `A` with `P^A = NP^A`. Contradiction. Hence the hardness half **cannot** be
  carried by the (relativizing) observer boundary — it must exploit non-relativizing structure of SAT that the
  observer framework does not see. This is exactly the predicted "fail at relativization."
* **Natural proofs (Razborov–Rudich).** "SAT has high boundary on every decomposition" is a property of the truth
  table that is constructive (computable in `2^{O(n)}`) and large (holds for random functions); if it were useful
  (implied super-polynomial lower bounds) it would break pseudorandom function generators. So the coverage claim,
  made general and constructive, is barred — unless SAT-specific (which re-opens the very machine-completeness gap)
  or non-constructive (which is Handicap-1's circular inf).
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
