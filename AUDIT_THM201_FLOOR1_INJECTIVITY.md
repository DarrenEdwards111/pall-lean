# Floor-1 Injectivity Audit → Theorem 201 (Holographic Upper-Bound Principle)

**Audit standard:** the non-collision discipline forced on us by the AC⁰ branch-holography
ladder (`descentPosValLabels`, brick [155b]). That work taught: an encoding that *counts*
objects by reducing them to labels is only as strong as its **proof that distinct objects
survive the adversary's free parameter without collapsing to the same label** — and that a
naive label silently collides (the [155b] audit found 4 collisions when the deep input `x`
varied per restriction; the fix was to *record the freed value* and re-prove injectivity,
paying `(2w+1)^k → (4w+1)^k`).

**Target:** Theorem 201 / Theorem 92 / properties (P1)–(P7) (§9.2–9.3) of *p vs np1*.
Claim under audit: for every `M ∈ DTIME(n^t)`, the compiled SoS polynomial satisfies
`Γ_{κ,ℓ}(p^{Π⁺}) ≤ n^{O(1)}` at `κ,ℓ = Θ(log n)`.

**Why the audit binds.** §9 *is* a holographic-labeling rank bound:
`rank ≤ (# canonical profiles) · max_h dim V_h`. Here `can(·)` (Def 20) is the **label**,
the interface-anonymous profiles `h` are the **label classes**, (P5) is the **span/recovery
direction**, and (P3)'s `R = C(log n)^c` is the **alphabet-over-live-set budget**. This is
structurally the same machine as `descentPosValLabels` → `_card_le` → `_injective`. So the
floor-1 checklist applies verbatim.

---

## The 6 checks

### Check 1 — Adversary identification
**Standard:** name every free parameter the encoding must survive. (AC⁰: the deep input `x`,
which varies *per restriction* — the parameter the switching count quantifies over.)

**Thm 201:** the free parameter is the **global dependency structure of `M`'s tableau** —
the universal quantifier `∀ M ∈ DTIME(n^t)`. The paper does **not** treat this as an
adversary. (P1)–(P5) are declared *"properties of the compiler construction (not extra
hypotheses)"* and the access schedule is fixed as *"instance-uniform / oblivious."*

**Verdict: FAIL.** The adversary (`M`'s wiring) is quantified *into* the compiler rather
than *confronted by* the label. This is the exact analogue of not noticing that `x` varies.

### Check 2 — Collision test under the adversary
**Standard:** explicitly test whether two objects with *globally different* structure can
produce the *same* label when the free parameter varies. ([155b]: two restrictions with
different freed-values collided into one positions-only label.)

**Thm 201:** (P3) asserts *"at most `R = C(log n)^c` interfaces are live at every step"* for
all compiled programs, forward-citing Lemma 19. But a genuine poly-time `M` can, at one
step, depend on polynomially many earlier cells (random access / pointer chasing). Those are
exactly the steps whose *distinct global reach collides into a bounded-liveness profile*.
The paper rules them out by fixing **radius-1, oblivious** access — i.e. it **narrows the
adversary from "all poly-time `M`" to "radius-1 oblivious-access `M`"** without proving the
restriction is WLOG.

**Verdict: FAIL.** The collision test is not run; it is replaced by an access-model
assumption that deletes the colliding cases. CEW = the live-interface count = the thing that
must be *proved* bounded, is *assumed* bounded.

### Check 3 — Span / recovery direction
**Standard:** prove either (a) distinct objects → distinct labels (counting upper bound), or
(b) canonical reps **span** the full row space (no rank lost in canonicalization). Proved,
not asserted.

**Thm 201 — the genuinely-proved part:** Lemma 24 (local update words act through the finite
monoid `M ⊆ Σ^Σ`; `A_u = A_{NF(u)}`) and the (P6) disjoint-support commutation are real,
correct, finite-monoid facts. This is the honest analogue of `posInTerm_recover` — a clean,
local round-trip. **This piece passes.**

**Thm 201 — the failing part:** the *global* span claim (P5), that all rows of a profile `h`
lie in `V_h = ⊗_τ Sym^{h(τ)}(W_τ)` with `dim V_h ≤ R^{O(1)}`, is row-span-preserving **only
if** no adversarial window escapes a canonical profile. Escape = high CEW = precisely the
case Check 2 assumed away. So (b) holds locally and **inherits Check 2's failure globally.**

**Verdict: PARTIAL** — local monoid recovery proved; global span contingent on the
unproven (P3).

### Check 4 — Value-augmentation (the [155b] fix), and why it is unavailable here
**Standard:** when the bare label collides, record the adversary's free data and re-prove
injectivity, paying the count. ([155b]: record the freed *value*; pay one bit/var.)

**Thm 201:** the honest fix would be to **record the global dependency reach** of each step
into its profile. But then the profile count is no longer `poly`/`polylog`: augmenting by a
width-`w` dependency multiplies the label space by ~`S^w`, and for adversarial `M` that `w`
is not polylog-bounded. **Applying the floor-1 fix converts `poly` rank into super-poly rank
— i.e. it flips the conclusion to the NP side.**

**Verdict: FAIL — and diagnostically so.** The bound survives *only by refusing the
augmentation the audit demands.* In [155b] augmentation cost a constant (the value is one
bit, path length already bounded by the switching event); here it costs the dependency width,
which is unbounded for general `M`. That asymmetry is the precise formal sense in which
"holography closes the god-move" is false: the closing move is the one that destroys the
upper bound.

### Check 5 — No fixed-basis smuggling
**Standard:** encoding constants must be genuinely adversary-independent (n-independent **and**
computation-independent), not "O(1) for the instances we like."

**Thm 201:** `Π⁺ = A` is a **single fixed** radius-1 block-local unitary used for **all** `M`,
claimed to diagonalize **every** compiled program's local constraints simultaneously (Def 49,
Lemma 200). Constants `S, b, d_τ` are declared *"depend only on the compiler."* But the
compiler is exactly what must absorb arbitrary `M`; a fixed radius-1 unitary that imposes a
universal local normal form on global computation is the maximal smuggle. Their `O(1)`-ness is
*asserted* and is **false** for genuinely non-local `M` — the "oblivious access schedule" is
silently doing the work.

**Verdict: FAIL.**

### Check 6 — Uniformity over the quantifier (the killer)
**Standard:** the bound must hold for the *full* quantifier with constants not secretly
depending on the object.

**Thm 201:** holding `Γ ≤ n^{O(1)}` over `∀ M ∈ DTIME(n^t)` requires Theorem 92 — that the
radius-1 oblivious compiler maps **every** poly-time `M` to polylog CEW. **That reduction is
the P-side collapse itself** (it is Theorem 170 / the God-Move in disguise).

This is not a heuristic objection — it is already a *theorem of this repo*. The formalized
Theorem 207 / semantic-closure anatomy (`ComputationalDepthSemanticClosureFrontier.lean`,
commit 1fdb7051) proved:

> `PaperLemma13StrengthSemanticClosure ↔ Theorem207StrictLiveBoundaryPort ↔ ¬∃ encoded SAT decider`

with the zero-rank obstruction *built into the `∀ configActionRank` quantifier* (it ranges
over zero-rank presentations). I.e. discharging the uniform closure **is** the separation;
`GlobalGodMoveGauge` hid this behind `Classical.choose`.

**Verdict: FAIL — and provably non-dischargeable by any sub-separation means.**

---

## Conclusion: the single undischarged obligation

All six checks localize the gap to **one** non-collision claim:

> **(P3) / Theorem 92:** the radius-1 oblivious `Π⁺`-compiler sends *every* `M ∈ DTIME(n^t)`
> to a constraint system whose live-interface count (CEW) stays `≤ C(log n)^c` — equivalently,
> the fixed local basis `Π⁺` does **not** collide globally-dependent computation steps into
> bounded-liveness profiles.

Everything downstream is sound or locally proved:
- Lemma 24 (finite-monoid action), (P6) commutation, (P7) normal forms — **clean**;
- the rank arithmetic *given* `R = polylog` — **clean**;
- the NP-side identity-minor invariance under `Π⁺` — **not contested by this audit**.

The gap is concentrated exactly at the adversary-survival step, which:
1. the paper discharges by *assumption* (oblivious/radius-1 access), not proof (Checks 1,2,5);
2. cannot be repaired by the floor-1 value-augmentation fix, because that fix flips the
   conclusion to super-poly rank (Check 4);
3. is **provably equivalent to the separation** by this repo's own Theorem 207 formalization
   (Check 6).

## Bearing on the original hope

Branch holography (the AC⁰ ladder) does **not** supply the missing (P3). What it supplies is
the *standard that exposes the gap*: §9's `can(·)`-labeling is exactly a holographic count,
and run against the floor-1 injectivity discipline it fails precisely where a real switching
argument is forced to *pay* — except here the payment is unbounded. The honest deliverable is
therefore a **no-go on Theorem 201's "Conceptual Proof,"** not a completion — consistent with
the healthiest prior move in the arc (commit 42d1fd10, proving one's own socket vacuous).

*Floor-1 audit; AC⁰-discipline applied to a P/poly-strength claim. No completion asserted.*
