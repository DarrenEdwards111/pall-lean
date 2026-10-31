# Scope — Layer 7: Open-Frontier Map

**Status: scope/audit only. No theorem claims. No proofs of open results.**

This document maps where the completed `AC⁰[p]` / `MOD_q` machinery can and cannot help with open
lower-bound frontiers. It is grounded in the *actual* repository state (commit lineage `…5bf90254`,
branch `razborov-recoverRho-wip`), not aspiration.

---

## 1. Completed foundation (formally available, sorry-free, standard axioms)

All in `PallLean/Paper93/DeepMath/PathB/`, axioms `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`:

* **Circuit model.** `BoolCircuitSyntax n` (const/input/not/and/or/mod gates), `eval`, `depth`, `size`,
  `subcircuits`; `IsAC0pSyntax p` (Boolean gates + `MOD p` gates only) — `ComputationalDepthRung4CircuitReal`,
  `…Layer3Agreement`.
* **`AC⁰[p]` polynomial approximation.** `toAgree` (probabilistic-polynomial approximant via form choice
  `FormSpace`), `toAgree_eval`, `toAgree_totalDegree_le` (degree `≤ ((p-1)t)^depth`) — `…Layer3Agreement`,
  `…Layer3Smolensky`.
* **Razborov–Smolensky agreement bound.** `composed_error_le` (`|cbad|·p^t ≤ s·2ⁿ`),
  `exists_large_agreement_set` (`p^t ≥ 4s ⇒ 3·2ⁿ ≤ 4·|G|`); parameterised tight form
  `exists_tight_agreement_set` (`p^t ≥ 4q·s ⇒ 4q·|cbad| ≤ 2ⁿ`) — `…Layer3Agreement`, `…Layer4Assembly`.
* **Dimension / band contradiction.** low-degree monomial count + central-binomial `√n` band margin
  (`lowDegMonomials_card_band_margin`, `centralBinom_sq_le`), `dim_bound_on_G`, `smolensky_contradiction`
  (parity) and the field-general `dim_contradiction_general`, `qary_contradiction` — `…Layer3DimensionCount`,
  `…Layer3Smolensky`, `…Layer4DimGeneral`, `…Layer4Bridge`.
* **PARITY lower bound.** `parity_function_lower_bound` (`…Layer3Smolensky`).
* **General `MOD_q` separation (`p ≠ q`).** `mod_q_indicators_false` (`…Layer4Capstone`),
  `mod_q_family_false` (`…Layer4PadSubcircuits`).
* **Extension-field / `q`-character machinery.** `GaloisField p (q-1)` primitive `q`-th root
  (`exists_primitiveRoot_galoisField`), base change `map φ` (`…Layer4BaseChange`), the `ζ`-character
  `qChar`, halving `qChar_halving`, reduction `qChar_reduction`, spanning `qSpan_eq_top`, residue-indicator
  assembly `weightChar_repr_of_indicators` — `…Layer4RootOfUnity/ModqChar/QaryReduction/QarySpan/WeightRepr`.

### Exact shape of the capstones (important for everything below)

`parity_function_lower_bound` and `mod_q_*` are **nonuniform, single-circuit, fixed-input-length**
statements. E.g. (paraphrased):

> For prime `p`, fixed depth bound `d`, horizon `t ≥ 1`, and `m ≥ 8·((p-1)t)^{2d}`: **any one**
> `Cir : BoolCircuitSyntax (2m+1)` that computes PARITY on `2m+1` bits, is `AC⁰[p]`, and has `depth ≤ d`,
> satisfies `p^t < 4·#subcircuits(Cir)` (i.e. size `> p^t/4`).

There is **no circuit-*family* object, no asymptotic "for all large n", and no complexity *class*** wired
to these yet. That gap is the subject of §3–§5.

---

## 2. Known vs open boundary (kept sharp — do not blur)

### Known / formalization targets (reachable, *not* open mathematics)

* **`MOD_q ∉ AC⁰[p]` (`p ≠ q` prime), `PARITY ∉ AC⁰[p]`** — **done** (nonuniform fixed-length form above).
* **Asymptotic restatement.** Package the per-`m` bound into a family statement "for every fixed depth `d`,
  any `AC⁰[p]` circuit family of depth `d` computing PARITY has super-polynomial size" by instantiating `t`
  as a slowly-growing function of `m`. *Standard, mechanical; not open.*
* **Mathlib-extraction candidates.** The central-binomial `√n`-type bound (`centralBinom_sq_le`), the
  low-degree monomial count, the `q`-th-root-in-`GaloisField` existence lemma — clean, reusable, not open.

### Open mathematical frontiers (NOT reachable by this machinery; state as open)

* **`NP ⊄ AC⁰[p]` as a *genuine* class separation** beyond "a specific easy function is hard" — see §3-B for
  why the easy reading is shallow and the deep reading is open/definition-dependent.
* **`NP ⊄ ACC⁰`** (Williams). RS alone does **not** reach it (§3-A).
* **Strong explicit lower bounds for `ACC⁰`** (composite moduli).
* **`P ≠ NP`.** Nothing in this machinery bears on it directly (§3-C).
* **Super-polynomial lower bounds for general (unrestricted-depth) Boolean circuits / `P/poly`.**

**These are open. Layer 7 will not claim any of them. At most it builds scaffolding and honestly
*conditional* statements.**

---

## 3. Candidate Layer 7 routes

### Route A — `ACC⁰` / Williams frontier

**Can the formalized RS machinery help with `ACC⁰`?**  *Only marginally; the core barrier is real.*

* `ACC⁰` allows `MOD_m` gates for **composite** `m` (and several moduli at once).
* RS (as formalized) separates `AC⁰[p]` from `MOD_q` for a **single prime** `p` and `q ≠ p`. The whole
  argument runs over `F_{p^k}` and uses that `p` is the *only* modulus in the circuit (`IsAC0pSyntax p`).
  With multiple/composite moduli the polynomial-approximation step has no single field to live in — **RS
  alone does not separate `ACC⁰`**. This is the well-known barrier.
* Williams' `NEXP ⊄ ACC⁰` does **not** use RS dimension counting; it uses **nontrivial `ACC⁰`-SAT
  algorithms** + the algorithm-to-lower-bound ("easy witness" / `NEXP` vs algorithms) framework.

**Formal objects a Williams-style proof would need (none of which RS provides):** an `ACC⁰` syntax/model
with composite `MOD` gates + family/size/depth; circuit evaluation; a **faster-than-brute-force `ACC⁰`-SAT
algorithm** abstraction; a `NEXP` formalization; and the **easy-witness / algorithm⇒lower-bound** bridge
(Impagliazzo–Kabanets–Wigderson-style). An exploratory `ACC0LikeCircuitFamily` exists in
`ComputationalDepthNFramePACInvariant.lean`, but it is **abstract/socket-style scaffolding**, not a proof.

**Verdict: out of reach. RS is the wrong tool; the missing pieces are an entire separate framework.**

### Route B — `NP ∉ AC⁰[p]`

**Can the current `MOD_q`/PARITY lower bound be lifted to a language-class statement?**  *A clean
*nonuniform* corollary is reachable; the deep class separation is shallow-or-definitional, not new math.*

Critical distinctions (the warning is correct and load-bearing):

* PARITY, `MOD_q` are **in `P`** (hence in `NP`). A lower bound for an easy function against `AC⁰[p]`
  therefore gives, *if the definitions are set up*, "**some** language in `NP` (indeed in `P`) is not in
  (nonuniform) `AC⁰[p]`" — this is **shallow**: it is RS repackaged, not a new separation, and it says
  nothing about hard `NP` languages.
* The honest content is **nonuniform circuit-family**: "the PARITY language family is not computed by any
  poly-size constant-depth `AC⁰[p]` circuit family." Calling that "`NP ⊄ AC⁰[p]`" is a *framing* that
  depends entirely on (a) defining `NP` and (b) the **uniform vs nonuniform** convention and the
  **language vs circuit-family** convention.
* **Blocking fact for this repo:** the existing `P`, `NP`, `Language`, `DTIME` live **only in
  `Step4Compiler.lean`** (which Layer 7 must not touch) and are **TM/time-based** (`Language := List Bool →
  Prop`), i.e. *uniform*. The completed lower bounds are *nonuniform, per-length, circuit-syntactic*. There
  is **no clean circuit-family `AC⁰[p]` class** in the computational-depth layers to phrase the corollary
  against.

**Three statement levels (must be distinguished in any deliverable):**
1. *Per-length nonuniform* (already have): no single `AC⁰[p]` circuit of bounded depth + sub-`p^t/4` size
   computes parity at length `2m+1`.
2. *Circuit-family nonuniform* (reachable, needs a small new layer): no poly-size constant-depth `AC⁰[p]`
   **family** computes the PARITY language. **This is the honest, new-to-the-repo deliverable.**
3. *Uniform `NP` class containment* (`NP ⊄ uniform-AC⁰[p]`): needs the TM `NP` (in the untouchable file)
   *and* a uniformity bridge — **not** cleanly reachable here, and the easy reading is shallow.

**What Route B can honestly produce:** build a *small, self-contained* nonuniform circuit-family layer
(boolean language, `AC⁰[p]` family with poly-size/const-depth, the PARITY language) and prove **level 2**
as a corollary of `parity_function_lower_bound`. State explicitly that this is *not* `P ≠ NP` and *not* a
hard-`NP`-function separation — it is "an explicit (easy) language outside nonuniform `AC⁰[p]`."

### Route C — `P ≠ NP` connection

**What does an `AC⁰[p]` lower bound say about `P` vs `NP`?**  *Directly, nothing.*

* `AC⁰[p]` is **far** below `P/poly` and general `P` computation (constant depth + one prime modulus vs
  arbitrary poly-size circuits / poly-time TMs). A separation here gives **zero** direct leverage on
  `P` vs `NP`.
* A `P ≠ NP` proof needs vastly stronger ingredients — general-circuit or uniform lower bounds — that this
  machinery does not touch.

**Missing bridges that would be required (all absent from the clean layers):** formal `P`, `NP` at the
level used (the only ones present are TM-based in the untouchable `Step4Compiler.lean`); a Cook–Levin
bridge; a **general poly-size circuit model** (unbounded depth, arbitrary gates); and **lower bounds for
that model** — not `AC⁰[p]`. **Layer 7 claims no `P≠NP` progress; `AC⁰[p]` bounds are infrastructure only.**

### Route D — formalization / publishing (highest-value *non-open* deliverable)

* Clean theorem names + module docs for the Layer 3/4 capstones; an audit file listing each capstone with
  its `#print axioms`.
* Extract the central-binomial `√n` lemma (and the monomial count) as standalone Mathlib-style lemmas.
* A paper note: *"A Lean formalization of Razborov–Smolensky `AC⁰[p]` lower bounds (PARITY and general
  `MOD_q`)."*
* A CI target building **only** the clean computational-depth layers (Layer 3/4 + new Layer 7 scaffolding),
  excluding the unrelated `Step4Compiler.lean` breakage.

**Verdict: entirely reachable, honest, and high-value. Good default if Route B stalls on definitions.**

---

## 4. Recommended next step

**Primary: Route B at level 2 (nonuniform circuit-family), carefully — with Route D packaging alongside.**

Rationale: Route B-level-2 is the one *new, rigorous, non-open* mathematical statement reachable from the
completed work — a genuine bridge from the per-length circuit bound to a **circuit-family language
separation** ("the PARITY language ∉ nonuniform-`AC⁰[p]`"). It is honest precisely because we will *not*
call it `P ≠ NP`, will *not* claim a hard-`NP`-function separation, and will flag the uniform-`NP` framing
as out of scope.

Guardrails for Route B:
* The existing `P`/`NP`/`Language` are in `Step4Compiler.lean` and are off-limits + uniformity-mismatched.
  So **build a small, fresh, self-contained nonuniform layer** rather than touching them. Minimal new defs:
  ```
  def BoolLang := (n : ℕ) → (Fin n → Bool) → Bool          -- a language as a length-indexed family
  structure AC0pFamily (p : ℕ) where                       -- one circuit per length, with bounds
    circ  : (n : ℕ) → BoolCircuitSyntax n
    isAC0p : ∀ n, IsAC0pSyntax p (circ n)
    depthBound : ℕ
    hdepth : ∀ n, (circ n).depth ≤ depthBound
    sizeBound : ℕ → ℕ                                       -- e.g. polynomial
    hsize : ∀ n, (subcircuits (circ n)).toFinset.card ≤ sizeBound n
  def Computes (F : AC0pFamily p) (L : BoolLang) : Prop := ∀ n x, (F.circ n).eval x = L n x
  def parityLang : BoolLang := fun _ x => decide (Odd (Finset.univ.filter (fun i => x i = true)).card)
  ```
  (adapt to existing names where present; do not duplicate).
* The honest theorem to *aim* for (state it, don't pre-claim it proved): *no `AC0pFamily p` of constant
  depth and polynomially-bounded size `Computes parityLang`* — obtained by feeding the family's depth/size
  bounds at length `2m+1` into `parity_function_lower_bound` and choosing the horizon `t` to outgrow any
  polynomial size bound (using `m ≥ 8·((p-1)t)^{2d}`). This is the one genuine corollary.
* If any needed definition is missing, **build the small definition first** (above); **do not fake** a
  separation or a class.

**Do not** start Route A (ACC⁰/Williams — out of reach) or Route C (P≠NP — no leverage) as proof efforts;
only scaffolding/documentation if at all.

---

## 5. Immediate next deliverable (after this doc)

Per the task: inspect existing definitions and produce `SCOPE_LAYER7_COMPLEXITY_CLASS_BRIDGE.md` answering
(1) what definitions already exist, (2) whether `parity_function_lower_bound` can imply an
`NP`-not-in-`AC⁰[p]`-style corollary and at which of the three levels, (3) the exact *honest* theorem
statement (level 2, nonuniform family), (4) what must be built first (the small nonuniform layer above).
Grounding already gathered: `P/NP/Language/DTIME` exist only in `Step4Compiler.lean` (TM-based, off-limits);
no circuit-family `AC⁰[p]` class exists in the clean layers; `parity_function_lower_bound` is the per-length
hook.

**Rules honored throughout Layer 7:** sorry-free; no custom axioms; do not edit Layer 5/6 theorem files or
`Step4Compiler.lean`; open targets stated as open with scaffolding only; no `P≠NP`-from-`AC⁰[p]` claims;
small buildable commits; `lake build` + `#print axioms` after each; push each clean commit.
