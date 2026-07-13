# ATTACK on step (6), round 4 — error-polarity forcing for SAT circuit diagonalization

Target (the actual wall): `Step6` = `SAT ∉ P/poly` (stronger than `P ≠ NP`).  Round-4 question (directed): can
self-reference force every erroneous SAT circuit to make a *witnessable* (NP-checkable) false-negative error,
collapsing Kannan-style `Σ₂` diagonalization to `NP`?  **Result: the polarity obstruction IS convertible — SAT's
downward self-reducibility turns any circuit into a false-negative-only one, so both error branches become
NP-witnessable (gate 2 passes).  But the conversion exposes a size obstruction: the self-referential diagonal must
encode the circuit and so exceeds its own length (gate 3 fails).  Polarity and size are DUAL; self-reducibility
trades one for the other and cannot beat both.  This is exactly why non-uniform SAT diagonalization is stuck at
`Σ₂`.  The obstruction is now formalized at its precise death-point, not surveyed.**

## 1. The polarity problem (the starting obstruction)

Diagonalization wants `φ_C` with "`φ_C` satisfiable ⟺ `C_n(φ_C) = 0`".  The branches are asymmetric:

* `C_n(φ_C) = 0` (circuit says UNSAT): to establish the error, `φ_C` must be SAT — a satisfying assignment
  witnesses it (NP). ✓
* `C_n(φ_C) = 1` (circuit says SAT): to establish the error, `φ_C` must be UNSAT — a coNP witness (proof of
  unsatisfiability). ✗

The second branch is why the argument reaches `Σ₂` (universally quantify "no satisfying assignment") rather than
`NP`.

## 2. The conversion — self-reducibility forces false-negative-only (gate 2 PASSES)

SAT is downward self-reducible (`sat_iff_restr`, machine-checked): `f` is SAT iff `f|_{x=0}` or `f|_{x=1}` is.
So replace a purported circuit `C` by

> `C'(f)` := run the greedy witness search (at each variable, follow a child `C` calls SAT), then **verify** the
> resulting assignment; output `1` iff verification succeeds.

`C'` is poly-size (`m` calls to `C` plus a verification).  Its decisive property, **unconditional**
(`verifyWrap_sound`, axiom-free): `C'` has **no false positives** — `C'(f) = 1` only after exhibiting a *verified*
witness, so `C'(f)=1 ⇒ f` genuinely SAT.  `C'` errs **only** by false negatives (`C'(f)=0` while `f` SAT), and a
false negative is NP-witnessable (the missed assignment).  If the base `C` is correct, `C'` is fully correct
(`verifyWrap_complete`).

**So against `C'`, both error branches are NP-checkable.**  The coNP "over-claims SAT" branch is eliminated — the
polarity problem is genuinely solved for `C'`.  This is real: it is the search-to-decision / self-reducibility
fact, and it passes gate 2.

## 3. The death-point — the diagonal exceeds its own length (gate 3 FAILS)

Now diagonalize against `C'_N`: build `φ*` with "`φ*` SAT ⟺ `C'_N(φ*) = 0`".  To reference `C'_N`'s behaviour on
itself, `φ*` must (Cook–Levin) **encode** the circuit `C'_N` and simulate it on `⌜φ*⌝`.  Encoding a size-`N^k`
circuit costs `≥ N^k` bits, so `|φ*| ≥ |C'_N| ≥ N^k`.  For `k ≥ 2`, `N^k > N` (`encode_exceeds_length`), so `φ*` is
**not** a length-`N` instance — it is an input for a strictly larger circuit `C'_{N^k}`, against which the
diagonal formula is larger still.  The self-reference never closes: **there is no fixed-length diagonal against the
circuit of its own length.**

Uniform diagonalization escapes this precisely because a machine `M_i` has an `O(1)` description independent of the
input length, so "`M_i` rejects me" stays length-`poly(n)`.  Non-uniform circuits have no such bounded description
— which is the classical reason `P/poly` resists diagonalization, recovered here through the specific
self-reducibility route.

## 4. Gate-by-gate verdict

1. **Nonuniform circuit, not a uniform algorithm** — ✓ (the whole argument is about `C_N`).
2. **Every error branch NP-checkable, no hidden UNSAT certificate** — ✓ **PASSES** via `C'` (false-negative-only).
   This is the round's genuine gain.
3. **Poly formula size after self-reference / Cook–Levin** — ✗ **FAILS**.  `|φ*| ≥ |C'_N| = N^k > N`.  This is the
   exact death-point, formalized.
4. **No assumption of PH noncollapse / `NP≠coNP` / the lower bound** — ✓ (self-reducibility is unconditional).
5. **SAT-specific, does not misfire on the QF calibration** — ✓.  The construction rests on formula
   self-encoding + self-reducibility; `QF A` is a fixed function, not a formula-acceptance problem, so the
   diagonal "instance SAT ⟺ `C` rejects it" does not type-check for it, and `QF A`'s own `C'` is simply correct
   (it is in P) — no false hardness.
6. **Lean only if a lemma passes all five** — the two conversion mechanisms (`sat_iff_restr`,
   `verifyWrap_sound`/`_complete`) pass gates 1–5 and are formalized; the failure lives at gate 3, formalized as
   `encode_exceeds_length`.  No lemma that *closes the wall* was manufactured.

## 5. The finding: a size obstruction for the literal-hardwiring self-reference (NOT an explanation of Σ₂)

**Correction (per Kannan 1982, Cai–Watanabe 2004).**  The classical placement of the fixed-polynomial circuit
lower bound at `Σ₂ᵖ` is a theorem, but it is NOT established by any "polarity↔size duality"; the actual arguments
(Kannan's, and Cai–Watanabe's constructive treatment) are different.  So this memo does not claim to explain the
`Σ₂ᵖ` placement.  What the round *does* establish, honestly:

* the polarity obstruction is convertible for a given circuit `C` (self-reducibility → false-negative-only `C'`,
  `verifyWrap_sound`); and
* the *specific* `literal-hardwiring` self-referential diagonal against `C'_N` cannot be a length-`N` instance,
  because encoding `C'_N` costs `≥ |C'_N|` bits — a **conditional** obstruction: `descLen C'_N > N ⇒` no
  length-`N` literal-hardwired diagonal (`CNFSelfReduction.hardwire_conditional`).

This is *not* a proof about `P/poly`, and we do **not** infer `descLen C'_N > N` from the `P/poly` upper bound.  A
route through the missing-witness frontier would need to reference `C_N`'s behaviour on a length-`N` instance
*without* literally encoding `C_N` — a bounded, uniform-like handle on a non-uniform object — which is the open
problem itself.  The encoded-CNF version of every mechanism here is `ComputationalDepthCNFSelfReduction.lean`; the
truth-table `BF` sketch was insufficient and is superseded.

Recommendation: freeze this route; the next genuinely new idea would have to break the size↔polarity duality
(reference a large circuit's self-behaviour from a small instance), and none is proposed.  No closure is claimed.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
