# Scope — Layer 7: Complexity-Class Bridge

**Status: scope/audit only. No theorem claims, no proofs. This pins the *exact honest target* and the
minimal definitions to build first.** Companion to `SCOPE_LAYER7_OPEN_FRONTIER.md` (Route B, level 2).

---

## 1. What definitions already exist?

### A. Clean nonuniform circuit primitives (usable; `PathB`, sorry-free)

* `BoolCircuitSyntax n` — circuits on `Fin n → Bool` inputs (`ComputationalDepthRung4CircuitReal`).
* `eval : BoolCircuitSyntax n → (Fin n → Bool) → Bool`, `depth`, `size` (same file).
* `subcircuits : BoolCircuitSyntax n → List (BoolCircuitSyntax n)` (`ComputationalDepthLayer3Agreement`);
  size is measured as `(subcircuits C).toFinset.card` throughout the RS development.
* `IsAC0pSyntax p : BoolCircuitSyntax n → Prop` — Boolean gates + `MOD p` gates only (same file).
* **Per-length capstone hook:** `parity_function_lower_bound` (`…Layer3Smolensky`):
  ```
  (p) [Fact p.Prime] {m d} (hp2 : (2:ZMod p) ≠ 0) (Cir : BoolCircuitSyntax (2*m+1))
  (hd : Cir.depth ≤ d) (t) (ht1 : 1 ≤ t)
  (hparity : ∀ x, Cir.eval x = decide (Odd (univ.filter (x ·)).card))
  (hmod : ∀ q r cs, modGate q r cs ∈ subcircuits Cir → q = p)
  (hm : 8 * (((p-1)*t)^d)^2 ≤ m)
  ⊢ p^t < 4 * (subcircuits Cir).toFinset.card
  ```
  i.e. **fixed length `2m+1`, one circuit, size `> p^t/4` in the band-margin regime.**
* (`mod_q_indicators_false`, `mod_q_family_false` — same fixed-length nonuniform shape, for `MOD_q`.)

### B. Off-limits, uniform, encoding-mismatched class layer (`Step4Compiler.lean` — must not touch)

* `Language := List Bool → Prop` (note: **`List Bool`**, not `Fin n → Bool`).
* `DTIME (f) := { L | ∃ M : DTM, timeSteps M n ≤ f n ∧ DTM_Decides M L }`.
* `P := ⋃ k, DTIME (n^k+1)`.
* `NP := { L | ∃ verifier V (poly-time DTM) and poly p, ∀ x, L x ↔ ∃ w, |w| ≤ p|x| ∧ V x w }`.

**Three independent gaps** between B and the circuit bounds in A: (i) **uniform** (TM) vs **nonuniform**
(per-length circuit); (ii) **input encoding** `List Bool` vs `Fin n → Bool`; (iii) the file is **off-limits**.

### C. What does *not* exist in the clean layers

No boolean-language type, no circuit *family* (one circuit per length), no poly-size/const-depth *class*,
no asymptotic ("for all large n") wrapper. Confirmed by search: none in `…Layer3*`, `…Layer4*`,
`…Rung4CircuitReal`. **This is the layer to build (small, fresh, nonuniform).**

---

## 2. Can `parity_function_lower_bound` imply an "`NP ∉ AC⁰[p]`"-style corollary?

Distinguish three levels (do **not** conflate):

* **Level 1 — per-length nonuniform.** *Already proved.* "No depth-`d`, size-`≤ p^t/4` `AC⁰[p]` circuit
  computes parity at length `2m+1` (in the band regime)." Direct reading of `parity_function_lower_bound`.

* **Level 2 — circuit-family nonuniform.** *Reachable; the honest new content.* "No constant-depth,
  polynomially-size-bounded `AC⁰[p]` circuit **family** computes the PARITY language." Obtained by
  instantiating `parity_function_lower_bound` at lengths `2m+1` and using that `p^t` (exponential in the
  horizon `t`) outgrows any fixed polynomial size bound. **Needs the small Layer-7 family layer + one
  exp-beats-poly arithmetic lemma — nothing open.**

* **Level 3 — uniform `NP`-class containment.** *Not cleanly reachable, and shallow even if forced.*
  Requires the TM `NP` (off-limits `Step4Compiler`), a `List Bool ↔ Fin n → Bool` encoding bridge, and a
  uniform↔nonuniform bridge. Moreover PARITY ∈ P ⊆ NP, so "∃ language in NP outside `AC⁰[p]`" is **RS
  repackaged**, not a new separation — it says nothing about hard `NP` languages. **Out of honest scope.**

**Answer:** yes at **level 2** (a genuine, new-to-the-repo, *non-open* corollary); **no** at level 3 in any
non-shallow, in-scope sense.

---

## 3. What exact theorem statement is honest?

The **level-2** statement, phrased over a small fresh nonuniform layer (names indicative):

```lean
/-- A boolean language as a length-indexed family of predicates on `Fin n → Bool`. -/
def BoolLang : Type := (n : ℕ) → (Fin n → Bool) → Bool

/-- The PARITY language. -/
def parityLang : BoolLang :=
  fun _ x => decide (Odd (Finset.univ.filter (fun i => x i = true)).card)

/-- A constant-depth `AC⁰[p]` circuit family with a per-length size bound. -/
structure AC0pFamily (p : ℕ) where
  circ        : (n : ℕ) → BoolCircuitSyntax n
  isAC0p      : ∀ n, IsAC0pSyntax p (circ n)
  depthBound  : ℕ
  hdepth      : ∀ n, (circ n).depth ≤ depthBound
  sizeBound   : ℕ → ℕ
  hsize       : ∀ n, (subcircuits (circ n)).toFinset.card ≤ sizeBound n

def Computes (p : ℕ) (F : AC0pFamily p) (L : BoolLang) : Prop :=
  ∀ n x, (F.circ n).eval x = L n x

/-- *HONEST TARGET (NOT yet proved; NOT P≠NP; NOT a hard-NP separation).*
No constant-depth, polynomially-bounded `AC⁰[p]` family computes PARITY. -/
theorem parity_not_in_nonuniform_AC0p
    (p : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (F : AC0pFamily p) (hpoly : IsPolyBounded F.sizeBound) :
    ¬ Computes p F parityLang
```

**Proof mechanism (to be built, not claimed here):** assume `Computes`. Fix the family's `d := depthBound`
and poly size bound `S := sizeBound`. For a horizon `t`, set the minimal admissible length via
`m := 8·((p-1)t)^{2d}` (so `hm` holds). At `n = 2m+1`, `F.circ n` computes parity (`Computes`), is `AC⁰[p]`
(`isAC0p`), has `depth ≤ d` (`hdepth`); so `parity_function_lower_bound` gives
`p^t < 4·#subcircuits ≤ 4·S(2m+1)`. But `S(2m+1)` is polynomial in `t` (its argument is poly in `t`), while
`p^t` is exponential in `t`; so for large enough `t`, `p^t ≥ 4·S(2m+1)` — contradiction. The only nontrivial
ingredient is **"exponential beats polynomial in `t`"** (existence of such a `t`).

**Honesty annotations that must accompany the statement:**
* This is a **nonuniform circuit-family** lower bound for an **explicit, easy (P-computable)** language.
* It is **not** `P ≠ NP`, **not** `NP ⊄ AC⁰[p]` in any deep sense, **not** a statement about hard `NP`
  functions. PARITY ∈ P ⊆ NP, so any "in NP" framing is shallow and definition-dependent (§2 level 3).
* `MOD_q` admits the identical packaging via `mod_q_family_false` (optional second corollary).

---

## 4. What needs to be built first?

In dependency order (each small, sorry-free, no custom axioms, separate buildable commit):

1. **`BoolLang`, `parityLang`** — trivial definitions (new file, e.g. `…Layer7CircuitFamily.lean`).
2. **`AC0pFamily p`, `Computes`** — the family structure + the "computes a language" predicate.
3. **`IsPolyBounded : (ℕ → ℕ) → Prop`** — a self-contained poly-bound predicate
   (`∃ a c b, ∀ n, f n ≤ a·n^c + b`); do **not** reuse the off-limits `Step4Compiler.IsPoly`.
4. **Exp-beats-poly lemma** — `∀ (p ≥ 2) (poly bound), ∃ t, p^t ≥ 4·(poly evaluated at 16((p-1)t)^{2d}+1)`.
   The one genuinely arithmetic step; elementary (Nat growth), but the real work of the corollary.
5. **`parity_not_in_nonuniform_AC0p`** — assemble 1–4 with `parity_function_lower_bound`.
6. *(optional)* `modq_not_in_nonuniform_AC0p` via `mod_q_family_false`; asymptotic restatements.

**Build/commit protocol:** after each step, `lake build` the new file + `#print axioms` the capstone
(expect `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`); push. Do not edit Layer 3/4 theorem
files or `Step4Compiler.lean`. If step 4's arithmetic is fiddly, isolate it as its own lemma before the
assembly — never `sorry` it.

**Reconfirmed scope guardrails:** target is level 2 only; level-3/`NP`-class framing stays out; no
`P≠NP` claims; open frontiers (ACC⁰, Williams, general circuits) untouched.

---

## Status (level 2 — DONE, sorry-free)

* `ComputationalDepthLayer7CircuitFamily` — `BoolLang`, `parityLang`, `AC0pFamily`, `Computes`,
  `IsPolyBounded` (the nonuniform layer).
* `ComputationalDepthLayer7ParityFamily` — `exists_poly_lt_pow` (exp beats poly) and
  **`parity_not_in_nonuniform_AC0p`** (PARITY ∉ nonuniform `AC⁰[p]`).
* `ComputationalDepthLayer7ModqFamily` — `modqLang` and **`modq_not_in_nonuniform_AC0p`** (`MOD_q` ∉
  nonuniform `AC⁰[p]`, distinct primes `p ≠ q`).

All `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.  Level 3 / `NP`-class / `P≠NP` remain
explicitly out of scope (open or shallow-definitional), as analysed above.
