import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Agreement

/-!
# Layer 7 (open frontier) — nonuniform circuit-family scaffolding

The small, self-contained **nonuniform** layer for the honest Route-B / level-2 target of
`SCOPE_LAYER7_COMPLEXITY_CLASS_BRIDGE.md`: stating circuit lower bounds at the level of a *language* and a
*circuit family* (one circuit per input length), rather than the per-length single-circuit form of
`parity_function_lower_bound`.

**This file is definitions only — no theorem claims, no lower bound proved here.**  It is deliberately
*independent* of the off-limits, TM/`List Bool`-based `P`/`NP`/`Language` in `Step4Compiler.lean`
(uniform, encoding-mismatched). Everything here is over the clean `BoolCircuitSyntax` (`Fin n → Bool`)
model.

Scope reminder (honest framing, to be attached to any eventual corollary): the target
`parity_not_in_nonuniform_AC0p` is a **nonuniform circuit-family** lower bound for an **explicit, easy
(P-computable)** language.  It is **not** `P ≠ NP`, **not** `NP ⊄ AC⁰[p]` in any deep sense, and **not** a
statement about hard `NP` functions.

Contents:
* `BoolLang` — a boolean language as a length-indexed family of predicates.
* `parityLang` — the PARITY language.
* `AC0pFamily p` — a constant-depth `AC⁰[p]` circuit family with a per-length size bound.
* `AC0pFamily.Computes` — the family computes a language.
* `IsPolyBounded` — a self-contained polynomial-growth predicate (not `Step4Compiler.IsPoly`).
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer7

open PallLean.Paper93.DeepMath.PathB

/-- A **boolean language** as a length-indexed family of predicates on `Fin n → Bool`.  (Deliberately on
`Fin n → Bool`, matching `BoolCircuitSyntax`, not the `List Bool` of the off-limits TM layer.) -/
def BoolLang : Type := (n : ℕ) → (Fin n → Bool) → Bool

/-- The **PARITY language**: at each length, `true` iff the input has an odd number of `true`s. -/
def parityLang : BoolLang :=
  fun _ x => decide (Odd (Finset.univ.filter (fun i => x i = true)).card)

open Classical in
/-- A **constant-depth `AC⁰[p]` circuit family** with a per-length size bound: one circuit `circ n` per
input length `n`, each `AC⁰[p]`, all of depth `≤ depthBound`, with `#subcircuits (circ n) ≤ sizeBound n`
(size measured exactly as in the Razborov–Smolensky development). -/
structure AC0pFamily (p : ℕ) where
  /-- The circuit at each input length. -/
  circ : (n : ℕ) → BoolCircuitSyntax n
  /-- Each circuit uses only Boolean gates and `MOD p` gates. -/
  isAC0p : ∀ n, BoolCircuitSyntax.IsAC0pSyntax p (circ n)
  /-- The common (constant) depth bound. -/
  depthBound : ℕ
  /-- Every circuit has depth at most `depthBound`. -/
  hdepth : ∀ n, (circ n).depth ≤ depthBound
  /-- The per-length size bound. -/
  sizeBound : ℕ → ℕ
  /-- Every circuit has at most `sizeBound n` distinct subcircuits (the RS size measure). -/
  hsize : ∀ n, (Layer3.subcircuits (circ n)).toFinset.card ≤ sizeBound n

/-- The family **computes** the language `L`: at every length, the circuit agrees with `L`. -/
def AC0pFamily.Computes {p : ℕ} (F : AC0pFamily p) (L : BoolLang) : Prop :=
  ∀ (n : ℕ) (x : Fin n → Bool), (F.circ n).eval x = L n x

/-- A self-contained **polynomial-growth** predicate `f n ≤ a·n^c + b` (independent of the off-limits
`Step4Compiler.IsPoly`). -/
def IsPolyBounded (f : ℕ → ℕ) : Prop :=
  ∃ a c b : ℕ, ∀ n, f n ≤ a * n ^ c + b

/-- Sanity check: a literal polynomial bound is `IsPolyBounded`. -/
theorem isPolyBounded_poly (a c b : ℕ) : IsPolyBounded (fun n => a * n ^ c + b) :=
  ⟨a, c, b, fun _ => le_refl _⟩

end PallLean.Paper93.DeepMath.PathB.Layer7

#print axioms PallLean.Paper93.DeepMath.PathB.Layer7.parityLang
#print axioms PallLean.Paper93.DeepMath.PathB.Layer7.AC0pFamily.Computes
#print axioms PallLean.Paper93.DeepMath.PathB.Layer7.isPolyBounded_poly
