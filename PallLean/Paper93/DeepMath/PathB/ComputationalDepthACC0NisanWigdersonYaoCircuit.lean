import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NisanWigdersonYao

/-!
# Yao predictor circuit efficiency — the predictor is a small circuit (proved)

Entry 193 proved Yao's predict-from-distinguish *success identity* and left **`YaoCircuitEfficiency`** as the residual
socket: the predictor derived from the distinguisher is a **small circuit** (the distinguisher is a bounded-size circuit,
hence so is the predictor).  Entry 195 noted this is exactly the gate-count content the semantic model does not capture.
This file discharges it by building a minimal but real **gate-level Boolean circuit syntax** (with an explicit `size`
gate-count and `eval` semantics), constructing the Yao predictor *circuit*, and proving its **exact size overhead** and
its **semantic correctness**.

The Yao predictor.  Given a distinguisher circuit `D` and the guessed-bit input index `gidx`, the predictor outputs
`g ⊕ ¬D(x)` (where `g = x gidx`): if `D` accepts (`D(x)=1`, so `¬D=0`) it outputs the guess `g`; if `D` rejects it
outputs the flipped guess `¬g` — exactly the guess-and-correct predictor of entry 193.  As a circuit it is
`cxor (var gidx) (cnot D)`, which **references `D` only once** and adds just three gates (`cxor`, `cnot`, the input read),
so `size(predictor) = size(D) + 3`.  (The `cxor` gate is `MOD₂`, which lies in `ACC⁰`, so the predictor stays in the
distinguisher's class.)

## What is proved (clean axioms, no `sorry`)

* **`Circ`** / **`Circ.size`** / **`Circ.eval`** — a Boolean circuit syntax over `n` inputs (basis `var, ⊤, ⊥, ¬, ∧,
  ∨, ⊕`), with a gate-count `size` and a Boolean-valued semantics `eval`.
* **`yao_predictor_size`** — the exact size overhead: `size (predictor D gidx) = size D + 3`.
* **`yao_predictor_eval`** — semantic correctness: `eval (predictor D gidx) x = if D(x) then g else ¬g`, the Yao
  guess-and-correct rule.
* **`smallPredictor_exists`** — the predictor is a *small circuit* computing the Yao rule: a circuit of size `≤ size D +
  3` realising the mux.
* **`yaoCircuitEfficiency_discharge`** — discharges the **entry-193 `YaoCircuitEfficiency` socket**: from the Yao
  next-bit predictor, the predictor is realisable as a small circuit (size within `+3` of the distinguisher).

## Honest scope

This builds a genuine gate-level circuit model (a syntactic circuit with an explicit gate count) and proves the Yao
**circuit efficiency** — the derived predictor circuit has size within an additive constant (`+3`) of the distinguisher
and computes the correct guess-and-correct function.  This is the gate-count fact the entry-195 semantic model omits.
The model is a *tree* circuit; the `+3` overhead references `D` once (no blow-up) because the construction is a single
`cxor` of an input with `¬D`.  This does not formalise `ACC⁰` *membership* of `D` itself (depth/gate-type constraints),
only the additive size overhead of the Yao step; combined with entries 193–195 it completes the Yao→predictor→
reconstruction chain at the level of *success, size, and correctness*.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonYaoCircuit

open PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonYao (YaoCircuitEfficiency)

/-- **A Boolean circuit over `n` inputs.**  Basis: input variables, the constants, NOT, AND, OR, and XOR (`= MOD₂`,
within `ACC⁰`). -/
inductive Circ (n : ℕ) where
  | var : Fin n → Circ n
  | tru : Circ n
  | fals : Circ n
  | cnot : Circ n → Circ n
  | cand : Circ n → Circ n → Circ n
  | cor : Circ n → Circ n → Circ n
  | cxor : Circ n → Circ n → Circ n

namespace Circ

/-- **Gate count.**  The number of nodes (gates and leaves) of a circuit. -/
def size {n : ℕ} : Circ n → ℕ
  | var _ => 1
  | tru => 1
  | fals => 1
  | cnot c => 1 + size c
  | cand a b => 1 + size a + size b
  | cor a b => 1 + size a + size b
  | cxor a b => 1 + size a + size b

/-- **Circuit semantics.**  The Boolean value computed on an input assignment `x : Fin n → Bool`. -/
def eval {n : ℕ} : Circ n → (Fin n → Bool) → Bool
  | var i, x => x i
  | tru, _ => true
  | fals, _ => false
  | cnot c, x => !(eval c x)
  | cand a b, x => eval a x && eval b x
  | cor a b, x => eval a x || eval b x
  | cxor a b, x => (eval a x) ^^ (eval b x)

end Circ

open Circ

/-- **The Yao predictor circuit.**  `predictor D gidx := (x gidx) ⊕ ¬D` — outputs the guessed bit `g = x gidx` if `D`
accepts, the flipped guess `¬g` otherwise.  It references `D` exactly once. -/
def predictor {n : ℕ} (D : Circ n) (gidx : Fin n) : Circ n :=
  cxor (var gidx) (cnot D)

/-- **The Yao predictor's exact size overhead (PROVED).**  `size (predictor D gidx) = size D + 3` — the predictor adds
exactly three gates (`cxor`, `cnot`, and the input read) on top of the distinguisher, with `D` referenced once. -/
theorem yao_predictor_size {n : ℕ} (D : Circ n) (gidx : Fin n) :
    (predictor D gidx).size = D.size + 3 := by
  simp only [predictor, Circ.size]; ring

/-- **The Yao predictor's semantic correctness (PROVED).**  `eval (predictor D gidx) x` equals the guess-and-correct
rule: the guess `x gidx` when `D` accepts, the flipped guess otherwise — matching the entry-193 construction. -/
theorem yao_predictor_eval {n : ℕ} (D : Circ n) (gidx : Fin n) (x : Fin n → Bool) :
    (predictor D gidx).eval x = (if D.eval x then x gidx else !(x gidx)) := by
  simp only [predictor, Circ.eval]
  cases hD : D.eval x <;> cases hg : x gidx <;> rfl

/-- **A small predictor circuit computing the Yao rule.**  There exists a circuit of size `≤ size D + 3` that computes
the guess-and-correct function `if D(x) then g else ¬g`. -/
def SmallPredictor {n : ℕ} (D : Circ n) (gidx : Fin n) : Prop :=
  ∃ P : Circ n, P.size ≤ D.size + 3 ∧
    ∀ x, P.eval x = (if D.eval x then x gidx else !(x gidx))

/-- **The Yao predictor is a small circuit (PROVED).**  The witness is `predictor D gidx`: size exactly `size D + 3`
(`yao_predictor_size`) and computing the guess-and-correct rule (`yao_predictor_eval`). -/
theorem smallPredictor_exists {n : ℕ} (D : Circ n) (gidx : Fin n) : SmallPredictor D gidx :=
  ⟨predictor D gidx, le_of_eq (yao_predictor_size D gidx), yao_predictor_eval D gidx⟩

/-- **Discharging the entry-193 `YaoCircuitEfficiency` socket (PROVED).**  Given the Yao next-bit predictor (the
guess-and-correct rule from the distinguishing advantage), the predictor is realisable as a *small circuit* — of size
within an additive `+3` of the distinguisher `D` — by `smallPredictor_exists`.  This is the gate-count content the
entry-195 semantic model omits, now proved over an explicit circuit syntax. -/
theorem yaoCircuitEfficiency_discharge {n : ℕ} (D : Circ n) (gidx : Fin n) (YaoNextBit : Prop) :
    YaoCircuitEfficiency YaoNextBit (SmallPredictor D gidx) :=
  fun _ => smallPredictor_exists D gidx

end PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonYaoCircuit

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonYaoCircuit.yao_predictor_size
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonYaoCircuit.yao_predictor_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonYaoCircuit.yaoCircuitEfficiency_discharge
