import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ThrSatMachine

/-!
# Multi-layer `ACC⁰ ∘ THR`: the top depth is free — only the bottom-gate count matters

`ACC0ThrSatMachine` extended the cell-count projection to threshold bottoms with an *arbitrary top
function*.  This file cashes that out for genuinely **multi-layer** circuits: an `ACC⁰ ∘ THR` circuit
is `k` threshold bottom gates feeding a multi-layer top, and its value is
`top(THR₁(x), …, THRₖ(x))` — a function of the `k` threshold outputs, hence of the **cell** (the
support weights).  So the *entire multi-layer circuit* factors through the same `(n+1)^k` cells, and
the identical cell search decides it — **regardless of the top's depth**.

The point: for `ACC⁰ ∘ THR` the projection speedup depends only on the number of **bottom** threshold
gates `k`, not on how deep the `ACC⁰` above them is.  Multi-layer is handled for free.

* **`TopCirc`** — an arbitrary multi-layer top circuit (`and/or/not/const`) over the `k` gate outputs;
* **`AccThrCircuit`** — `k` threshold bottom gates + a multi-layer `TopCirc` top;
* **`AccThrCircuit.toSym` / `accThr_eval_eq`** — it is a `Depth2SymCircuit` (top = the layered eval);
* **`accThr_decideSAT_correct` (proved)** — cell search decides multi-layer `ACC⁰ ∘ THR` SAT;
* **`accThr_steps_le` / `accThr_beats_bruteforce` (proved)** — in `≤ (n+1)^k` steps, `< 2^n` for
  small `k` — the bound is *independent of the top depth*.

**Honest scope.**  This handles **arbitrary top depth** (so, multi-layer) over `k` threshold bottoms,
in the **small-`k`** regime `(n+1)^k < 2^n`.  It is **not** the full Murray–Williams `ACC⁰ ∘ THR`-SAT
theorem for `poly(n)`-many gates — that needs reducing the *effective bottom-gate count* via a
Beigel–Tarui-style collapse, and threshold gates (unlike `MOD`) resist the low-degree method, which
is exactly the hard technical core there.  Nothing here is `NEXP/NP ⊄ ACC⁰∘THR` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ThrMultiLayer

open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ThrSatMachine

variable {n k : ℕ}

/-- An arbitrary **multi-layer** top circuit over `k` inputs (the bottom-gate outputs). -/
inductive TopCirc (k : ℕ)
  | inp : Fin k → TopCirc k
  | cst : Bool → TopCirc k
  | not : TopCirc k → TopCirc k
  | and : TopCirc k → TopCirc k → TopCirc k
  | or : TopCirc k → TopCirc k → TopCirc k

/-- Evaluation of the multi-layer top. -/
def TopCirc.eval : TopCirc k → (Fin k → Bool) → Bool
  | .inp j, b => b j
  | .cst c, _ => c
  | .not c, b => !(c.eval b)
  | .and c d, b => c.eval b && d.eval b
  | .or c d, b => c.eval b || d.eval b

/-- A **multi-layer `ACC⁰ ∘ THR` circuit**: `k` threshold bottom gates (supports + thresholds), with
an arbitrary multi-layer top over their outputs. -/
structure AccThrCircuit (n k : ℕ) where
  /-- Each bottom threshold gate's support. -/
  supports : Fin k → Finset (Fin n)
  /-- Each bottom threshold gate's threshold. -/
  thr : Fin k → ℕ
  /-- The multi-layer top over the `k` threshold outputs. -/
  topCirc : TopCirc k

/-- The circuit value: the multi-layer top of the threshold outputs. -/
def AccThrCircuit.eval (C : AccThrCircuit n k) (x : Fin n → Bool) : Bool :=
  C.topCirc.eval (fun j => thrPred (C.thr j) (weightVec C.supports x j))

/-- It is a `Depth2SymCircuit` whose top is the layered evaluation — the multi-layer top collapses
into the (arbitrary) top slot. -/
def AccThrCircuit.toSym (C : AccThrCircuit n k) : Depth2SymCircuit n k where
  supports := C.supports
  pred := fun j => thrPred (C.thr j)
  top := C.topCirc.eval

/-- **The multi-layer circuit and its cell form agree (proved by `rfl`).** -/
theorem accThr_eval_eq (C : AccThrCircuit n k) (x : Fin n → Bool) :
    C.eval x = C.toSym.eval x := rfl

/-- **Cell search decides multi-layer `ACC⁰ ∘ THR` SAT (proved)** — independent of the top depth. -/
theorem accThr_decideSAT_correct (C : AccThrCircuit n k) :
    (symCellSearch C.toSym).result = true ↔ Satisfiable C.eval :=
  symDecideSAT_correct C.toSym

/-- **The step bound is independent of the top depth (proved): `≤ (n+1)^k`.** -/
theorem accThr_steps_le (C : AccThrCircuit n k) :
    (symCellSearch C.toSym).steps ≤ (n + 1) ^ k :=
  symCellSearch_steps_le C.toSym

/-- **Beats brute force in the small-`k` regime (proved)** — for any top depth. -/
theorem accThr_beats_bruteforce (C : AccThrCircuit n k) (hregime : (n + 1) ^ k < 2 ^ n) :
    (symCellSearch C.toSym).steps < 2 ^ n :=
  symCellSearch_beats_bruteforce C.toSym hregime

end PallLean.Paper93.DeepMath.PathB.ACC0ThrMultiLayer

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ThrMultiLayer.accThr_decideSAT_correct
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ThrMultiLayer.accThr_steps_le
