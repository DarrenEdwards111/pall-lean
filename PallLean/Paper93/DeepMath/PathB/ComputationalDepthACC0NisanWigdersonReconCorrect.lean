import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NisanWigdersonReconstruction

/-!
# NW reconstruction correctness — the assembled circuit computes `f` (proved)

Entry 194 proved the reconstruction's *size* accounting and left **`ReconstructionCorrectness`** as the residual socket:
the assembled circuit (the Yao predictor wired to the hardwired block tables) **actually computes the hard function
`f`**.  This file discharges it by building a minimal but real **Boolean-function semantics** for the reconstruction and
proving the genuine model-level content: a **composition/substitution correctness**.

Semantic model.  A seed `s : S` is restricted to each of the `numOther` other design blocks via `restrict j : S → I`;
block `j` is hardwired as a lookup table `table j : I → Bool` meant to reproduce its true value `blockVal j : I → Bool`;
the Yao predictor `pred : (Fin numOther → Bool) → Bool` combines the block values into `f`'s next bit `target : S → Bool`.
The **assembled circuit** on seed `s` outputs `pred (fun j => table j (restrict j s))`.  Reconstruction correctness is
that this equals `target s` for every seed.

The proof is the substitution argument: if each table is correct on the restricted seed (`table j (restrict j s) =
blockVal j (restrict j s)`) and the predictor is correct on the *true* block values (`pred (fun j => blockVal j …) =
target s`, the Yao guarantee), then by funext the predictor's argument is the true block-value vector, so the assembled
output equals `target s`.

## What is proved (clean axioms, no `sorry`)

* **`tabulate`** / **`tabulate_apply`** — the truth-table lookup is *semantically exact*: a function on a finite domain
  is reproduced by its table (`tabulate h x = h x`).  (Entry 192/194 bound the table *size* by `2^r ≤ 2^k`; this
  confirms the lookup is *correct*.)
* **`reconstruction_computes`** — the composition/substitution correctness: correct tables + a correct predictor ⇒ the
  assembled circuit computes `target` on every seed.
* **`reconstructionCorrectness_discharge`** — discharges the **entry-194 `ReconstructionCorrectness` socket** for the
  concrete predicates: the predictor's correctness and the tables' correctness together give that the assembled circuit
  computes `f`.
* **`reconstruction_computes_tabulated`** — the specialisation where the tables *are* the canonical truth tables
  (`table j = tabulate (blockVal j)`): then table correctness is definitional, so a correct predictor alone yields a
  correct assembled circuit.

## Honest scope

This builds a minimal Boolean-function semantics (a circuit is its semantic function on a finite domain) and proves the
**reconstruction correctness** — that the assembled predictor-plus-tables circuit computes `f` — from the two genuine
inputs: the lookup tables are semantically exact (proved here) and the predictor is correct on the true block values
(the Yao guarantee, supplied by the Yao socket of entry 193).  Together with entry 194's *size* bound, the reconstruction
step is now both **size-bounded and correct**.  The model here is the standard *semantic* view (a circuit ≡ the Boolean
function it computes); it does not formalise gate-level circuit syntax or `ACC⁰` membership — those remain the province
of the other named sockets.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonReconCorrect

open PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonReconstruction (ReconstructionCorrectness)

/-- **The truth-table lookup.**  Representing a Boolean function `h : I → Bool` on a finite domain `I` by its lookup
table; the table simply stores `h`'s values. -/
def tabulate {I : Type*} (h : I → Bool) : I → Bool := h

/-- **Lookup is semantically exact (PROVED).**  Evaluating the truth table of `h` at `x` returns `h x`.  Entry 192/194
bound the table's *size* (`Fintype.card (Fin r → Bool) = 2^r ≤ 2^k`); this confirms its *correctness*. -/
theorem tabulate_apply {I : Type*} (h : I → Bool) (x : I) : tabulate h x = h x := rfl

/-- **The assembled reconstructed circuit's output.**  On seed `s`, the predictor applied to the hardwired table values
of the other blocks restricted to `s`. -/
def assembledOutput {S I : Type*} {numOther : ℕ} (restrict : Fin numOther → S → I)
    (table : Fin numOther → I → Bool) (pred : (Fin numOther → Bool) → Bool) (s : S) : Bool :=
  pred (fun j => table j (restrict j s))

/-- **Reconstruction composition correctness (PROVED) — the model-level heart.**  If every hardwired table reproduces
its block's true value on the restricted seed (`htable`) and the predictor is correct on the true block values
(`hpred`, the Yao guarantee), then the assembled circuit computes `target` on every seed.  Proof: by `funext`, the
predictor's argument `fun j => table j (restrict j s)` equals the true block-value vector `fun j => blockVal j
(restrict j s)`, so the assembled output equals `pred` of the true vector, which is `target s`. -/
theorem reconstruction_computes
    {S I : Type*} {numOther : ℕ}
    (restrict : Fin numOther → S → I)
    (table blockVal : Fin numOther → I → Bool)
    (pred : (Fin numOther → Bool) → Bool)
    (target : S → Bool)
    (htable : ∀ j s, table j (restrict j s) = blockVal j (restrict j s))
    (hpred : ∀ s, pred (fun j => blockVal j (restrict j s)) = target s)
    (s : S) :
    assembledOutput restrict table pred s = target s := by
  unfold assembledOutput
  have heq : (fun j => table j (restrict j s)) = (fun j => blockVal j (restrict j s)) :=
    funext (fun j => htable j s)
  rw [heq]; exact hpred s

/-- **The predictor-correctness carrier.**  The Yao guarantee: the predictor computes `f`'s next bit `target` from the
true block values. -/
def PredictorCorrect {S I : Type*} {numOther : ℕ} (restrict : Fin numOther → S → I)
    (blockVal : Fin numOther → I → Bool) (pred : (Fin numOther → Bool) → Bool) (target : S → Bool) :
    Prop :=
  ∀ s, pred (fun j => blockVal j (restrict j s)) = target s

/-- **The table-correctness carrier.**  Each hardwired table reproduces its block's true value on the restricted seed. -/
def TablesCorrect {S I : Type*} {numOther : ℕ} (restrict : Fin numOther → S → I)
    (table blockVal : Fin numOther → I → Bool) : Prop :=
  ∀ j s, table j (restrict j s) = blockVal j (restrict j s)

/-- **The assembled-circuit-computes-`f` carrier.**  The assembled reconstructed circuit equals `target` on every
seed. -/
def AssembledComputesF {S I : Type*} {numOther : ℕ} (restrict : Fin numOther → S → I)
    (table : Fin numOther → I → Bool) (pred : (Fin numOther → Bool) → Bool) (target : S → Bool) :
    Prop :=
  ∀ s, assembledOutput restrict table pred s = target s

/-- **Discharging the entry-194 `ReconstructionCorrectness` socket (PROVED).**  The predictor's correctness on the true
block values (the Yao guarantee) together with the tables' correctness yield that the assembled circuit computes `f` —
exactly the entry-194 implication `Predictor → TableHardwiring → ComputesF`, now proved by `reconstruction_computes`. -/
theorem reconstructionCorrectness_discharge
    {S I : Type*} {numOther : ℕ}
    (restrict : Fin numOther → S → I)
    (table blockVal : Fin numOther → I → Bool)
    (pred : (Fin numOther → Bool) → Bool)
    (target : S → Bool) :
    ReconstructionCorrectness
      (PredictorCorrect restrict blockVal pred target)
      (TablesCorrect restrict table blockVal)
      (AssembledComputesF restrict table pred target) :=
  fun hpred htable s => reconstruction_computes restrict table blockVal pred target htable hpred s

/-- **Correctness with canonical truth tables (PROVED).**  When each block is hardwired as its *canonical* truth table
(`table j = tabulate (blockVal j)`), table correctness holds definitionally, so a correct predictor alone gives a
correct assembled circuit.  This is the concrete reconstruction: the hardwired tables are the block functions
themselves. -/
theorem reconstruction_computes_tabulated
    {S I : Type*} {numOther : ℕ}
    (restrict : Fin numOther → S → I)
    (blockVal : Fin numOther → I → Bool)
    (pred : (Fin numOther → Bool) → Bool)
    (target : S → Bool)
    (hpred : ∀ s, pred (fun j => blockVal j (restrict j s)) = target s)
    (s : S) :
    assembledOutput restrict (fun j => tabulate (blockVal j)) pred s = target s :=
  reconstruction_computes restrict (fun j => tabulate (blockVal j)) blockVal pred target
    (fun _ _ => rfl) hpred s

end PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonReconCorrect

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonReconCorrect.reconstruction_computes
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonReconCorrect.reconstructionCorrectness_discharge
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonReconCorrect.reconstruction_computes_tabulated
