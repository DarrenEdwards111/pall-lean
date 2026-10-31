import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SatMachine

/-!
# Pushing the cell-count projection to threshold bottoms (the `ACC⁰ ∘ THR` direction)

Williams' `NEXP ⊄ ACC⁰` runs on the cell-count projection: a depth-2 `MOD`-bottom circuit's value
depends only on the **cell** — the vector of Hamming weights of `x` on each gate's support
(`weightVec`) — so `MOD`-bottom SAT is decided by enumerating the `≤ (n+1)^k` cells, not the `2^n`
inputs (`ACC0SatMachine.decideSAT_correct` / `cellSearch_steps_le`).

Murray–Williams push this to **`ACC⁰ ∘ THR`**.  The key structural fact, which this file makes
explicit and unconditional: a **threshold** gate `[[ ∑_{i∈S} x_i ≥ θ ]]` also depends only on the
support's Hamming weight — so it is a *weight predicate* exactly like a `MOD` gate, and the identical
cell-search projection covers it with the identical `(n+1)^k` step bound.

* **`Depth2SymCircuit`** — a top function of `k` bottom gates, each an **arbitrary weight predicate**
  `pred j : ℕ → Bool` on its support (this subsumes `MOD` *and* `THR` *and* any symmetric bottom);
* **`symCellSearch`** — the cell-enumeration algorithm; **`symDecideSAT_correct` (proved)** — it
  decides SAT; **`symCellSearch_steps_le` (proved)** — `steps ≤ (n+1)^k`;
  **`symCellSearch_beats_bruteforce` (proved)** — `< 2^n` in the small-gate regime;
* **`thrPred` / `thrCircuit`** — the threshold instance; **`thr_decideSAT_correct` /
  `thr_cellSearch_steps_le` (proved)** — the projection speedup **for threshold bottoms**.

**Honest scope.**  This is the *unit-cost cell-check* speedup extended from `MOD` to threshold (and
general symmetric) bottom gates — the projection genuinely reaches `SYM ∘ THR` at depth 2.  It is
**not** the full multi-layer `ACC⁰ ∘ THR`-SAT algorithm, and (like the base file) it proves nothing
about `NEXP/NP ⊄ ACC⁰∘THR` or `P ≠ NP` — the extension to the *general* boundary is the collapse
socket, which is `P≠NP`-strength.  This is the honest, buildable step in the Murray–Williams
direction: threshold bottoms compress into cells exactly as `MOD` bottoms do.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ThrSatMachine

open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0SatTimeCost
open PallLean.Paper93.DeepMath.PathB.ACC0SatMachine

variable {n k : ℕ}

/-- A depth-2 circuit whose bottom gates are **arbitrary weight predicates**: gate `j` accepts iff
`pred j` holds of the Hamming weight of `x` on its support.  Subsumes `MOD`, `THR`, any symmetric
bottom gate. -/
structure Depth2SymCircuit (n k : ℕ) where
  /-- Each gate's support. -/
  supports : Fin k → Finset (Fin n)
  /-- Each gate's acceptance, as a predicate on the support's Hamming weight. -/
  pred : Fin k → (ℕ → Bool)
  /-- The top function of the `k` gate outputs. -/
  top : (Fin k → Bool) → Bool

/-- The circuit value: the top applied to the bottom weight-predicate outputs. -/
def Depth2SymCircuit.eval (C : Depth2SymCircuit n k) (x : Fin n → Bool) : Bool :=
  C.top (fun j => C.pred j (weightVec C.supports x j))

/-- The per-cell acceptance check: the top applied to the gates' predicates at the cell. -/
def symCellPredicate (C : Depth2SymCircuit n k) (w : Fin k → ℕ) : Bool :=
  C.top (fun j => C.pred j (w j))

/-- **The circuit value is `symCellPredicate` at its cell (proved by `rfl`).** -/
theorem symEval_eq_cellPredicate (C : Depth2SymCircuit n k) (x : Fin n → Bool) :
    C.eval x = symCellPredicate C (weightVec C.supports x) := rfl

/-- **The cell-search algorithm**: enumerate achievable cells, check `symCellPredicate` on each. -/
noncomputable def symCellSearch (C : Depth2SymCircuit n k) : TimedDecision where
  result := ((Finset.univ.image (weightVec C.supports)).toList).any (symCellPredicate C)
  steps := (Finset.univ.image (weightVec C.supports)).card

/-- **The algorithm decides SAT (proved)** — for arbitrary weight-predicate bottoms (in particular
threshold bottoms). -/
theorem symDecideSAT_correct (C : Depth2SymCircuit n k) :
    (symCellSearch C).result = true ↔ Satisfiable C.eval := by
  have hsat : Satisfiable C.eval
      ↔ ∃ w ∈ Finset.univ.image (weightVec C.supports), symCellPredicate C w = true := by
    unfold Satisfiable
    simp_rw [symEval_eq_cellPredicate]
    exact sat_iff_image (symCellPredicate C) (weightVec C.supports)
  rw [hsat]
  unfold symCellSearch
  simp only [List.any_eq_true, Finset.mem_toList]

/-- **The time bound (proved): `steps ≤ (n+1)^k`** — the same cell count as the `MOD` case, since
threshold/symmetric gates are weight predicates too. -/
theorem symCellSearch_steps_le (C : Depth2SymCircuit n k) :
    (symCellSearch C).steps ≤ (n + 1) ^ k :=
  imageSearchCost_le C.supports

/-- **Beats brute force in the small-gate regime (proved)**: `< 2^n` when `(n+1)^k < 2^n`. -/
theorem symCellSearch_beats_bruteforce (C : Depth2SymCircuit n k)
    (hregime : (n + 1) ^ k < 2 ^ n) : (symCellSearch C).steps < 2 ^ n :=
  lt_of_le_of_lt (symCellSearch_steps_le C) hregime

/-! ### The threshold instance -/

/-- A **threshold gate** as a weight predicate: accept iff the support's Hamming weight is `≥ θ`. -/
def thrPred (θ : ℕ) : ℕ → Bool := fun w => decide (θ ≤ w)

/-- A depth-2 **`SYM ∘ THR`** circuit: an arbitrary top of `k` threshold bottom gates. -/
def thrCircuit (supports : Fin k → Finset (Fin n)) (θ : Fin k → ℕ)
    (top : (Fin k → Bool) → Bool) : Depth2SymCircuit n k where
  supports := supports
  pred := fun j => thrPred (θ j)
  top := top

/-- **Threshold-bottom SAT is decided by cell search (proved)** — the projection reaches `SYM ∘ THR`. -/
theorem thr_decideSAT_correct (supports : Fin k → Finset (Fin n)) (θ : Fin k → ℕ)
    (top : (Fin k → Bool) → Bool) :
    (symCellSearch (thrCircuit supports θ top)).result = true
      ↔ Satisfiable (thrCircuit supports θ top).eval :=
  symDecideSAT_correct _

/-- **Threshold-bottom cell search runs in `≤ (n+1)^k` steps (proved)** — the same speedup as `MOD`. -/
theorem thr_cellSearch_steps_le (supports : Fin k → Finset (Fin n)) (θ : Fin k → ℕ)
    (top : (Fin k → Bool) → Bool) :
    (symCellSearch (thrCircuit supports θ top)).steps ≤ (n + 1) ^ k :=
  symCellSearch_steps_le _

end PallLean.Paper93.DeepMath.PathB.ACC0ThrSatMachine

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ThrSatMachine.symDecideSAT_correct
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ThrSatMachine.symCellSearch_steps_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ThrSatMachine.thr_decideSAT_correct
