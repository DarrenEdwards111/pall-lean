import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer10Monotone
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer7CircuitFamily

/-!
# Layer 11 — the real DAG / straight-line circuit model (with gate sharing)

The honest fix demanded by `SCOPE_MODEL_FORMULA_CORRECTION.md`: a genuine **circuit** model where a gate's
output is computed once and may feed many later gates **at no extra size** — i.e. fan-out > 1 / sharing.
This is the model underlying `P/poly`; the Layer 8–10 inductive `Circuit` is a *tree* (formula), this is a
*DAG*.

* `GateN` / `DagCircuit` — a straight-line program: a list of gates (each referencing earlier wires by
  index) and an output wire.  Wire `i < n` is input `i`; gate `k` produces wire `n+k`.
* `DagCircuit.eval` — compute every wire left-to-right (each wire stored once; **sharing is free**) and read
  the output.  `DagCircuit.size` = number of gates.
* `SIZE_dag` / `Ppoly_dag` / `PpolyClass_dag` — `SIZE(s)` and **`P/poly`** over the DAG model (now genuinely
  `P/poly`, not `NC¹`).
* `np_not_subset_ppoly_dag`, `p_ne_np_of_np_hard_dag` — the Layer 10B bridges, **now over the correct
  model**: `hPsub : P ⊆ PpolyClass_dag` is the *true* standard inclusion `P ⊆ P/poly`, not the dubious
  `P ⊆ NC¹`.  (The proofs are model-agnostic set logic.)

## Sharing is real (demonstrations)

* `parity3Dag` — a linear (`8`-gate) DAG circuit computing `parityFn 3` (`native_decide`-verified), **below**
  the `khrap` formula lower bound `9` for `parityFn 3`.  As `n` grows the gap widens (linear DAG vs `n²`
  formula) — this is exactly the circuit/formula separation the tree model could not express.
* `sharing_demo` — a `3`-gate circuit where wire `2` feeds two later gates; a formula would recompute it.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer11

open PallLean.Paper93.DeepMath.PathB

/-- A gate in a straight-line program, referencing earlier wires by index. -/
inductive GateN
  | const : Bool → GateN
  | not : ℕ → GateN
  | and : ℕ → ℕ → GateN
  | or : ℕ → ℕ → GateN

/-- Evaluate a gate against the wire values computed so far (`getD … false` for out-of-range refs, which
forces references to be to *earlier* wires). -/
def GateN.eval (acc : List Bool) : GateN → Bool
  | .const b => b
  | .not i => !(acc.getD i false)
  | .and i j => (acc.getD i false) && (acc.getD j false)
  | .or i j => (acc.getD i false) || (acc.getD j false)

/-- A **DAG circuit** (straight-line program) on `n` inputs: a list of gates and an output wire.  Wire
`i < n` is input `i`; gate `k` produces wire `n+k`. -/
structure DagCircuit (n : ℕ) where
  gates : List GateN
  out : ℕ

/-- Evaluation: compute each wire once, left-to-right — a gate value is stored and may be referenced by
arbitrarily many later gates, so **sharing costs nothing** — then read the output wire. -/
def DagCircuit.eval {n : ℕ} (C : DagCircuit n) (x : Fin n → Bool) : Bool :=
  let inputs : List Bool := (List.finRange n).map x
  (C.gates.foldl (fun acc g => acc ++ [g.eval acc]) inputs).getD C.out false

/-- **DAG circuit size** = number of gates (independent of fan-out). -/
def DagCircuit.size {n : ℕ} (C : DagCircuit n) : ℕ := C.gates.length

/-- `SIZE(s)` over the DAG model. -/
def SIZE_dag (n s : ℕ) : Set ((Fin n → Bool) → Bool) :=
  {f | ∃ C : DagCircuit n, C.size ≤ s ∧ ∀ x, C.eval x = f x}

/-- **`P/poly`** over the DAG model — the genuine `P/poly`. -/
def Ppoly_dag (L : Layer7.BoolLang) : Prop :=
  ∃ p : ℕ → ℕ, Layer7.IsPolyBounded p ∧ ∀ n, (fun x => L n x) ∈ SIZE_dag n (p n)

/-- `P/poly` as a class. -/
def PpolyClass_dag : Set Layer7.BoolLang := {L | Ppoly_dag L}

/-- **Bridge 1 (correct model).**  An `NP` language with a super-polynomial **DAG-circuit** lower bound
witnesses `NP ⊄ P/poly`. -/
theorem np_not_subset_ppoly_dag {NP : Set Layer7.BoolLang} {L : Layer7.BoolLang}
    (hLNP : L ∈ NP) (hhard : ¬ Ppoly_dag L) : ¬ (NP ⊆ PpolyClass_dag) :=
  fun hsub => hhard (hsub hLNP)

/-- **Circuit route to `P ≠ NP` (correct model).**  With `P ⊆ P/poly` (now the *genuine* standard
inclusion) and an `NP` language with a super-polynomial DAG-circuit lower bound, `P ≠ NP`.  Both inputs
explicit; the `P ⊆ P/poly` premise is no longer the dubious `P ⊆ NC¹`. -/
theorem p_ne_np_of_np_hard_dag {P NP : Set Layer7.BoolLang} (hPsub : P ⊆ PpolyClass_dag)
    {L : Layer7.BoolLang} (hLNP : L ∈ NP) (hhard : ¬ Ppoly_dag L) : P ≠ NP :=
  fun hPeqNP => (np_not_subset_ppoly_dag hLNP hhard) (hPeqNP ▸ hPsub)

/-! ### Sharing is real -/

/-- A linear (`8`-gate) DAG circuit for `parityFn 3` (each XOR `= (a∨b)∧¬(a∧b)`, chained). -/
def parity3Dag : DagCircuit 3 :=
  ⟨[.or 0 1, .and 0 1, .not 4, .and 3 5, .or 6 2, .and 6 2, .not 8, .and 7 9], 10⟩

theorem parity3Dag_size : parity3Dag.size = 8 := rfl

/-- The `8`-gate DAG circuit computes PARITY on `3` bits — below the `n²=9` formula bound (`khrap`). -/
theorem parity3Dag_correct : ∀ x : Fin 3 → Bool, parity3Dag.eval x = Layer10.parityFn 3 x := by
  native_decide

/-- Sharing demo: wire `2` (`= x₀∧x₁`) feeds two later gates; size `3`, computed once. -/
theorem sharing_demo : ∀ x : Fin 2 → Bool,
    DagCircuit.eval (n := 2) ⟨[.and 0 1, .not 2, .or 2 3], 4⟩ x = true := by native_decide

end PallLean.Paper93.DeepMath.PathB.Layer11

#print axioms PallLean.Paper93.DeepMath.PathB.Layer11.p_ne_np_of_np_hard_dag
#print axioms PallLean.Paper93.DeepMath.PathB.Layer11.parity3Dag_correct
