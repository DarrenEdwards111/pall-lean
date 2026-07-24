import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRelativizationBarrier

/-!
# A concrete oracle-circuit model instantiating the relativization barrier

`RelativizationBarrier` proved the obstruction abstractly, over any oracle-relativized size class
`SIZErel` and any `OracleCollapseBarrier`.  This file builds a **concrete** model and inhabits the
barrier for a **concrete** collapse oracle, so the abstraction is grounded rather than hypothetical.

* **`OCirc n`** — Boolean circuits over `n` inputs with `and/or/not/const` gates **plus oracle gates**
  `oracle k (children)` that query the oracle on the `k` child values.
* **`evalO O c` / `sizeO c`** — evaluation relative to oracle `O`, and gate size.
* **`SIZErelC O n s`** — functions computed by a size-`≤ s` oracle circuit with oracle `O` (a genuine
  `SIZErel` for the abstract framework).
* **`concrete_oracle_collapse`** — the **BGS mechanism, concretely**: relative to the oracle that *is*
  the target language `L`, a single oracle gate on the inputs computes `L n` in size `n + 1`.  So
  `L^O ∈ P^O/poly`, inhabiting `OracleCollapseBarrier L SIZErelC`.
* **`no_relativizing_separatingMeasure_concrete`** — plugging the concrete model into the abstract
  obstruction: **no measure separates `L` relative to every oracle in this real model.**

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.OracleCircuitModel

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.RelativizationBarrier

/-- An **oracle**: a Boolean answer to a query of every arity `k`. -/
abbrev Oracle := (k : ℕ) → (Fin k → Bool) → Bool

/-- **Oracle circuits** over `n` inputs: standard gates plus an arity-`k` oracle gate. -/
inductive OCirc (n : ℕ) : Type
  | inp : Fin n → OCirc n
  | const : Bool → OCirc n
  | not : OCirc n → OCirc n
  | and : OCirc n → OCirc n → OCirc n
  | or : OCirc n → OCirc n → OCirc n
  | oracle : (k : ℕ) → (Fin k → OCirc n) → OCirc n

/-- Evaluation of an oracle circuit relative to oracle `O`. -/
def evalO {n : ℕ} (O : Oracle) : OCirc n → (Fin n → Bool) → Bool
  | .inp i, x => x i
  | .const b, _ => b
  | .not c, x => !(evalO O c x)
  | .and a b, x => evalO O a x && evalO O b x
  | .or a b, x => evalO O a x || evalO O b x
  | .oracle k ch, x => O k (fun i => evalO O (ch i) x)

/-- Gate size of an oracle circuit. -/
def sizeO {n : ℕ} : OCirc n → ℕ
  | .inp _ => 1
  | .const _ => 1
  | .not c => sizeO c + 1
  | .and a b => sizeO a + sizeO b + 1
  | .or a b => sizeO a + sizeO b + 1
  | .oracle k ch => (∑ i, sizeO (ch i)) + 1

/-- **The oracle-relativized size class** `SIZErelC O n s`: functions computed by a size-`≤ s` oracle
circuit with oracle `O`.  This is a concrete `SIZErel` for the abstract framework. -/
def SIZErelC (O : Oracle) (n s : ℕ) : Set ((Fin n → Bool) → Bool) :=
  { f | ∃ c : OCirc n, sizeO c ≤ s ∧ ∀ x, evalO O c x = f x }

/-- The single-oracle-gate circuit that queries the `n` inputs directly. -/
def directQuery (n : ℕ) : OCirc n := .oracle n (fun i => .inp i)

theorem evalO_directQuery {n : ℕ} (O : Oracle) (x : Fin n → Bool) :
    evalO O (directQuery n) x = O n x := rfl

theorem sizeO_directQuery (n : ℕ) : sizeO (directQuery n) = n + 1 := by
  simp only [directQuery, sizeO]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/-- **The concrete collapse oracle (proved)**: relative to the oracle that *is* `L`, the target sits in
size `n + 1` — one oracle gate on the inputs.  Hence `OracleCollapseBarrier L SIZErelC` holds. -/
theorem concrete_oracle_collapse (L : Layer7.BoolLang) :
    OracleCollapseBarrier L SIZErelC := by
  refine ⟨(fun k q => L k q), (fun n => n + 1),
    ⟨2, 1, 2, fun n => by show n + 1 ≤ 2 * n ^ 1 + 2; rw [pow_one]; omega⟩, ?_⟩
  intro n
  exact ⟨directQuery n, le_of_eq (sizeO_directQuery n), fun x => evalO_directQuery _ x⟩

/-- **THE CONCRETE RELATIVIZATION OBSTRUCTION (proved).**  In this real oracle-circuit model, no
measure separates `L` relative to every oracle: the oracle that *is* `L` collapses it, contradicting
condition (B) relative to that oracle. -/
theorem no_relativizing_separatingMeasure_concrete (L : Layer7.BoolLang)
    (rm : RelativizingSeparatingMeasure L SIZErelC) : False :=
  no_relativizing_separatingMeasure SIZErelC rm (concrete_oracle_collapse L)

/-- Restated: under this concrete model the relativizing-measure type is uninhabited. -/
theorem not_nonempty_relativizing_concrete (L : Layer7.BoolLang) :
    ¬ Nonempty (RelativizingSeparatingMeasure L SIZErelC) :=
  separatingMeasure_nonrelativizing SIZErelC (concrete_oracle_collapse L)

end PallLean.Paper93.DeepMath.PathB.OracleCircuitModel

#print axioms PallLean.Paper93.DeepMath.PathB.OracleCircuitModel.concrete_oracle_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.OracleCircuitModel.no_relativizing_separatingMeasure_concrete
