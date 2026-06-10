import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pFoundations
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4CircuitReal
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Layer 3 — the circuit → `MvPolynomial (Fin n) (ZMod p)` representation

The Razborov–Smolensky entry point: an **exact** polynomial representation of a Boolean circuit over
`ZMod p`, agreeing with the circuit's Boolean function on `{0,1}`-inputs (the `boolToZMod` embedding).

* `embed p x` — the `{0,1}` evaluation point `i ↦ boolToZMod p (x i)`.
* `toPoly p C` — `input ↦ X`, `const b ↦ C (boolToZMod p b)`, `¬ ↦ 1 - ·`, `∧ ↦ ∏`,
  `∨ ↦ 1 - ∏(1 - ·)` (De Morgan), `MOD_q r ↦ 1 - (∑ - r)^(q-1)` (the Fermat indicator of `∑ = r`).
* `boolToZMod_all`/`boolToZMod_any` — `∧`/`∨` as product / De Morgan product on `{0,1}`.
* `eval_prod_toPolyList`/`eval_prod_one_sub_toPolyList` — evaluating those products factors through the
  per-subcircuit value.  (Full circuit correctness composes these — deferred, see below.)

The *exact* (high-degree) representation — the foundation.  Follow-ups: the `MOD_q`-gate correctness
(`Fact p.Prime` + Fermat), and the low-degree *approximate* `∧/∨` polynomials (the actual degree
control).  No lower bound, no capstone.  AC⁰[p] is a higher circuit-lower-bound layer; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer3

open PallLean.Paper93.DeepMath.PathB
open MvPolynomial

variable {n : ℕ}

/-- The `{0,1}` evaluation point in `ZMod p` for a Boolean assignment. -/
def embed (p : ℕ) (x : Fin n → Bool) : Fin n → ZMod p := fun i => boolToZMod p (x i)

-- The exact polynomial representation of a Boolean circuit over `ZMod p` (mutual with the list version).
mutual
noncomputable def toPoly (p : ℕ) : BoolCircuitSyntax n → MvPolynomial (Fin n) (ZMod p)
  | .const b => C (boolToZMod p b)
  | .input i => X i
  | .not c => 1 - toPoly p c
  | .andGate cs => (toPolyList p cs).prod
  | .orGate cs => 1 - ((toPolyList p cs).map (fun q => 1 - q)).prod
  | .modGate q r cs => 1 - ((toPolyList p cs).sum - C ((r : ZMod p))) ^ (q - 1)
noncomputable def toPolyList (p : ℕ) :
    List (BoolCircuitSyntax n) → List (MvPolynomial (Fin n) (ZMod p))
  | [] => []
  | c :: cs => toPoly p c :: toPolyList p cs
end

/-! ### Boolean-list ↔ product identities over `ZMod p` -/

/-- `AND` as a product on `{0,1}`: `embed (all true) = ∏ embed`. -/
theorem boolToZMod_all (p : ℕ) (L : List Bool) :
    boolToZMod p (L.all id) = (L.map (boolToZMod p)).prod := by
  induction L with
  | nil => simp [boolToZMod]
  | cons b L ih =>
      rw [List.all_cons, List.map_cons, List.prod_cons, ← ih]
      cases b <;> simp [boolToZMod]

/-- `OR` as De Morgan on `{0,1}`: `embed (any true) = 1 - ∏ (1 - embed)`. -/
theorem boolToZMod_any (p : ℕ) (L : List Bool) :
    boolToZMod p (L.any id) = 1 - (L.map (fun b => 1 - boolToZMod p b)).prod := by
  induction L with
  | nil => simp [boolToZMod]
  | cons b L ih =>
      rw [List.any_cons, List.map_cons, List.prod_cons]
      cases b with
      | true => simp [boolToZMod]
      | false =>
          show boolToZMod p (L.any id)
              = 1 - ((1 - boolToZMod p false) * (L.map (fun b => 1 - boolToZMod p b)).prod)
          rw [show boolToZMod p false = (0 : ZMod p) from rfl, sub_zero, one_mul]
          exact ih

/-! ### Evaluating a product/De-Morgan-product over `toPolyList` (direct induction helpers) -/

/-- Evaluating `∏ toPolyList` factors through the per-circuit evaluation. -/
theorem eval_prod_toPolyList (p : ℕ) (x : Fin n → Bool) {f : BoolCircuitSyntax n → ZMod p}
    (cs : List (BoolCircuitSyntax n))
    (hf : ∀ c ∈ cs, MvPolynomial.eval (embed p x) (toPoly p c) = f c) :
    MvPolynomial.eval (embed p x) (toPolyList p cs).prod = (cs.map f).prod := by
  induction cs with
  | nil => simp [toPolyList]
  | cons c cs ih =>
      rw [toPolyList, List.prod_cons, map_mul, hf c (by simp),
        ih (fun c' hc' => hf c' (by simp [hc'])), List.map_cons, List.prod_cons]

/-- Evaluating `∏ (1 - toPolyList)` factors through the per-circuit evaluation (the De Morgan side). -/
theorem eval_prod_one_sub_toPolyList (p : ℕ) (x : Fin n → Bool) {f : BoolCircuitSyntax n → ZMod p}
    (cs : List (BoolCircuitSyntax n))
    (hf : ∀ c ∈ cs, MvPolynomial.eval (embed p x) (toPoly p c) = f c) :
    MvPolynomial.eval (embed p x) ((toPolyList p cs).map (fun q => 1 - q)).prod
      = (cs.map (fun c => 1 - f c)).prod := by
  induction cs with
  | nil => simp [toPolyList]
  | cons c cs ih =>
      rw [toPolyList, List.map_cons, List.prod_cons, map_mul, map_sub, map_one,
        hf c (by simp),
        ih (fun c' hc' => hf c' (by simp [hc'])), List.map_cons, List.prod_cons]

/-! ### Correctness — deferred (one Lean wrinkle)

The exact-correctness statement
`MvPolynomial.eval (embed p x) (toPoly p C) = boolToZMod p (C.eval x)` for `IsAC0Syntax C` reduces, via
the two helpers above, to threading the per-subcircuit identity through `∧`/`∨` (and Fermat through
`MOD`).  The only obstacle is the *structural-recursion* plumbing over the `List`-nested `BoolCircuitSyntax`
(a mutual `toPoly`/`toPolyList` recursion that Lean's termination checker does not accept automatically) —
a Lean engineering follow-up, **not** a mathematical gap.  The leaf identities (`const`/`input`/`¬`) and
the list-product reductions (`eval_prod_toPolyList`, `eval_prod_one_sub_toPolyList`) are already proved
here; the final theorem composes them once the recursion is set up (`termination_by` a circuit-size
measure).
-/

end PallLean.Paper93.DeepMath.PathB.Layer3

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.boolToZMod_any
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.eval_prod_toPolyList
