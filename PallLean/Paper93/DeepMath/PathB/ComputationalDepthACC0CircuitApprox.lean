import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BasisBridge

/-!
# A circuit datatype and the approximation invariant, with the structural induction set up

This file sets up the datatype and invariant for the Razborov–Smolensky depth induction: an unbounded-fan-in Boolean
circuit `Circ n`, and the invariant `Approximable C D E` = "`C` has an `F₂` polynomial approximant of total degree
`≤ D` that errs on `≤ E` inputs".  The base cases of the induction are proved; the `OR`/`AND` inductive step is the
remaining target (it combines all the machinery: per-gate small-error forms `…ACC0SmallErrorForm`, degree composition
`…ACC0LayerCompose`, per-point composition `…ACC0CompositionCorrect`, and error accumulation `…ACC0ErrorAccumulation`).

`Circ` uses **List** fan-in for `or`/`and` — unbounded fan-in is the whole point of the polynomial method (bounded
fan-in is the easy exact case).

## What is proved (clean axioms, no `sorry`)

* `Circ` / `Circ.eval` / `Circ.size` — the unbounded-fan-in circuit, its Boolean value, and gate count (the `or`/`and`
  recursions over the `List` use `attach` + a `sizeOf` termination argument).
* `errCard` / `Approximable` — the error count of a polynomial vs a circuit, and the approximation invariant.
* `approximable_inp` (`D=1, E=0`), `approximable_const` (`D=0, E=0`), `approximable_not` (preserves `D, E`) — the base
  cases (and the `¬` step), all *exact* (error 0 carried, or preserved).

## Honest scope — the inductive step that remains

The `OR`/`AND` inductive step is:

> if subcircuits `c_1, …, c_k` are `Approximable` with degrees `≤ D` and errors `≤ E_i`, then `Circ.or cs` (resp.
> `and`) is `Approximable` with degree `≤ t·D` and error `≤ (∑ E_i) + 2^{-t}·2^n`.

Degree `≤ t·D` is `…ACC0LayerCompose`; the error split is per-point composition (`…ACC0CompositionCorrect`) + union
bound (`…ACC0ErrorAccumulation`) over the subgate errors plus the gate's own boosting error
(`…ACC0SmallErrorForm`, in the *input*-space variant).  Assembling that step, iterating it to the depth-`d` bound
`degree ≤ t^d`, `error ≤ size·2^{-t}`, and handling `MOD` (prime-power only — composite `MOD` is the genuine open
barrier) is the rest of the Beigel–Tarui/Yao front half, **Wall 1**.  This file is the scaffolding: datatype,
invariant, and base cases.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md` and
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CircuitApprox

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.Layer3

variable {n : ℕ}

/-- An **unbounded-fan-in Boolean circuit** over `n` inputs. -/
inductive Circ (n : ℕ) where
  | inp : Fin n → Circ n
  | const : Bool → Circ n
  | not : Circ n → Circ n
  | or : List (Circ n) → Circ n
  | and : List (Circ n) → Circ n

/-- The Boolean value of a circuit on an input. -/
def Circ.eval (x : Fin n → Bool) : Circ n → Bool
  | .inp i => x i
  | .const b => b
  | .not c => !(Circ.eval x c)
  | .or cs => cs.attach.any (fun c => Circ.eval x c.1)
  | .and cs => cs.attach.all (fun c => Circ.eval x c.1)
  termination_by c => sizeOf c
  decreasing_by
    all_goals simp_wf
    all_goals (have h := List.sizeOf_lt_of_mem c.2; omega)

/-- Circuit size (gate count). -/
def Circ.size : Circ n → ℕ
  | .inp _ => 1
  | .const _ => 1
  | .not c => 1 + Circ.size c
  | .or cs => 1 + (cs.attach.map (fun c => Circ.size c.1)).sum
  | .and cs => 1 + (cs.attach.map (fun c => Circ.size c.1)).sum
  termination_by c => sizeOf c
  decreasing_by
    all_goals simp_wf
    all_goals (have h := List.sizeOf_lt_of_mem c.2; omega)

/-- The number of inputs on which polynomial `P` disagrees with circuit `C` (embedding `F₂`). -/
noncomputable def errCard (P : MvPolynomial (Fin n) (ZMod 2)) (C : Circ n) : ℕ :=
  (Finset.univ.filter
    (fun x => MvPolynomial.eval (fun i => boolToZMod 2 (x i)) P ≠ boolToZMod 2 (Circ.eval x C))).card

/-- **The approximation invariant**: `C` has an `F₂` polynomial of total degree `≤ D` erring on `≤ E` inputs. -/
def Approximable (C : Circ n) (D E : ℕ) : Prop :=
  ∃ P : MvPolynomial (Fin n) (ZMod 2), P.totalDegree ≤ D ∧ errCard P C ≤ E

/-- `errCard = 0` when `P` computes `C` exactly on the cube (proved). -/
theorem errCard_eq_zero_of_exact (P : MvPolynomial (Fin n) (ZMod 2)) (C : Circ n)
    (h : ∀ x, MvPolynomial.eval (fun i => boolToZMod 2 (x i)) P = boolToZMod 2 (Circ.eval x C)) :
    errCard P C = 0 := by
  rw [errCard, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _
  simp only [ne_eq, not_not]
  exact h x

/-- **Base case — input gate (proved): `Approximable (inp i) 1 0`.** -/
theorem approximable_inp (i : Fin n) : Approximable (Circ.inp i) 1 0 := by
  refine ⟨MvPolynomial.X i, le_of_eq (MvPolynomial.totalDegree_X i), le_of_eq ?_⟩
  apply errCard_eq_zero_of_exact
  intro x
  simp [Circ.eval, MvPolynomial.eval_X]

/-- **Base case — constant gate (proved): `Approximable (const b) 0 0`.** -/
theorem approximable_const (b : Bool) : Approximable (Circ.const b : Circ n) 0 0 := by
  refine ⟨(MvPolynomial.C (boolToZMod 2 b) : MvPolynomial (Fin n) (ZMod 2)),
    le_of_eq (MvPolynomial.totalDegree_C _), le_of_eq ?_⟩
  apply errCard_eq_zero_of_exact
  intro x
  simp [Circ.eval, MvPolynomial.eval_C]

/-- **`¬` step (proved): `Approximable C D E → Approximable (not C) D E`.**  Take `1 − P`; degree and error are
preserved (`1 − ·` is a bijection on `F₂` and flips the Boolean value). -/
theorem approximable_not {C : Circ n} {D E : ℕ} (h : Approximable C D E) :
    Approximable (Circ.not C) D E := by
  obtain ⟨P, hdeg, herr⟩ := h
  refine ⟨1 - P, ?_, ?_⟩
  · refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [MvPolynomial.totalDegree_one]
    exact max_le (Nat.zero_le D) hdeg
  · -- the error set of `1 - P` vs `not C` equals that of `P` vs `C`
    refine le_trans (le_of_eq ?_) herr
    rw [errCard, errCard]
    congr 1
    apply Finset.filter_congr
    intro x _
    rw [MvPolynomial.eval_sub, map_one]
    have hnot : Circ.eval x (Circ.not C) = !(Circ.eval x C) := by simp [Circ.eval]
    rw [hnot]
    have hbn : boolToZMod 2 (!(Circ.eval x C)) = 1 - boolToZMod 2 (Circ.eval x C) := by
      cases Circ.eval x C <;> decide
    rw [hbn]
    exact (by decide : ∀ u v : ZMod 2, (1 - u ≠ 1 - v) ↔ (u ≠ v))
      (MvPolynomial.eval (fun i => boolToZMod 2 (x i)) P) (boolToZMod 2 (Circ.eval x C))

end PallLean.Paper93.DeepMath.PathB.ACC0CircuitApprox

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitApprox.approximable_inp
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitApprox.approximable_const
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitApprox.approximable_not
