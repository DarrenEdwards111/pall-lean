import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSymAndPoly
import Mathlib

/-!
# General arithmetisation of `AC⁰` circuits (PROVED)

Every `MOD`-free `ACC0` circuit (i.e. an `AC⁰` circuit: `AND`/`OR`/`NOT` over inputs) is **exactly represented**
by a multivariate polynomial over `ℤ`: the polynomial, evaluated at a Boolean point, equals the circuit's value.

  `toPoly` — the arithmetisation `Circuit n → MvPolynomial (Fin n) ℤ` (`var ↦ Xᵢ`, `not ↦ 1-·`, `and ↦ ∏`,
        `or ↦ 1 - ∏(1-·)`), defined by mutual structural recursion with a list helper.
  `ModFree` — the predicate selecting `MOD`-free circuits.
  `toPoly_eval` — **faithful**: for a `MOD`-free circuit, `eval (toPoly C) x = [C accepts x]` on `{0,1}ⁿ`.

The arithmetisation is exact but not low-degree (`AND`/`OR` multiply degrees); the *low-degree* (probabilistic)
approximation and the `MOD_q` degree lower bound remain the genuine targets.
-/

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.SymAnd (boolPt)

namespace PallLean.Paper93.DeepMath.PathB.ACC0.Circuit

variable {n : ℕ}

mutual
/-- The arithmetisation of a circuit as an integer polynomial.  `MOD` gates map to `0` (placeholder; the
correctness theorem is restricted to `MOD`-free circuits).  Defined by mutual structural recursion with a list
helper. -/
noncomputable def toPoly : Circuit n → MvPolynomial (Fin n) ℤ
  | var i => X i
  | const b => MvPolynomial.C (b.toNat : ℤ)
  | not c => 1 - toPoly c
  | and cs => (toPolyList cs).prod
  | or cs => 1 - ((toPolyList cs).map (fun p => 1 - p)).prod
  | mod _ _ => 0
noncomputable def toPolyList : List (Circuit n) → List (MvPolynomial (Fin n) ℤ)
  | [] => []
  | c :: cs => toPoly c :: toPolyList cs
end

/-- The list helper is exactly `map toPoly`. -/
theorem toPolyList_eq_map (cs : List (Circuit n)) : toPolyList cs = cs.map toPoly := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [toPolyList, ih]

mutual
/-- The circuit uses no `MOD` gates. -/
def ModFree : Circuit n → Prop
  | var _ => True
  | const _ => True
  | not c => ModFree c
  | and cs => ModFreeList cs
  | or cs => ModFreeList cs
  | mod _ _ => False
def ModFreeList : List (Circuit n) → Prop
  | [] => True
  | c :: cs => ModFree c ∧ ModFreeList cs
end

@[simp] theorem ModFree_not (c : Circuit n) : ModFree (not c) ↔ ModFree c := by rw [ModFree]
@[simp] theorem ModFree_and (cs : List (Circuit n)) : ModFree (and cs) ↔ ModFreeList cs := by rw [ModFree]
@[simp] theorem ModFree_or (cs : List (Circuit n)) : ModFree (or cs) ↔ ModFreeList cs := by rw [ModFree]
@[simp] theorem ModFreeList_cons (c : Circuit n) (cs : List (Circuit n)) :
    ModFreeList (c :: cs) ↔ ModFree c ∧ ModFreeList cs := by rw [ModFreeList]

/-- `AND` of booleans is the product of their `0/1` values (over `ℤ`). -/
theorem toNat_and_int (b c : Bool) : (((b && c).toNat : ℤ)) = (b.toNat : ℤ) * (c.toNat : ℤ) := by
  cases b <;> cases c <;> simp

/-- `OR` of booleans is `1 - (1-b)(1-c)` (De Morgan, over `ℤ`). -/
theorem toNat_or_int (b c : Bool) :
    (((b || c).toNat : ℤ)) = 1 - (1 - (b.toNat : ℤ)) * (1 - (c.toNat : ℤ)) := by
  cases b <;> cases c <;> simp

/-- The product of child polynomials evaluates to the `AND` of the children (given each child is faithful). -/
theorem prod_eval (x : Fin n → Bool) (cs : List (Circuit n))
    (h : ∀ c ∈ cs, MvPolynomial.eval (boolPt x) (toPoly c) = ((Circuit.eval x c).toNat : ℤ)) :
    MvPolynomial.eval (boolPt x) ((toPolyList cs).prod) = ((cs.all (Circuit.eval x)).toNat : ℤ) := by
  induction cs with
  | nil => simp [toPolyList]
  | cons c cs ih =>
    rw [toPolyList, List.prod_cons, map_mul, h c (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun c' hc' => h c' (List.mem_cons.mpr (Or.inr hc'))), List.all_cons, toNat_and_int]

/-- The product of `(1 - child)` evaluates to `1 - OR` of the children (De Morgan). -/
theorem prodNot_eval (x : Fin n → Bool) (cs : List (Circuit n))
    (h : ∀ c ∈ cs, MvPolynomial.eval (boolPt x) (toPoly c) = ((Circuit.eval x c).toNat : ℤ)) :
    MvPolynomial.eval (boolPt x) (((toPolyList cs).map (fun p => 1 - p)).prod)
      = (1 - ((cs.any (Circuit.eval x)).toNat : ℤ)) := by
  induction cs with
  | nil => simp [toPolyList]
  | cons c cs ih =>
    rw [toPolyList, List.map_cons, List.prod_cons, map_mul, map_sub, map_one,
      h c (List.mem_cons.mpr (Or.inl rfl)), ih (fun c' hc' => h c' (List.mem_cons.mpr (Or.inr hc'))),
      List.any_cons, toNat_or_int]
    ring

/-- `ModFreeList` is the conjunction over the children. -/
theorem ModFreeList_forall (cs : List (Circuit n)) : ModFreeList cs ↔ ∀ c ∈ cs, ModFree c := by
  induction cs with
  | nil => simp [ModFreeList]
  | cons c cs ih => simp [ih]

set_option linter.unusedVariables false in
/-- **Faithful arithmetisation.**  For a `MOD`-free (`AC⁰`) circuit, its integer polynomial `toPoly C`,
evaluated at a Boolean point, equals the circuit's `0/1` value `[C accepts x]` — the polynomial computes the
circuit exactly on `{0,1}ⁿ`.  Proved by well-founded recursion on circuit size (each child is smaller), using
the list helpers `prod_eval`/`prodNot_eval`. -/
theorem toPoly_eval (x : Fin n → Bool) :
    ∀ C : Circuit n, ModFree C →
      MvPolynomial.eval (boolPt x) (toPoly C) = ((Circuit.eval x C).toNat : ℤ)
  | var i, _ => by simp [toPoly, boolPt, Circuit.eval_var]
  | const b, _ => by simp [toPoly, Circuit.eval_const]
  | not c, h => by
      rw [toPoly, map_sub, map_one, toPoly_eval x c (by simpa using h), Circuit.eval_not]
      cases Circuit.eval x c <;> simp
  | and cs, h => by
      rw [toPoly, prod_eval x cs
        (fun c hc => toPoly_eval x c ((ModFreeList_forall cs).mp (by simpa using h) c hc)),
        Circuit.eval_and]
  | or cs, h => by
      rw [toPoly, map_sub, map_one, prodNot_eval x cs
        (fun c hc => toPoly_eval x c ((ModFreeList_forall cs).mp (by simpa using h) c hc)),
        Circuit.eval_or]
      ring
  | mod m cs, h => by simp [ModFree] at h
termination_by C => sizeOf C
decreasing_by
  all_goals simp_wf
  all_goals (rename_i hc; have := List.sizeOf_lt_of_mem hc; omega)

end PallLean.Paper93.DeepMath.PathB.ACC0.Circuit

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.prod_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.toPoly_eval
