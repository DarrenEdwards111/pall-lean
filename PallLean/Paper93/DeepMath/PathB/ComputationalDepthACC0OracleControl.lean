import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModComposition

/-!
# Oracle-control circuits: AC⁰ control over MOD-oracle leaves, reduced to decision-tree observers

`…ACC0ModComposition` proved: a **shallow decision tree** over `MOD`-oracle outputs is observer-searchable.  This file
supplies the *control-layer* syntax and the deterministic reduction: an `AC⁰` **control circuit** over `m` oracle
leaves (`OracleControl`) reduces to a decision tree over the `m` oracle positions — so composing with `MOD` gates as
oracles is observer-searchable when the control's decision-tree depth is small.

* The control layer is a Boolean circuit (`leaf j` queries oracle bit `j`, `const`, `¬`, `∧`, `∨`).
* `control_to_decision_tree`: **any** control over `m` leaves reduces to a `BoolDecisionTree` of depth `≤ m` (the
  complete query tree over all `m` positions) — making the decision-tree-depth hypothesis dischargeable.
* `oracle_control_dt_searchable`: if the control is computed by a depth-`d` tree, the `AC⁰`-over-`MOD` composite is
  SAT-searchable in `< 2^n` once `2^d < 2^n`.
* `oracle_control_over_mod_searchable`: the unconditional fragment speedup — control over `m` `MOD` oracles is
  SAT-searchable below brute force whenever `2^m < 2^n` (fewer than `≈ n` `MOD` gates), regardless of control structure.

## What is proved (clean axioms, no `sorry`)

* `OracleControl` / `controlEval` — the control-layer syntax and semantics.
* `treeOf` / `treeOf_eval` / `treeOf_depth_le`, `fullTree` / `fullTree_eval` / `fullTree_depth_le` — the complete
  query-tree reduction of any Boolean function on `m` bits to a depth-`≤ m` decision tree.
* `control_to_decision_tree` — every control reduces to a depth-`≤ m` decision tree.
* `oracle_control_dt_searchable` / `oracle_control_over_mod_searchable` — the searchable theorems.

## Honest scope — the next hard rung

This is the **deterministic** control→DT reduction: the depth bound is `m` in general (the trivial complete tree), and
`d` when a depth-`d` tree is *supplied*.  The genuine open step — **`random_restriction_makes_control_shallow`**: that
a random restriction makes the control layer (e.g. a DNF/CNF over the oracle leaves) collapse to a *shallow* tree with
high probability — is **not** attempted here.  It is the real next hard one, and it bites against the no-go's deeper
form: the oracle outputs `gⱼ(x)` are determined by `x`, not independent random bits, so the switching analysis does not
transfer to the control-over-oracles layer for free.  Composes a single `AC⁰`-over-`MOD` level only.  Still the
cell/observer model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0OracleControl

open scoped Classical
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver
open PallLean.Paper93.DeepMath.PathB.ACC0DecisionTreeObserver
open PallLean.Paper93.DeepMath.PathB.ACC0ModComposition

variable {n m : ℕ}

/-! ## The control-layer syntax -/

/-- A Boolean **control circuit** over `m` oracle leaves (`leaf j` reads oracle bit `j`). -/
inductive OracleControl (m : ℕ) where
  | leaf : Fin m → OracleControl m
  | const : Bool → OracleControl m
  | cnot : OracleControl m → OracleControl m
  | cand : OracleControl m → OracleControl m → OracleControl m
  | cor : OracleControl m → OracleControl m → OracleControl m

/-- Evaluate a control circuit against an oracle-bit family `y : Fin m → Bool`. -/
def controlEval : OracleControl m → (Fin m → Bool) → Bool
  | .leaf j, y => y j
  | .const b, _ => b
  | .cnot c, y => !(controlEval c y)
  | .cand a b, y => controlEval a y && controlEval b y
  | .cor a b, y => controlEval a y || controlEval b y

/-! ## The complete query-tree reduction -/

/-- The complete decision tree querying the positions in `L` in order; at a leaf (all of `L` fixed) it returns `f`
applied to the accumulated assignment. -/
def treeOf (f : (Fin m → Bool) → Bool) : List (Fin m) → (Fin m → Bool) → BoolDecisionTree m
  | [], acc => BoolDecisionTree.leaf (f acc)
  | j :: rest, acc =>
      BoolDecisionTree.query j (treeOf f rest (Function.update acc j false))
                               (treeOf f rest (Function.update acc j true))

/-- **`treeOf` computes `f` on the assignment that follows `y` on `L` and `acc` elsewhere (proved).** -/
theorem treeOf_eval (f : (Fin m → Bool) → Bool) :
    ∀ (L : List (Fin m)) (acc y : Fin m → Bool),
      (treeOf f L acc).eval y = f (fun k => if k ∈ L then y k else acc k) := by
  intro L
  induction L with
  | nil =>
      intro acc y
      simp [treeOf]
  | cons j rest ih =>
      intro acc y
      simp only [treeOf, BoolDecisionTree.eval]
      rw [ih (Function.update acc j true) y, ih (Function.update acc j false) y, ← apply_ite f]
      congr 1
      funext k
      rw [apply_ite (fun z : Fin m → Bool => z k)]
      by_cases hkj : k = j
      · subst hkj
        simp only [Function.update_self, List.mem_cons, true_or, if_true]
        cases hyj : y k <;> simp
      · simp [List.mem_cons, hkj]

/-- **`treeOf` has depth `≤ |L|` (proved).** -/
theorem treeOf_depth_le (f : (Fin m → Bool) → Bool) :
    ∀ (L : List (Fin m)) (acc : Fin m → Bool), (treeOf f L acc).depth ≤ L.length := by
  intro L
  induction L with
  | nil => intro acc; simp [treeOf]
  | cons j rest ih =>
      intro acc
      simp only [treeOf, BoolDecisionTree.depth, List.length_cons]
      exact Nat.succ_le_succ (max_le (ih _) (ih _))

/-- The complete decision tree over all `m` positions. -/
def fullTree (f : (Fin m → Bool) → Bool) : BoolDecisionTree m :=
  treeOf f (List.finRange m) (fun _ => false)

/-- **The complete tree computes `f` exactly (proved).** -/
theorem fullTree_eval (f : (Fin m → Bool) → Bool) (y : Fin m → Bool) :
    (fullTree f).eval y = f y := by
  rw [fullTree, treeOf_eval]
  congr 1
  funext k
  simp [List.mem_finRange]

/-- **The complete tree has depth `≤ m` (proved).** -/
theorem fullTree_depth_le (f : (Fin m → Bool) → Bool) : (fullTree f).depth ≤ m := by
  rw [fullTree]
  exact le_trans (treeOf_depth_le f _ _) (by simp [List.length_finRange])

/-- **Every control circuit reduces to a depth-`≤ m` decision tree (proved).** -/
theorem control_to_decision_tree (C : OracleControl m) :
    ∃ T : BoolDecisionTree m, (∀ y, controlEval C y = T.eval y) ∧ T.depth ≤ m :=
  ⟨fullTree (controlEval C), fun y => (fullTree_eval (controlEval C) y).symm, fullTree_depth_le _⟩

/-! ## The searchable theorems -/

/-- **If the control is computed by a depth-`d` decision tree, the `AC⁰`-over-`MOD` composite is SAT-searchable in
`< 2^n` once `2^d < 2^n` (proved).**  The `MOD` gates are queried as oracles (the no-go is respected). -/
theorem oracle_control_dt_searchable (C : OracleControl m) (g : Fin m → ModGate n)
    (T : BoolDecisionTree m) (hT : ∀ y, controlEval C y = T.eval y) (hreg : 2 ^ T.depth < 2 ^ n) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (stat : (Fin n → Bool) → S) (gg : S → Bool),
      (Satisfiable (fun x => controlEval C (fun j => (g j).eval x)) ↔
          ∃ s ∈ Finset.univ.image stat, gg s = true)
        ∧ (Finset.univ.image stat).card < 2 ^ n := by
  have heq : (fun x => controlEval C (fun j => (g j).eval x))
      = (fun x => BoolDecisionTree.eval T (fun j => (g j).eval x)) := by
    funext x; rw [hT]
  rw [heq]
  exact acc0_over_mod_searchable T g hreg

/-- **Unconditional fragment speedup (proved): an `AC⁰` control over `m` `MOD` oracles is SAT-searchable below brute
force whenever `2^m < 2^n`** (e.g. fewer than `≈ n` `MOD` gates), regardless of the control's structure. -/
theorem oracle_control_over_mod_searchable (C : OracleControl m) (g : Fin m → ModGate n)
    (hreg : 2 ^ m < 2 ^ n) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (stat : (Fin n → Bool) → S) (gg : S → Bool),
      (Satisfiable (fun x => controlEval C (fun j => (g j).eval x)) ↔
          ∃ s ∈ Finset.univ.image stat, gg s = true)
        ∧ (Finset.univ.image stat).card < 2 ^ n := by
  obtain ⟨T, hT, hd⟩ := control_to_decision_tree C
  exact oracle_control_dt_searchable C g T hT
    (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hd) hreg)

end PallLean.Paper93.DeepMath.PathB.ACC0OracleControl

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0OracleControl.treeOf_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0OracleControl.control_to_decision_tree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0OracleControl.oracle_control_over_mod_searchable
