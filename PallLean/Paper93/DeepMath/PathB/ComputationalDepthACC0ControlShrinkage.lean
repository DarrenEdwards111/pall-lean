import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0OracleControl

/-!
# Control shrinkage under a leaf restriction — the provable half, and where it stops

The open rung of `…ACC0OracleControl` is `random_restriction_makes_control_shallow`.  This file proves the part that is
genuinely provable — the **leaf-level** shrinkage — and pins precisely where it stops.

A *leaf restriction* `ρ : Fin m → Option Bool` fixes some oracle leaves to constants and frees the rest.  The control,
read through `ρ`, depends only on its **free leaves**, so its complete query tree over those free leaves has depth at
most `|leafFree ρ|`.  Hence:

* **`control_restriction_shallow`** — the `ρ`-restricted control is a decision tree of depth `≤ |leafFree ρ|`.
* **`control_restriction_searchable`** — the `ρ`-restricted composite `x ↦ controlEval C (j ↦ (ρ j).getD (gⱼ x))` is
  SAT-searchable below `2ⁿ` once `2^{|leafFree ρ|} < 2^n` (few free leaves), via the `AC⁰`-over-`MOD` observer.

So the observer state space *does* shrink to `2^{|leafFree ρ|}` — the contextual-control thesis, made concrete: fixing
leaves shrinks the state count.

## Where it stops (the barrier, stated honestly)

`control_restriction_searchable` searches the *restricted* composite, where the fixed leaves ignore the oracle.  To
help the *original* composite (`x ↦ controlEval C (gⱼ x)`) the leaf restriction must be **realized by an input
restriction** — and a `MOD`/parity oracle leaf becomes a constant under an `x`-restriction *only when its whole support
is fixed* (`…ACC0MODResidualObserver.parity_constant_iff_support_fully_fixed`: no absorbing value).  For wide/overlapping
`MOD` supports a restriction rarely fixes a whole support, so the free-leaf count stays high and the depth does **not**
drop below `n`.  That is the same `MOD` wall, now localized to the control layer: leaf shrinkage is free, but
`x`-realizable leaf shrinkage for wide `MOD` is the open content.

## Honest scope

`control_restriction_shallow` / `control_restriction_searchable` are *proved* (clean axioms, no `sorry`); they are the
leaf-level shrinkage.  The `x`-realizability of an aggressive leaf restriction over wide `MOD` oracles — the step that
would turn this into a general `ACC⁰`-SAT speedup — is **not** established (the barrier above).  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ControlShrinkage

open scoped Classical
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0DecisionTreeObserver
open PallLean.Paper93.DeepMath.PathB.ACC0ModComposition
open PallLean.Paper93.DeepMath.PathB.ACC0OracleControl

variable {n m : ℕ}

/-- The **free leaves** of a leaf restriction: the oracle positions left unfixed. -/
def leafFree (ρ : Fin m → Option Bool) : Finset (Fin m) :=
  Finset.univ.filter (fun j => ρ j = none)

/-- The control read through a leaf restriction: fixed leaves take `ρ`'s value, free leaves read `y`. -/
def restrictedControlEval (C : OracleControl m) (ρ : Fin m → Option Bool) (y : Fin m → Bool) : Bool :=
  controlEval C (fun j => (ρ j).getD (y j))

/-- **The restricted control depends only on the free leaves (proved).** -/
theorem restrictedControlEval_eq_of_agree (C : OracleControl m) (ρ : Fin m → Option Bool)
    (y y' : Fin m → Bool) (h : ∀ j ∈ leafFree ρ, y j = y' j) :
    restrictedControlEval C ρ y = restrictedControlEval C ρ y' := by
  unfold restrictedControlEval
  congr 1
  funext j
  by_cases hj : ρ j = none
  · rw [hj]
    simp only [Option.getD_none]
    exact h j (by simp [leafFree, hj])
  · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hj
    rw [hb]
    simp

/-- **Leaf-level shrinkage (proved): the `ρ`-restricted control is a decision tree of depth `≤ |leafFree ρ|`.** -/
theorem control_restriction_shallow (C : OracleControl m) (ρ : Fin m → Option Bool) :
    ∃ T : BoolDecisionTree m,
      (∀ y, restrictedControlEval C ρ y = T.eval y) ∧ T.depth ≤ (leafFree ρ).card := by
  refine ⟨treeOf (restrictedControlEval C ρ) (leafFree ρ).toList (fun _ => false), ?_, ?_⟩
  · intro y
    rw [treeOf_eval]
    exact restrictedControlEval_eq_of_agree C ρ y _
      (fun j hj => (if_pos (Finset.mem_toList.mpr hj)).symm)
  · exact le_trans (treeOf_depth_le _ _ _) (le_of_eq (Finset.length_toList _))

/-- **The restricted composite is SAT-searchable below `2ⁿ` when few leaves are free (proved).**  The observer state
space has shrunk to `2^{|leafFree ρ|}`; once that is `< 2^n`, satisfiability reduces to scanning `< 2^n` statistic
cells.  This is the leaf-level shrinkage cashed out through the `AC⁰`-over-`MOD` observer. -/
theorem control_restriction_searchable (C : OracleControl m) (ρ : Fin m → Option Bool)
    (g : Fin m → ModGate n) (hfree : 2 ^ (leafFree ρ).card < 2 ^ n) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (stat : (Fin n → Bool) → S) (gg : S → Bool),
      (Satisfiable (fun x => restrictedControlEval C ρ (fun j => (g j).eval x)) ↔
          ∃ s ∈ Finset.univ.image stat, gg s = true)
        ∧ (Finset.univ.image stat).card < 2 ^ n := by
  obtain ⟨T, hT, hd⟩ := control_restriction_shallow C ρ
  have heq : (fun x => restrictedControlEval C ρ (fun j => (g j).eval x))
      = (fun x => BoolDecisionTree.eval T (fun j => (g j).eval x)) := by
    funext x; rw [hT]
  rw [heq]
  exact acc0_over_mod_searchable T g
    (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hd) hfree)

end PallLean.Paper93.DeepMath.PathB.ACC0ControlShrinkage

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ControlShrinkage.restrictedControlEval_eq_of_agree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ControlShrinkage.control_restriction_shallow
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ControlShrinkage.control_restriction_searchable
