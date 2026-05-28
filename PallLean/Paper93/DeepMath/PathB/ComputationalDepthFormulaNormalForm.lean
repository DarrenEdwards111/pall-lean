import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFormulaLeafSemantics

/-!
# Normal form for `BFormula`: labeled full binary trees

**STATUS: NORMALIZATION RUNG OF THE NEČIPORUK COUNTING LEMMA.**

To count the distinct subfunctions a formula exposes on a block, we first put a
formula into a countable normal form.  The obstruction is that raw `BFormula`s of
bounded *variable*-leaf count are still an infinite set (unary chains and constant
subtrees blow up the syntax without changing the variable-leaf count).

This file removes both: `NF` is a **labeled full binary tree** — every leaf is a
variable literal, every internal node a binary gate, with *no* unary gates and
*no* internal constants.  We give a normalizer `norm : BFormula n → Bool ⊕ NF n`
(`inl` = a constant function, `inr` = a genuine tree), and prove:

* `seval_norm` : `norm` preserves the computed function, and
* `leaves_norm_le` : the tree has at most `litCount F` leaves.

Composed with `block_realization`, every block subfunction is `NF.eval` of a tree
with at most `leavesIn S F` leaves — a *finite, Catalan-countable* object.  The
quantitative card bound is the next file.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-! ## Normal-form trees -/

/-- A labeled full binary tree: variable-literal leaves and binary-gate nodes.
No unary gates, no constants — the countable normal form. -/
inductive NF (n : Nat) where
  | leaf : Fin n -> Bool -> NF n
  | node : (Bool -> Bool -> Bool) -> NF n -> NF n -> NF n

namespace NF

variable {n : Nat}

/-- Evaluation, matching `BFormula.eval` on literals. -/
def eval : NF n -> (Fin n -> Bool) -> Bool
  | leaf i b, x => cond b (x i) (!(x i))
  | node g l r, x => g (eval l x) (eval r x)

/-- Number of leaves (= number of variable literals). -/
def leaves : NF n -> Nat
  | leaf _ _ => 1
  | node _ l r => leaves l + leaves r

/-- Semantics of a `Bool ⊕ NF` value: a constant function or a tree. -/
def seval : Bool ⊕ NF n -> (Fin n -> Bool) -> Bool
  | Sum.inl c, _ => c
  | Sum.inr t, x => eval t x

/-- Apply a unary function to a normal form, folding into the gate (for nodes) or
the literal/constant (for leaves). Returns `inl` when the result is constant. -/
def applyU (u : Bool -> Bool) : NF n -> Bool ⊕ NF n
  | leaf i b => if u b = u (!b) then Sum.inl (u b) else Sum.inr (leaf i (u b))
  | node g l r => Sum.inr (node (fun x y => u (g x y)) l r)

/-- The combined leaf identity behind `applyU` correctness. -/
private theorem leaf_aux (u : Bool -> Bool) (b bi : Bool) :
    (if u b = u (!b) then u b else cond (u b) bi (!bi)) = u (cond b bi (!bi)) := by
  cases b <;> cases bi <;>
    simp only [Bool.not_true, Bool.not_false, cond_true, cond_false] <;>
    cases hu1 : u true <;> cases hu2 : u false <;> simp_all

theorem seval_applyU (u : Bool -> Bool) (s : NF n) (x : Fin n -> Bool) :
    seval (applyU u s) x = u (eval s x) := by
  cases s with
  | leaf i b =>
      rw [applyU, apply_ite (fun w => seval w x)]
      simp only [seval, eval]
      exact leaf_aux u b (x i)
  | node g l r => simp [applyU, seval, eval]

theorem leaves_applyU_le (u : Bool -> Bool) (s : NF n) {t : NF n}
    (h : applyU u s = Sum.inr t) : leaves t <= leaves s := by
  cases s with
  | leaf i b =>
      simp only [applyU] at h
      by_cases hu : u b = u (!b)
      · rw [if_pos hu] at h; simp at h
      · rw [if_neg hu] at h
        have ht := Sum.inr_injective h
        rw [← ht]; simp [NF.leaves]
  | node g l r =>
      simp only [applyU, Sum.inr.injEq] at h
      rw [← h]; simp [NF.leaves]

end NF

/-! ## Normalizer -/

open NF

/-- Normalize a `BFormula` to a constant (`inl`) or a labeled full binary tree
(`inr`), eliminating unary gates and internal constants. -/
def norm {n : Nat} : BFormula n -> Bool ⊕ NF n
  | BFormula.lit i b => Sum.inr (NF.leaf i b)
  | BFormula.cst c => Sum.inl c
  | BFormula.un u t =>
      match norm t with
      | Sum.inl c => Sum.inl (u c)
      | Sum.inr s => NF.applyU u s
  | BFormula.bin g a b =>
      match norm a, norm b with
      | Sum.inl x, Sum.inl y => Sum.inl (g x y)
      | Sum.inl x, Sum.inr s => NF.applyU (fun v => g x v) s
      | Sum.inr s, Sum.inl y => NF.applyU (fun v => g v y) s
      | Sum.inr s, Sum.inr t => Sum.inr (NF.node g s t)

variable {n : Nat}

/-- The normalizer preserves the computed function. -/
theorem seval_norm (F : BFormula n) (x : Fin n -> Bool) :
    NF.seval (norm F) x = BFormula.eval F x := by
  induction F with
  | lit i b => rfl
  | cst c => rfl
  | un u t ih =>
      simp only [norm]
      split
      · rename_i c hnt
        rw [hnt] at ih; simp only [NF.seval] at ih
        simp only [NF.seval, BFormula.eval, ← ih]
      · rename_i s hnt
        rw [hnt] at ih; simp only [NF.seval] at ih
        rw [NF.seval_applyU, ih]; simp only [BFormula.eval]
  | bin g a b iha ihb =>
      simp only [norm]
      split
      · rename_i px py hna hnb
        rw [hna] at iha; rw [hnb] at ihb
        simp only [NF.seval] at iha ihb
        simp only [NF.seval, BFormula.eval, ← iha, ← ihb]
      · rename_i px s hna hnb
        rw [hna] at iha; rw [hnb] at ihb
        simp only [NF.seval] at iha ihb
        rw [NF.seval_applyU]
        simp only [BFormula.eval, ← iha, ← ihb]
      · rename_i s py hna hnb
        rw [hna] at iha; rw [hnb] at ihb
        simp only [NF.seval] at iha ihb
        rw [NF.seval_applyU]
        simp only [BFormula.eval, ← iha, ← ihb]
      · rename_i s t hna hnb
        rw [hna] at iha; rw [hnb] at ihb
        simp only [NF.seval] at iha ihb
        simp only [NF.seval, BFormula.eval, NF.eval, ← iha, ← ihb]

/-- The normal-form tree has at most `litCount F` leaves. -/
theorem leaves_norm_le (F : BFormula n) {t : NF n} (h : norm F = Sum.inr t) :
    NF.leaves t <= BFormula.litCount F := by
  induction F generalizing t with
  | lit i b =>
      simp only [norm, Sum.inr.injEq] at h
      rw [← h]; simp [NF.leaves, BFormula.litCount]
  | cst c => simp only [norm] at h; exact absurd h (by simp)
  | un u s ih =>
      simp only [norm] at h
      split at h
      · exact absurd h (by simp)
      · rename_i w hns
        exact Nat.le_trans (NF.leaves_applyU_le u w h) (ih hns)
  | bin g a b iha ihb =>
      simp only [norm] at h
      split at h
      · exact absurd h (by simp)
      · rename_i px s hna hnb
        simp only [BFormula.litCount]
        exact Nat.le_trans (NF.leaves_applyU_le _ s h)
          (Nat.le_trans (ihb hnb) (Nat.le_add_left _ _))
      · rename_i s py hna hnb
        simp only [BFormula.litCount]
        exact Nat.le_trans (NF.leaves_applyU_le _ s h)
          (Nat.le_trans (iha hna) (Nat.le_add_right _ _))
      · rename_i s w hna hnb
        simp only [Sum.inr.injEq] at h
        rw [← h]
        simp only [NF.leaves, BFormula.litCount]
        exact Nat.add_le_add (iha hna) (ihb hnb)

/-! ## Kernel-only trace -/

#print axioms seval_norm
#print axioms leaves_norm_le

end PallLean.Paper93.DeepMath.PathB
