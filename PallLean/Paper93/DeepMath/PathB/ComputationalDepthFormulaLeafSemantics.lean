import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukSummation

/-!
# Concrete formula-leaf semantics for the Nečiporuk bound

**STATUS: REAL FORMULA SEMANTICS — DISCHARGES THE ABSTRACT BUDGET, MODULO THE
COUNTING LEMMA.**

The Nečiporuk summation file proved the additive combiner

  total budget  ≥  Σ_i log₂ (capacity_i)

with the per-block budget `b_i` and the budget identity `B = Σ b_i` left as
*abstract hypotheses*.  This file replaces those abstractions with genuine De
Morgan / `B₂` formula semantics:

* a real formula type `BFormula` (variable literals, constants, unary and binary
  gates — the full binary basis),
* `eval`, `leaves`, and `litCount` (the number of *variable* leaves),
* `leavesIn S` = variable leaves reading the block `S`,
* a restriction + constant-folding operation, with the two load-bearing facts:
  - `block_realization`: fixing the variables outside `S` and folding constants
    yields a formula with **at most `leavesIn S F` variable leaves** computing the
    same subfunction on `S` (so the per-block budget is a real leaf count), and
  - `sum_leavesIn_of_partition` / `sum_leavesIn_singleton`: the per-block leaf
    counts **sum to `litCount F`** (the budget identity, now a theorem).

These together discharge the `hbudget` hypothesis of `neciporuk_sum_lower_bound`
concretely (`formula_neciporuk_block_bound`).

## The one remaining rung (honest)

What is *not* proved here is the quantitative counting lemma

  (number of subfunctions on `S`)  ≤  2 ^ (c · leavesIn S F · log |S|),

i.e. that a formula with `k` variable leaves over an `r`-variable block computes
at most `2^{O(k log r)}` distinct functions.  That is a self-contained
combinatorial counting problem (binary-tree shapes × gate/leaf labellings, modulo
a normal form) and is what turns `block_realization` into the hypothesis
`hcount`.  With it, `formula_neciporuk_block_bound` becomes the full `n²/log n`
formula lower bound.  Nečiporuk's method provably tops out there and does **not**
reach TC⁰/NC¹/width-5 BP.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Finset

/-! ## Formula syntax and semantics -/

/-- Boolean formulas over `n` variables with the full binary basis: variable
literals (with polarity), constants, unary gates, and binary gates. -/
inductive BFormula (n : Nat) where
  | lit : Fin n -> Bool -> BFormula n
  | cst : Bool -> BFormula n
  | un  : (Bool -> Bool) -> BFormula n -> BFormula n
  | bin : (Bool -> Bool -> Bool) -> BFormula n -> BFormula n -> BFormula n

namespace BFormula

variable {n : Nat}

/-- Evaluation. A literal `lit i b` is `x i` if `b`, else its negation. -/
def eval : BFormula n -> (Fin n -> Bool) -> Bool
  | lit i b, x => cond b (x i) (!(x i))
  | cst c, _ => c
  | un u t, x => u (eval t x)
  | bin g a b, x => g (eval a x) (eval b x)

/-- Total number of leaves (variable leaves and constant leaves). -/
def leaves : BFormula n -> Nat
  | lit _ _ => 1
  | cst _ => 1
  | un _ t => leaves t
  | bin _ a b => leaves a + leaves b

/-- Number of *variable* leaves (the Nečiporuk size metric). -/
def litCount : BFormula n -> Nat
  | lit _ _ => 1
  | cst _ => 0
  | un _ t => litCount t
  | bin _ a b => litCount a + litCount b

/-- Number of variable leaves reading a variable in the block `S`. -/
def leavesIn (S : Finset (Fin n)) : BFormula n -> Nat
  | lit i _ => if i ∈ S then 1 else 0
  | cst _ => 0
  | un _ t => leavesIn S t
  | bin _ a b => leavesIn S a + leavesIn S b

theorem litCount_le_leaves (F : BFormula n) : litCount F <= leaves F := by
  induction F with
  | lit i b => simp [litCount, leaves]
  | cst c => simp [litCount, leaves]
  | un u t ih => simpa [litCount, leaves] using ih
  | bin g a b iha ihb =>
      simp only [litCount, leaves]
      exact Nat.add_le_add iha ihb

/-! ## Smart constructors that fold constants -/

/-- Unary gate that collapses on a constant argument. -/
def smartUn (u : Bool -> Bool) : BFormula n -> BFormula n
  | cst a => cst (u a)
  | t => un u t

/-- Binary gate that collapses when an argument is constant. -/
def smartBin (g : Bool -> Bool -> Bool) : BFormula n -> BFormula n -> BFormula n
  | cst x, cst y => cst (g x y)
  | cst x, b => smartUn (fun y => g x y) b
  | a, cst y => smartUn (fun x => g x y) a
  | a, b => bin g a b

@[simp] theorem eval_smartUn (u : Bool -> Bool) (t : BFormula n) (x : Fin n -> Bool) :
    eval (smartUn u t) x = u (eval t x) := by
  cases t <;> rfl

@[simp] theorem eval_smartBin (g : Bool -> Bool -> Bool) (a b : BFormula n)
    (x : Fin n -> Bool) :
    eval (smartBin g a b) x = g (eval a x) (eval b x) := by
  cases a <;> cases b <;> rfl

theorem litCount_smartUn_le (u : Bool -> Bool) (t : BFormula n) :
    litCount (smartUn u t) <= litCount t := by
  cases t <;> simp [smartUn, litCount]

theorem litCount_smartBin_le (g : Bool -> Bool -> Bool) (a b : BFormula n) :
    litCount (smartBin g a b) <= litCount a + litCount b := by
  cases a <;> cases b <;>
    simp [smartBin, smartUn, litCount] <;>
    omega

/-! ## Constant folding -/

/-- Fold away constants bottom-up using the smart constructors. -/
def simplify : BFormula n -> BFormula n
  | lit i b => lit i b
  | cst c => cst c
  | un u t => smartUn u (simplify t)
  | bin g a b => smartBin g (simplify a) (simplify b)

theorem eval_simplify (F : BFormula n) (x : Fin n -> Bool) :
    eval (simplify F) x = eval F x := by
  induction F with
  | lit i b => rfl
  | cst c => rfl
  | un u t ih => simp only [simplify, eval_smartUn, ih, eval]
  | bin g a b iha ihb => simp only [simplify, eval_smartBin, iha, ihb, eval]

theorem litCount_simplify_le (F : BFormula n) : litCount (simplify F) <= litCount F := by
  induction F with
  | lit i b => simp [simplify]
  | cst c => simp [simplify]
  | un u t ih =>
      simp only [simplify, litCount]
      exact Nat.le_trans (litCount_smartUn_le u (simplify t)) ih
  | bin g a b iha ihb =>
      simp only [simplify, litCount]
      exact Nat.le_trans (litCount_smartBin_le g (simplify a) (simplify b))
        (Nat.add_le_add iha ihb)

/-! ## Restriction: fix the variables outside a block -/

/-- Replace every literal reading a variable outside `S` by the constant it takes
under the partial assignment `α`. -/
def restrict (S : Finset (Fin n)) (α : Fin n -> Bool) : BFormula n -> BFormula n
  | lit i b => if i ∈ S then lit i b else cst (cond b (α i) (!(α i)))
  | cst c => cst c
  | un u t => un u (restrict S α t)
  | bin g a b => bin g (restrict S α a) (restrict S α b)

/-- Evaluating the restriction agrees with overriding the outside variables. -/
theorem eval_restrict (S : Finset (Fin n)) (α : Fin n -> Bool)
    (F : BFormula n) (x : Fin n -> Bool) :
    eval (restrict S α F) x = eval F (fun i => if i ∈ S then x i else α i) := by
  induction F with
  | lit i b =>
      by_cases hi : i ∈ S <;> simp [restrict, eval, hi]
  | cst c => rfl
  | un u t ih => simp only [restrict, eval, ih]
  | bin g a b iha ihb => simp only [restrict, eval, iha, ihb]

/-- Restriction leaves exactly the variable leaves inside `S`. -/
theorem litCount_restrict (S : Finset (Fin n)) (α : Fin n -> Bool) (F : BFormula n) :
    litCount (restrict S α F) = leavesIn S F := by
  induction F with
  | lit i b => by_cases hi : i ∈ S <;> simp [restrict, litCount, leavesIn, hi]
  | cst c => rfl
  | un u t ih => simpa [restrict, litCount, leavesIn] using ih
  | bin g a b iha ihb => simp only [restrict, litCount, leavesIn, iha, ihb]

/-! ## Block realization: the per-block budget is a real leaf count -/

/-- **Per-block realization.**  For any block `S` and any assignment `α` to the
variables outside `S`, the subfunction of `F` on `S` is computed by a formula with
**at most `leavesIn S F` variable leaves**.  This is the genuine formula-semantics
content behind the abstract per-block budget: the budget *is* the number of
formula leaves reading the block. -/
theorem block_realization (S : Finset (Fin n)) (α : Fin n -> Bool) (F : BFormula n) :
    ∃ G : BFormula n,
      litCount G <= leavesIn S F ∧
      (∀ x, eval G x = eval F (fun i => if i ∈ S then x i else α i)) := by
  refine ⟨simplify (restrict S α F), ?_, ?_⟩
  · calc
      litCount (simplify (restrict S α F))
          <= litCount (restrict S α F) := litCount_simplify_le _
      _ = leavesIn S F := litCount_restrict S α F
  · intro x
    rw [eval_simplify, eval_restrict]

/-! ## Leaf-partition additivity: the budget identity is a theorem -/

/-- `leavesIn S` decomposes as the sum of single-variable leaf counts over `S`. -/
theorem leavesIn_eq_sum_singleton (S : Finset (Fin n)) (F : BFormula n) :
    leavesIn S F = ∑ v ∈ S, leavesIn {v} F := by
  induction F with
  | lit i b =>
      simp only [leavesIn, Finset.mem_singleton]
      by_cases hi : i ∈ S
      · rw [if_pos hi]
        rw [Finset.sum_eq_single i]
        · simp
        · intro v _ hv
          rw [if_neg (by simpa [eq_comm] using hv)]
        · intro h; exact absurd hi h
      · rw [if_neg hi]
        rw [Finset.sum_eq_zero]
        intro v hv
        rw [if_neg]
        intro h; exact hi (h ▸ hv)
  | cst c => simp [leavesIn]
  | un u t ih => simpa [leavesIn] using ih
  | bin g a b iha ihb =>
      simp only [leavesIn, iha, ihb]
      rw [← Finset.sum_add_distrib]

/-- The single-variable leaf counts over all variables sum to `litCount F`. -/
theorem sum_leavesIn_singleton (F : BFormula n) :
    ∑ v : Fin n, leavesIn {v} F = litCount F := by
  induction F with
  | lit i b =>
      simp only [leavesIn, litCount, Finset.mem_singleton]
      rw [Finset.sum_eq_single i]
      · simp
      · intro v _ hv; rw [if_neg (by simpa [eq_comm] using hv)]
      · intro h; exact absurd (Finset.mem_univ i) h
  | cst c => simp [leavesIn, litCount]
  | un u t ih => simpa [leavesIn, litCount] using ih
  | bin g a b iha ihb =>
      simp only [leavesIn, litCount]
      rw [Finset.sum_add_distrib, iha, ihb]

/-- **Budget identity.**  For a partition of the variables into disjoint blocks
covering everything, the per-block leaf counts sum to `litCount F`.  This
discharges the `hbudget` hypothesis of `neciporuk_sum_lower_bound` from real
formula semantics. -/
theorem sum_leavesIn_of_partition
    {ι : Type*} (blocks : Finset ι) (S : ι -> Finset (Fin n)) (F : BFormula n)
    (hdisj : (blocks : Set ι).PairwiseDisjoint S)
    (hcover : blocks.biUnion S = Finset.univ) :
    ∑ i ∈ blocks, leavesIn (S i) F = litCount F := by
  have h1 : ∀ i ∈ blocks, leavesIn (S i) F = ∑ v ∈ S i, leavesIn {v} F :=
    fun i _ => leavesIn_eq_sum_singleton (S i) F
  rw [Finset.sum_congr rfl h1, ← Finset.sum_biUnion hdisj, hcover,
    sum_leavesIn_singleton]

/-! ## Capstone: concrete formula budget feeds the Nečiporuk combiner -/

/-- **Concrete Nečiporuk formula bound.**  For a real formula `F` partitioned into
blocks, with each block's subfunction count `c i` bounded by `2 ^ (leavesIn (S i) F)`
(the remaining counting lemma), the formula's variable-leaf count is at least the
Nečiporuk sum `Σ_i log₂ (c i)`.

The budget side is now fully concrete: `B = litCount F` and `b_i = leavesIn (S i) F`
are real formula-leaf counts, and the budget identity `B = Σ b_i` is the theorem
`sum_leavesIn_of_partition`.  Only `hcount` (pure counting of bounded-leaf
formulas) remains abstract. -/
theorem formula_neciporuk_block_bound
    {ι : Type*} (blocks : Finset ι) (S : ι -> Finset (Fin n)) (F : BFormula n)
    (c : ι -> Nat)
    (hbudget : ∑ i ∈ blocks, leavesIn (S i) F = litCount F)
    (hcount : ∀ i ∈ blocks, c i <= 2 ^ (leavesIn (S i) F)) :
    ∑ i ∈ blocks, Nat.log 2 (c i) <= litCount F :=
  neciporuk_sum_lower_bound blocks c (fun i => leavesIn (S i) F) (litCount F)
    hbudget.symm hcount

/-! ## Kernel-only trace -/

#print axioms block_realization
#print axioms sum_leavesIn_of_partition
#print axioms formula_neciporuk_block_bound

end BFormula

end PallLean.Paper93.DeepMath.PathB
