import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Lattice
import Mathlib.Logic.Equiv.Basic
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFormulaLeafSemantics
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRemainingLine

/-!
# The doubling, proved — in a named restricted model

`RemainingLine.CostSuper cbudget := ∀ d, 2 · cbudget d ≤ cbudget (d+1)` is *the*
open line: for the SAT family it is `NP ⊄ P/poly = P ≠ NP`, deliberately left
unproved (`ComputationalDepthRemainingLine`).  This file proves `CostSuper`
**unconditionally for a different, named family** where the doubling genuinely
holds, and states exactly why SAT does not inherit it.

## The model and the family

* **Model:** Boolean formulas (a *tree* — fan-out one — over the full unary/binary
  basis), size = number of variable leaves (`TForm.litCount`).  Fan-out one is the
  restriction: a formula cannot reuse a sub-computation, i.e. **no mass production**.
* **Family:** the disjoint self-composition tower.  Variables at level `d` are the
  leaves `Vars d` of a complete binary tree (`|Vars d| = 2^d`), and
  `tfn (d+1) x = tfn d (x∘inl) ∧ tfn d (x∘inr)` composes two copies of level `d`
  over **disjoint** variable blocks.  `tfn d` is the `AND` of all `2^d` leaves.

## What is proved (unconditionally, axiom-clean)

* `card_le_litCount` — a formula computing a function that depends on all its
  variables needs at least one leaf per variable (the anti-sharing core: fan-out
  one ⇒ every relevant variable is paid for).
* `cbudget_eq : cbudget d = 2 ^ d` — the minimum formula size of level `d` is
  *exactly* `2^d` (lower bound from `card_le_litCount`, upper bound from the
  explicit tower formula `tform d`).
* `cost_super : CostSuper cbudget` — **the doubling, proved.**
  `2 · cbudget d = 2·2^d = 2^(d+1) = cbudget (d+1)`.
* `not_polybounded : ¬ PolyBounded cbudget` — feeding `cost_super` into the repo's
  `RemainingLine.what_remains`: this family's per-level cost has no polynomial
  bound *in the level `d`*.

## Honest cap — why this is NOT `P ≠ NP`

The doubling is real, but it is bought with **variable disjointness**: level `d+1`
uses `2^d + 2^d` *fresh* variables, so `cbudget d = 2^d` is exactly `|Vars d|` —
**linear in the input size**, not superpolynomial in it.  `not_polybounded` is
superpoly in the *level* `d`, but `d = log₂ n`, so in `n` the family is linear.

SAT self-reduces with **shared** variables: `SAT_{n+1}` has one more variable than
`SAT_n`, not twice as many.  There the per-variable accounting used here gives only
`+1`, not `×2`; forcing `×2` while the variable count grows by `+1` is precisely
"the two branches cannot share circuitry over their common variables" — the
Uhlig no-sharing / Valiant rigidity wall, which is open.  So the two ingredients
needed for `P ≠ NP` — the doubling **and** `n = poly(d)` — are separated here: this
family has the doubling but pays for it in variables; SAT keeps `n = d` but cannot
get the doubling.  This file makes that trade precise and machine-checked.
-/

namespace PallLean.Paper93.DeepMath.PathB.MuxDoubling

open Finset

/-! ## A formula model over an arbitrary (finite) variable set -/

/-- Boolean formulas over variable set `V`, full unary/binary basis.  A *tree*:
each node has one parent, so no sub-formula can be shared (fan-out one). -/
inductive TForm (V : Type) where
  | lit : V → Bool → TForm V
  | cst : Bool → TForm V
  | un  : (Bool → Bool) → TForm V → TForm V
  | bin : (Bool → Bool → Bool) → TForm V → TForm V → TForm V

namespace TForm

variable {V W : Type}

/-- Evaluation. -/
def eval : TForm V → (V → Bool) → Bool
  | lit i b, x => cond b (x i) (!(x i))
  | cst c, _ => c
  | un u t, x => u (eval t x)
  | bin g a b, x => g (eval a x) (eval b x)

/-- Number of variable leaves — the formula size metric. -/
def litCount : TForm V → Nat
  | lit _ _ => 1
  | cst _ => 0
  | un _ t => litCount t
  | bin _ a b => litCount a + litCount b

/-- Number of variable leaves reading the specific variable `i`. -/
def leafOn [DecidableEq V] (i : V) : TForm V → Nat
  | lit j _ => if j = i then 1 else 0
  | cst _ => 0
  | un _ t => leafOn i t
  | bin _ a b => leafOn i a + leafOn i b

/-- Relabel variables along `g`. -/
def map (g : V → W) : TForm V → TForm W
  | lit i b => lit (g i) b
  | cst c => cst c
  | un u t => un u (map g t)
  | bin gg a b => bin gg (map g a) (map g b)

theorem eval_map (g : V → W) (F : TForm V) (x : W → Bool) :
    eval (map g F) x = eval F (fun v => x (g v)) := by
  induction F with
  | lit i b => rfl
  | cst c => rfl
  | un u t ih => simp [map, eval, ih]
  | bin gg a b iha ihb => simp [map, eval, iha, ihb]

theorem litCount_map (g : V → W) (F : TForm V) : litCount (map g F) = litCount F := by
  induction F with
  | lit i b => rfl
  | cst c => rfl
  | un u t ih => simpa [map, litCount] using ih
  | bin gg a b iha ihb => simp [map, litCount, iha, ihb]

/-- If no leaf reads `i`, the formula is independent of `i`. -/
theorem eval_indep_of_leafOn_zero [DecidableEq V] (i : V) (F : TForm V)
    (h : leafOn i F = 0) (x : V → Bool) (b : Bool) :
    eval F (Function.update x i b) = eval F x := by
  induction F with
  | lit j c =>
      have hji : j ≠ i := by
        intro e; subst e; simp [leafOn] at h
      simp only [eval, Function.update_apply, if_neg hji]
  | cst c => rfl
  | un u t ih =>
      simp only [leafOn] at h
      simp only [eval, ih h]
  | bin g a b iha ihb =>
      simp only [leafOn] at h
      have ha : leafOn i a = 0 := by omega
      have hb : leafOn i b = 0 := by omega
      simp only [eval, iha ha, ihb hb]

/-- Contrapositive: if `F` distinguishes a flip of `i`, some leaf reads `i`. -/
theorem leafOn_pos_of_eval_depends [DecidableEq V] (i : V) (F : TForm V)
    (h : ∃ x b, eval F (Function.update x i b) ≠ eval F x) : 1 ≤ leafOn i F := by
  rcases Nat.eq_zero_or_pos (leafOn i F) with h0 | hp
  · exfalso
    obtain ⟨x, b, hx⟩ := h
    exact hx (eval_indep_of_leafOn_zero i F h0 x b)
  · exact hp

/-- Leaf counts partition: `∑_v leafOn v F = litCount F`. -/
theorem sum_leafOn [Fintype V] [DecidableEq V] (F : TForm V) :
    ∑ v, leafOn v F = litCount F := by
  induction F with
  | lit j c => simp [leafOn, litCount, Finset.sum_ite_eq]
  | cst c => simp [leafOn, litCount]
  | un u t ih => simpa [leafOn, litCount] using ih
  | bin g a b iha ihb =>
      simp only [leafOn, litCount]
      rw [Finset.sum_add_distrib, iha, ihb]

/-- **Anti-sharing core.**  Any formula computing a function that depends on every
variable has at least one leaf per variable — so its size is at least the number of
variables.  Fan-out one means a needed variable cannot be "shared away". -/
theorem card_le_litCount [Fintype V] [DecidableEq V]
    (φ : (V → Bool) → Bool) (F : TForm V)
    (hcomp : ∀ x, eval F x = φ x)
    (hdep : ∀ v : V, ∃ x b, φ (Function.update x v b) ≠ φ x) :
    Fintype.card V ≤ litCount F := by
  have hsum : (∑ _v : V, (1 : Nat)) = Fintype.card V := by
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ]
  rw [← sum_leafOn F, ← hsum]
  apply Finset.sum_le_sum
  intro v _
  obtain ⟨x, b, hx⟩ := hdep v
  exact leafOn_pos_of_eval_depends v F ⟨x, b, by rw [hcomp, hcomp]; exact hx⟩

end TForm

/-! ## The disjoint self-composition tower -/

/-- Leaves of a complete binary tree of depth `d`: the variables of level `d`.
`Vars (d+1)` is two disjoint copies of `Vars d`. -/
inductive Vars : Nat → Type where
  | leaf : Vars 0
  | inl : {d : Nat} → Vars d → Vars (d + 1)
  | inr : {d : Nat} → Vars d → Vars (d + 1)
  deriving DecidableEq

/-- `Vars (d+1) ≃ Vars d ⊕ Vars d` — the disjointness of the two blocks. -/
def varsEquivSum {d : Nat} : Vars (d + 1) ≃ Vars d ⊕ Vars d where
  toFun v := match v with
    | Vars.inl w => Sum.inl w
    | Vars.inr w => Sum.inr w
  invFun s := match s with
    | Sum.inl w => Vars.inl w
    | Sum.inr w => Vars.inr w
  left_inv v := by cases v with | inl w => rfl | inr w => rfl
  right_inv s := by cases s with | inl w => rfl | inr w => rfl

/-- `Vars d` is finite. -/
def varsFintype : (d : Nat) → Fintype (Vars d)
  | 0 => ⟨{Vars.leaf}, by intro v; cases v; exact Finset.mem_singleton_self _⟩
  | (d + 1) =>
      letI := varsFintype d
      Fintype.ofEquiv (Vars d ⊕ Vars d) varsEquivSum.symm

instance (d : Nat) : Fintype (Vars d) := varsFintype d

theorem card_vars : (d : Nat) → Fintype.card (Vars d) = 2 ^ d
  | 0 => rfl
  | (d + 1) => by
      rw [Fintype.card_congr (varsEquivSum (d := d)), Fintype.card_sum, card_vars d, pow_succ]
      omega

/-- The level-`d` function: `AND` of all `2^d` leaves, composed over disjoint blocks. -/
def tfn : (d : Nat) → (Vars d → Bool) → Bool
  | 0, x => x Vars.leaf
  | (d + 1), x => (tfn d (fun v => x (Vars.inl v))) && (tfn d (fun v => x (Vars.inr v)))

/-- The explicit tower formula realizing `tfn d` — the upper-bound witness. -/
def tform : (d : Nat) → TForm (Vars d)
  | 0 => TForm.lit Vars.leaf true
  | (d + 1) => TForm.bin (· && ·) (TForm.map Vars.inl (tform d)) (TForm.map Vars.inr (tform d))

theorem tform_eval : ∀ (d : Nat) (x : Vars d → Bool), TForm.eval (tform d) x = tfn d x
  | 0, x => rfl
  | (d + 1), x => by
      simp only [tform, TForm.eval, TForm.eval_map, tfn]
      rw [tform_eval d, tform_eval d]

theorem tform_litCount : ∀ (d : Nat), TForm.litCount (tform d) = 2 ^ d
  | 0 => rfl
  | (d + 1) => by
      simp only [tform, TForm.litCount, TForm.litCount_map]
      rw [tform_litCount d, pow_succ]
      omega

/-- `tfn d x = true` exactly when every leaf is set. -/
theorem tfn_true_iff : ∀ (d : Nat) (x : Vars d → Bool), tfn d x = true ↔ ∀ v, x v = true
  | 0, x => by
      simp only [tfn]
      constructor
      · intro h v; cases v; exact h
      · intro h; exact h Vars.leaf
  | (d + 1), x => by
      simp only [tfn, Bool.and_eq_true]
      rw [tfn_true_iff d, tfn_true_iff d]
      constructor
      · rintro ⟨hl, hr⟩ v
        cases v with
        | inl w => exact hl w
        | inr w => exact hr w
      · intro h
        exact ⟨fun w => h (Vars.inl w), fun w => h (Vars.inr w)⟩

/-- Every level-`d` variable is relevant: flipping it off a satisfied input changes `tfn d`. -/
theorem tfn_depends (d : Nat) (v : Vars d) :
    ∃ x b, tfn d (Function.update x v b) ≠ tfn d x := by
  refine ⟨(fun _ => true), false, ?_⟩
  have hall : tfn d (fun _ => true) = true := (tfn_true_iff d _).mpr (fun _ => rfl)
  have hne : tfn d (Function.update (fun _ => true) v false) ≠ true := by
    intro hc
    have hv := (tfn_true_iff d _).mp hc v
    rw [Function.update_apply] at hv
    simp at hv
  rw [hall]
  exact hne

/-! ## The minimum formula size and the doubling -/

/-- `cbudget d` = minimum number of leaves over all formulas computing `tfn d`. -/
noncomputable def cbudget (d : Nat) : Nat :=
  sInf { m | ∃ F : TForm (Vars d), (∀ x, TForm.eval F x = tfn d x) ∧ TForm.litCount F = m }

theorem cbudget_le (d : Nat) : cbudget d ≤ 2 ^ d :=
  Nat.sInf_le ⟨tform d, tform_eval d, tform_litCount d⟩

theorem le_cbudget (d : Nat) : 2 ^ d ≤ cbudget d := by
  have hne :
      ({ m | ∃ F : TForm (Vars d),
          (∀ x, TForm.eval F x = tfn d x) ∧ TForm.litCount F = m }).Nonempty :=
    ⟨2 ^ d, tform d, tform_eval d, tform_litCount d⟩
  obtain ⟨F, hcomp, hlit⟩ := Nat.sInf_mem hne
  have hcard := TForm.card_le_litCount (tfn d) F hcomp (tfn_depends d)
  rw [card_vars d] at hcard
  rw [hlit] at hcard
  exact hcard

/-- **The minimum formula size of the tower is exactly `2^d`.** -/
theorem cbudget_eq (d : Nat) : cbudget d = 2 ^ d :=
  le_antisymm (cbudget_le d) (le_cbudget d)

/-- **The doubling, proved** — `CostSuper` holds for this named family:
`2 · cbudget d ≤ cbudget (d+1)`. -/
theorem cost_super : RemainingLine.CostSuper cbudget := by
  intro d
  rw [cbudget_eq d, cbudget_eq (d + 1), pow_succ]
  omega

theorem cbudget_base : 1 ≤ cbudget 0 := by
  rw [cbudget_eq]; decide

/-- Feeding the proved doubling into the repo's capstone: this family's per-level
cost has no polynomial bound **in the level `d`**.  (See the honest cap in the
module docstring: `d = log₂ n`, so in the input size `n` the family is linear —
this is not `NP ⊄ P/poly`.) -/
theorem not_polybounded : ¬ RemainingLine.PolyBounded cbudget :=
  RemainingLine.what_remains cbudget cbudget_base cost_super

/-! ## Kernel-only trace -/

#print axioms cbudget_eq
#print axioms cost_super
#print axioms not_polybounded

end PallLean.Paper93.DeepMath.PathB.MuxDoubling
