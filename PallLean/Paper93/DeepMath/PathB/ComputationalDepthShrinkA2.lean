import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA1

/-!
# Shrinkage brick A2: restrictions and the simplifying surgery

Single-variable restrictions and the syntactic tree operations the one-step
lemma counts over:

* `subst1` — substitute one variable by a constant (kills exactly the leaves
  of that variable: **`subst1_lsize0`**, an exact count via `cntC`);
* `mkAnd`/`mkOr` — smart constructors absorbing constant children
  (evaluation-correct, size-nonincreasing);
* `simpC` — the recursive constant-elimination pass;
* **`subst1_eval`/`simpC_eval` (proved)** — both operations compute the
  restricted function;
* **`simpC_lsize0` (proved)** — simplification never increases the measure.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-! ### Restrictions -/

/-- A restriction: `none` = free, `some b` = fixed. -/
def Restr (n : ℕ) := Fin n → Option Bool

/-- The restricted function (variables stay in place). -/
def restrictF {n : ℕ} (ρ : Restr n) (f : (Fin n → Bool) → Bool) :
    (Fin n → Bool) → Bool :=
  fun x => f (fun i => (ρ i).getD (x i))

/-! ### Substitution -/

/-- The var-`i` leaf count. -/
def cntC {n : ℕ} (i : Fin n) : DMTreeC n → ℕ
  | .lit j _ => if j = i then 1 else 0
  | .cst _ => 0
  | .and l r => cntC i l + cntC i r
  | .or l r => cntC i l + cntC i r

/-- Substitute variable `i` by constant `b`. -/
def subst1 {n : ℕ} (i : Fin n) (b : Bool) : DMTreeC n → DMTreeC n
  | .lit j v => if j = i then .cst (b == v) else .lit j v
  | .cst v => .cst v
  | .and l r => .and (subst1 i b l) (subst1 i b r)
  | .or l r => .or (subst1 i b l) (subst1 i b r)

theorem subst1_eval {n : ℕ} (i : Fin n) (b : Bool) (t : DMTreeC n)
    (x : Fin n → Bool) :
    (subst1 i b t).eval x = t.eval (Function.update x i b) := by
  induction t with
  | lit j v =>
    by_cases hj : j = i
    · subst hj
      show (if j = j then (DMTreeC.cst (b == v) : DMTreeC n)
        else .lit j v).eval x = (Function.update x j b j == v)
      rw [if_pos rfl, Function.update_self]
      rfl
    · show (if j = i then (DMTreeC.cst (b == v) : DMTreeC n)
        else .lit j v).eval x = (Function.update x i b j == v)
      rw [if_neg hj, Function.update_of_ne hj]
      rfl
  | cst v => rfl
  | and l r ihl ihr => simp only [subst1, DMTreeC.eval, ihl, ihr]
  | or l r ihl ihr => simp only [subst1, DMTreeC.eval, ihl, ihr]

/-- **Substitution kills exactly the leaves of its variable (proved).** -/
theorem subst1_lsize0 {n : ℕ} (i : Fin n) (b : Bool) (t : DMTreeC n) :
    (subst1 i b t).lsize0 + cntC i t = t.lsize0 := by
  induction t with
  | lit j v =>
    by_cases hj : j = i
    · show (if j = i then (DMTreeC.cst (b == v) : DMTreeC n)
        else .lit j v).lsize0 + (if j = i then 1 else 0) = 1
      rw [if_pos hj, if_pos hj]
      rfl
    · show (if j = i then (DMTreeC.cst (b == v) : DMTreeC n)
        else .lit j v).lsize0 + (if j = i then 1 else 0) = 1
      rw [if_neg hj, if_neg hj]
      rfl
  | cst v => rfl
  | and l r ihl ihr =>
    show (subst1 i b l).lsize0 + (subst1 i b r).lsize0
      + (cntC i l + cntC i r) = l.lsize0 + r.lsize0
    omega
  | or l r ihl ihr =>
    show (subst1 i b l).lsize0 + (subst1 i b r).lsize0
      + (cntC i l + cntC i r) = l.lsize0 + r.lsize0
    omega

/-! ### Smart constructors -/

/-- AND with constant absorption. -/
def mkAnd {n : ℕ} : DMTreeC n → DMTreeC n → DMTreeC n
  | .cst false, _ => .cst false
  | .cst true, r => r
  | l, .cst false => .cst false
  | l, .cst true => l
  | l, r => .and l r

/-- OR with constant absorption. -/
def mkOr {n : ℕ} : DMTreeC n → DMTreeC n → DMTreeC n
  | .cst true, _ => .cst true
  | .cst false, r => r
  | l, .cst true => .cst true
  | l, .cst false => l
  | l, r => .or l r

theorem mkAnd_eval {n : ℕ} (l r : DMTreeC n) (x : Fin n → Bool) :
    (mkAnd l r).eval x = (l.eval x && r.eval x) := by
  cases l with
  | cst v =>
    cases v
    · rfl
    · rfl
  | lit i b =>
    cases r with
    | cst v =>
      cases v
      · show false = ((x i == b) && false)
        rw [Bool.and_false]
      · show (x i == b) = ((x i == b) && true)
        rw [Bool.and_true]
    | lit j v => rfl
    | and rl rr => rfl
    | or rl rr => rfl
  | and ll lr =>
    cases r with
    | cst v =>
      cases v
      · show false = ((ll.eval x && lr.eval x) && false)
        rw [Bool.and_false]
      · show (ll.eval x && lr.eval x) = ((ll.eval x && lr.eval x) && true)
        rw [Bool.and_true]
    | lit j v => rfl
    | and rl rr => rfl
    | or rl rr => rfl
  | or ll lr =>
    cases r with
    | cst v =>
      cases v
      · show false = ((ll.eval x || lr.eval x) && false)
        rw [Bool.and_false]
      · show (ll.eval x || lr.eval x) = ((ll.eval x || lr.eval x) && true)
        rw [Bool.and_true]
    | lit j v => rfl
    | and rl rr => rfl
    | or rl rr => rfl

theorem mkOr_eval {n : ℕ} (l r : DMTreeC n) (x : Fin n → Bool) :
    (mkOr l r).eval x = (l.eval x || r.eval x) := by
  cases l with
  | cst v =>
    cases v
    · rfl
    · rfl
  | lit i b =>
    cases r with
    | cst v =>
      cases v
      · show (x i == b) = ((x i == b) || false)
        rw [Bool.or_false]
      · show true = ((x i == b) || true)
        rw [Bool.or_true]
    | lit j v => rfl
    | and rl rr => rfl
    | or rl rr => rfl
  | and ll lr =>
    cases r with
    | cst v =>
      cases v
      · show (ll.eval x && lr.eval x) = ((ll.eval x && lr.eval x) || false)
        rw [Bool.or_false]
      · show true = ((ll.eval x && lr.eval x) || true)
        rw [Bool.or_true]
    | lit j v => rfl
    | and rl rr => rfl
    | or rl rr => rfl
  | or ll lr =>
    cases r with
    | cst v =>
      cases v
      · show (ll.eval x || lr.eval x) = ((ll.eval x || lr.eval x) || false)
        rw [Bool.or_false]
      · show true = ((ll.eval x || lr.eval x) || true)
        rw [Bool.or_true]
    | lit j v => rfl
    | and rl rr => rfl
    | or rl rr => rfl

theorem mkAnd_lsize0 {n : ℕ} (l r : DMTreeC n) :
    (mkAnd l r).lsize0 ≤ l.lsize0 + r.lsize0 := by
  cases l with
  | cst v =>
    cases v
    · exact Nat.zero_le _
    · show r.lsize0 ≤ 0 + r.lsize0
      omega
  | lit i b =>
    cases r with
    | cst v =>
      cases v
      · exact Nat.zero_le _
      · show (DMTreeC.lit i b).lsize0 ≤ (DMTreeC.lit i b).lsize0 + 0
        omega
    | lit j v => exact le_refl _
    | and rl rr => exact le_refl _
    | or rl rr => exact le_refl _
  | and ll lr =>
    cases r with
    | cst v =>
      cases v
      · exact Nat.zero_le _
      · show (DMTreeC.and ll lr).lsize0 ≤ (DMTreeC.and ll lr).lsize0 + 0
        omega
    | lit j v => exact le_refl _
    | and rl rr => exact le_refl _
    | or rl rr => exact le_refl _
  | or ll lr =>
    cases r with
    | cst v =>
      cases v
      · exact Nat.zero_le _
      · show (DMTreeC.or ll lr).lsize0 ≤ (DMTreeC.or ll lr).lsize0 + 0
        omega
    | lit j v => exact le_refl _
    | and rl rr => exact le_refl _
    | or rl rr => exact le_refl _

theorem mkOr_lsize0 {n : ℕ} (l r : DMTreeC n) :
    (mkOr l r).lsize0 ≤ l.lsize0 + r.lsize0 := by
  cases l with
  | cst v =>
    cases v
    · show r.lsize0 ≤ 0 + r.lsize0
      omega
    · exact Nat.zero_le _
  | lit i b =>
    cases r with
    | cst v =>
      cases v
      · show (DMTreeC.lit i b).lsize0 ≤ (DMTreeC.lit i b).lsize0 + 0
        omega
      · exact Nat.zero_le _
    | lit j v => exact le_refl _
    | and rl rr => exact le_refl _
    | or rl rr => exact le_refl _
  | and ll lr =>
    cases r with
    | cst v =>
      cases v
      · show (DMTreeC.and ll lr).lsize0 ≤ (DMTreeC.and ll lr).lsize0 + 0
        omega
      · exact Nat.zero_le _
    | lit j v => exact le_refl _
    | and rl rr => exact le_refl _
    | or rl rr => exact le_refl _
  | or ll lr =>
    cases r with
    | cst v =>
      cases v
      · show (DMTreeC.or ll lr).lsize0 ≤ (DMTreeC.or ll lr).lsize0 + 0
        omega
      · exact Nat.zero_le _
    | lit j v => exact le_refl _
    | and rl rr => exact le_refl _
    | or rl rr => exact le_refl _

/-! ### The simplification pass -/

/-- Recursive constant elimination. -/
def simpC {n : ℕ} : DMTreeC n → DMTreeC n
  | .lit i b => .lit i b
  | .cst v => .cst v
  | .and l r => mkAnd (simpC l) (simpC r)
  | .or l r => mkOr (simpC l) (simpC r)

theorem simpC_eval {n : ℕ} (t : DMTreeC n) (x : Fin n → Bool) :
    (simpC t).eval x = t.eval x := by
  induction t with
  | lit i b => rfl
  | cst v => rfl
  | and l r ihl ihr =>
    show (mkAnd (simpC l) (simpC r)).eval x = (l.eval x && r.eval x)
    rw [mkAnd_eval, ihl, ihr]
  | or l r ihl ihr =>
    show (mkOr (simpC l) (simpC r)).eval x = (l.eval x || r.eval x)
    rw [mkOr_eval, ihl, ihr]

theorem simpC_lsize0 {n : ℕ} (t : DMTreeC n) : (simpC t).lsize0 ≤ t.lsize0 := by
  induction t with
  | lit i b => exact le_refl _
  | cst v => exact le_refl _
  | and l r ihl ihr =>
    show (mkAnd (simpC l) (simpC r)).lsize0 ≤ l.lsize0 + r.lsize0
    calc (mkAnd (simpC l) (simpC r)).lsize0
        ≤ (simpC l).lsize0 + (simpC r).lsize0 := mkAnd_lsize0 _ _
      _ ≤ l.lsize0 + r.lsize0 := Nat.add_le_add ihl ihr
  | or l r ihl ihr =>
    show (mkOr (simpC l) (simpC r)).lsize0 ≤ l.lsize0 + r.lsize0
    calc (mkOr (simpC l) (simpC r)).lsize0
        ≤ (simpC l).lsize0 + (simpC r).lsize0 := mkOr_lsize0 _ _
      _ ≤ l.lsize0 + r.lsize0 := Nat.add_le_add ihl ihr

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.subst1_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.subst1_lsize0
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.simpC_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.simpC_lsize0
