import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCircuitDependency

/-!
# N-Frame: gate elimination — the strict restriction engine

Dependency counting (previous file) is the degenerate case of gate elimination.  This file builds the genuine,
non-degenerate engine — in the **tree** model, where it is clean: no wire-index surgery, only structural rewriting.

**The mechanism.**  Restrict a variable `i` to a constant `b` (`substVar`: swap each `var i` leaf for `cst b`, volume
unchanged, computes the restricted function).  A constant leaf sitting under an operator is *reducible*: `un op (cst v)`
folds to `cst (op v)`; `bin op (cst v) r` folds to `un (op v ·) r`; `bin op l (cst v)` to `un (· op v) l` — each a
semantics-preserving rewrite removing **exactly one node** (`exists_reduce`).  When `f` genuinely depends on `i`, its
optimal tree contains a `var i` leaf whose parent is an operator, so restriction *creates* a reducible node
(`substVar_hasRed`).

  `exists_reduce` — **PROVED**: a reducible tree has an equivalent tree of strictly smaller volume.
  `budget_restrict_lt` — **PROVED, the engine**: if `f` depends on `i` and `budget f ≥ 2`, then
        `budget (f|ᵢ₌b) + 1 ≤ budget f` — each restriction of a live variable strictly kills a gate.
  `sat3_signbit_restrict_lt` — **PROVED, calibration on the target**: restricting a clause block's sign bit strictly
        decreases the SAT family's tree budget.

## Honest scope

This is the exact engine behind the classical `2n − O(1)` and `3n`/`5n` circuit lower bounds.  Its single step is now
formal and clean.  Scaling it past the linear `N/3` already proved requires a **dependence-preserving restriction
schedule** — a sequence of variables each still live after the earlier fixings — which is the delicate combinatorial
core of every super-linear gate-elimination bound and is the open rung (in the DAG model it also reinstates the
wire-surgery this tree formulation sidesteps).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Substitution of a variable by a constant -/

/-- Replace every `var i` leaf by `cst b`. -/
def substVar {n : ℕ} (i : Fin n) (b : Bool) : Trans n → Trans n
  | .var j => if j = i then .cst b else .var j
  | .cst c => .cst c
  | .un op s => .un op (substVar i b s)
  | .bin op s t => .bin op (substVar i b s) (substVar i b t)

theorem substVar_eval {n : ℕ} (i : Fin n) (b : Bool) (t : Trans n) (x : Fin n → Bool) :
    eval (substVar i b t) x = eval t (Function.update x i b) := by
  induction t with
  | var j =>
    show eval (if j = i then Trans.cst b else Trans.var j) x = Function.update x i b j
    by_cases hj : j = i
    · rw [if_pos hj, hj]
      show b = Function.update x i b i
      rw [Function.update_self]
    · rw [if_neg hj]
      show x j = Function.update x i b j
      rw [Function.update_of_ne hj]
  | cst c => rfl
  | un op s ih =>
    show op (eval (substVar i b s) x) = op (eval s (Function.update x i b))
    rw [ih]
  | bin op s t ihs iht =>
    show op (eval (substVar i b s) x) (eval (substVar i b t) x)
        = op (eval s (Function.update x i b)) (eval t (Function.update x i b))
    rw [ihs, iht]

theorem substVar_volume {n : ℕ} (i : Fin n) (b : Bool) (t : Trans n) :
    volume (substVar i b t) = volume t := by
  induction t with
  | var j =>
    by_cases hj : j = i <;> simp [substVar, volume, hj]
  | cst c => rfl
  | un op s ih =>
    show volume (substVar i b s) + 1 = volume s + 1
    rw [ih]
  | bin op s t ihs iht =>
    show volume (substVar i b s) + volume (substVar i b t) + 1 = volume s + volume t + 1
    rw [ihs, iht]

/-! ### Reducibility and the one-node rewrite -/

/-- Is the tree a constant leaf? -/
def isCst {n : ℕ} : Trans n → Bool
  | .cst _ => true
  | _ => false

theorem isCst_eq {n : ℕ} (t : Trans n) (h : isCst t = true) : ∃ v, t = Trans.cst v := by
  cases t with
  | cst v => exact ⟨v, rfl⟩
  | var j => exact absurd h (by simp [isCst])
  | un op s => exact absurd h (by simp [isCst])
  | bin op s t => exact absurd h (by simp [isCst])

/-- Does the tree contain a constant leaf directly under an operator? -/
def hasRed {n : ℕ} : Trans n → Bool
  | .var _ => false
  | .cst _ => false
  | .un _ s => isCst s || hasRed s
  | .bin _ s t => isCst s || isCst t || hasRed s || hasRed t

/-- **The one-node rewrite (proved)**: a reducible tree has an equivalent tree of strictly smaller volume. -/
theorem exists_reduce {n : ℕ} (t : Trans n) (h : hasRed t = true) :
    ∃ t' : Trans n, eval t' = eval t ∧ volume t' + 1 ≤ volume t := by
  induction t with
  | var j => exact absurd h (by simp [hasRed])
  | cst c => exact absurd h (by simp [hasRed])
  | un op s ih =>
    by_cases hcs : isCst s = true
    · obtain ⟨v, rfl⟩ := isCst_eq s hcs
      refine ⟨Trans.cst (op v), ?_, ?_⟩
      · funext x
        rfl
      · show (1 : ℕ) + 1 ≤ 1 + 1
        omega
    · have hs : hasRed s = true := by
        have : (isCst s || hasRed s) = true := h
        rw [Bool.or_eq_true] at this
        rcases this with h1 | h1
        · exact absurd h1 hcs
        · exact h1
      obtain ⟨s', hse, hsv⟩ := ih hs
      refine ⟨Trans.un op s', ?_, ?_⟩
      · funext x
        show op (eval s' x) = op (eval s x)
        rw [show eval s' = eval s from hse]
      · have e1 : volume (Trans.un op s') = volume s' + 1 := rfl
        have e2 : volume (Trans.un op s) = volume s + 1 := rfl
        omega
  | bin op s t ihs iht =>
    by_cases hcs : isCst s = true
    · obtain ⟨v, rfl⟩ := isCst_eq s hcs
      refine ⟨Trans.un (fun a => op v a) t, ?_, ?_⟩
      · funext x
        rfl
      · show volume t + 1 + 1 ≤ 1 + volume t + 1
        omega
    · by_cases hct : isCst t = true
      · obtain ⟨v, rfl⟩ := isCst_eq t hct
        refine ⟨Trans.un (fun a => op a v) s, ?_, ?_⟩
        · funext x
          rfl
        · show volume s + 1 + 1 ≤ volume s + 1 + 1
          omega
      · have hor : (hasRed s || hasRed t) = true := by
          have hall : (isCst s || isCst t || hasRed s || hasRed t) = true := h
          rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true] at hall
          rcases hall with ((h1 | h1) | h1) | h1
          · exact absurd h1 hcs
          · exact absurd h1 hct
          · rw [Bool.or_eq_true]; exact Or.inl h1
          · rw [Bool.or_eq_true]; exact Or.inr h1
        rw [Bool.or_eq_true] at hor
        rcases hor with hs | ht
        · obtain ⟨s', hse, hsv⟩ := ihs hs
          refine ⟨Trans.bin op s' t, ?_, ?_⟩
          · funext x
            show op (eval s' x) (eval t x) = op (eval s x) (eval t x)
            rw [show eval s' = eval s from hse]
          · have e1 : volume (Trans.bin op s' t) = volume s' + volume t + 1 := rfl
            have e2 : volume (Trans.bin op s t) = volume s + volume t + 1 := rfl
            omega
        · obtain ⟨t', hte, htv⟩ := iht ht
          refine ⟨Trans.bin op s t', ?_, ?_⟩
          · funext x
            show op (eval s x) (eval t' x) = op (eval s x) (eval t x)
            rw [show eval t' = eval t from hte]
          · have e1 : volume (Trans.bin op s t') = volume s + volume t' + 1 := rfl
            have e2 : volume (Trans.bin op s t) = volume s + volume t + 1 := rfl
            omega

/-! ### Dependence forces a variable leaf, restriction forces reducibility -/

/-- The variable-membership flag. -/
def hasVar {n : ℕ} (i : Fin n) : Trans n → Bool
  | .var j => decide (j = i)
  | .cst _ => false
  | .un _ s => hasVar i s
  | .bin _ s t => hasVar i s || hasVar i t

theorem eval_update_of_hasVar_false {n : ℕ} (i : Fin n) (t : Trans n)
    (h : hasVar i t = false) (x : Fin n → Bool) (b : Bool) :
    eval t (Function.update x i b) = eval t x := by
  induction t with
  | var j =>
    have hj : ¬(j = i) := by
      intro hji
      rw [show hasVar i (Trans.var j) = decide (j = i) from rfl, hji] at h
      simp at h
    show Function.update x i b j = x j
    rw [Function.update_of_ne hj]
  | cst c => rfl
  | un op s ih =>
    show op (eval s (Function.update x i b)) = op (eval s x)
    rw [ih h]
  | bin op s t ihs iht =>
    have h2 : hasVar i s = false ∧ hasVar i t = false := by
      have : (hasVar i s || hasVar i t) = false := h
      rw [Bool.or_eq_false_iff] at this
      exact this
    show op (eval s (Function.update x i b)) (eval t (Function.update x i b))
        = op (eval s x) (eval t x)
    rw [ihs h2.1, iht h2.2]

theorem hasVar_of_depends {n : ℕ} (i : Fin n) (t : Trans n) (x₁ x₀ : Fin n → Bool)
    (hdiff : ∀ c, c ≠ i → x₁ c = x₀ c) (hne : eval t x₁ ≠ eval t x₀) :
    hasVar i t = true := by
  by_contra hcon
  rw [Bool.not_eq_true] at hcon
  apply hne
  have hx : x₁ = Function.update x₀ i (x₁ i) := by
    funext c
    by_cases hc : c = i
    · rw [hc, Function.update_self]
    · rw [Function.update_of_ne hc]
      exact hdiff c hc
  rw [hx]
  exact eval_update_of_hasVar_false i t hcon x₀ (x₁ i)

theorem leaf_hasVar {n : ℕ} (i : Fin n) (t : Trans n) (hvar : hasVar i t = true)
    (hvol : volume t = 1) : t = Trans.var i := by
  cases t with
  | var j =>
    have : decide (j = i) = true := hvar
    rw [decide_eq_true_eq] at this
    rw [this]
  | cst c => exact absurd hvar (by simp [hasVar])
  | un op s =>
    exact absurd hvol (by
      show ¬(volume s + 1 = 1)
      have := volume_pos s
      omega)
  | bin op s t =>
    exact absurd hvol (by
      show ¬(volume s + volume t + 1 = 1)
      have := volume_pos s
      have := volume_pos t
      omega)

/-- **Restriction forces reducibility (proved)**: if `t` depends on `i` and has volume `≥ 2`, substituting `i`
creates a constant leaf under an operator. -/
theorem substVar_hasRed {n : ℕ} (i : Fin n) (b : Bool) (t : Trans n)
    (hvar : hasVar i t = true) (hvol : 2 ≤ volume t) :
    hasRed (substVar i b t) = true := by
  induction t with
  | var j =>
    exact absurd hvol (by
      show ¬(2 ≤ 1)
      omega)
  | cst c => exact absurd hvar (by simp [hasVar])
  | un op s ih =>
    have hvs : hasVar i s = true := hvar
    show (isCst (substVar i b s) || hasRed (substVar i b s)) = true
    rw [Bool.or_eq_true]
    by_cases hs1 : volume s = 1
    · left
      have hsi := leaf_hasVar i s hvs hs1
      rw [hsi]
      show isCst (if i = i then Trans.cst b else Trans.var i) = true
      rw [if_pos rfl]
      rfl
    · right
      have hge : 2 ≤ volume s := by
        have := volume_pos s
        omega
      exact ih hvs hge
  | bin op s t ihs iht =>
    show (isCst (substVar i b s) || isCst (substVar i b t)
        || hasRed (substVar i b s) || hasRed (substVar i b t)) = true
    have hvar' : (hasVar i s || hasVar i t) = true := hvar
    rw [Bool.or_eq_true] at hvar'
    rcases hvar' with hs | ht
    · by_cases hs1 : volume s = 1
      · have hsi := leaf_hasVar i s hs hs1
        rw [hsi]
        show (isCst (if i = i then Trans.cst b else Trans.var i) || _ || _ || _) = true
        rw [if_pos rfl]
        rfl
      · have hge : 2 ≤ volume s := by
          have := volume_pos s
          omega
        have := ihs hs hge
        rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true]
        left; right
        exact this
    · by_cases ht1 : volume t = 1
      · have hti := leaf_hasVar i t ht ht1
        rw [hti]
        show (_ || isCst (if i = i then Trans.cst b else Trans.var i) || _ || _) = true
        rw [if_pos rfl]
        rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true]
        left; left; right
        rfl
      · have hge : 2 ≤ volume t := by
          have := volume_pos t
          omega
        have := iht ht hge
        rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true]
        right
        exact this

/-! ### The gate-elimination engine -/

/-- **THE GATE-ELIMINATION ENGINE (proved)**: restricting a live variable strictly kills a gate.  If `f` depends on
`i` (a 1/0-pair differing only at `i`) and `budget f ≥ 2`, then `budget (f|ᵢ₌b) + 1 ≤ budget f`. -/
theorem budget_restrict_lt {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) (b : Bool)
    (x₁ x₀ : Fin n → Bool) (hdiff : ∀ c, c ≠ i → x₁ c = x₀ c) (hne : f x₁ ≠ f x₀)
    (h2 : 2 ≤ budget f) :
    budget (fun x => f (Function.update x i b)) + 1 ≤ budget f := by
  have hne' : {v | ∃ t : Trans n, eval t = f ∧ volume t = v}.Nonempty :=
    ⟨volume (dnfFor f), dnfFor f, eval_dnfFor f, rfl⟩
  obtain ⟨t, hte, htv⟩ := Nat.sInf_mem hne'
  have hbud : volume t = budget f := htv
  have hvar : hasVar i t = true := by
    apply hasVar_of_depends i t x₁ x₀ hdiff
    rw [show eval t = f from hte]
    exact hne
  have hvol : 2 ≤ volume t := by omega
  have hred := substVar_hasRed i b t hvar hvol
  obtain ⟨t', hte', htv'⟩ := exists_reduce (substVar i b t) hred
  have hcomp : eval t' = fun x => f (Function.update x i b) := by
    funext x
    rw [show eval t' = eval (substVar i b t) from hte', substVar_eval,
      show eval t = f from hte]
  have hbg : budget (fun x => f (Function.update x i b)) ≤ volume t' :=
    Nat.sInf_le ⟨t', hcomp, rfl⟩
  have hsv : volume (substVar i b t) = volume t := substVar_volume i b t
  omega

/-- **Calibration on the SAT target (proved)**: restricting a clause block's sign bit strictly decreases the SAT
family's tree budget — the engine engages on the true target. -/
theorem sat3_signbit_restrict_lt (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (c : Fin (sat3M N)) (b : Bool) :
    budget (fun x => sat3Family N (Function.update x (sat3SignBit N c) b)) + 1
      ≤ budget (sat3Family N) := by
  obtain ⟨x₁, x₀, h1, h0, hforce⟩ := sat3_forcing_pair N hv hm3 c
  have h2 : 2 ≤ budget (sat3Family N) := by
    have hlb := sat3_budget_lb_improved N hv
    have hmv : 3 ≤ sat3M N * sat3V N :=
      le_trans hm3 (Nat.le_mul_of_pos_right _ (by omega))
    omega
  refine budget_restrict_lt (sat3Family N) (sat3SignBit N c) b x₁ x₀ ?_ ?_ h2
  · intro d hd
    by_contra hbb
    exact hd (hforce d hbb)
  · rw [h1, h0]
    decide

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.exists_reduce
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.budget_restrict_lt
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_signbit_restrict_lt
