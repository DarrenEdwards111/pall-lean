import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameBoundaryTreewidth

/-!
# N-Frame: pushing the dimension gap — and the no-go that redirects it

This file pushes the boundary-*dimension* gap on concrete targets — and proves the honest outcome, which is a **no-go**:

  `boundaryDim_parity_le` — **PROVED**: parity has boundary dimension `≤ 2` (an XOR caterpillar).  The natural first
        target is *low* — as HAL's screens predicted (parity is a simple local automaton), and unlike sensitivity, the
        dimension does not get fooled into rating parity hard.
  `boundaryDim_le_three` — **PROVED, the no-go**: *every* Boolean function has boundary dimension `≤ 3`.  A DNF
        caterpillar (an OR-chain of AND-chain minterms) evaluates any function with three live registers — at
        exponential *volume*.

**What the no-go means.**  The *pure* dimension gap is empty: no target — not SAT, not the permanent, nothing — can tear
the boundary in *width alone*, because unbounded volume can always buy constant width.  The tearing book1 describes is
therefore necessarily **joint**: high width *under a polynomial volume budget*.  The thermodynamic reading is exact —
`volume` is the energy, `width` is the dimension, and the invariant with separating content is the *trade-off* (dimension
under bounded energy), not either measure alone.  This is a genuine sharpening: it converts "find a high-dimension
target" (impossible, by this file) into "prove a width–volume trade-off lower bound" — which is exactly the classical
size–width trade-off territory (Nečiporuk-style bounds, where this repo already has a real `n²/log n` restricted kernel).

## Honest scope

Both results are unconditional.  The no-go does **not** refute the boundary programme — it locates its content: the joint
budget `poly volume ∧ low width` defines the genuine observer class, and the open gap is a trade-off lower bound (an
`NP` target needing super-constant width at every polynomial-volume embedding).  That trade-off bound is a real open
problem (formula/branching-program strength, far beyond this file), untouched here.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {n : ℕ}

/-! ### The specific target: parity is low-dimension -/

/-- Parity `⊕ᵢ xᵢ` as a Boolean transduction. -/
def parityFn (n : ℕ) : (Fin n → Bool) → Bool :=
  fun x => (List.finRange n).foldr (fun i acc => xor (x i) acc) false

/-- The parity transducer: an XOR caterpillar over the variables. -/
def xorVars : List (Fin n) → Trans n
  | [] => Trans.cst false
  | i :: is => Trans.bin xor (Trans.var i) (xorVars is)

theorem eval_xorVars (is : List (Fin n)) (x : Fin n → Bool) :
    eval (xorVars is) x = is.foldr (fun i acc => xor (x i) acc) false := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [xorVars, eval, ih]

theorem width_xorVars_le (is : List (Fin n)) : width (xorVars is) ≤ 2 := by
  induction is with
  | nil => simp [xorVars, width]
  | cons i is ih =>
    simp only [xorVars, width]
    split <;> omega

/-- **Parity has boundary dimension `≤ 2` (proved).**  The natural first target is *low*: parity is a one-register local
sweep, so the cut-based dimension — unlike sensitivity — does not mistake it for a hard function. -/
theorem boundaryDim_parity_le : boundaryDim (parityFn n) ≤ 2 :=
  le_trans
    (Nat.sInf_le ⟨xorVars (List.finRange n), by funext x; rw [eval_xorVars]; rfl, rfl⟩)
    (width_xorVars_le _)

/-! ### The no-go: every function has dimension ≤ 3 -/

/-- A literal: the variable or its negation, matching the bit `b`. -/
def literal (b : Bool) (i : Fin n) : Trans n :=
  if b then Trans.var i else Trans.un not (Trans.var i)

theorem eval_literal (b : Bool) (i : Fin n) (x : Fin n → Bool) :
    eval (literal b i) x = (x i == b) := by
  cases b <;> cases h : x i <;> simp [literal, eval, h]

theorem width_literal (b : Bool) (i : Fin n) : width (literal b i) = 1 := by
  cases b <;> simp [literal, width]

/-- The minterm caterpillar for an assignment `a`: an AND-chain of literals over the listed variables. -/
def mintermOn (a : Fin n → Bool) : List (Fin n) → Trans n
  | [] => Trans.cst true
  | i :: is => Trans.bin (· && ·) (literal (a i) i) (mintermOn a is)

theorem width_mintermOn (a : Fin n → Bool) (is : List (Fin n)) :
    width (mintermOn a is) ≤ 2 := by
  induction is with
  | nil => simp [mintermOn, width]
  | cons i is ih =>
    have hl := width_literal (a i) i
    simp only [mintermOn, width]
    split <;> omega

theorem eval_mintermOn (a : Fin n → Bool) (is : List (Fin n)) (x : Fin n → Bool) :
    eval (mintermOn a is) x = is.all (fun i => x i == a i) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [mintermOn, eval, eval_literal, ih]

/-- **The full minterm recognises exactly its assignment (proved).** -/
theorem eval_minterm_eq_true_iff (a x : Fin n → Bool) :
    eval (mintermOn a (List.finRange n)) x = true ↔ x = a := by
  rw [eval_mintermOn, List.all_eq_true]
  constructor
  · intro h
    funext i
    exact beq_iff_eq.mp (h i (List.mem_finRange i))
  · rintro rfl i _
    simp

/-- The DNF caterpillar: an OR-chain of minterms over a list of accepted assignments. -/
def dnfOn : List (Fin n → Bool) → Trans n
  | [] => Trans.cst false
  | a :: l => Trans.bin (· || ·) (mintermOn a (List.finRange n)) (dnfOn l)

/-- **The DNF caterpillar has cut-width `≤ 3` (proved)** — three live registers evaluate any accepted-assignment list. -/
theorem width_dnfOn (l : List (Fin n → Bool)) : width (dnfOn l) ≤ 3 := by
  induction l with
  | nil => simp [dnfOn, width]
  | cons a l ih =>
    have hm := width_mintermOn a (List.finRange n)
    simp only [dnfOn, width]
    split <;> omega

theorem eval_dnfOn (l : List (Fin n → Bool)) (x : Fin n → Bool) :
    eval (dnfOn l) x = l.any (fun a => eval (mintermOn a (List.finRange n)) x) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [dnfOn, eval, ih]

/-- The DNF transducer for `f`: the OR-chain over `f`'s accepted assignments. -/
noncomputable def dnfFor (f : (Fin n → Bool) → Bool) : Trans n :=
  dnfOn ((Finset.univ : Finset (Fin n → Bool)).toList.filter f)

/-- **The DNF transducer computes `f` (proved).** -/
theorem eval_dnfFor (f : (Fin n → Bool) → Bool) : eval (dnfFor f) = f := by
  funext x
  rw [dnfFor, eval_dnfOn]
  cases h : f x with
  | true =>
    apply List.any_eq_true.mpr
    refine ⟨x, ?_, (eval_minterm_eq_true_iff x x).mpr rfl⟩
    rw [List.mem_filter]
    exact ⟨Finset.mem_toList.mpr (Finset.mem_univ x), h⟩
  | false =>
    apply List.any_eq_false.mpr
    intro a ha hcon
    rw [List.mem_filter] at ha
    have hxa := (eval_minterm_eq_true_iff a x).mp hcon
    have hfa := ha.2
    rw [← hxa, h] at hfa
    exact Bool.noConfusion hfa

/-- **THE NO-GO (proved): every Boolean function has boundary dimension `≤ 3`.**  The pure dimension gap is empty — no
target tears the boundary in width alone, because exponential volume buys constant width.  The separating content of the
thermodynamic boundary is necessarily the **joint** budget: width under polynomial volume. -/
theorem boundaryDim_le_three (f : (Fin n → Bool) → Bool) : boundaryDim f ≤ 3 :=
  le_trans (Nat.sInf_le ⟨dnfFor f, eval_dnfFor f, rfl⟩) (width_dnfOn _)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.boundaryDim_parity_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.boundaryDim_le_three
