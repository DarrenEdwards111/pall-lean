import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockCircuitCollapse

/-!
# Block-DT model, foundation 13: the DT → CNF/DNF representation swap (branch only)

The circuit-collapse rung (`circuit_collapse_exists`) produces, under one restriction, a *shallow*
canonical decision tree for every bottom gate.  The switching lemma's depth reduction needs the next
step: a depth-`d` decision tree is simultaneously a **width-`d` DNF** (one term per accepting leaf path)
and a **width-`d` CNF** (one clause per rejecting leaf path).  Re-expressing the shallow DT as a CNF is
the **swap** `∨∧ ↦ ∧∨` that merges the bottom two circuit layers and drops the depth by one.

This module formalises that swap on a self-contained decision-tree datatype with Boolean semantics:

* `DTree`, `eval`, `depth` — binary decision trees over `Fin n` and their evaluation/depth.
* `toDNF` / `eval_eq_dnf` / `toDNF_width` — the accepting-path DNF, equivalent to `eval`, width `≤ depth`.
* `toCNF` / `eval_eq_cnf` / `toCNF_width` — the rejecting-path CNF, equivalent to `eval`, width `≤ depth`.

Together: one shallow tree, two bounded-width normal forms — the representation swap.

Clean, no `sorry`, no `native_decide`.  AC⁰/depth-3; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

/-- A binary decision tree over `n` Boolean variables.  `node v lo hi` queries `v`: branch to `lo` if
`x v = false`, to `hi` if `x v = true`. -/
inductive DTree (n : ℕ) where
  | leaf : Bool → DTree n
  | node : Fin n → DTree n → DTree n → DTree n
deriving Repr

namespace DTree

variable {n : ℕ}

/-- Evaluate a decision tree at an assignment. -/
def eval : DTree n → (Fin n → Bool) → Bool
  | leaf b, _ => b
  | node v lo hi, x => if x v then hi.eval x else lo.eval x

/-- The depth (longest root-to-leaf path) of a decision tree. -/
def depth : DTree n → ℕ
  | leaf _ => 0
  | node _ lo hi => max lo.depth hi.depth + 1

/-- A literal: a variable together with its required value. -/
abbrev Lit (n : ℕ) := Fin n × Bool

/-- A term (conjunction) is satisfied if every literal matches. -/
def termSat (x : Fin n → Bool) (t : List (Lit n)) : Prop := ∀ p ∈ t, x p.1 = p.2

/-- A DNF (disjunction of terms) is satisfied if some term is. -/
def dnfSat (x : Fin n → Bool) (ts : List (List (Lit n))) : Prop := ∃ t ∈ ts, termSat x t

/-- A clause (disjunction) is satisfied if some literal matches. -/
def clauseSat (x : Fin n → Bool) (c : List (Lit n)) : Prop := ∃ p ∈ c, x p.1 = p.2

/-- A CNF (conjunction of clauses) is satisfied if every clause is. -/
def cnfSat (x : Fin n → Bool) (cs : List (List (Lit n))) : Prop := ∀ c ∈ cs, clauseSat x c

/-! ### The accepting-path DNF -/

/-- The DNF of accepting leaf paths: one term per `true`-leaf, recording the path literals. -/
def toDNF : DTree n → List (List (Lit n))
  | leaf true => [[]]
  | leaf false => []
  | node v lo hi =>
      lo.toDNF.map (fun t => (v, false) :: t) ++ hi.toDNF.map (fun t => (v, true) :: t)

/-- **DT ≡ DNF.**  The tree accepts `x` iff the accepting-path DNF is satisfied at `x`. -/
theorem eval_eq_dnf (t : DTree n) (x : Fin n → Bool) :
    t.eval x = true ↔ dnfSat x t.toDNF := by
  induction t with
  | leaf b =>
    cases b <;> simp [eval, toDNF, dnfSat, termSat]
  | node v lo hi ihlo ihhi =>
    simp only [eval, toDNF, dnfSat, List.mem_append, List.mem_map]
    constructor
    · intro hev
      by_cases hxv : x v = true
      · simp only [hxv, if_true] at hev
        obtain ⟨t', ht', hsat⟩ := ihhi.mp hev
        exact ⟨(v, true) :: t', Or.inr ⟨t', ht', rfl⟩, by
          simp only [termSat, List.mem_cons]
          rintro p (rfl | hp)
          · exact hxv
          · exact hsat p hp⟩
      · simp only [Bool.not_eq_true] at hxv
        simp only [hxv] at hev
        obtain ⟨t', ht', hsat⟩ := ihlo.mp hev
        exact ⟨(v, false) :: t', Or.inl ⟨t', ht', rfl⟩, by
          simp only [termSat, List.mem_cons]
          rintro p (rfl | hp)
          · exact hxv
          · exact hsat p hp⟩
    · rintro ⟨t', ht', hsat⟩
      rcases ht' with ⟨t0, ht0, rfl⟩ | ⟨t0, ht0, rfl⟩
      · have hxv : x v = false := hsat (v, false) (List.mem_cons_self)
        simp only [hxv]
        refine ihlo.mpr ⟨t0, ht0, ?_⟩
        intro p hp; exact hsat p (List.mem_cons_of_mem _ hp)
      · have hxv : x v = true := hsat (v, true) (List.mem_cons_self)
        simp only [hxv, if_true]
        refine ihhi.mpr ⟨t0, ht0, ?_⟩
        intro p hp; exact hsat p (List.mem_cons_of_mem _ hp)

/-- **DNF width bound.**  Every accepting-path term has length `≤ depth`. -/
theorem toDNF_width (t : DTree n) : ∀ s ∈ t.toDNF, s.length ≤ t.depth := by
  induction t with
  | leaf b => cases b <;> simp [toDNF, depth]
  | node v lo hi ihlo ihhi =>
    intro s hs
    simp only [toDNF, List.mem_append, List.mem_map] at hs
    rcases hs with ⟨t0, ht0, rfl⟩ | ⟨t0, ht0, rfl⟩
    · simp only [List.length_cons, depth]
      have := ihlo t0 ht0; omega
    · simp only [List.length_cons, depth]
      have := ihhi t0 ht0; omega

/-! ### The rejecting-path CNF -/

/-- The CNF of rejecting leaf paths: one clause per `false`-leaf, recording the *negated* path literals
(so the clause is satisfied exactly when `x` leaves that rejecting path). -/
def toCNF : DTree n → List (List (Lit n))
  | leaf true => []
  | leaf false => [[]]
  | node v lo hi =>
      lo.toCNF.map (fun c => (v, true) :: c) ++ hi.toCNF.map (fun c => (v, false) :: c)

/-- **DT ≡ CNF.**  The tree accepts `x` iff the rejecting-path CNF is satisfied at `x`. -/
theorem eval_eq_cnf (t : DTree n) (x : Fin n → Bool) :
    t.eval x = true ↔ cnfSat x t.toCNF := by
  induction t with
  | leaf b =>
    cases b <;> simp [eval, toCNF, cnfSat, clauseSat]
  | node v lo hi ihlo ihhi =>
    simp only [eval, toCNF, cnfSat, List.mem_append, List.mem_map]
    constructor
    · rintro hev c (⟨c0, hc0, rfl⟩ | ⟨c0, hc0, rfl⟩)
      · by_cases hxv : x v = true
        · exact ⟨(v, true), List.mem_cons_self, hxv⟩
        · simp only [Bool.not_eq_true] at hxv
          simp only [hxv] at hev
          obtain ⟨p, hp, hpx⟩ := ihlo.mp hev c0 hc0
          exact ⟨p, List.mem_cons_of_mem _ hp, hpx⟩
      · by_cases hxv : x v = true
        · simp only [hxv, if_true] at hev
          obtain ⟨p, hp, hpx⟩ := ihhi.mp hev c0 hc0
          exact ⟨p, List.mem_cons_of_mem _ hp, hpx⟩
        · simp only [Bool.not_eq_true] at hxv
          exact ⟨(v, false), List.mem_cons_self, hxv⟩
    · intro hcnf
      by_cases hxv : x v = true
      · simp only [hxv, if_true]
        refine ihhi.mpr ?_
        intro c0 hc0
        obtain ⟨p, hp, hpx⟩ := hcnf ((v, false) :: c0) (Or.inr ⟨c0, hc0, rfl⟩)
        rcases List.mem_cons.mp hp with rfl | hp'
        · simp only at hpx; rw [hxv] at hpx; exact absurd hpx (by decide)
        · exact ⟨p, hp', hpx⟩
      · simp only [Bool.not_eq_true] at hxv
        simp only [hxv]
        refine ihlo.mpr ?_
        intro c0 hc0
        obtain ⟨p, hp, hpx⟩ := hcnf ((v, true) :: c0) (Or.inl ⟨c0, hc0, rfl⟩)
        rcases List.mem_cons.mp hp with rfl | hp'
        · simp only at hpx; rw [hxv] at hpx; exact absurd hpx (by decide)
        · exact ⟨p, hp', hpx⟩

/-- **CNF width bound.**  Every rejecting-path clause has length `≤ depth`. -/
theorem toCNF_width (t : DTree n) : ∀ c ∈ t.toCNF, c.length ≤ t.depth := by
  induction t with
  | leaf b => cases b <;> simp [toCNF, depth]
  | node v lo hi ihlo ihhi =>
    intro c hc
    simp only [toCNF, List.mem_append, List.mem_map] at hc
    rcases hc with ⟨c0, hc0, rfl⟩ | ⟨c0, hc0, rfl⟩
    · simp only [List.length_cons, depth]
      have := ihlo c0 hc0; omega
    · simp only [List.length_cons, depth]
      have := ihhi c0 hc0; omega

/-- **The representation swap.**  A single depth-`d` decision tree is *both* a width-`≤ d` DNF and a
width-`≤ d` CNF computing the same function — the `∨∧ ↦ ∧∨` swap underlying switching depth reduction. -/
theorem dnf_cnf_swap (t : DTree n) (x : Fin n → Bool) :
    (dnfSat x t.toDNF ↔ cnfSat x t.toCNF)
      ∧ (∀ s ∈ t.toDNF, s.length ≤ t.depth)
      ∧ (∀ c ∈ t.toCNF, c.length ≤ t.depth) :=
  ⟨(eval_eq_dnf t x).symm.trans (eval_eq_cnf t x), toDNF_width t, toCNF_width t⟩

end DTree

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.eval_eq_dnf
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.eval_eq_cnf
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.dnf_cnf_swap
