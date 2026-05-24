import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSelfReduction
import Mathlib.Tactic

/-
# Concrete prefix-to-CNF reduction

This file discharges the syntactic reduction socket from
`ComputationalDepthSelfReduction.lean`.

Given a formula `φ` and a prefix `p`, we construct an ordinary CNF formula by
adding unit clauses that force the first `p.length` variables to match `p`.
The main theorem proves:

  Satisfiable (φ with prefix-unit clauses) ↔ SatisfiableWithPrefix φ p.

This is still formalization infrastructure.  It does not prove the SAT lower
bound `DeepSATSearch`.
-/

namespace SATDepthMachine

/-! ## Unit clauses for prefix bits -/

/-- Literal forcing variable `i` to Boolean value `b`. -/
def unitLit (i : Nat) (b : Bool) : Lit where
  var := i
  pol := if b then Polarity.pos else Polarity.neg

/-- Unit clause forcing variable `i` to Boolean value `b`. -/
def unitClause (i : Nat) (b : Bool) : Clause :=
  [unitLit i b]

/-- Shift a literal one variable to the right. -/
def shiftLit (l : Lit) : Lit where
  var := l.var + 1
  pol := l.pol

/-- Shift every literal in a clause one variable to the right. -/
def shiftClause (c : Clause) : Clause :=
  c.map shiftLit

/-- Shift every clause one variable to the right. -/
def shiftClauses (cs : List Clause) : List Clause :=
  cs.map shiftClause

/-- Unit clauses forcing a prefix.  The recursive definition keeps the proof
aligned with the assignment head/tail split. -/
def prefixUnitClauses : RawAssignment -> List Clause
  | [] => []
  | b :: bs => unitClause 0 b :: shiftClauses (prefixUnitClauses bs)

/-- CNF formula obtained by adding unit clauses for the prefix. -/
def encodeWithPrefixUnits (φ : CNF) (p : RawAssignment) : CNF where
  vars := φ.vars
  clauses := prefixUnitClauses p ++ φ.clauses

/-! ## Evaluation lemmas -/

theorem shiftLit_eval_cons (b : Bool) (a : RawAssignment) (l : Lit) :
    Lit.eval (b :: a) (shiftLit l) = Lit.eval a l := by
  cases l with
  | mk var pol =>
      cases pol <;> rfl

theorem shiftClause_eval_cons (b : Bool) (a : RawAssignment) (c : Clause) :
    Clause.eval (b :: a) (shiftClause c) = Clause.eval a c := by
  induction c with
  | nil =>
      rfl
  | cons l ls ih =>
      have htail :
          ls.any ((fun l => Lit.eval (b :: a) l) ∘ shiftLit) =
            ls.any (fun l => Lit.eval a l) := by
        simpa [Clause.eval, shiftClause] using ih
      simp [Clause.eval, shiftClause, shiftLit_eval_cons, htail]

theorem shiftClauses_all_cons
    (b : Bool) (a : RawAssignment) (cs : List Clause) :
    (shiftClauses cs).all (fun c => Clause.eval (b :: a) c) =
      cs.all (fun c => Clause.eval a c) := by
  induction cs with
  | nil =>
      rfl
  | cons c cs ih =>
      have htail :
          (cs.map shiftClause).all (fun c => Clause.eval (b :: a) c) =
            cs.all (fun c => Clause.eval a c) := by
        simpa [shiftClauses] using ih
      simp [shiftClauses, shiftClause_eval_cons, htail]

theorem unitClause_eval_cons_self (b : Bool) (a : RawAssignment) :
    Clause.eval (b :: a) (unitClause 0 b) = true := by
  cases b <;> rfl

theorem eq_of_unitClause_eval_cons_true
    {x b : Bool} {a : RawAssignment}
    (h : Clause.eval (x :: a) (unitClause 0 b) = true) :
    x = b := by
  cases x <;> cases b <;>
    simp [Clause.eval, unitClause, unitLit, Lit.eval, RawAssignment.lookup] at h ⊢

theorem prefixUnitClauses_all_iff_extends :
    ∀ (p a : RawAssignment),
      (prefixUnitClauses p).all (fun c => Clause.eval a c) = true ↔
        ExtendsPrefix p a
  | [], a => by
      constructor
      · intro _h
        exact ⟨a, by simp⟩
      · intro _h
        rfl
  | b :: bs, [] => by
      constructor
      · intro h
        simp [prefixUnitClauses, unitClause, Clause.eval, Lit.eval,
          RawAssignment.lookup, unitLit] at h
      · intro h
        rcases h with ⟨s, hs⟩
        cases hs
  | b :: bs, x :: xs => by
      constructor
      · intro h
        rw [prefixUnitClauses, List.all_cons, Bool.and_eq_true] at h
        rw [shiftClauses_all_cons] at h
        have hx : x = b := eq_of_unitClause_eval_cons_true h.1
        have htailAll :
            (prefixUnitClauses bs).all (fun c => Clause.eval xs c) = true := h.2
        have htail : ExtendsPrefix bs xs :=
          (prefixUnitClauses_all_iff_extends bs xs).mp htailAll
        rcases htail with ⟨s, hs⟩
        subst hx
        exact ⟨s, by simp [hs]⟩
      · intro h
        rcases h with ⟨s, hs⟩
        cases hs
        rw [prefixUnitClauses, List.all_cons, Bool.and_eq_true]
        constructor
        · exact unitClause_eval_cons_self b (bs ++ s)
        · rw [shiftClauses_all_cons]
          exact (prefixUnitClauses_all_iff_extends bs (bs ++ s)).mpr
            ⟨s, rfl⟩

theorem prefixUnitClauses_all_true_of_extends
    {p a : RawAssignment} (h : ExtendsPrefix p a) :
    (prefixUnitClauses p).all (fun c => Clause.eval a c) = true :=
  (prefixUnitClauses_all_iff_extends p a).mpr h

theorem extends_of_prefixUnitClauses_all_true
    {p a : RawAssignment}
    (h : (prefixUnitClauses p).all (fun c => Clause.eval a c) = true) :
    ExtendsPrefix p a :=
  (prefixUnitClauses_all_iff_extends p a).mp h

theorem cnf_eval_prefix_append_true_iff
    (φ : CNF) (p a : RawAssignment) :
    (encodeWithPrefixUnits φ p).eval a = true ↔
      (prefixUnitClauses p).all (fun c => Clause.eval a c) = true ∧
        φ.eval a = true := by
  unfold encodeWithPrefixUnits CNF.eval
  rw [List.all_append, Bool.and_eq_true]

/-! ## Prefix reduction correctness -/

theorem encodeWithPrefixUnits_sound
    (φ : CNF) (p : RawAssignment) :
    Satisfiable (encodeWithPrefixUnits φ p) ↔
      SatisfiableWithPrefix φ p := by
  constructor
  · intro h
    rcases h with ⟨a, hsat⟩
    rcases hsat with ⟨hlen, heval⟩
    have hboth := (cnf_eval_prefix_append_true_iff φ p a).mp heval
    have hprefix : ExtendsPrefix p a :=
      extends_of_prefixUnitClauses_all_true hboth.1
    exact ⟨a, ⟨hlen, hboth.2⟩, hprefix⟩
  · intro h
    rcases h with ⟨a, hsat, hprefix⟩
    refine ⟨a, ?_⟩
    rcases hsat with ⟨hlen, heval⟩
    constructor
    · exact hlen
    · exact (cnf_eval_prefix_append_true_iff φ p a).mpr
        ⟨prefixUnitClauses_all_true_of_extends hprefix, heval⟩

/-- The concrete prefix-query reduction used by Cook self-reducibility. -/
def prefixUnitCNFReduction : PrefixConstraintCNFReduction where
  encode := encodeWithPrefixUnits
  sound := encodeWithPrefixUnits_sound

/-! ## Kernel-only axiom trace -/

#print axioms shiftLit_eval_cons
#print axioms shiftClause_eval_cons
#print axioms shiftClauses_all_cons
#print axioms prefixUnitClauses_all_iff_extends
#print axioms cnf_eval_prefix_append_true_iff
#print axioms encodeWithPrefixUnits_sound
#print axioms prefixUnitCNFReduction

end SATDepthMachine
