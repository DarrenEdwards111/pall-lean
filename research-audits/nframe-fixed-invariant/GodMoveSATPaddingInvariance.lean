import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSeparationTarget
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCellSpread

/-!
# SAT decoding and the machine's blank convention

Adding trailing false bits preserves the exact decoded formula, even on malformed
or truncated words. Consequently SATLang respects this observational equivalence
of the Boolean tape machine. Its separation target does not distinguish inputs
solely by their invisible trailing-blank lengths.

In contrast, appending a true bit at the physical end of an arbitrary unmarked
List Bool cannot be a total halting machine transduction: the empty list and one
false bit have identical infinite blank-padded observations but require distinct
outputs. A runtime bridge for the list evaluator needs an explicit marked or
self-delimiting memory representation.
-/

namespace GodMoveSATPaddingInvariance

open PallLean.Paper93.DeepMath.PathB
open CookLevinEmit CookLevinEmitCodec SeparationTarget

def Padded (xs ys : List Bool) : Prop := ∃ k, ys = xs ++ List.replicate k false

theorem padded_head {xs ys : List Bool} (h : Padded xs ys) :
    ys.headD false = xs.headD false := by
  obtain ⟨k, rfl⟩ := h
  cases xs with
  | nil => cases k <;> rfl
  | cons b bs => rfl

theorem padded_tail {xs ys : List Bool} (h : Padded xs ys) : Padded xs.tail ys.tail := by
  obtain ⟨k, rfl⟩ := h
  cases xs with
  | nil =>
    cases k with
    | zero => exact ⟨0, rfl⟩
    | succ k => exact ⟨k, rfl⟩
  | cons b bs => exact ⟨k, rfl⟩

theorem decodeNat_append_false (xs : List Bool) (k : ℕ) :
    (decodeNat (xs ++ List.replicate k false)).1 = (decodeNat xs).1 ∧
      Padded (decodeNat xs).2 (decodeNat (xs ++ List.replicate k false)).2 := by
  induction xs generalizing k with
  | nil =>
    cases k with
    | zero => exact ⟨rfl, 0, rfl⟩
    | succ k => exact ⟨rfl, k, rfl⟩
  | cons b bs ih =>
    cases b with
    | false => exact ⟨rfl, k, rfl⟩
    | true => exact ⟨congrArg (· + 1) (ih k).1, (ih k).2⟩

theorem decodeNat_padded {xs ys : List Bool} (h : Padded xs ys) :
    (decodeNat ys).1 = (decodeNat xs).1 ∧
      Padded (decodeNat xs).2 (decodeNat ys).2 := by
  obtain ⟨k, rfl⟩ := h
  exact decodeNat_append_false xs k

theorem decodeVar_padded {xs ys : List Bool} (h : Padded xs ys) :
    (decodeVar' ys).1 = (decodeVar' xs).1 ∧
      Padded (decodeVar' xs).2 (decodeVar' ys).2 := by
  have h1 := decodeNat_padded h
  have h2 := decodeNat_padded h1.2
  have h3 := decodeNat_padded h2.2
  constructor
  · simp only [decodeVar', h1.1, h2.1, h3.1]
  · exact h3.2

theorem decodeLit_padded {xs ys : List Bool} (h : Padded xs ys) :
    (decodeLit' ys).1 = (decodeLit' xs).1 ∧
      Padded (decodeLit' xs).2 (decodeLit' ys).2 := by
  have hv := decodeVar_padded h
  constructor
  · exact Prod.ext hv.1 (padded_head hv.2)
  · exact padded_tail hv.2

theorem decodeLits_padded (n : ℕ) {xs ys : List Bool} (h : Padded xs ys) :
    (decodeLits' n ys).1 = (decodeLits' n xs).1 ∧
      Padded (decodeLits' n xs).2 (decodeLits' n ys).2 := by
  induction n generalizing xs ys with
  | zero => exact ⟨rfl, h⟩
  | succ n ih =>
    have hv := decodeLit_padded h
    have ht := ih hv.2
    exact ⟨congrArg₂ List.cons hv.1 ht.1, ht.2⟩

theorem decodeClause_padded {xs ys : List Bool} (h : Padded xs ys) :
    (decodeClause' ys).1 = (decodeClause' xs).1 ∧
      Padded (decodeClause' xs).2 (decodeClause' ys).2 := by
  have hn := decodeNat_padded h
  simp only [decodeClause', hn.1]
  exact decodeLits_padded (decodeNat xs).1 hn.2

theorem decodeClauses_padded (n : ℕ) {xs ys : List Bool} (h : Padded xs ys) :
    (decodeClauses' n ys).1 = (decodeClauses' n xs).1 ∧
      Padded (decodeClauses' n xs).2 (decodeClauses' n ys).2 := by
  induction n generalizing xs ys with
  | zero => exact ⟨rfl, h⟩
  | succ n ih =>
    have hv := decodeClause_padded h
    have ht := ih hv.2
    exact ⟨congrArg₂ List.cons hv.1 ht.1, ht.2⟩

theorem decodeFormula_padded {xs ys : List Bool} (h : Padded xs ys) :
    decodeFormula' ys = decodeFormula' xs := by
  have hn := decodeNat_padded h
  simp only [decodeFormula', hn.1]
  exact (decodeClauses_padded (decodeNat xs).1 hn.2).1

theorem decodeFormula_append_false (xs : List Bool) (k : ℕ) :
    decodeFormula' (xs ++ List.replicate k false) = decodeFormula' xs :=
  decodeFormula_padded ⟨k, rfl⟩

theorem SATLang_append_false (xs : List Bool) (k : ℕ) :
    SATLang (xs ++ List.replicate k false) = SATLang xs := by
  unfold SATLang
  rw [decodeFormula_append_false]

open ComposableMachine CellSpread

/-- Exact finite-control runs preserve equality of all tape observations. -/
theorem run_congr (M : Machine) (t : ℕ) {c d : Cfg M} (h : Congr c d) :
    Congr (run M t c) (run M t d) := by
  induction t with
  | zero => exact h
  | succ t ih => rw [run_succ, run_succ]; exact step_congr ih

/-- The obstruction concerns raw unmarked list append, not an encoded memory
layout with a physically detectable terminal marker. It uses no clock bound. -/
theorem not_transduces_raw_append_true (M : Machine) (T : ℕ → ℕ) :
    ¬ Transduces M (fun xs => xs ++ [true]) T := by
  intro h
  have h0 := h []
  have h1 := h [false]
  have hc : Congr (init M []) (init M [false]) := by
    refine ⟨rfl, rfl, ?_⟩
    intro i
    cases i <;> rfl
  have hr := run_congr M (max (T 0) (T 1)) hc
  have hs0 := run_stable M [] (le_max_left (T 0) (T 1)) h0.1
  have hs1 := run_stable M [false] (le_max_right (T 0) (T 1)) h1.1
  rw [hs0, hs1] at hr
  have ht0 : (run M (T 0) (init M [])).tp = [true] := h0.2
  have ht1 : (run M (T 1) (init M [false])).tp = [false, true] := h1.2
  have he := hr.2.2 0
  rw [ht0, ht1] at he
  cases he

end GodMoveSATPaddingInvariance

#print axioms GodMoveSATPaddingInvariance.decodeFormula_append_false
#print axioms GodMoveSATPaddingInvariance.SATLang_append_false
#print axioms GodMoveSATPaddingInvariance.run_congr
#print axioms GodMoveSATPaddingInvariance.not_transduces_raw_append_true
