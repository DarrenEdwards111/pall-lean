import SubsetMachine

/-!
# G4.4 item 4 follow-up (2): the branch's `SATLang` is padding-invariant

Against codex/godmove-gap-repairs @ 21921958: `SeparationTarget.SATLang w = [Satisfiable (decodeFormula' w)]`
with the coordinate codec `CookLevinEmitCodec.decodeFormula'` (unary counts, `decodeNat [] = (0, [])`,
`headD false`, `tail`). Every decoder reads past the end of the word as `false`, so it cannot tell `w` from
`w ++ [false]`: decoding respects `TapeEq` (equality of `getD · false` at every index).

* `decodeFormula'_tapeEq`: `TapeEq a b → decodeFormula' a = decodeFormula' b`.
* `SATLang_append_false`: `SATLang (x ++ [false]) = SATLang x` (and `_replicate`).

So the model fact `SubsetMachine.decides_append_false` (every `ComposableMachine`-decided language is
`false`-padding invariant) does NOT by itself make `SAT_not_in_P` vacuous or trivially true.
-/

set_option autoImplicit false

namespace SATPad

open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (decodeNat)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.SeparationTarget (SATLang)
open SubsetMachine (TapeEq getD_append_replicate_false)

theorem tapeEq_tail {a b : List Bool} (h : TapeEq a b) : TapeEq a.tail b.tail := by
  intro i
  have := h (i + 1)
  cases a <;> cases b <;> simp at this ⊢ <;> exact this

theorem headD_eq {a b : List Bool} (h : TapeEq a b) : a.headD false = b.headD false := by
  have := h 0
  cases a <;> cases b <;> simp at this ⊢ <;> exact this

theorem tapeEq_nil_cons_false {b : List Bool} (h : TapeEq [] (false :: b)) : TapeEq [] b := by
  intro i; have := h (i + 1); simpa using this

theorem decodeNat_tapeEq : ∀ (a b : List Bool), TapeEq a b →
    (decodeNat a).1 = (decodeNat b).1 ∧ TapeEq (decodeNat a).2 (decodeNat b).2
  | [], [], _ => ⟨rfl, fun _ => rfl⟩
  | [], true :: _, h => absurd (h 0) (by simp)
  | [], false :: b, h => ⟨by simp [decodeNat], by
      simp only [decodeNat]; exact tapeEq_nil_cons_false h⟩
  | true :: _, [], h => absurd (h 0) (by simp)
  | false :: a, [], h => ⟨by simp [decodeNat], by
      simp only [decodeNat]
      exact fun i => (tapeEq_nil_cons_false (fun j => (h j).symm) i).symm⟩
  | true :: _, false :: _, h => absurd (h 0) (by simp)
  | false :: _, true :: _, h => absurd (h 0) (by simp)
  | false :: a, false :: b, h => ⟨by simp [decodeNat], by
      simp only [decodeNat]; exact fun i => by simpa using h (i + 1)⟩
  | true :: a, true :: b, h => by
      have ih := decodeNat_tapeEq a b (fun i => by simpa using h (i + 1))
      simp only [decodeNat]
      exact ⟨by rw [ih.1], ih.2⟩

theorem decodeVar'_tapeEq {a b : List Bool} (h : TapeEq a b) :
    (decodeVar' a).1 = (decodeVar' b).1 ∧ TapeEq (decodeVar' a).2 (decodeVar' b).2 := by
  obtain ⟨e1, h1⟩ := decodeNat_tapeEq a b h
  obtain ⟨e2, h2⟩ := decodeNat_tapeEq _ _ h1
  obtain ⟨e3, h3⟩ := decodeNat_tapeEq _ _ h2
  simp only [decodeVar']
  exact ⟨by rw [e1, e2, e3], h3⟩

theorem decodeLit'_tapeEq {a b : List Bool} (h : TapeEq a b) :
    (decodeLit' a).1 = (decodeLit' b).1 ∧ TapeEq (decodeLit' a).2 (decodeLit' b).2 := by
  obtain ⟨e1, h1⟩ := decodeVar'_tapeEq h
  simp only [decodeLit']
  exact ⟨by rw [e1, headD_eq h1], tapeEq_tail h1⟩

theorem decodeLits'_tapeEq (k : ℕ) : ∀ {a b : List Bool}, TapeEq a b →
    (decodeLits' k a).1 = (decodeLits' k b).1 ∧ TapeEq (decodeLits' k a).2 (decodeLits' k b).2 := by
  induction k with
  | zero => intro a b h; exact ⟨rfl, h⟩
  | succ k ih =>
    intro a b h
    obtain ⟨e1, h1⟩ := decodeLit'_tapeEq h
    obtain ⟨e2, h2⟩ := ih h1
    simp only [decodeLits']
    exact ⟨by rw [e1, e2], h2⟩

theorem decodeClause'_tapeEq {a b : List Bool} (h : TapeEq a b) :
    (decodeClause' a).1 = (decodeClause' b).1 ∧ TapeEq (decodeClause' a).2 (decodeClause' b).2 := by
  obtain ⟨e1, h1⟩ := decodeNat_tapeEq a b h
  simp only [decodeClause']
  rw [e1]
  exact decodeLits'_tapeEq _ h1

theorem decodeClauses'_tapeEq (k : ℕ) : ∀ {a b : List Bool}, TapeEq a b →
    (decodeClauses' k a).1 = (decodeClauses' k b).1 ∧
      TapeEq (decodeClauses' k a).2 (decodeClauses' k b).2 := by
  induction k with
  | zero => intro a b h; exact ⟨rfl, h⟩
  | succ k ih =>
    intro a b h
    obtain ⟨e1, h1⟩ := decodeClause'_tapeEq h
    obtain ⟨e2, h2⟩ := ih h1
    simp only [decodeClauses']
    exact ⟨by rw [e1, e2], h2⟩

/-- **Decoding cannot see trailing `false`s.** -/
theorem decodeFormula'_tapeEq {a b : List Bool} (h : TapeEq a b) :
    decodeFormula' a = decodeFormula' b := by
  obtain ⟨e1, h1⟩ := decodeNat_tapeEq a b h
  simp only [decodeFormula']
  rw [e1]
  exact (decodeClauses'_tapeEq _ h1).1

theorem SATLang_tapeEq {a b : List Bool} (h : TapeEq a b) : SATLang a = SATLang b := by
  unfold SATLang
  rw [decodeFormula'_tapeEq h]

/-- **`SATLang (x ++ [false]) = SATLang x`** for the branch's own `SATLang` (kernel-checked). -/
theorem SATLang_append_false (x : List Bool) : SATLang (x ++ [false]) = SATLang x :=
  SATLang_tapeEq (fun i => getD_append_replicate_false x 1 i)

theorem SATLang_append_replicate_false (x : List Bool) (k : ℕ) :
    SATLang (x ++ List.replicate k false) = SATLang x :=
  SATLang_tapeEq (fun i => getD_append_replicate_false x k i)

end SATPad

#print axioms SATPad.decodeNat_tapeEq
#print axioms SATPad.decodeFormula'_tapeEq
#print axioms SATPad.SATLang_tapeEq
#print axioms SATPad.SATLang_append_false
#print axioms SATPad.SATLang_append_replicate_false
set_option pp.fullNames true in
#check @SATPad.SATLang_append_false
set_option pp.fullNames true in
#check @SATPad.SATLang_append_replicate_false
set_option pp.fullNames true in
#check @SATPad.decodeFormula'_tapeEq
