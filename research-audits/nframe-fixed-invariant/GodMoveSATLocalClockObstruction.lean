import GodMoveSATRuntimeFrontier
import GodMoveBooleanFace
import GodMoveMultilinearRestriction

/-!
# A correct SAT decider with one-step easy runs and unchanged source rank

The actual codec decodes every false-headed word as the empty CNF. The wrapper
below accepts that entire slice in exactly one step and otherwise enters the
supplied correct SAT machine without modifying its tape or head. Global SAT
correctness and the original normalized source are retained.

The full-length canonical source therefore still has its proved large rank,
although the wrapper has constant local runtime on all-false words of those
lengths. This refutes using such a local clock to bound the FULL source. The
false-head restriction itself is the constant polynomial one; no hardness is
claimed for that restricted face, and the global-clock SAT bound remains open.
-/

namespace GodMoveSATLocalClockObstruction

open PallLean.Paper93.DeepMath.PathB
open ComposableMachine SeparationTarget CookLevinReduction CookLevinEmit CookLevinEmitCodec
open ComposablePpolyDischarge SATCircuitSeparationBridge
open GodMoveSATRuntimeFrontier GodMoveSATSourceCanonicity GodMoveMachineFaceExtraction
open GodMoveBooleanInterpolation GodMoveCircuitConnection
open MvPolynomial MultilinearSPDP PiStarConcrete

/-- The clause-count unary prefix is zero when the first observed bit is false. -/
theorem decodeFormula_of_first_false (xs : List Bool) (h : xs.getD 0 false = false) :
    decodeFormula' xs = [] := by
  cases xs with
  | nil => rfl
  | cons b bs =>
      have hb : b = false := h
      subst b
      rfl

theorem SATLang_of_first_false (xs : List Bool) (h : xs.getD 0 false = false) :
    SATLang xs = true := by
  rw [SATLang, decodeFormula_of_first_false xs h, if_pos satisfiable_nil]

/-- Two additional states: initial test and accepting halt. The fallback
transition is a legal stay/no-write control step into the original machine. -/
def shortcut (M : Machine) : Machine where
  State := Bool ⊕ M.State
  fin := inferInstance
  dec := inferInstance
  start := Sum.inl false
  halt := fun s => match s with | .inl b => b | .inr q => M.halt q
  δ := fun s b => match s with
    | .inl _ => if b then (.inr M.start, none, 2) else (.inl true, none, 2)
    | .inr q => let tr := M.δ q b; (.inr tr.1, tr.2.1, tr.2.2)
  accept := fun s => match s with | .inl b => b | .inr q => M.accept q

def embed (M : Machine) (c : Cfg M) : Cfg (shortcut M) := ⟨.inr c.st, c.hd, c.tp⟩
def accepted (M : Machine) (xs : List Bool) : Cfg (shortcut M) := ⟨.inl true, 0, xs⟩
def shortcutClock (T : ℕ → ℕ) (L : ℕ) : ℕ := T L + 1

theorem shortcut_step_embed (M : Machine) (c : Cfg M) :
    step (shortcut M) (embed M c) = embed M (step M c) := by
  unfold step
  cases h : M.halt c.st <;> simp [shortcut, embed, h]

theorem shortcut_run_embed (M : Machine) (t : ℕ) (c : Cfg M) :
    run (shortcut M) t (embed M c) = embed M (run M t c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, ih, shortcut_step_embed, ← run_succ]

theorem shortcut_first_false (M : Machine) (xs : List Bool)
    (h : xs.getD 0 false = false) :
    run (shortcut M) 1 (init (shortcut M) xs) = accepted M xs := by
  have hread : xs[0]?.getD false = false := h
  simp [run, step, shortcut, init, accepted, moveHead, hread]

theorem shortcut_first_true (M : Machine) (xs : List Bool)
    (h : xs.getD 0 false = true) :
    run (shortcut M) 1 (init (shortcut M) xs) = embed M (init M xs) := by
  have hread : xs[0]?.getD false = true := h
  simp [run, step, shortcut, init, embed, moveHead, hread]

theorem shortcut_run_false (M : Machine) (xs : List Bool) (t : ℕ)
    (h : xs.getD 0 false = false) :
    run (shortcut M) (t + 1) (init (shortcut M) xs) = accepted M xs := by
  rw [Nat.add_comm t 1, run_add, shortcut_first_false M xs h]
  exact run_of_halted (shortcut M) (c := accepted M xs) rfl t

theorem shortcut_run_true (M : Machine) (xs : List Bool) (t : ℕ)
    (h : xs.getD 0 false = true) :
    run (shortcut M) (t + 1) (init (shortcut M) xs) = embed M (run M t (init M xs)) := by
  rw [Nat.add_comm t 1, run_add, shortcut_first_true M xs h, shortcut_run_embed]

/-- Only correctness of the supplied SAT machine is used, not a polynomial
clock or a new rank/preservation premise. -/
theorem shortcut_decides (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) :
    Decides (shortcut M) SATLang (shortcutClock T) := by
  intro xs
  cases h : xs.getD 0 false with
  | false =>
      have hs := shortcut_run_false M xs (T xs.length) h
      have hsat := SATLang_of_first_false xs h
      constructor
      · change (shortcut M).halt (run (shortcut M) (T xs.length + 1) (init (shortcut M) xs)).st = true
        rw [hs]
        rfl
      · change (shortcut M).accept (run (shortcut M) (T xs.length + 1) (init (shortcut M) xs)).st = _
        rw [hs, hsat]
        rfl
  | true =>
      have hs := shortcut_run_true M xs (T xs.length) h
      constructor
      · change (shortcut M).halt (run (shortcut M) (T xs.length + 1) (init (shortcut M) xs)).st = true
        rw [hs]
        exact (hD xs).1
      · change (shortcut M).accept (run (shortcut M) (T xs.length + 1) (init (shortcut M) xs)).st = _
        rw [hs]
        exact (hD xs).2

/-- This is an exact first-halting time, not merely a chosen upper clock. -/
theorem first_halt_false_head (M : Machine) (xs : List Bool)
    (h : xs.getD 0 false = false) :
    HaltsBy (shortcut M) xs 1 ∧ ¬ HaltsBy (shortcut M) xs 0 := by
  constructor
  · unfold HaltsBy
    rw [shortcut_first_false M xs h]
    rfl
  · simp [HaltsBy, run_zero, init, shortcut]

theorem first_halt_all_false (M : Machine) (L : ℕ) :
    HaltsBy (shortcut M) (List.replicate L false) 1 ∧
      ¬ HaltsBy (shortcut M) (List.replicate L false) 0 := by
  apply first_halt_false_head
  cases L <;> rfl

/-- Its full-length decision polynomial is unchanged, despite its new fast slice. -/
theorem normalizedSource_unchanged (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) (L : ℕ) :
    circuitTarget (circuitFor (shortcut M) L (shortcutClock T L)) =
      circuitTarget (circuitFor M L (T L)) :=
  normalizedSource_independent_of_decider (shortcut M) M SATLang (shortcutClock T) T
    (shortcut_decides M T hD) hD L

theorem paperSourceRank_unchanged (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) (n : ℕ) :
    paperSourceRank (shortcut M) (shortcutClock T) n = paperSourceRank M T n := by
  unfold paperSourceRank machineSource
  rw [normalizedSource_unchanged M T hD]

/-- At every designated paper length there is an actual one-step input, yet
the corresponding FULL source exceeds every polynomial in length plus that
local time. The literal `1` is justified by `first_halt_all_false`. -/
theorem no_full_source_bound_from_easy_run (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) :
    ¬ ∃ C d n0 : ℕ, ∀ n ≥ n0,
      paperSourceRank (shortcut M) (shortcutClock T) n ≤
        C * (paperInputLength n + 1 + 1) ^ d := by
  rintro ⟨C, d, n0, hbound⟩
  apply GodMoveSATPaperWindowLower.no_eventual_polynomial_paper_source_encoded_bound
    (shortcut M) (shortcutClock T) (shortcut_decides M T hD)
  refine ⟨C * 2 ^ d, d, n0, ?_⟩
  intro n hn
  calc
    _ ≤ C * (paperInputLength n + 1 + 1) ^ d := hbound n hn
    _ ≤ C * (2 * (paperInputLength n + 1)) ^ d :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) d)
    _ = (C * 2 ^ d) * (paperInputLength n + 1) ^ d := by rw [mul_pow, mul_assoc]

/-- Fixing the first bit to false gives the constant polynomial one. This is
the actual coordinate-face restriction of the canonical source, in its original
ambient variables; its high full-source rank is not rank of this easy face. -/
theorem false_head_face_eq_one (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) (L : ℕ) :
    piSubst (fun j : Fin (L + 1) => j ≠ 0) (fun _ => (0 : ℚ))
      (circuitTarget (circuitFor M (L + 1) (T (L + 1)))) = 1 := by
  rw [normalizedSource_eq_languageCharacteristic M SATLang T hD]
  apply GodMoveCircuitNormalization.multilinear_eq_of_boolean_eval
  · exact GodMoveMultilinearRestriction.isMultilinear_piSubst _ _ _ (interpolate_isMultilinear _)
  · intro a ha i
    exact (MvPolynomial.degreeOf_le_iff.mp
      (show (1 : GodMoveBooleanInterpolation.Poly (L + 1)).degreeOf i ≤ 1 by simp)) a ha
  · intro a
    have he := GodMoveBooleanFace.eval_piSubst_boolean
      (fun j : Fin (L + 1) => j ≠ 0) (fun _ => false)
      (languageCharacteristic SATLang (L + 1)) a
    simp only [bit, Bool.false_eq_true, ↓reduceIte] at he
    rw [he]
    rw [languageCharacteristic, eval_interpolate]
    rw [SATLang_of_first_false]
    · simp [bit]
    · rw [wordOfFin_getD]
      simp

end GodMoveSATLocalClockObstruction

#print axioms GodMoveSATLocalClockObstruction.SATLang_of_first_false
#print axioms GodMoveSATLocalClockObstruction.shortcut_run_embed
#print axioms GodMoveSATLocalClockObstruction.shortcut_decides
#print axioms GodMoveSATLocalClockObstruction.first_halt_all_false
#print axioms GodMoveSATLocalClockObstruction.normalizedSource_unchanged
#print axioms GodMoveSATLocalClockObstruction.paperSourceRank_unchanged
#print axioms GodMoveSATLocalClockObstruction.no_full_source_bound_from_easy_run
#print axioms GodMoveSATLocalClockObstruction.false_head_face_eq_one
