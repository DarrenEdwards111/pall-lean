import GodMoveSmallSeparatingSamples

/-!
# Counterexample-guided sample refinement has at most one step per wire

The residual space consists of computed-wire polynomials vanishing on every
sample selected so far. A supplied polynomial and Boolean point witnessing
failure of separation make the next residual space strictly smaller.
Consequently at most `wireRank c`, hence at most `c.length`, successful
refinements are possible. Residual dimension zero is exactly separation.

Counterexample discovery is an explicit outstanding operation. None of these
iteration bounds gives a runtime bound for finding the next polynomial or
Boolean assignment, deciding that no counterexample exists, or computing rank.
-/

namespace GodMoveSampleRefinement

open GodMoveBooleanInterpolation GodMoveCircuitNormalization GodMoveComputedWireRank
open GodMoveSamplingBarrier GodMoveSmallSeparatingSamples
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer (CGate)

/-- The unresolved kernel, as a submodule of the actual finite wire space. -/
noncomputable def residualSpace {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) : Submodule ℚ (wireSpace c) :=
  ⨅ a ∈ samples, LinearMap.ker (restrictedEval c a)

@[simp] theorem mem_residualSpace {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (p : wireSpace c) :
    p ∈ residualSpace c samples ↔
      ∀ a ∈ samples, MvPolynomial.eval (booleanPoint a) p.val = 0 := by
  simp [residualSpace]

noncomputable def residualRank {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) : ℕ :=
  Module.finrank ℚ (residualSpace c samples)

theorem residualSpace_nil {n : ℕ} (c : List (CGate n)) :
    residualSpace c [] = ⊤ := by
  ext p
  simp

theorem residualRank_nil {n : ℕ} (c : List (CGate n)) :
    residualRank c [] = wireRank c := by
  rw [residualRank, residualSpace_nil]
  exact finrank_top ℚ (wireSpace c)

theorem residualSpace_append {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (a : Assignment n) :
    residualSpace c (samples ++ [a]) =
      residualSpace c samples ⊓ LinearMap.ker (restrictedEval c a) := by
  ext p
  simp [or_imp, forall_and]

theorem residualSpace_append_le {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (a : Assignment n) :
    residualSpace c (samples ++ [a]) ≤ residualSpace c samples := by
  rw [residualSpace_append]
  exact inf_le_left

/-- A refinement witness contains both the unresolved polynomial and a point
where it does not vanish. Finding this witness is not part of the definition. -/
def Counterexample {n : ℕ} (c : List (CGate n)) (samples : List (Assignment n))
    (a : Assignment n) : Prop :=
  ∃ p : wireSpace c, p ∈ residualSpace c samples ∧ restrictedEval c a p ≠ 0

theorem residualSpace_append_lt {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (a : Assignment n)
    (h : Counterexample c samples a) :
    residualSpace c (samples ++ [a]) < residualSpace c samples := by
  obtain ⟨p, hp, hpa⟩ := h
  apply lt_of_le_of_ne (residualSpace_append_le c samples a)
  intro heq
  have hmem : p ∈ residualSpace c (samples ++ [a]) := heq.symm ▸ hp
  exact hpa ((mem_residualSpace c _ p).mp hmem a (by simp))

/-- Each supplied counterexample consumes at least one remaining dimension. -/
theorem residualRank_append_lt {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (a : Assignment n)
    (h : Counterexample c samples a) :
    residualRank c (samples ++ [a]) < residualRank c samples :=
  Submodule.finrank_lt_finrank_of_lt (residualSpace_append_lt c samples a h)

theorem residualSpace_eq_bot_iff_separates {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) :
    residualSpace c samples = ⊥ ↔ SeparatesWires c samples := by
  constructor
  · intro heq p hp hzero
    have hmem : (⟨p, hp⟩ : wireSpace c) ∈ residualSpace c samples :=
      (mem_residualSpace c samples _).mpr hzero
    rw [heq] at hmem
    exact congrArg Subtype.val (show (⟨p, hp⟩ : wireSpace c) = 0 from by simpa using hmem)
  · intro hsep
    apply (Submodule.eq_bot_iff _).mpr
    intro p hp
    apply Subtype.ext
    exact hsep p.val p.property ((mem_residualSpace c samples p).mp hp)

/-- Zero residual dimension is a complete stopping criterion, as a theorem;
this does not give a procedure for computing that dimension. -/
theorem residualRank_eq_zero_iff_separates {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) :
    residualRank c samples = 0 ↔ SeparatesWires c samples := by
  rw [residualRank, Submodule.finrank_eq_zero, residualSpace_eq_bot_iff_separates]

/-- Every failure of separation has a Boolean counterexample because all
computed-wire polynomials are multilinear. This is existence, not discovery. -/
theorem exists_counterexample_iff_not_separates {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) :
    (∃ a, Counterexample c samples a) ↔ ¬ SeparatesWires c samples := by
  classical
  constructor
  · rintro ⟨a, p, hp, hpa⟩ hsep
    have hpzero := hsep p.val p.property ((mem_residualSpace c samples p).mp hp)
    apply hpa
    simp [restrictedEval_apply, hpzero]
  · intro hsep
    unfold SeparatesWires at hsep
    push_neg at hsep
    obtain ⟨p, hp, hzero, hpne⟩ := hsep
    have he : ∃ a, MvPolynomial.eval (booleanPoint a) p ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hpne
      apply multilinear_eq_of_boolean_eval p 0 (isMultilinear_of_mem_wireSpace c p hp)
        (by simp [MultilinearSPDP.IsMultilinear])
      intro a
      simpa using hn a
    obtain ⟨a, ha⟩ := he
    exact ⟨a, ⟨p, hp⟩, (mem_residualSpace c samples _).mpr hzero, ha⟩

/-- A trace of successful refinements. The witness search is deliberately
external: every step supplies its own semantic counterexample proof. -/
def SuccessfulRefinements {n : ℕ} (c : List (CGate n)) :
    List (Assignment n) → List (Assignment n) → Prop
  | _, [] => True
  | samples, a :: rest => Counterexample c samples a ∧
      SuccessfulRefinements c (samples ++ [a]) rest

/-- The remaining dimension plus the number of successful steps cannot exceed
the initial unresolved dimension. -/
theorem residualRank_add_steps_le {n : ℕ} (c : List (CGate n))
    (samples added : List (Assignment n)) (h : SuccessfulRefinements c samples added) :
    residualRank c (samples ++ added) + added.length ≤ residualRank c samples := by
  induction added generalizing samples with
  | nil => simp
  | cons a rest ih =>
    obtain ⟨hstep, hrest⟩ := h
    have hdrop := residualRank_append_lt c samples a hstep
    have htail := ih (samples ++ [a]) hrest
    have heq : samples ++ a :: rest = (samples ++ [a]) ++ rest := by simp
    rw [heq, List.length_cons]
    omega

/-- Any trace starting from no samples has at most one successful step per
independent computed-wire direction. -/
theorem successful_steps_le_wireRank {n : ℕ} (c : List (CGate n))
    (added : List (Assignment n)) (h : SuccessfulRefinements c [] added) :
    added.length ≤ wireRank c := by
  have hbudget := residualRank_add_steps_le c [] added h
  rw [residualRank_nil] at hbudget
  omega

theorem successful_steps_le_length {n : ℕ} (c : List (CGate n))
    (added : List (Assignment n)) (h : SuccessfulRefinements c [] added) :
    added.length ≤ c.length :=
  (successful_steps_le_wireRank c added h).trans (wireRank_le_length c)

/-- Reaching the dimension bound guarantees separation; no further successful
counterexample can remain after that many refinements. -/
theorem separates_of_full_refinement {n : ℕ} (c : List (CGate n))
    (added : List (Assignment n)) (h : SuccessfulRefinements c [] added)
    (hlen : added.length = wireRank c) : SeparatesWires c added := by
  apply (residualRank_eq_zero_iff_separates c added).mp
  have hbudget := residualRank_add_steps_le c [] added h
  simp only [List.nil_append, residualRank_nil, hlen] at hbudget
  omega

end GodMoveSampleRefinement

#print axioms GodMoveSampleRefinement.residualRank_append_lt
#print axioms GodMoveSampleRefinement.residualRank_eq_zero_iff_separates
#print axioms GodMoveSampleRefinement.exists_counterexample_iff_not_separates
#print axioms GodMoveSampleRefinement.residualRank_add_steps_le
#print axioms GodMoveSampleRefinement.successful_steps_le_wireRank
#print axioms GodMoveSampleRefinement.successful_steps_le_length
#print axioms GodMoveSampleRefinement.separates_of_full_refinement
