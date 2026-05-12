import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeTemplateCollapse
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetClosedFormDetSummary
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetPosDefN5N6
import PallLean.WithinProfileBound

/-!
# Small-`n` sanity check for the template-collapse predicate vocabulary

This file is a **vocabulary sanity check** at small dimensions `n = 5` and
`n = 6` for the predicate

```
WithinProfileBound.CookLevinProfileTemplateCollapseLemma M n hn htb hns
```

introduced in `WithinProfileBound.lean` and threaded through
`SATDeciderGaugeTemplateCollapse.lean`.

## Scope and disclaimer

This file makes **no claim** to discharge the template-collapse predicate at
small `n`, nor to prove `P ≠ NP` at any scale.  The honest large-`n` discharge
of `CookLevinProfileTemplateCollapseLemma` is a frontier obligation that
requires a compiled coefficient basis construction not yet in the repository
(see Agent 3 diagnostic in `WithinProfileBound`, around line 5599).

The purpose here is strictly **typecheck-level**: we verify that

1. The template-collapse predicate **typechecks** at concrete `n = 5` and
   `n = 6` for an explicit small `DTM` witness (`smallDTM`).
2. The vocabulary `compiledGadget α n` referenced in the user's question
   lives in a *matrix-valued* world (`Matrix (Fin n) (Fin n) ℝ`), whereas
   the template-collapse predicate operates on a *Turing machine* `M : DTM`
   and a polynomial spanning vocabulary
   (`MvPolynomial (Fin n) ℚ`).
3. The round-70 closed-form determinant stack
   (`compiledGadget_closed_form_det_2_to_6`) supplies value witnesses
   `(compiledGadget α 5).det = α(α+5)^4` and
   `(compiledGadget α 6).det = α(α+6)^5`.  These are **independent** of the
   template-collapse vocabulary: there is no direct coupling that would let
   one "satisfy" or "fail" the other.

In particular, the user's question

> does `compiledGadget 1 5` (or `compiledGadget α 5` for `α` from IVT)
> satisfy `templateCollapse` at `n = 5`?

is a **category-mismatch question**: `compiledGadget α n` is a matrix, not a
Turing machine, so it cannot be plugged into the predicate's signature.  The
predicate is well-formed at `n = 5, 6` for any `M : DTM` with
`M.numStates ≤ n` and `M.timeBound ≤ 4`; the gadget matrix is a separate,
matrix-valued object.

## What this file demonstrates

* `smallDTM` — a tiny `DTM` with `numStates = 3`, `timeBound = 1`.
  Hypotheses `hns : M.numStates ≤ n` are satisfied for `n ∈ {5, 6}`.
* `templateCollapsePredAt5` / `templateCollapsePredAt6` — the predicate
  itself, as a `Prop`, instantiated at `n = 5` and `n = 6` for `smallDTM`.
  These are *only* `Prop` definitions; we do not try to prove them.  Their
  successful elaboration is the sanity check.
* `compiledGadgetDet5_at_one` / `compiledGadgetDet6_at_one` — the round-70
  closed-form determinant values at `α = 1` for `n = 5, 6`.  These witness
  that the matrix-side vocabulary at the same `n` is compatible with the
  closed-form det stack but independent of the template-collapse predicate.
* `templateCollapse_vocabulary_disjoint_from_compiledGadget_5` — a precise
  documentation comment-theorem stating that the predicate's signature
  takes a `DTM`, not a matrix, and the matrix-side closed-form det at `α=1`
  is `1296`.  No coupling.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine
open WithinProfileBound
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.PathB.Positroid

/-! ### A tiny `DTM` witness

We take the smallest possible `DTM`: `numStates = 3` (the structural minimum),
`timeBound = 1` (the structural minimum).  All transitions go to state 0
writing bit `false` and moving right.  This is enough to satisfy
`numStates ≤ n` for any `n ≥ 3`, in particular for `n ∈ {5, 6}`. -/
def smallDTM : DTM where
  numStates := 3
  hStates := by decide
  transition := fun _ _ => (⟨0, by decide⟩, false, true)
  timeBound := 1
  hTimeBound := by decide

/-- The small DTM has `numStates = 3 ≤ 5`. -/
theorem smallDTM_numStates_le_five : smallDTM.numStates ≤ 5 := by
  unfold smallDTM; decide

/-- The small DTM has `numStates = 3 ≤ 6`. -/
theorem smallDTM_numStates_le_six : smallDTM.numStates ≤ 6 := by
  unfold smallDTM; decide

/-- The small DTM has `timeBound = 1 ≤ 4`. -/
theorem smallDTM_timeBound_le_four : smallDTM.timeBound ≤ 4 := by
  unfold smallDTM; decide

/-! ### Vocabulary typecheck of the template-collapse predicate at `n = 5, 6` -/

/-- The template-collapse predicate at `n = 5` for `smallDTM`, **as a `Prop`**.

This definition exists solely to verify that the predicate's signature
elaborates at concrete small `n`.  No proof is attempted: the discharge
of this `Prop` is a frontier obligation, not a small-`n` claim. -/
def templateCollapsePredAt5 : Prop :=
  CookLevinProfileTemplateCollapseLemma
    smallDTM 5 (by norm_num : (5 : ℕ) ≥ 2)
    smallDTM_timeBound_le_four
    smallDTM_numStates_le_five

/-- The template-collapse predicate at `n = 6` for `smallDTM`, **as a `Prop`**. -/
def templateCollapsePredAt6 : Prop :=
  CookLevinProfileTemplateCollapseLemma
    smallDTM 6 (by norm_num : (6 : ℕ) ≥ 2)
    smallDTM_timeBound_le_four
    smallDTM_numStates_le_six

/-- The bounded-profile variant typechecks at `n = 5`. -/
def templateCollapseBoundedProfilePredAt5 : Prop :=
  CookLevinProfileTemplateCollapseLemmaBoundedProfile
    smallDTM 5 (by norm_num : (5 : ℕ) ≥ 2)
    smallDTM_timeBound_le_four
    smallDTM_numStates_le_five

/-- The bounded-profile variant typechecks at `n = 6`. -/
def templateCollapseBoundedProfilePredAt6 : Prop :=
  CookLevinProfileTemplateCollapseLemmaBoundedProfile
    smallDTM 6 (by norm_num : (6 : ℕ) ≥ 2)
    smallDTM_timeBound_le_four
    smallDTM_numStates_le_six

/-! ### Matrix-side vocabulary at `n = 5, 6` (round-70 closed-form det stack)

These are statements about the *matrix* `compiledGadget α n`, not the
Turing-machine-level template-collapse predicate above.  They are recorded
here only to make the *vocabulary disjointness* explicit. -/

/-- Round-70 closed-form determinant at `n = 5, α = 1`: value is `1296`. -/
theorem compiledGadgetDet5_at_one_value :
    (compiledGadget 1 5).det = 1296 :=
  compiledGadget_5x5_at_one_det_eq_1296

/-- Round-70 closed-form determinant at `n = 6, α = 1`: value is `16807`. -/
theorem compiledGadgetDet6_at_one_value :
    (compiledGadget 1 6).det = 16807 :=
  compiledGadget_6x6_at_one_det_eq_16807

/-- Round-70 closed-form determinant for general `α` at `n = 5`. -/
theorem compiledGadgetDet5_general (α : ℝ) :
    (compiledGadget α 5).det = α * (α + 5)^4 :=
  (compiledGadget_closed_form_det_2_to_6 α).2.2.2.1

/-- Round-70 closed-form determinant for general `α` at `n = 6`. -/
theorem compiledGadgetDet6_general (α : ℝ) :
    (compiledGadget α 6).det = α * (α + 6)^5 :=
  (compiledGadget_closed_form_det_2_to_6 α).2.2.2.2

/-! ### Vocabulary-disjointness witness

The conjunction below records, in a single statement, that:

1. The template-collapse predicate at `n = 5` is a `Prop` parameterised by
   a `DTM`, hypotheses, **not** a matrix.
2. The matrix `compiledGadget 1 5` has the closed-form determinant value
   `1296`, completely independent of the template-collapse predicate.

This makes precise that the user's question "does `compiledGadget 1 5`
satisfy templateCollapse at `n = 5`?" is a category mismatch: the predicate
and the matrix live in disjoint vocabularies. -/
theorem templateCollapse_vocabulary_disjoint_from_compiledGadget_5 :
    -- The predicate at `n = 5` is a `Prop`, defined.
    (templateCollapsePredAt5 = templateCollapsePredAt5)
    -- The matrix-side closed-form value at `α = 1, n = 5`.
    ∧ (compiledGadget 1 5).det = 1296 :=
  ⟨rfl, compiledGadget_5x5_at_one_det_eq_1296⟩

/-- Vocabulary-disjointness witness at `n = 6`. -/
theorem templateCollapse_vocabulary_disjoint_from_compiledGadget_6 :
    (templateCollapsePredAt6 = templateCollapsePredAt6)
    ∧ (compiledGadget 1 6).det = 16807 :=
  ⟨rfl, compiledGadget_6x6_at_one_det_eq_16807⟩

/-! ### Summary report (as a comment)

**Verdict on the user's question.**

* Step 1: The predicate `templateCollapse` (i.e.
  `CookLevinProfileTemplateCollapseLemma`) is defined in
  `WithinProfileBound.lean` (line 1387 / 1204).  It requires:
  for every profile histogram `h : ProfileHistogram`, there exists a
  finite family `G : Finset (MvPolynomial (Fin n) ℚ)` such that
  `allBoundedProfilePostSpan ... h ≤ Submodule.span ℚ G ∧
   G.card ≤ profileTemplateBound h`.
* Step 2: The predicate's signature takes a `DTM`, not a matrix.  Therefore
  `compiledGadget α 5` (a `Matrix (Fin 5) (Fin 5) ℝ`) **cannot be plugged
  into the predicate** — the question is a category mismatch.
* Step 3: The predicate **does** typecheck at `n = 5` and `n = 6` for any
  `DTM M` with `M.numStates ≤ n` and `M.timeBound ≤ 4` (DTMs require
  `numStates ≥ 3`, so this is `numStates ∈ {3, 4, 5}` for `n = 5` and
  `numStates ∈ {3, 4, 5, 6}` for `n = 6`).  The witness `smallDTM` above
  has `numStates = 3`, `timeBound = 1`.
* Step 4: The conjunct that fails-to-apply is the **input domain** of the
  predicate.  No conjunct of the predicate body itself is being tested,
  because the predicate is not being instantiated at a matrix.

This is the **useful information about whether Codex's vocabulary is
composable at small `n`**: it composes (the predicate elaborates), but the
matrix vocabulary `compiledGadget α n` is **disjoint** from it and cannot
serve as a small-`n` test instance for the predicate. -/

/-! ### Axiom audit anchors -/
#print axioms templateCollapsePredAt5
#print axioms templateCollapsePredAt6
#print axioms templateCollapseBoundedProfilePredAt5
#print axioms templateCollapseBoundedProfilePredAt6
#print axioms compiledGadgetDet5_at_one_value
#print axioms compiledGadgetDet6_at_one_value
#print axioms compiledGadgetDet5_general
#print axioms compiledGadgetDet6_general
#print axioms templateCollapse_vocabulary_disjoint_from_compiledGadget_5
#print axioms templateCollapse_vocabulary_disjoint_from_compiledGadget_6

end PallLean.Paper93.DeepMath.PathB
