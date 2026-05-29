import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth2ThresholdCircuit

/-!
# UPP/sign-rank bridge substrate for depth-2 threshold circuits

This file builds the honest algebraic core behind the UPP bridge:

* a finite transcript expectation realizer is a sum of split rectangle terms;
* such a realizer immediately gives a sign-rank upper bound;
* if every bottom gate supplies an **exact signed-output** transcript realizer,
  then the top threshold gate supplies a whole-circuit transcript realizer.

The last hypothesis is intentionally stronger than ordinary sign-rank of the
bottom gates.  A sign-rank witness only has the correct sign; it does not give the
actual `±1` bottom output with uniform bias.  That uniform/exact-output issue is
the real UPP top-gate frontier, so this file proves the substrate without
pretending that `bottomGate_hasSignRankLE_two` composes through the top gate.
-/

namespace PallLean.Paper93.DeepMath.PathB

open scoped BigOperators

variable {m n : Nat}

/-- A finite unbounded-error transcript expectation realizer.  The real matrix
`∑ t, alice t i * bob t j` has the target sign pattern.  Algebraically, this is
exactly the rectangle-sum object whose rank is at most the transcript count. -/
structure UPPTranscriptRealizer (M : Fin m -> Fin n -> Bool)
    (τ : Type*) [Fintype τ] where
  alice : τ -> Fin m -> ℝ
  bob : τ -> Fin n -> ℝ
  sign_ok : ∀ i j, 0 < sgn (M i j) * (∑ t : τ, alice t i * bob t j)

/-- A transcript realizer gives a `HasSignRankLE` witness with dimension equal to
the number of transcripts.  This is the formal `protocol ⇒ sign-rank` direction. -/
theorem hasSignRankLE_of_uppTranscriptRealizer
    {M : Fin m -> Fin n -> Bool} {τ : Type*} [Fintype τ]
    (P : UPPTranscriptRealizer M τ) :
    HasSignRankLE M (Fintype.card τ) := by
  classical
  let e : τ ≃ Fin (Fintype.card τ) := Fintype.equivFin τ
  refine
    ⟨Matrix.of (fun i t => P.alice (e.symm t) i),
      Matrix.of (fun t j => P.bob (e.symm t) j), ?_⟩
  intro i j
  have hsum :
      (∑ t : Fin (Fintype.card τ), P.alice (e.symm t) i * P.bob (e.symm t) j)
        = ∑ t : τ, P.alice t i * P.bob t j := by
    exact Fintype.sum_equiv e.symm
      (fun t : Fin (Fintype.card τ) => P.alice (e.symm t) i * P.bob (e.symm t) j)
      (fun t : τ => P.alice t i * P.bob t j)
      (fun _ => rfl)
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [hsum]
  exact P.sign_ok i j

/-- Stronger bottom-gate object: the transcript expectation is exactly the
`±1` signed output matrix, not merely some same-sign matrix.  This is the
additional uniform-output ingredient needed before a top threshold can be
combined algebraically. -/
structure ExactSignedOutputRealizer (M : Fin m -> Fin n -> Bool)
    (τ : Type*) [Fintype τ] where
  alice : τ -> Fin m -> ℝ
  bob : τ -> Fin n -> ℝ
  exact : ∀ i j, (∑ t : τ, alice t i * bob t j) = sgn (M i j)

/-- Exact signed output is, in particular, a UPP transcript realizer. -/
def ExactSignedOutputRealizer.toUPPTranscriptRealizer
    {M : Fin m -> Fin n -> Bool} {τ : Type*} [Fintype τ]
    (P : ExactSignedOutputRealizer M τ) : UPPTranscriptRealizer M τ where
  alice := P.alice
  bob := P.bob
  sign_ok := by
    intro i j
    rw [P.exact i j, sgn_mul_self]
    norm_num

/-- Exact signed output gives the corresponding sign-rank upper bound. -/
theorem hasSignRankLE_of_exactSignedOutputRealizer
    {M : Fin m -> Fin n -> Bool} {τ : Type*} [Fintype τ]
    (P : ExactSignedOutputRealizer M τ) :
    HasSignRankLE M (Fintype.card τ) :=
  hasSignRankLE_of_uppTranscriptRealizer P.toUPPTranscriptRealizer

namespace Depth2Threshold

/-- If each bottom gate is available as an exact signed-output transcript
realizer, then the whole `THR ∘ LTF` circuit has a transcript realizer whose
transcripts are either the constant top-bias transcript or one transcript from
one bottom gate.

This is the precise algebraic composition step.  It does **not** assert that the
ordinary rank-2 bottom sign-rank witnesses are exact signed-output realizers. -/
def wholeCircuitUPPRealizer_of_exactBottomOutputs
    (C : Depth2Threshold m n)
    {τ : Fin C.s -> Type*} [∀ k, Fintype (τ k)]
    (P : ∀ k, ExactSignedOutputRealizer (C.bottomGate k) (τ k))
    (hne : ∀ i j, (∑ k, C.w k * sgn (C.bottomGate k i j)) - C.θ ≠ 0) :
    UPPTranscriptRealizer C.eval (Option (Sigma τ)) where
  alice
    | none => fun _ => -C.θ
    | some ⟨k, t⟩ => fun i => C.w k * (P k).alice t i
  bob
    | none => fun _ => 1
    | some ⟨k, t⟩ => fun j => (P k).bob t j
  sign_ok := by
    intro i j
    have hterm : ∀ k : Fin C.s,
        (∑ t : τ k, (C.w k * (P k).alice t i) * (P k).bob t j)
          = C.w k * sgn (C.bottomGate k i j) := by
      intro k
      calc
        (∑ t : τ k, (C.w k * (P k).alice t i) * (P k).bob t j)
            = C.w k * (∑ t : τ k, (P k).alice t i * (P k).bob t j) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun t _ => ?_)
              ring
        _ = C.w k * sgn (C.bottomGate k i j) := by
              rw [(P k).exact i j]
    have hsum :
        (∑ r : Option (Sigma τ),
          (match r with
            | none => fun _ : Fin m => -C.θ
            | some ⟨k, t⟩ => fun i => C.w k * (P k).alice t i) i *
          (match r with
            | none => fun _ : Fin n => 1
            | some ⟨k, t⟩ => fun j => (P k).bob t j) j)
          = (∑ k, C.w k * sgn (C.bottomGate k i j)) - C.θ := by
      rw [Fintype.sum_option, Fintype.sum_sigma]
      simp only [mul_one]
      rw [show
        (∑ x : Fin C.s,
            ∑ y : τ x, (C.w x * (P x).alice y i) * (P x).bob y j)
          = ∑ x : Fin C.s, C.w x * sgn (C.bottomGate x i j) from
        Finset.sum_congr rfl (fun k _ => hterm k)]
      ring
    rw [hsum]
    rcases lt_or_gt_of_ne (hne i j) with hlt | hgt
    · have hb : C.eval i j = false := by
        simp only [eval, decide_eq_false_iff_not, not_lt]
        linarith
      rw [hb, show sgn false = (-1 : ℝ) from rfl]
      nlinarith
    · have hb : C.eval i j = true := by
        simp only [eval, decide_eq_true_eq]
        linarith
      rw [hb, show sgn true = (1 : ℝ) from rfl]
      nlinarith

/-- Whole-circuit sign-rank upper bound from exact signed-output bottom
realizers.  The dimension is the transcript count
`1 + ∑ k, |τ k|`, expressed as the cardinality of `Option (Sigma τ)`.

This is a real composition theorem, but it is deliberately conditional on exact
bottom-output realizers; proving the UPP `O(log s)` top-gate bound for ordinary
bottom LTFs is the remaining communication-complexity theorem. -/
theorem wholeCircuit_hasSignRankLE_of_exactBottomOutputs
    (C : Depth2Threshold m n)
    {τ : Fin C.s -> Type*} [∀ k, Fintype (τ k)]
    (P : ∀ k, ExactSignedOutputRealizer (C.bottomGate k) (τ k))
    (hne : ∀ i j, (∑ k, C.w k * sgn (C.bottomGate k i j)) - C.θ ≠ 0) :
    WholeCircuitSignRankBound C (Fintype.card (Option (Sigma τ))) :=
  hasSignRankLE_of_uppTranscriptRealizer
    (wholeCircuitUPPRealizer_of_exactBottomOutputs C P hne)

/-- The transcript count in the exact-output bridge is
`1 + ∑ k, |τ k|`. -/
theorem card_option_sigma_bottomTranscripts
    (C : Depth2Threshold m n)
    {τ : Fin C.s -> Type*} [∀ k, Fintype (τ k)] :
    Fintype.card (Option (Sigma τ)) = 1 + ∑ k, Fintype.card (τ k) := by
  rw [Fintype.card_option, Fintype.card_sigma]
  omega

#print axioms hasSignRankLE_of_uppTranscriptRealizer
#print axioms hasSignRankLE_of_exactSignedOutputRealizer
#print axioms wholeCircuitUPPRealizer_of_exactBottomOutputs
#print axioms wholeCircuit_hasSignRankLE_of_exactBottomOutputs
#print axioms card_option_sigma_bottomTranscripts

end Depth2Threshold

end PallLean.Paper93.DeepMath.PathB
