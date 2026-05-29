import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth2ThresholdCircuit

/-!
# UPP/sign-rank bridge substrate for depth-2 threshold circuits

This file builds the honest algebraic core behind the UPP bridge:

* a finite transcript expectation realizer is a sum of split rectangle terms;
* such a realizer immediately gives a sign-rank upper bound;
* if every bottom gate supplies an **exact signed-output** transcript realizer,
  then the top threshold gate supplies a whole-circuit transcript realizer;
* more usefully, if every weighted bottom contribution is approximated with a
  controlled error and the top gate has larger margin than the total error, then
  the whole circuit again supplies a transcript realizer.

The exact-output theorem is a clean endpoint but not the live UPP route: exact
`±1` bottom matrices can be full rank.  The margin-controlled theorem is the
honest algebraic substrate for biased UPP composition.  The remaining hard step
is the margin-free probabilistic communication theorem that constructs such
low-transcript biased realizers for threshold-of-halfspaces without assuming a
top margin.
-/

namespace PallLean.Paper93.DeepMath.PathB

open scoped BigOperators

universe u

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


/-! ## Protocol semantics: finite rectangle protocols -/

/-- A finite unbounded-error communication protocol in transcript form.

For each transcript `t`, Alice contributes a nonnegative factor depending only on
row input `i`, Bob contributes a nonnegative factor depending only on column
input `j`, and `out t` is the Boolean answer attached to that transcript.  The
normalization field says these rectangle weights form a probability distribution
on transcripts for every input pair.  The `bias_ok` field is the UPP condition:
the signed expected output has the same sign as the target matrix.

This is still an abstract transcript-normal-form protocol, not yet a theorem that
`THR ∘ LTF` circuits admit `O(log s)` such protocols. -/
structure UPPCommunicationProtocol (M : Fin m -> Fin n -> Bool)
    (τ : Type*) [Fintype τ] where
  aliceProb : τ -> Fin m -> ℝ
  bobProb : τ -> Fin n -> ℝ
  out : τ -> Bool
  alice_nonneg : ∀ t i, 0 ≤ aliceProb t i
  bob_nonneg : ∀ t j, 0 ≤ bobProb t j
  prob_sum_one : ∀ i j, (∑ t : τ, aliceProb t i * bobProb t j) = 1
  bias_ok : ∀ i j,
    0 < sgn (M i j) * (∑ t : τ, (sgn (out t) * aliceProb t i) * bobProb t j)

/-- The signed expected output of a finite UPP protocol is a transcript realizer.
This is the semantic `protocol ⇒ transcript realizer` step. -/
def UPPCommunicationProtocol.toTranscriptRealizer
    {M : Fin m -> Fin n -> Bool} {τ : Type*} [Fintype τ]
    (P : UPPCommunicationProtocol M τ) : UPPTranscriptRealizer M τ where
  alice := fun t i => sgn (P.out t) * P.aliceProb t i
  bob := fun t j => P.bobProb t j
  sign_ok := by
    intro i j
    exact P.bias_ok i j

/-- Protocols inherit the sign-rank upper bound through their signed expectation
matrix. -/
theorem hasSignRankLE_of_uppCommunicationProtocol
    {M : Fin m -> Fin n -> Bool} {τ : Type*} [Fintype τ]
    (P : UPPCommunicationProtocol M τ) :
    HasSignRankLE M (Fintype.card τ) :=
  hasSignRankLE_of_uppTranscriptRealizer P.toTranscriptRealizer

/-- UPP protocol cost at most `c`: there is a finite transcript protocol with at
most `2^c` transcripts. -/
def UPPProtocolCostLE (M : Fin m -> Fin n -> Bool) (c : Nat) : Prop :=
  ∃ (τ : Type u) (_ : Fintype τ),
    Fintype.card τ ≤ 2 ^ c ∧ Nonempty (UPPCommunicationProtocol M τ)

/-- The formal cost bridge for actual protocol semantics:
`UPP protocol cost c ⇒ sign-rank ≤ 2^c`. -/
theorem hasSignRankLE_of_uppProtocolCostLE
    {M : Fin m -> Fin n -> Bool} {c : Nat} (h : UPPProtocolCostLE M c) :
    HasSignRankLE M (2 ^ c) := by
  rcases h with ⟨τ, hτ, hcard, hP⟩
  letI : Fintype τ := hτ
  rcases hP with ⟨P⟩
  exact hasSignRankLE_mono (M := M) hcard
    (hasSignRankLE_of_uppCommunicationProtocol P)

/-- Any concrete finite UPP protocol gives the corresponding cost bound whenever
its transcript count is within the budget. -/
theorem uppProtocolCostLE_of_protocol
    {M : Fin m -> Fin n -> Bool} {τ : Type u} [Fintype τ] {c : Nat}
    (P : UPPCommunicationProtocol M τ) (hcard : Fintype.card τ ≤ 2 ^ c) :
    UPPProtocolCostLE.{u} M c :=
  ⟨τ, inferInstance, hcard, ⟨P⟩⟩

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

/-- A weighted bottom-gate transcript approximation.  The transcript matrix
approximates the **weighted** signed bottom output
`C.w k * sgn (C.bottomGate k i j)` up to error `ε`.

This is the algebraic object the real UPP route needs: exact output is not
required, but the approximation error must be controlled tightly enough for the
top gate's margin. -/
structure WeightedApproxBottomRealizer (C : Depth2Threshold m n) (k : Fin C.s)
    (τ : Type*) [Fintype τ] where
  alice : τ -> Fin m -> ℝ
  bob : τ -> Fin n -> ℝ
  ε : ℝ
  eps_nonneg : 0 ≤ ε
  approx : ∀ i j,
    |(∑ t : τ, alice t i * bob t j) - C.w k * sgn (C.bottomGate k i j)| ≤ ε

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

/-- Total bottom-approximation error for the margin-controlled UPP bridge. -/
def weightedApproxError
    (C : Depth2Threshold m n)
    {τ : Fin C.s -> Type*} [∀ k, Fintype (τ k)]
    (P : ∀ k, WeightedApproxBottomRealizer C k (τ k)) : ℝ :=
  ∑ k, (P k).ε

/-- The exact real-valued top argument before applying `decide`. -/
noncomputable def topArgument (C : Depth2Threshold m n) (i : Fin m) (j : Fin n) : ℝ :=
  (∑ k, C.w k * sgn (C.bottomGate k i j)) - C.θ

/-- Margin-controlled biased-output composition.  If each weighted bottom
contribution has a transcript approximation and the total error is strictly
smaller than the top gate's margin at every input, then the sum of those
transcripts plus the bias transcript realizes the whole circuit's sign pattern.

This is the useful algebraic bridge below the full UPP theorem.  It still has an
explicit margin hypothesis; the margin-free UPP construction is the remaining
probabilistic communication complexity step. -/
def wholeCircuitUPPRealizer_of_weightedApproxBottomOutputs
    (C : Depth2Threshold m n)
    {τ : Fin C.s -> Type*} [∀ k, Fintype (τ k)]
    (P : ∀ k, WeightedApproxBottomRealizer C k (τ k))
    (hmargin : ∀ i j, weightedApproxError C P < |topArgument C i j|) :
    UPPTranscriptRealizer C.eval (Option (Sigma τ)) where
  alice
    | none => fun _ => -C.θ
    | some ⟨k, t⟩ => fun i => (P k).alice t i
  bob
    | none => fun _ => 1
    | some ⟨k, t⟩ => fun j => (P k).bob t j
  sign_ok := by
    intro i j
    let approxTop : ℝ :=
      (∑ k : Fin C.s, ∑ t : τ k, (P k).alice t i * (P k).bob t j) - C.θ
    let exactTop : ℝ := topArgument C i j
    have hsum :
        (∑ r : Option (Sigma τ),
          (match r with
            | none => fun _ : Fin m => -C.θ
            | some ⟨k, t⟩ => fun i => (P k).alice t i) i *
          (match r with
            | none => fun _ : Fin n => 1
            | some ⟨k, t⟩ => fun j => (P k).bob t j) j)
          = approxTop := by
      rw [Fintype.sum_option, Fintype.sum_sigma]
      simp only [mul_one]
      ring
    have hdiff :
        |approxTop - exactTop| ≤ weightedApproxError C P := by
      have hrewrite :
          approxTop - exactTop
            =
          ∑ k : Fin C.s,
            ((∑ t : τ k, (P k).alice t i * (P k).bob t j)
              - C.w k * sgn (C.bottomGate k i j)) := by
        simp only [approxTop, exactTop, topArgument]
        calc
          ((∑ k : Fin C.s, ∑ t : τ k, (P k).alice t i * (P k).bob t j) - C.θ)
              - ((∑ k : Fin C.s, C.w k * sgn (C.bottomGate k i j)) - C.θ)
              =
            (∑ k : Fin C.s, ∑ t : τ k, (P k).alice t i * (P k).bob t j)
              - ∑ k : Fin C.s, C.w k * sgn (C.bottomGate k i j) := by
                ring
          _ =
            ∑ k : Fin C.s,
              ((∑ t : τ k, (P k).alice t i * (P k).bob t j)
                - C.w k * sgn (C.bottomGate k i j)) := by
                rw [Finset.sum_sub_distrib]
      rw [hrewrite]
      calc
        |∑ k : Fin C.s,
            ((∑ t : τ k, (P k).alice t i * (P k).bob t j)
              - C.w k * sgn (C.bottomGate k i j))|
            ≤ ∑ k : Fin C.s,
              |(∑ t : τ k, (P k).alice t i * (P k).bob t j)
                - C.w k * sgn (C.bottomGate k i j)| := by
                simpa using
                  (Finset.abs_sum_le_sum_abs
                    (fun k : Fin C.s =>
                      (∑ t : τ k, (P k).alice t i * (P k).bob t j)
                        - C.w k * sgn (C.bottomGate k i j))
                    Finset.univ)
        _ ≤ ∑ k : Fin C.s, (P k).ε := by
                exact Finset.sum_le_sum (fun k _ => (P k).approx i j)
    have hWnonneg : 0 ≤ weightedApproxError C P := by
      exact Finset.sum_nonneg (fun k _ => (P k).eps_nonneg)
    have habslt : |approxTop - exactTop| < |exactTop| :=
      lt_of_le_of_lt hdiff (by simpa [exactTop] using hmargin i j)
    have hexact_ne : exactTop ≠ 0 := by
      intro hz
      have hbad : weightedApproxError C P < 0 := by
        simpa [exactTop, hz] using hmargin i j
      linarith
    rw [hsum]
    rcases lt_or_gt_of_ne hexact_ne with hlt | hgt
    · have hlt_abs : |approxTop - exactTop| < -exactTop := by
        rwa [abs_of_neg hlt] at habslt
      have hbounds := abs_lt.mp hlt_abs
      have happrox_neg : approxTop < 0 := by
        linarith
      have hb : C.eval i j = false := by
        have hltTop : topArgument C i j < 0 := by
          simpa [exactTop] using hlt
        simp only [eval, decide_eq_false_iff_not, not_lt]
        exact le_of_lt hltTop
      rw [hb, show sgn false = (-1 : ℝ) from rfl]
      nlinarith
    · have hgt_abs : |approxTop - exactTop| < exactTop := by
        rwa [abs_of_pos hgt] at habslt
      have hbounds := abs_lt.mp hgt_abs
      have happrox_pos : 0 < approxTop := by
        linarith
      have hb : C.eval i j = true := by
        have hgtTop : 0 < topArgument C i j := by
          simpa [exactTop] using hgt
        simp only [eval, decide_eq_true_eq]
        exact hgtTop
      rw [hb, show sgn true = (1 : ℝ) from rfl]
      nlinarith

/-- Whole-circuit sign-rank upper bound from margin-controlled weighted bottom
approximations.  The bound is still the transcript count
`1 + ∑ k, |τ k|`; the nontrivial live UPP problem is constructing such bottom
realizers with few transcripts and no global top-margin assumption. -/
theorem wholeCircuit_hasSignRankLE_of_weightedApproxBottomOutputs
    (C : Depth2Threshold m n)
    {τ : Fin C.s -> Type*} [∀ k, Fintype (τ k)]
    (P : ∀ k, WeightedApproxBottomRealizer C k (τ k))
    (hmargin : ∀ i j, weightedApproxError C P < |topArgument C i j|) :
    WholeCircuitSignRankBound C (Fintype.card (Option (Sigma τ))) :=
  hasSignRankLE_of_uppTranscriptRealizer
    (wholeCircuitUPPRealizer_of_weightedApproxBottomOutputs C P hmargin)

/-- The transcript count in the exact-output bridge is
`1 + ∑ k, |τ k|`. -/
theorem card_option_sigma_bottomTranscripts
    (C : Depth2Threshold m n)
    {τ : Fin C.s -> Type*} [∀ k, Fintype (τ k)] :
    Fintype.card (Option (Sigma τ)) = 1 + ∑ k, Fintype.card (τ k) := by
  rw [Fintype.card_option, Fintype.card_sigma]
  omega

#print axioms hasSignRankLE_of_uppTranscriptRealizer
#print axioms UPPCommunicationProtocol.toTranscriptRealizer
#print axioms hasSignRankLE_of_uppCommunicationProtocol
#print axioms hasSignRankLE_of_uppProtocolCostLE
#print axioms uppProtocolCostLE_of_protocol
#print axioms hasSignRankLE_of_exactSignedOutputRealizer
#print axioms wholeCircuitUPPRealizer_of_exactBottomOutputs
#print axioms wholeCircuit_hasSignRankLE_of_exactBottomOutputs
#print axioms wholeCircuitUPPRealizer_of_weightedApproxBottomOutputs
#print axioms wholeCircuit_hasSignRankLE_of_weightedApproxBottomOutputs
#print axioms card_option_sigma_bottomTranscripts

end Depth2Threshold

end PallLean.Paper93.DeepMath.PathB
