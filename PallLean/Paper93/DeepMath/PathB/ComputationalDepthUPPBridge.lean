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


/-- Negating a Boolean flips its ±1 sign. -/
theorem sgn_not (b : Bool) : sgn (!b) = -sgn b := by
  cases b <;> norm_num [sgn]

/-- Flip a protocol output when multiplying by a negative weight. -/
theorem sgn_weighted_output (w : ℝ) (b : Bool) :
    sgn (if 0 ≤ w then b else !b) * |w| = w * sgn b := by
  by_cases hw : 0 ≤ w
  · simp [hw, abs_of_nonneg hw]
    ring
  · have hlt : w < 0 := lt_of_not_ge hw
    simp [hw, sgn_not, abs_of_neg hlt]
    ring

/-- A Boolean output representing the sign of `-θ` contributes exactly `-θ` when
weighted by `|θ|`. -/
theorem sgn_bias_output (θ : ℝ) :
    sgn (decide (0 < -θ)) * |θ| = -θ := by
  by_cases h : 0 < -θ
  · have hθ : θ < 0 := by linarith
    rw [show decide (0 < -θ) = true by simp [h],
      show sgn true = (1 : ℝ) from rfl, abs_of_neg hθ]
    ring
  · have hθ : 0 ≤ θ := by linarith
    rw [show decide (0 < -θ) = false by simp [h],
      show sgn false = (-1 : ℝ) from rfl, abs_of_nonneg hθ]
    ring

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
`THR ∘ LTF` circuits have `O(log s)` such protocols. -/
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

/-! ## Bottom split-halfspace protocol -/

/-- Ten transcripts for the elementary split-halfspace UPP protocol.  Four
transcripts carry the signed row/column bias, and six neutral transcripts fill
the remaining probability mass without changing the signed expectation. -/
inductive SplitHalfspaceTranscript where
  | alphaPos | alphaNeg
  | betaPos | betaNeg
  | fillConstPos | fillConstNeg
  | fillAlphaPos | fillAlphaNeg
  | fillBetaPos | fillBetaNeg
  deriving DecidableEq

instance : Fintype SplitHalfspaceTranscript where
  elems :=
    { .alphaPos, .alphaNeg,
      .betaPos, .betaNeg,
      .fillConstPos, .fillConstNeg,
      .fillAlphaPos, .fillAlphaNeg,
      .fillBetaPos, .fillBetaNeg }
  complete := by
    intro x
    cases x <;> simp

private lemma sum_splitHalfspaceTranscript {A : Type*} [AddCommMonoid A]
    (f : SplitHalfspaceTranscript -> A) :
    (∑ t : SplitHalfspaceTranscript, f t)
      =
    f .alphaPos + f .alphaNeg
      + f .betaPos + f .betaNeg
      + f .fillConstPos + f .fillConstNeg
      + f .fillAlphaPos + f .fillAlphaNeg
      + f .fillBetaPos + f .fillBetaNeg := by
  have huniv :
      (Finset.univ : Finset SplitHalfspaceTranscript)
        =
      { .alphaPos, .alphaNeg,
        .betaPos, .betaNeg,
        .fillConstPos, .fillConstNeg,
        .fillAlphaPos, .fillAlphaNeg,
        .fillBetaPos, .fillBetaNeg } := by
    ext x
    cases x <;> simp
  rw [huniv]
  simp [Finset.sum_insert, add_assoc]

private lemma max_pos_sub_max_neg (x : ℝ) :
    max x 0 - max (-x) 0 = x := by
  by_cases hx : 0 ≤ x
  · have hnx : -x ≤ 0 := by linarith
    rw [max_eq_left hx, max_eq_right hnx]
    ring
  · have hxle : x ≤ 0 := le_of_not_ge hx
    have hnneg : 0 ≤ -x := by linarith
    rw [max_eq_right hxle, max_eq_left hnneg]
    ring

private lemma max_pos_add_max_neg (x : ℝ) :
    max x 0 + max (-x) 0 = |x| := by
  by_cases hx : 0 ≤ x
  · have hnx : -x ≤ 0 := by linarith
    rw [max_eq_left hx, max_eq_right hnx, abs_of_nonneg hx]
    ring
  · have hxle : x ≤ 0 := le_of_not_ge hx
    have hlt : x < 0 := lt_of_not_ge hx
    have hnneg : 0 ≤ -x := by linarith
    rw [max_eq_right hxle, max_eq_left hnneg, abs_of_neg hlt]
    ring

/-- The signed contribution carried by the two transcripts encoding a real
number `x`. -/
private lemma split_signed_part (x : ℝ) :
    max x 0 - max (-x) 0 = x :=
  max_pos_sub_max_neg x

/-- The probability mass used by the two transcripts encoding a real number
`x`. -/
private lemma split_unsigned_part (x : ℝ) :
    max x 0 + max (-x) 0 = |x| :=
  max_pos_add_max_neg x

/-- A split halfspace `sign(α i + β j)` has a concrete constant-transcript UPP
protocol once a positive scale `δ` is small enough that
`|δ * α i|, |δ * β j| ≤ 1/4`.

The signed expectation of this protocol is exactly `δ * (α i + β j)`, while the
unsigned transcript weights sum to `1`.  This is the real bottom-gate protocol
step; the remaining convenience lemma is to choose such a `δ` automatically from
finite `α` and `β`. -/
noncomputable def splitHalfspaceUPPProtocol_of_scaled
    (α : Fin m -> ℝ) (β : Fin n -> ℝ) (δ : ℝ)
    (hδ : 0 < δ)
    (hα : ∀ i, |δ * α i| ≤ (1 / 4 : ℝ))
    (hβ : ∀ j, |δ * β j| ≤ (1 / 4 : ℝ))
    (hne : ∀ i j, α i + β j ≠ 0) :
    UPPCommunicationProtocol (bipartiteHalfspace α β) SplitHalfspaceTranscript where
  aliceProb
    | .alphaPos => fun i => max (δ * α i) 0
    | .alphaNeg => fun i => max (-(δ * α i)) 0
    | .betaPos => fun _ => 1
    | .betaNeg => fun _ => 1
    | .fillConstPos => fun _ => (1 / 4 : ℝ)
    | .fillConstNeg => fun _ => (1 / 4 : ℝ)
    | .fillAlphaPos => fun i => ((1 / 4 : ℝ) - |δ * α i|) / 2
    | .fillAlphaNeg => fun i => ((1 / 4 : ℝ) - |δ * α i|) / 2
    | .fillBetaPos => fun _ => 1
    | .fillBetaNeg => fun _ => 1
  bobProb
    | .alphaPos => fun _ => 1
    | .alphaNeg => fun _ => 1
    | .betaPos => fun j => max (δ * β j) 0
    | .betaNeg => fun j => max (-(δ * β j)) 0
    | .fillConstPos => fun _ => 1
    | .fillConstNeg => fun _ => 1
    | .fillAlphaPos => fun _ => 1
    | .fillAlphaNeg => fun _ => 1
    | .fillBetaPos => fun j => ((1 / 4 : ℝ) - |δ * β j|) / 2
    | .fillBetaNeg => fun j => ((1 / 4 : ℝ) - |δ * β j|) / 2
  out
    | .alphaPos => true
    | .alphaNeg => false
    | .betaPos => true
    | .betaNeg => false
    | .fillConstPos => true
    | .fillConstNeg => false
    | .fillAlphaPos => true
    | .fillAlphaNeg => false
    | .fillBetaPos => true
    | .fillBetaNeg => false
  alice_nonneg := by
    intro t i
    cases t <;> simp
    · have hi : |δ| * |α i| ≤ (1 / 4 : ℝ) := by
        simpa [abs_mul] using hα i
      nlinarith
    · have hi : |δ| * |α i| ≤ (1 / 4 : ℝ) := by
        simpa [abs_mul] using hα i
      nlinarith
  bob_nonneg := by
    intro t j
    cases t <;> simp
    · have hj : |δ| * |β j| ≤ (1 / 4 : ℝ) := by
        simpa [abs_mul] using hβ j
      nlinarith
    · have hj : |δ| * |β j| ≤ (1 / 4 : ℝ) := by
        simpa [abs_mul] using hβ j
      nlinarith
  prob_sum_one := by
    intro i j
    rw [sum_splitHalfspaceTranscript]
    change
        max (δ * α i) 0 * 1
          + max (-(δ * α i)) 0 * 1
          + 1 * max (δ * β j) 0
          + 1 * max (-(δ * β j)) 0
          + (1 / 4 : ℝ) * 1
          + (1 / 4 : ℝ) * 1
          + (((1 / 4 : ℝ) - |δ * α i|) / 2) * 1
          + (((1 / 4 : ℝ) - |δ * α i|) / 2) * 1
          + 1 * (((1 / 4 : ℝ) - |δ * β j|) / 2)
          + 1 * (((1 / 4 : ℝ) - |δ * β j|) / 2)
        = 1
    simp only [mul_one, one_mul]
    ring_nf
    nlinarith [split_unsigned_part (δ * α i), split_unsigned_part (δ * β j)]
  bias_ok := by
    intro i j
    have hbias :
        (∑ t : SplitHalfspaceTranscript,
            (sgn
                ((match t with
                  | .alphaPos => true
                  | .alphaNeg => false
                  | .betaPos => true
                  | .betaNeg => false
                  | .fillConstPos => true
                  | .fillConstNeg => false
                  | .fillAlphaPos => true
                  | .fillAlphaNeg => false
                  | .fillBetaPos => true
                  | .fillBetaNeg => false) : Bool) *
              (match t with
                | .alphaPos => fun i => max (δ * α i) 0
                | .alphaNeg => fun i => max (-(δ * α i)) 0
                | .betaPos => fun _ => 1
                | .betaNeg => fun _ => 1
                | .fillConstPos => fun _ => (1 / 4 : ℝ)
                | .fillConstNeg => fun _ => (1 / 4 : ℝ)
                | .fillAlphaPos => fun i => ((1 / 4 : ℝ) - |δ * α i|) / 2
                | .fillAlphaNeg => fun i => ((1 / 4 : ℝ) - |δ * α i|) / 2
                | .fillBetaPos => fun _ => 1
                | .fillBetaNeg => fun _ => 1) i) *
              (match t with
                | .alphaPos => fun _ => 1
                | .alphaNeg => fun _ => 1
                | .betaPos => fun j => max (δ * β j) 0
                | .betaNeg => fun j => max (-(δ * β j)) 0
                | .fillConstPos => fun _ => 1
                | .fillConstNeg => fun _ => 1
                | .fillAlphaPos => fun _ => 1
                | .fillAlphaNeg => fun _ => 1
                | .fillBetaPos => fun j => ((1 / 4 : ℝ) - |δ * β j|) / 2
                | .fillBetaNeg => fun j => ((1 / 4 : ℝ) - |δ * β j|) / 2) j)
          = δ * (α i + β j) := by
      rw [sum_splitHalfspaceTranscript]
      change
          (1 : ℝ) * max (δ * α i) 0 * 1
            + (-1 : ℝ) * max (-(δ * α i)) 0 * 1
            + (1 : ℝ) * 1 * max (δ * β j) 0
            + (-1 : ℝ) * 1 * max (-(δ * β j)) 0
            + (1 : ℝ) * (1 / 4 : ℝ) * 1
            + (-1 : ℝ) * (1 / 4 : ℝ) * 1
            + (1 : ℝ) * (((1 / 4 : ℝ) - |δ * α i|) / 2) * 1
            + (-1 : ℝ) * (((1 / 4 : ℝ) - |δ * α i|) / 2) * 1
            + (1 : ℝ) * 1 * (((1 / 4 : ℝ) - |δ * β j|) / 2)
            + (-1 : ℝ) * 1 * (((1 / 4 : ℝ) - |δ * β j|) / 2)
          = δ * (α i + β j)
      simp only [mul_one, one_mul]
      ring_nf
      rw [split_signed_part (δ * α i), split_signed_part (δ * β j)]
    rw [hbias]
    have hscaled : δ * (α i + β j) ≠ 0 := mul_ne_zero (ne_of_gt hδ) (hne i j)
    rcases lt_or_gt_of_ne hscaled with hlt | hgt
    · have hbase : α i + β j < 0 := by
        nlinarith [hδ]
      have hb : bipartiteHalfspace α β i j = false := by
        simp only [bipartiteHalfspace, decide_eq_false_iff_not, not_lt]
        exact le_of_lt hbase
      rw [hb, show sgn false = (-1 : ℝ) from rfl]
      nlinarith
    · have hbase : 0 < α i + β j := by
        nlinarith [hδ]
      have hb : bipartiteHalfspace α β i j = true := by
        simp only [bipartiteHalfspace, decide_eq_true_eq]
        exact hbase
      rw [hb, show sgn true = (1 : ℝ) from rfl]
      nlinarith

/-- The scaled split-halfspace protocol has ten transcripts, hence cost at most
`4` (`10 ≤ 2^4`). -/
theorem splitHalfspace_uppProtocolCostLE_four_of_scaled
    (α : Fin m -> ℝ) (β : Fin n -> ℝ) (δ : ℝ)
    (hδ : 0 < δ)
    (hα : ∀ i, |δ * α i| ≤ (1 / 4 : ℝ))
    (hβ : ∀ j, |δ * β j| ≤ (1 / 4 : ℝ))
    (hne : ∀ i j, α i + β j ≠ 0) :
    UPPProtocolCostLE.{0} (bipartiteHalfspace α β) 4 :=
  ⟨SplitHalfspaceTranscript, inferInstance, by decide,
    ⟨splitHalfspaceUPPProtocol_of_scaled α β δ hδ hα hβ hne⟩⟩

private lemma abs_le_sum_abs_fin {ι : Type*} [Fintype ι]
    (f : ι -> ℝ) (i : ι) : |f i| ≤ ∑ x, |f x| := by
  exact Finset.single_le_sum (fun x _ => abs_nonneg (f x)) (Finset.mem_univ i)

/-- A finite family of row/column weights admits a positive scale small enough
for the split-halfspace protocol.  The explicit choice is
`δ = (1/4) / (1 + ∑|α| + ∑|β|)`. -/
theorem exists_splitHalfspace_scale
    (α : Fin m -> ℝ) (β : Fin n -> ℝ) :
    ∃ δ : ℝ,
      0 < δ ∧
      (∀ i, |δ * α i| ≤ (1 / 4 : ℝ)) ∧
      (∀ j, |δ * β j| ≤ (1 / 4 : ℝ)) := by
  classical
  let B : ℝ := 1 + (∑ i : Fin m, |α i|) + (∑ j : Fin n, |β j|)
  let δ : ℝ := (1 / 4 : ℝ) / B
  have hsumα_nonneg : 0 ≤ ∑ i : Fin m, |α i| := by
    exact Finset.sum_nonneg (fun i _ => abs_nonneg (α i))
  have hsumβ_nonneg : 0 ≤ ∑ j : Fin n, |β j| := by
    exact Finset.sum_nonneg (fun j _ => abs_nonneg (β j))
  have hBpos : 0 < B := by
    dsimp [B]
    nlinarith
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact div_pos (by norm_num) hBpos
  have hδB : δ * B = (1 / 4 : ℝ) := by
    dsimp [δ]
    exact div_mul_cancel₀ (1 / 4 : ℝ) (ne_of_gt hBpos)
  refine ⟨δ, hδpos, ?_, ?_⟩
  · intro i
    have hi_sum : |α i| ≤ ∑ x : Fin m, |α x| :=
      abs_le_sum_abs_fin α i
    have hiB : |α i| ≤ B := by
      dsimp [B]
      nlinarith
    calc
      |δ * α i| = δ * |α i| := by
        rw [abs_mul, abs_of_pos hδpos]
      _ ≤ δ * B := mul_le_mul_of_nonneg_left hiB (le_of_lt hδpos)
      _ = (1 / 4 : ℝ) := hδB
  · intro j
    have hj_sum : |β j| ≤ ∑ y : Fin n, |β y| :=
      abs_le_sum_abs_fin β j
    have hjB : |β j| ≤ B := by
      dsimp [B]
      nlinarith
    calc
      |δ * β j| = δ * |β j| := by
        rw [abs_mul, abs_of_pos hδpos]
      _ ≤ δ * B := mul_le_mul_of_nonneg_left hjB (le_of_lt hδpos)
      _ = (1 / 4 : ℝ) := hδB

/-- Unconditional constant-cost UPP protocol for every nondegenerate split
halfspace.  The scale is chosen from the finite input tables `α` and `β`. -/
theorem splitHalfspace_uppProtocolCostLE_four
    (α : Fin m -> ℝ) (β : Fin n -> ℝ)
    (hne : ∀ i j, α i + β j ≠ 0) :
    UPPProtocolCostLE.{0} (bipartiteHalfspace α β) 4 := by
  obtain ⟨δ, hδ, hα, hβ⟩ := exists_splitHalfspace_scale α β
  exact splitHalfspace_uppProtocolCostLE_four_of_scaled α β δ hδ hα hβ hne


/-- A finite UPP protocol with **constant signed bias** `δ`: its signed expected
output is exactly `δ * sgn(M i j)` at every input.  This is stronger than plain
UPP bias and is the right composable object for weighted top thresholds. -/
structure ConstantBiasUPPProtocol (M : Fin m -> Fin n -> Bool)
    (τ : Type*) [Fintype τ] where
  aliceProb : τ -> Fin m -> ℝ
  bobProb : τ -> Fin n -> ℝ
  out : τ -> Bool
  δ : ℝ
  δ_pos : 0 < δ
  alice_nonneg : ∀ t i, 0 ≤ aliceProb t i
  bob_nonneg : ∀ t j, 0 ≤ bobProb t j
  prob_sum_one : ∀ i j, (∑ t : τ, aliceProb t i * bobProb t j) = 1
  bias_exact : ∀ i j,
    (∑ t : τ, (sgn (out t) * aliceProb t i) * bobProb t j) = δ * sgn (M i j)

/-- Constant-bias protocols are ordinary UPP protocols. -/
def ConstantBiasUPPProtocol.toUPPCommunicationProtocol
    {M : Fin m -> Fin n -> Bool} {τ : Type*} [Fintype τ]
    (P : ConstantBiasUPPProtocol M τ) : UPPCommunicationProtocol M τ where
  aliceProb := P.aliceProb
  bobProb := P.bobProb
  out := P.out
  alice_nonneg := P.alice_nonneg
  bob_nonneg := P.bob_nonneg
  prob_sum_one := P.prob_sum_one
  bias_ok := by
    intro i j
    rw [P.bias_exact i j]
    have hδ := P.δ_pos
    rw [show sgn (M i j) * (P.δ * sgn (M i j))
        = P.δ * (sgn (M i j) * sgn (M i j)) by ring, sgn_mul_self]
    simpa using hδ

/-- Constant-bias protocols inherit the sign-rank upper bound. -/
theorem hasSignRankLE_of_constantBiasUPPProtocol
    {M : Fin m -> Fin n -> Bool} {τ : Type*} [Fintype τ]
    (P : ConstantBiasUPPProtocol M τ) :
    HasSignRankLE M (Fintype.card τ) :=
  hasSignRankLE_of_uppCommunicationProtocol P.toUPPCommunicationProtocol


namespace Depth2Threshold

/-- The exact real-valued top argument before applying `decide`. -/
noncomputable def topArgument (C : Depth2Threshold m n) (i : Fin m) (j : Fin n) : ℝ :=
  (∑ k, C.w k * sgn (C.bottomGate k i j)) - C.θ

/-- Every nondegenerate bottom `LTF` gate of a depth-2 threshold circuit has
constant UPP protocol cost. -/
theorem bottomGate_uppProtocolCostLE_four
    (C : Depth2Threshold m n) (k : Fin C.s)
    (hne : ∀ i j, C.α k i + C.β k j ≠ 0) :
    UPPProtocolCostLE.{0} (C.bottomGate k) 4 := by
  simpa [bottomGate] using
    (splitHalfspace_uppProtocolCostLE_four (C.α k) (C.β k) hne)

/-- Total unnormalised mass used by the top-threshold mixture of constant-bias
bottom protocols. -/
noncomputable def topMixtureMass
    (C : Depth2Threshold m n)
    {τ : Fin C.s -> Type u} [∀ k, Fintype (τ k)]
    (P : ∀ k, ConstantBiasUPPProtocol (C.bottomGate k) (τ k)) : ℝ :=
  |C.θ| + ∑ k : Fin C.s, |C.w k| / (P k).δ

/-- A real UPP protocol for a `THR ∘ LTF` circuit from constant-bias protocols
for all bottom gates.  The protocol first samples either the top bias, one bottom
protocol, or a neutral filler pair.  Negative top/bottom weights are handled by
flipping the sampled Boolean output, so all rectangle weights remain
nonnegative.

This is the formal top-composition step: once each bottom LTF has a finite
constant-bias UPP protocol, the whole depth-2 threshold circuit has a protocol
with `3 + ∑ k |τ k|` transcripts, hence logarithmic cost in the number of bottom
transcripts. -/
noncomputable def wholeCircuitUPPProtocol_of_constantBiasBottom
    (C : Depth2Threshold m n)
    {τ : Fin C.s -> Type u} [∀ k, Fintype (τ k)]
    (P : ∀ k, ConstantBiasUPPProtocol (C.bottomGate k) (τ k))
    (γ : ℝ)
    (hγpos : 0 < γ)
    (hγmass : γ * topMixtureMass C P ≤ 1)
    (hne : ∀ i j, topArgument C i j ≠ 0) :
    UPPCommunicationProtocol C.eval (Sum (Fin 3) (Sigma τ)) where
  aliceProb
    | Sum.inl q => fun _ =>
        if q = (0 : Fin 3) then γ * |C.θ|
        else (1 - γ * topMixtureMass C P) / 2
    | Sum.inr kt => fun i => γ * (|C.w kt.1| / (P kt.1).δ) * (P kt.1).aliceProb kt.2 i
  bobProb
    | Sum.inl _ => fun _ => 1
    | Sum.inr kt => fun j => (P kt.1).bobProb kt.2 j
  out
    | Sum.inl q =>
        if q = (0 : Fin 3) then decide (0 < -C.θ)
        else if q = (1 : Fin 3) then true else false
    | Sum.inr kt => if 0 ≤ C.w kt.1 then (P kt.1).out kt.2 else !(P kt.1).out kt.2
  alice_nonneg := by
    intro r i
    cases r with
    | inl q =>
        by_cases hq : q = (0 : Fin 3)
        · simp [hq]
          exact mul_nonneg (le_of_lt hγpos) (abs_nonneg C.θ)
        · have hfill : 0 ≤ 1 - γ * topMixtureMass C P := by linarith
          simp [hq]
          linarith
    | inr kt =>
        have hδ : 0 ≤ (P kt.1).δ := le_of_lt (P kt.1).δ_pos
        have hdiv : 0 ≤ |C.w kt.1| / (P kt.1).δ := div_nonneg (abs_nonneg _) hδ
        exact mul_nonneg (mul_nonneg (le_of_lt hγpos) hdiv) ((P kt.1).alice_nonneg kt.2 i)
  bob_nonneg := by
    intro r j
    cases r with
    | inl q => simp
    | inr kt => exact (P kt.1).bob_nonneg kt.2 j
  prob_sum_one := by
    intro i j
    rw [Fintype.sum_sum_type]
    have hfin3 :
        (∑ q : Fin 3,
          (if q = (0 : Fin 3) then γ * |C.θ| else (1 - γ * topMixtureMass C P) / 2) * 1)
        = γ * |C.θ| + (1 - γ * topMixtureMass C P) := by
      rw [Fin.sum_univ_three]
      simp
      ring
    have hbottom :
        (∑ kt : Sigma τ,
          (γ * (|C.w kt.1| / (P kt.1).δ) * (P kt.1).aliceProb kt.2 i) *
            (P kt.1).bobProb kt.2 j)
        = γ * (∑ k : Fin C.s, |C.w k| / (P k).δ) := by
      rw [Fintype.sum_sigma]
      calc
        (∑ k : Fin C.s, ∑ t : τ k,
          (γ * (|C.w k| / (P k).δ) * (P k).aliceProb t i) * (P k).bobProb t j)
            = ∑ k : Fin C.s, γ * (|C.w k| / (P k).δ) *
                (∑ t : τ k, (P k).aliceProb t i * (P k).bobProb t j) := by
              refine Finset.sum_congr rfl (fun k _ => ?_)
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun t _ => by ring)
        _ = ∑ k : Fin C.s, γ * (|C.w k| / (P k).δ) := by
              refine Finset.sum_congr rfl (fun k _ => ?_)
              rw [(P k).prob_sum_one i j]
              ring
        _ = γ * (∑ k : Fin C.s, |C.w k| / (P k).δ) := by
              rw [Finset.mul_sum]
    rw [hfin3, hbottom]
    simp [topMixtureMass]
    ring
  bias_ok := by
    intro i j
    rw [Fintype.sum_sum_type]
    have hfin3 :
        (∑ q : Fin 3,
          (sgn (if q = (0 : Fin 3) then decide (0 < -C.θ)
            else if q = (1 : Fin 3) then true else false) *
            (if q = (0 : Fin 3) then γ * |C.θ| else (1 - γ * topMixtureMass C P) / 2)) * 1)
        = γ * (-C.θ) := by
      rw [Fin.sum_univ_three]
      change (sgn (decide (0 < -C.θ)) * (γ * |C.θ|)) * 1
          + (sgn true * ((1 - γ * topMixtureMass C P) / 2)) * 1
          + (sgn false * ((1 - γ * topMixtureMass C P) / 2)) * 1
        = γ * (-C.θ)
      rw [show sgn true = (1 : ℝ) from rfl, show sgn false = (-1 : ℝ) from rfl]
      have hbias := sgn_bias_output C.θ
      nlinarith [hbias]
    have hbottom :
        (∑ kt : Sigma τ,
          (sgn (if 0 ≤ C.w kt.1 then (P kt.1).out kt.2 else !(P kt.1).out kt.2) *
            (γ * (|C.w kt.1| / (P kt.1).δ) * (P kt.1).aliceProb kt.2 i)) *
            (P kt.1).bobProb kt.2 j)
        = γ * (∑ k : Fin C.s, C.w k * sgn (C.bottomGate k i j)) := by
      rw [Fintype.sum_sigma]
      calc
        (∑ k : Fin C.s, ∑ t : τ k,
          (sgn (if 0 ≤ C.w k then (P k).out t else !(P k).out t) *
            (γ * (|C.w k| / (P k).δ) * (P k).aliceProb t i)) *
            (P k).bobProb t j)
          = ∑ k : Fin C.s, γ * (C.w k / (P k).δ) *
              (∑ t : τ k, (sgn ((P k).out t) * (P k).aliceProb t i) * (P k).bobProb t j) := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun t _ => ?_)
            have hw := sgn_weighted_output (C.w k) ((P k).out t)
            calc
              (sgn (if 0 ≤ C.w k then (P k).out t else !(P k).out t) *
                  (γ * (|C.w k| / (P k).δ) * (P k).aliceProb t i)) *
                  (P k).bobProb t j
                  = γ * ((sgn (if 0 ≤ C.w k then (P k).out t else !(P k).out t) * |C.w k|) / (P k).δ) *
                    ((P k).aliceProb t i * (P k).bobProb t j) := by ring
              _ = γ * ((C.w k * sgn ((P k).out t)) / (P k).δ) *
                    ((P k).aliceProb t i * (P k).bobProb t j) := by rw [hw]
              _ = γ * (C.w k / (P k).δ) *
                    ((sgn ((P k).out t) * (P k).aliceProb t i) * (P k).bobProb t j) := by ring
        _ = ∑ k : Fin C.s, γ * (C.w k / (P k).δ) * ((P k).δ * sgn (C.bottomGate k i j)) := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [(P k).bias_exact i j]
        _ = γ * (∑ k : Fin C.s, C.w k * sgn (C.bottomGate k i j)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            have hδne : (P k).δ ≠ 0 := ne_of_gt (P k).δ_pos
            field_simp [hδne]
    rw [hfin3, hbottom]
    have hsum : γ * (-C.θ) + γ * (∑ k : Fin C.s, C.w k * sgn (C.bottomGate k i j))
        = γ * topArgument C i j := by
      simp [topArgument]
      ring
    rw [hsum]
    have htop_ne := hne i j
    rcases lt_or_gt_of_ne htop_ne with hlt | hgt
    · have hb : C.eval i j = false := by
        simp only [eval, decide_eq_false_iff_not, not_lt]
        exact le_of_lt hlt
      rw [hb, show sgn false = (-1 : ℝ) from rfl]
      nlinarith [hγpos]
    · have hb : C.eval i j = true := by
        simp only [eval, decide_eq_true_eq]
        exact hgt
      rw [hb, show sgn true = (1 : ℝ) from rfl]
      nlinarith [hγpos]

/-- Transcript count for the composed whole-circuit protocol. -/
theorem card_topCompositionTranscripts
    (C : Depth2Threshold m n)
    {τ : Fin C.s -> Type u} [∀ k, Fintype (τ k)] :
    Fintype.card (Sum (Fin 3) (Sigma τ)) = 3 + ∑ k, Fintype.card (τ k) := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]

/-- Cost form of the top-composed protocol.  If the composed transcript count is
bounded by `2^c`, the whole circuit has UPP cost at most `c`. -/
theorem wholeCircuit_uppProtocolCostLE_of_constantBiasBottom
    (C : Depth2Threshold m n)
    {τ : Fin C.s -> Type u} [∀ k, Fintype (τ k)]
    (P : ∀ k, ConstantBiasUPPProtocol (C.bottomGate k) (τ k))
    (γ : ℝ)
    (hγpos : 0 < γ)
    (hγmass : γ * topMixtureMass C P ≤ 1)
    (hne : ∀ i j, topArgument C i j ≠ 0)
    (c : Nat)
    (hcard : 3 + ∑ k, Fintype.card (τ k) ≤ 2 ^ c) :
    UPPProtocolCostLE.{u} C.eval c := by
  refine ⟨Sum (Fin 3) (Sigma τ), inferInstance, ?_,
    ⟨wholeCircuitUPPProtocol_of_constantBiasBottom C P γ hγpos hγmass hne⟩⟩
  rwa [card_topCompositionTranscripts C]

end Depth2Threshold

/-- Stronger bottom-gate object: the transcript expectation is exactly the
`±1` signed output matrix, not merely some same-sign matrix.  This is the
additional uniform-output ingredient needed before a top threshold can be
combined algebraically. -/
structure ExactSignedOutputRealizer (M : Fin m -> Fin n -> Bool)
    (τ : Type*) [Fintype τ] where
  alice : τ -> Fin m -> ℝ
  bob : τ -> Fin n -> ℝ
  exact : ∀ i j, (∑ t : τ, alice t i * bob t j) = sgn (M i j)

/-- A constant-bias UPP protocol is an exact signed-output realizer after
rescaling one side by `1 / δ`.

This is the formal guardrail around the top-gate composition route: constant
bias is not the cheap margin-free UPP object.  It is the exact-output endpoint,
so a cheap constant-bias bottom protocol would already be a cheap exact
realization of the bottom gate's full `±1` sign matrix. -/
noncomputable def ExactSignedOutputRealizer.ofConstantBiasUPPProtocol
    {M : Fin m -> Fin n -> Bool} {τ : Type*} [Fintype τ]
    (P : ConstantBiasUPPProtocol M τ) :
    ExactSignedOutputRealizer M τ where
  alice t i := (sgn (P.out t) / P.δ) * P.aliceProb t i
  bob := P.bobProb
  exact := by
    intro i j
    have hδne : P.δ ≠ 0 := ne_of_gt P.δ_pos
    calc
      (∑ t : τ, ((sgn (P.out t) / P.δ) * P.aliceProb t i) * P.bobProb t j)
          = (1 / P.δ) *
              (∑ t : τ, (sgn (P.out t) * P.aliceProb t i) * P.bobProb t j) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun t _ => ?_)
            ring
      _ = (1 / P.δ) * (P.δ * sgn (M i j)) := by
            rw [P.bias_exact i j]
      _ = sgn (M i j) := by
            field_simp [hδne]

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
#print axioms splitHalfspaceUPPProtocol_of_scaled
#print axioms splitHalfspace_uppProtocolCostLE_four_of_scaled
#print axioms exists_splitHalfspace_scale
#print axioms splitHalfspace_uppProtocolCostLE_four
#print axioms bottomGate_uppProtocolCostLE_four
#print axioms ConstantBiasUPPProtocol.toUPPCommunicationProtocol
#print axioms hasSignRankLE_of_constantBiasUPPProtocol
#print axioms Depth2Threshold.wholeCircuitUPPProtocol_of_constantBiasBottom
#print axioms Depth2Threshold.wholeCircuit_uppProtocolCostLE_of_constantBiasBottom
#print axioms ExactSignedOutputRealizer.ofConstantBiasUPPProtocol
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
