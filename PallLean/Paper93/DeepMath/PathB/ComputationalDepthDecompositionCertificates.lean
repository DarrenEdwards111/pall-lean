import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCertifiedFragments

/-
# Constructing candidate certificates from decompositions

`ComputationalDepthCertifiedFragments.lean` allowed certified easy fragments to
carry candidate lists directly.  This file pushes one layer lower: build those
candidate certificates from actual structural data.

What is fully constructed here:

* bounded-variable CNF: the variable bound itself gives the exhaustive candidate
  certificate, with an exact `2^vars` size theorem for the candidate list.

What is honestly exposed as the next algorithmic obligation:

* low-rank incidence: a rank/signature decomposition must provide a signature
  candidate enumerator and prove it covers satisfiable formulas;
* bounded overlap: a separator/overlap decomposition must provide a
  separator-conditioned candidate enumerator and prove it covers satisfiable
  formulas.

The bridge from those decompositions to the earlier certified fragments is
proved here.  The hard future work is constructing the decompositions with
polynomial-size candidate lists for interesting classes.
-/

namespace SATDepthMachine

/-! ## Exact size of exhaustive candidate lists -/

/-- `allBoolLists n` has exactly `2^n` candidates. -/
theorem length_allBoolLists : ∀ n : Nat, (allBoolLists n).length = 2 ^ n
  | 0 => by simp [allBoolLists]
  | n + 1 => by
      simp [allBoolLists, length_allBoolLists n, Nat.pow_succ]
      omega

/-- Bounded-variable exhaustive candidates have size bounded by `2^k`. -/
theorem length_boundedVariable_candidates_le
    (k : Nat) (φ : CNF) (h : BoundedVariableCNF k φ) :
    ((boundedVariableCandidateGenerator k).candidates φ).length ≤ 2 ^ k := by
  simp [boundedVariableCandidateGenerator, length_allBoolLists]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) h

/-- The bounded-variable assumption constructs the earlier explicit low-level
candidate certificate. -/
def boundedVariableCandidateCertificate
    (k : Nat) (φ : CNF) (h : BoundedVariableCNF k φ) :
    LowRankCandidateCertificate k φ where
  candidates := (boundedVariableCandidateGenerator k).candidates φ
  rankBound := trivial
  sound_length := by
    intro a ha
    exact (boundedVariableCandidateGenerator k).sound_length φ a ha
  complete := by
    intro hsat
    exact (boundedVariableCandidateGenerator k).complete φ h hsat

/-- Therefore bounded-variable CNFs are also certified low-rank-style easy
instances, with the rank parameter used only as a size/complexity placeholder. -/
theorem certifiedLowRank_of_boundedVariable
    (k : Nat) (φ : CNF) (h : BoundedVariableCNF k φ) :
    CertifiedLowRankIncidenceCNF k φ :=
  ⟨boundedVariableCandidateCertificate k φ h⟩

/-- Bounded-variable CNFs also instantiate the bounded-overlap certificate
interface. -/
def boundedVariableOverlapCandidateCertificate
    (k : Nat) (φ : CNF) (h : BoundedVariableCNF k φ) :
    BoundedOverlapCandidateCertificate k φ where
  candidates := (boundedVariableCandidateGenerator k).candidates φ
  separatorBound := trivial
  sound_length := by
    intro a ha
    exact (boundedVariableCandidateGenerator k).sound_length φ a ha
  complete := by
    intro hsat
    exact (boundedVariableCandidateGenerator k).complete φ h hsat

/-- Therefore bounded-variable CNFs are certified bounded-overlap easy
instances as well. -/
theorem certifiedBoundedOverlap_of_boundedVariable
    (k : Nat) (φ : CNF) (h : BoundedVariableCNF k φ) :
    CertifiedBoundedOverlapCNF k φ :=
  ⟨boundedVariableOverlapCandidateCertificate k φ h⟩

/-! ## State/fiber candidate enumeration -/

/-- Flatten the candidate fibers attached to finitely many structural states. -/
def flattenStateCandidates {σ : Type} :
    List σ -> (σ -> List RawAssignment) -> List RawAssignment
  | [], _ => []
  | s :: rest, candidatesOf =>
      candidatesOf s ++ flattenStateCandidates rest candidatesOf

/-- If a state is enumerated and a candidate lies in that state's fiber, then it
lies in the flattened candidate list. -/
theorem mem_flattenStateCandidates_of_mem
    {σ : Type} {states : List σ} {candidatesOf : σ -> List RawAssignment}
    {s : σ} {a : RawAssignment}
    (hs : s ∈ states) (ha : a ∈ candidatesOf s) :
    a ∈ flattenStateCandidates states candidatesOf := by
  induction states with
  | nil => simp at hs
  | cons t rest ih =>
      simp [flattenStateCandidates] at hs ⊢
      cases hs with
      | inl h =>
          left
          subst h
          exact ha
      | inr h =>
          right
          exact ih h

/-- Sound candidate lengths lift from every fiber to the flattened list. -/
theorem sound_length_of_mem_flattenStateCandidates
    {σ : Type} {φ : CNF} {states : List σ}
    {candidatesOf : σ -> List RawAssignment}
    (hsound : ∀ (s : σ) (a : RawAssignment),
      a ∈ candidatesOf s -> a.length = φ.vars)
    {a : RawAssignment}
    (ha : a ∈ flattenStateCandidates states candidatesOf) :
    a.length = φ.vars := by
  induction states with
  | nil => simp [flattenStateCandidates] at ha
  | cons s rest ih =>
      simp [flattenStateCandidates] at ha
      cases ha with
      | inl h => exact hsound s a h
      | inr h => exact ih h

/-! ## Low-rank decomposition -> candidate certificate -/

/-- Structural low-rank/signature decomposition.

A future concrete theorem should build this from the signed incidence matrix:
low rank gives a small set of reachable signatures, and each signature yields a
candidate assignment or a finite candidate fiber. -/
structure LowRankSignatureDecomposition (r : Nat) (φ : CNF) where
  signatures : Type
  finiteSignatures : List signatures
  /-- Candidate fiber for each reachable low-rank signature. -/
  candidatesOf : signatures -> List RawAssignment
  rankBound : True
  sound_length : ∀ (s : signatures) (a : RawAssignment),
    a ∈ candidatesOf s -> a.length = φ.vars
  complete : Satisfiable φ ->
    ∃ (s : signatures) (a : RawAssignment),
      s ∈ finiteSignatures ∧
      a ∈ candidatesOf s ∧
      Satisfies φ a

/-- Candidate list induced by a low-rank signature decomposition. -/
def LowRankSignatureDecomposition.candidates
    {r : Nat} {φ : CNF}
    (D : LowRankSignatureDecomposition r φ) : List RawAssignment :=
  flattenStateCandidates D.finiteSignatures D.candidatesOf

/-- A low-rank signature decomposition constructs the candidate certificate used
by the finite-search layer. -/
def lowRankCandidateCertificate_of_decomposition
    {r : Nat} {φ : CNF}
    (D : LowRankSignatureDecomposition r φ) :
    LowRankCandidateCertificate r φ where
  candidates := D.candidates
  rankBound := D.rankBound
  sound_length := by
    intro a ha
    exact sound_length_of_mem_flattenStateCandidates D.sound_length ha
  complete := by
    intro hsat
    rcases D.complete hsat with ⟨s, a, hs, ha, hsatA⟩
    exact ⟨a, mem_flattenStateCandidates_of_mem hs ha, hsatA⟩

/-- Low-rank signature decompositions instantiate certified low-rank incidence. -/
theorem certifiedLowRankIncidence_of_decomposition
    {r : Nat} {φ : CNF}
    (D : LowRankSignatureDecomposition r φ) :
    CertifiedLowRankIncidenceCNF r φ :=
  ⟨lowRankCandidateCertificate_of_decomposition D⟩

/-! ## Bounded-overlap decomposition -> candidate certificate -/

/-- Structural bounded-overlap/separator decomposition.

The intended algorithmic meaning is: enumerate separator assignments, solve the
independent components/fibers, and collect candidate full assignments. -/
structure BoundedOverlapDecomposition (b : Nat) (φ : CNF) where
  separatorStates : Type
  finiteSeparatorStates : List separatorStates
  /-- Candidate fiber produced after conditioning on a separator state. -/
  candidatesOf : separatorStates -> List RawAssignment
  separatorBound : True
  sound_length : ∀ (s : separatorStates) (a : RawAssignment),
    a ∈ candidatesOf s -> a.length = φ.vars
  complete : Satisfiable φ ->
    ∃ (s : separatorStates) (a : RawAssignment),
      s ∈ finiteSeparatorStates ∧
      a ∈ candidatesOf s ∧
      Satisfies φ a

/-- Candidate list induced by a bounded-overlap decomposition. -/
def BoundedOverlapDecomposition.candidates
    {b : Nat} {φ : CNF}
    (D : BoundedOverlapDecomposition b φ) : List RawAssignment :=
  flattenStateCandidates D.finiteSeparatorStates D.candidatesOf

/-- A bounded-overlap decomposition constructs the candidate certificate used by
the finite-search layer. -/
def boundedOverlapCandidateCertificate_of_decomposition
    {b : Nat} {φ : CNF}
    (D : BoundedOverlapDecomposition b φ) :
    BoundedOverlapCandidateCertificate b φ where
  candidates := D.candidates
  separatorBound := D.separatorBound
  sound_length := by
    intro a ha
    exact sound_length_of_mem_flattenStateCandidates D.sound_length ha
  complete := by
    intro hsat
    rcases D.complete hsat with ⟨s, a, hs, ha, hsatA⟩
    exact ⟨a, mem_flattenStateCandidates_of_mem hs ha, hsatA⟩

/-- Bounded-overlap decompositions instantiate certified bounded-overlap CNF. -/
theorem certifiedBoundedOverlap_of_decomposition
    {b : Nat} {φ : CNF}
    (D : BoundedOverlapDecomposition b φ) :
    CertifiedBoundedOverlapCNF b φ :=
  ⟨boundedOverlapCandidateCertificate_of_decomposition D⟩

/-! ## Search consequences -/

/-- A low-rank signature decomposition is enough to run finite search. -/
theorem lowRankDecomposition_finiteSearch_complete
    {r : Nat} {φ : CNF}
    (D : LowRankSignatureDecomposition r φ)
    (hsat : Satisfiable φ) :
    ∃ a : RawAssignment,
      finiteCandidateSearch
        (certifiedLowRankCandidateGenerator r) φ = some a ∧
        Satisfies φ a :=
  certifiedLowRankIncidence_finiteSearch_complete r φ
    (certifiedLowRankIncidence_of_decomposition D) hsat

/-- A bounded-overlap decomposition is enough to run finite search. -/
theorem boundedOverlapDecomposition_finiteSearch_complete
    {b : Nat} {φ : CNF}
    (D : BoundedOverlapDecomposition b φ)
    (hsat : Satisfiable φ) :
    ∃ a : RawAssignment,
      finiteCandidateSearch
        (certifiedBoundedOverlapCandidateGenerator b) φ = some a ∧
        Satisfies φ a :=
  certifiedBoundedOverlap_finiteSearch_complete b φ
    (certifiedBoundedOverlap_of_decomposition D) hsat

/-! ## Kernel-only axiom trace -/

#print axioms length_allBoolLists
#print axioms length_boundedVariable_candidates_le
#print axioms certifiedLowRank_of_boundedVariable
#print axioms certifiedBoundedOverlap_of_boundedVariable
#print axioms lowRankCandidateCertificate_of_decomposition
#print axioms certifiedLowRankIncidence_of_decomposition
#print axioms boundedOverlapCandidateCertificate_of_decomposition
#print axioms certifiedBoundedOverlap_of_decomposition
#print axioms lowRankDecomposition_finiteSearch_complete
#print axioms boundedOverlapDecomposition_finiteSearch_complete

end SATDepthMachine
