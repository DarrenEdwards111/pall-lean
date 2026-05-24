import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFiniteSearchAlgorithms

/-
# Certified easy fragments for computational-depth SAT search

This file instantiates the finite-candidate kernel with concrete certificate
classes.  It is the first executable easy-side layer after the restricted target
socket:

* bounded-variable CNF: exhaustive enumeration is finite and constant-size when
  the variable bound is fixed;
* certified low-rank incidence: the certificate supplies the compressed
  signature candidate list;
* certified bounded overlap: the certificate supplies the separator-conditioned
  candidate list.

The low-rank/overlap certificates are intentionally explicit: the real
algorithmic work in future files is to construct these candidate lists from a
rank/overlap decomposition with polynomial size bounds.  Once supplied, the
search correctness theorem is fully proved here.
-/

namespace SATDepthMachine

/-! ## Bounded-variable CNF: a concrete finite fragment -/

/-- CNF formulas over at most `k` variables.  For fixed `k`, exhaustive search
has constant-size candidate list `≤ 2^k`. -/
def BoundedVariableCNF (k : Nat) (φ : CNF) : Prop :=
  φ.vars ≤ k

/-- Exhaustive candidate generator for bounded-variable formulas. -/
def boundedVariableCandidateGenerator
    (k : Nat) : FiniteCandidateGenerator (BoundedVariableCNF k) where
  candidates := fun φ => allBoolLists φ.vars
  sound_length := by
    intro φ a h
    exact (mem_allBoolLists_iff_length).mp h
  complete := by
    intro φ _hR hsat
    rcases hsat with ⟨a, ha⟩
    exact ⟨a, (mem_allBoolLists_iff_length).mpr ha.1, ha⟩

/-- Bounded-variable formulas are semantically searchable by finite candidate
enumeration.  The polynomial-depth reading applies when `k` is fixed or grows
slowly enough for the candidate list to remain polynomial. -/
theorem boundedVariable_finiteSearch_complete
    (k : Nat) (φ : CNF)
    (hR : BoundedVariableCNF k φ) (hsat : Satisfiable φ) :
    ∃ a : RawAssignment,
      finiteCandidateSearch (boundedVariableCandidateGenerator k) φ = some a ∧
        Satisfies φ a :=
  finiteCandidateSearch_complete (boundedVariableCandidateGenerator k) φ hR hsat

/-! ## Candidate-certified low-rank incidence -/

/-- A low-rank incidence certificate strengthened with the actual compressed
candidate list produced by the rank/signature algorithm.

`rankBound` records the intended rank parameter; `complete` is the semantic
claim that the compressed signatures cover at least one satisfying assignment
whenever the formula is satisfiable. -/
structure LowRankCandidateCertificate (r : Nat) (φ : CNF) where
  candidates : List RawAssignment
  rankBound : True
  sound_length : ∀ a : RawAssignment, a ∈ candidates -> a.length = φ.vars
  complete : Satisfiable φ ->
    ∃ a : RawAssignment, a ∈ candidates ∧ Satisfies φ a

/-- CNFs with an explicit low-rank/signature candidate certificate. -/
def CertifiedLowRankIncidenceCNF (r : Nat) (φ : CNF) : Prop :=
  Nonempty (LowRankCandidateCertificate r φ)

/-- Extract the certified compressed candidate list. -/
noncomputable def certifiedLowRankCandidates
    (r : Nat) (φ : CNF) (h : CertifiedLowRankIncidenceCNF r φ) :
    List RawAssignment :=
  (Classical.choice h).candidates

/-- Total candidate-list extractor for the certified low-rank class.  Outside
the certified class it returns the empty list. -/
noncomputable def certifiedLowRankCandidateList
    (r : Nat) (φ : CNF) : List RawAssignment := by
  classical
  exact if h : CertifiedLowRankIncidenceCNF r φ then
    certifiedLowRankCandidates r φ h
  else
    []

/-- Candidate generator induced by low-rank/signature certificates. -/
noncomputable def certifiedLowRankCandidateGenerator
    (r : Nat) : FiniteCandidateGenerator (CertifiedLowRankIncidenceCNF r) where
  candidates := certifiedLowRankCandidateList r
  sound_length := by
    classical
    intro φ a ha
    unfold certifiedLowRankCandidateList at ha
    by_cases h : CertifiedLowRankIncidenceCNF r φ
    · simp [h, certifiedLowRankCandidates] at ha
      exact (Classical.choice h).sound_length a ha
    · simp [h] at ha
  complete := by
    classical
    intro φ hR hsat
    unfold certifiedLowRankCandidateList
    simp [hR, certifiedLowRankCandidates]
    exact (Classical.choice hR).complete hsat

/-- Certified low-rank incidence formulas are searchable by the compressed
signature candidate list. -/
theorem certifiedLowRankIncidence_finiteSearch_complete
    (r : Nat) (φ : CNF)
    (hR : CertifiedLowRankIncidenceCNF r φ) (hsat : Satisfiable φ) :
    ∃ a : RawAssignment,
      finiteCandidateSearch (certifiedLowRankCandidateGenerator r) φ = some a ∧
        Satisfies φ a :=
  finiteCandidateSearch_complete
    (certifiedLowRankCandidateGenerator r) φ hR hsat

/-! ## Candidate-certified bounded overlap -/

/-- A bounded-overlap certificate strengthened with the separator-conditioned
candidate list.

`separatorBound` records the intended `2^b` conditioning knob.  The real future
algorithmic theorem should construct `candidates` from a separator/overlap
decomposition and prove a polynomial size bound when `b = O(log n)`. -/
structure BoundedOverlapCandidateCertificate (b : Nat) (φ : CNF) where
  candidates : List RawAssignment
  separatorBound : True
  sound_length : ∀ a : RawAssignment, a ∈ candidates -> a.length = φ.vars
  complete : Satisfiable φ ->
    ∃ a : RawAssignment, a ∈ candidates ∧ Satisfies φ a

/-- CNFs with an explicit bounded-overlap/conditioning candidate certificate. -/
def CertifiedBoundedOverlapCNF (b : Nat) (φ : CNF) : Prop :=
  Nonempty (BoundedOverlapCandidateCertificate b φ)

noncomputable def certifiedBoundedOverlapCandidates
    (b : Nat) (φ : CNF) (h : CertifiedBoundedOverlapCNF b φ) :
    List RawAssignment :=
  (Classical.choice h).candidates

/-- Total candidate-list extractor for the certified bounded-overlap class.
Outside the certified class it returns the empty list. -/
noncomputable def certifiedBoundedOverlapCandidateList
    (b : Nat) (φ : CNF) : List RawAssignment := by
  classical
  exact if h : CertifiedBoundedOverlapCNF b φ then
    certifiedBoundedOverlapCandidates b φ h
  else
    []

/-- Candidate generator induced by bounded-overlap certificates. -/
noncomputable def certifiedBoundedOverlapCandidateGenerator
    (b : Nat) : FiniteCandidateGenerator (CertifiedBoundedOverlapCNF b) where
  candidates := certifiedBoundedOverlapCandidateList b
  sound_length := by
    classical
    intro φ a ha
    unfold certifiedBoundedOverlapCandidateList at ha
    by_cases h : CertifiedBoundedOverlapCNF b φ
    · simp [h, certifiedBoundedOverlapCandidates] at ha
      exact (Classical.choice h).sound_length a ha
    · simp [h] at ha
  complete := by
    classical
    intro φ hR hsat
    unfold certifiedBoundedOverlapCandidateList
    simp [hR, certifiedBoundedOverlapCandidates]
    exact (Classical.choice hR).complete hsat

/-- Certified bounded-overlap formulas are searchable by the
separator-conditioned candidate list. -/
theorem certifiedBoundedOverlap_finiteSearch_complete
    (b : Nat) (φ : CNF)
    (hR : CertifiedBoundedOverlapCNF b φ) (hsat : Satisfiable φ) :
    ∃ a : RawAssignment,
      finiteCandidateSearch (certifiedBoundedOverlapCandidateGenerator b) φ = some a ∧
        Satisfies φ a :=
  finiteCandidateSearch_complete
    (certifiedBoundedOverlapCandidateGenerator b) φ hR hsat

/-! ## Kernel-only axiom trace -/

#print axioms boundedVariable_finiteSearch_complete
#print axioms certifiedLowRankCandidateGenerator
#print axioms certifiedLowRankIncidence_finiteSearch_complete
#print axioms certifiedBoundedOverlapCandidateGenerator
#print axioms certifiedBoundedOverlap_finiteSearch_complete

end SATDepthMachine
