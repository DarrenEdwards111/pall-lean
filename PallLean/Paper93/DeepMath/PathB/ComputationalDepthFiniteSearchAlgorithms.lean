import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRestrictedTargets

/-
# Finite search algorithms for restricted computational-depth targets

This file proves the first genuinely executable smaller-target lemma: finite
candidate enumeration.  It is intentionally modest but useful.

* `allBoolLists n` enumerates every raw assignment of length `n`.
* `firstSatisfying` searches a finite candidate list.
* if a restricted class supplies polynomially-many/structured candidates that
  are complete for satisfiable formulas, then the semantic search problem is
  shallow for that fragment.

This is the common kernel behind the easy-side attacks:

* bounded treewidth: candidates are produced by DP over a tree decomposition;
* low-rank incidence: candidates are produced by compressed signatures;
* bounded overlap: candidates are produced by conditioning on separators.

The file does not claim those concrete candidate generators yet.  It proves the
finite-search core they must instantiate.
-/

namespace SATDepthMachine

/-! ## Exhaustive assignment enumeration -/

/-- All Boolean lists of length `n`. -/
def allBoolLists : Nat -> List RawAssignment
  | 0 => [[]]
  | n + 1 =>
      (allBoolLists n).map (fun a => false :: a) ++
        (allBoolLists n).map (fun a => true :: a)

/-- Every list in `allBoolLists n` has length `n`. -/
theorem length_of_mem_allBoolLists :
    ∀ {n : Nat} {a : RawAssignment}, a ∈ allBoolLists n -> a.length = n
  | 0, a, h => by
      simp [allBoolLists] at h
      exact h ▸ rfl
  | n + 1, a, h => by
      simp [allBoolLists] at h
      rcases h with h | h
      · rcases h with ⟨tail, htail, rfl⟩
        simp [length_of_mem_allBoolLists htail]
      · rcases h with ⟨tail, htail, rfl⟩
        simp [length_of_mem_allBoolLists htail]

/-- Every Boolean list of length `n` occurs in `allBoolLists n`. -/
theorem mem_allBoolLists_of_length :
    ∀ {n : Nat} {a : RawAssignment}, a.length = n -> a ∈ allBoolLists n
  | 0, a, hlen => by
      cases a with
      | nil => simp [allBoolLists]
      | cons b rest => simp at hlen
  | n + 1, a, hlen => by
      cases a with
      | nil => simp at hlen
      | cons b rest =>
          have hrest : rest.length = n := by
            simp at hlen
            exact hlen
          have hmem : rest ∈ allBoolLists n :=
            mem_allBoolLists_of_length hrest
          cases b <;> simp [allBoolLists, hmem]

/-- Exact membership characterization for the exhaustive assignment list. -/
theorem mem_allBoolLists_iff_length
    {n : Nat} {a : RawAssignment} :
    a ∈ allBoolLists n ↔ a.length = n :=
  ⟨length_of_mem_allBoolLists, mem_allBoolLists_of_length⟩

/-! ## Finite candidate search -/

/-- Return the first satisfying assignment in a finite candidate list, if any. -/
def firstSatisfying (φ : CNF) : List RawAssignment -> Option RawAssignment
  | [] => none
  | a :: rest =>
      if Satisfies φ a then some a else firstSatisfying φ rest

/-- If `firstSatisfying` returns an assignment, it is satisfying. -/
theorem firstSatisfying_sound
    (φ : CNF) :
    ∀ {xs : List RawAssignment} {a : RawAssignment},
      firstSatisfying φ xs = some a -> Satisfies φ a
  | [], a, h => by
      simp [firstSatisfying] at h
  | x :: xs, a, h => by
      unfold firstSatisfying at h
      by_cases hx : Satisfies φ x
      · simp [hx] at h
        exact h ▸ hx
      · simp [hx] at h
        exact firstSatisfying_sound φ h

/-- If a satisfying candidate occurs in the list, finite search finds one. -/
theorem firstSatisfying_complete
    (φ : CNF) :
    ∀ {xs : List RawAssignment},
      (∃ a : RawAssignment, a ∈ xs ∧ Satisfies φ a) ->
        ∃ a : RawAssignment,
          firstSatisfying φ xs = some a ∧ Satisfies φ a
  | [], h => by
      rcases h with ⟨a, ha, _⟩
      simp at ha
  | x :: xs, h => by
      rcases h with ⟨a, ha, hsat⟩
      unfold firstSatisfying
      by_cases hx : Satisfies φ x
      · exact ⟨x, by simp [hx], hx⟩
      · simp [hx]
        have htail : ∃ a : RawAssignment, a ∈ xs ∧ Satisfies φ a := by
          simp at ha
          cases ha with
          | inl hax => exact (hx (hax ▸ hsat)).elim
          | inr hain => exact ⟨a, hain, hsat⟩
        exact firstSatisfying_complete φ htail

/-- Exhaustive search over all assignments of the right length. -/
def exhaustiveSATSearch (φ : CNF) : Option RawAssignment :=
  firstSatisfying φ (allBoolLists φ.vars)

/-- Exhaustive search is correct for every satisfiable CNF.  This is not a
polynomial-depth theorem; it is the finite semantic core used by restricted
candidate generators. -/
theorem exhaustiveSATSearch_complete
    (φ : CNF) (hsat : Satisfiable φ) :
    ∃ a : RawAssignment,
      exhaustiveSATSearch φ = some a ∧ Satisfies φ a := by
  rcases hsat with ⟨a, ha⟩
  unfold exhaustiveSATSearch
  exact firstSatisfying_complete φ
    ⟨a, (mem_allBoolLists_iff_length).mpr ha.1, ha⟩

/-- Any output of exhaustive search is sound. -/
theorem exhaustiveSATSearch_sound
    (φ : CNF) {a : RawAssignment}
    (h : exhaustiveSATSearch φ = some a) :
    Satisfies φ a := by
  unfold exhaustiveSATSearch at h
  exact firstSatisfying_sound φ h

/-! ## Candidate-generator interface for easy fragments -/

/-- A semantic finite-candidate generator for a restricted class `R`.

For bounded treewidth this list is produced by DP; for low-rank incidence by
signature enumeration; for bounded overlap by separator conditioning. -/
structure FiniteCandidateGenerator (R : CNF -> Prop) where
  candidates : CNF -> List RawAssignment
  sound_length : ∀ φ : CNF, ∀ a : RawAssignment,
    a ∈ candidates φ -> a.length = φ.vars
  complete : ∀ φ : CNF, R φ -> Satisfiable φ ->
    ∃ a : RawAssignment, a ∈ candidates φ ∧ Satisfies φ a

/-- Search induced by a finite-candidate generator. -/
def finiteCandidateSearch
    {R : CNF -> Prop} (G : FiniteCandidateGenerator R) (φ : CNF) :
    Option RawAssignment :=
  firstSatisfying φ (G.candidates φ)

/-- Finite-candidate search is complete on its restricted class. -/
theorem finiteCandidateSearch_complete
    {R : CNF -> Prop} (G : FiniteCandidateGenerator R)
    (φ : CNF) (hR : R φ) (hsat : Satisfiable φ) :
    ∃ a : RawAssignment,
      finiteCandidateSearch G φ = some a ∧ Satisfies φ a := by
  unfold finiteCandidateSearch
  exact firstSatisfying_complete φ (G.complete φ hR hsat)

/-- Finite-candidate search is sound. -/
theorem finiteCandidateSearch_sound
    {R : CNF -> Prop} (G : FiniteCandidateGenerator R)
    (φ : CNF) {a : RawAssignment}
    (h : finiteCandidateSearch G φ = some a) :
    Satisfies φ a := by
  unfold finiteCandidateSearch at h
  exact firstSatisfying_sound φ h

/-- Exhaustive search is the universal finite-candidate generator.  It is useful
as a semantic baseline; polynomial shallowness for a fragment requires replacing
this by a small/structured candidate list. -/
def exhaustiveCandidateGenerator : FiniteCandidateGenerator (fun _φ : CNF => True) where
  candidates := fun φ => allBoolLists φ.vars
  sound_length := by
    intro φ a h
    exact (mem_allBoolLists_iff_length).mp h
  complete := by
    intro φ _hR hsat
    rcases hsat with ⟨a, ha⟩
    exact ⟨a, (mem_allBoolLists_iff_length).mpr ha.1, ha⟩

/-! ## Named fragment algorithm sockets -/

/-- Bounded-treewidth shallowness reduces to providing a DP candidate generator. -/
theorem boundedTreewidth_finiteSearch_complete
    (w : Nat) (G : FiniteCandidateGenerator (BoundedTreewidthCNF w))
    (φ : CNF) (hR : BoundedTreewidthCNF w φ) (hsat : Satisfiable φ) :
    ∃ a : RawAssignment,
      finiteCandidateSearch G φ = some a ∧ Satisfies φ a :=
  finiteCandidateSearch_complete G φ hR hsat

/-- Low-rank-incidence shallowness reduces to providing a compressed-signature
candidate generator. -/
theorem lowRankIncidence_finiteSearch_complete
    (r : Nat) (G : FiniteCandidateGenerator (LowRankIncidenceCNF r))
    (φ : CNF) (hR : LowRankIncidenceCNF r φ) (hsat : Satisfiable φ) :
    ∃ a : RawAssignment,
      finiteCandidateSearch G φ = some a ∧ Satisfies φ a :=
  finiteCandidateSearch_complete G φ hR hsat

/-- Bounded-overlap shallowness reduces to providing a separator-conditioning
candidate generator. -/
theorem boundedOverlap_finiteSearch_complete
    (b : Nat) (G : FiniteCandidateGenerator (BoundedOverlapCNF b))
    (φ : CNF) (hR : BoundedOverlapCNF b φ) (hsat : Satisfiable φ) :
    ∃ a : RawAssignment,
      finiteCandidateSearch G φ = some a ∧ Satisfies φ a :=
  finiteCandidateSearch_complete G φ hR hsat

/-! ## Kernel-only axiom trace -/

#print axioms mem_allBoolLists_iff_length
#print axioms firstSatisfying_sound
#print axioms firstSatisfying_complete
#print axioms exhaustiveSATSearch_complete
#print axioms finiteCandidateSearch_complete
#print axioms boundedTreewidth_finiteSearch_complete
#print axioms lowRankIncidence_finiteSearch_complete
#print axioms boundedOverlap_finiteSearch_complete

end SATDepthMachine
