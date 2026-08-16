import PallLean.Paper93.DeepMath.PathB.ComputationalDepth2CNFLargeMatchingSemantics

/-!
# Constructing a saturated 2-CNF matching

This file gives a deterministic greedy construction on a finite list of clause supports.  Processing the tail first,
it inserts the current support exactly when it is disjoint from all supports already selected.  The result is
pairwise disjoint and its union intersects every nonempty input support.  Applied to a finset's duplicate-free list,
it yields the saturated matching required by the matching-or-cover dichotomy.
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoCNFGreedyMatching

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.TwoCNFMatchingCover

variable {V : Type*} [DecidableEq V]

def listSupport : List (Finset V) → Finset V
  | [] => ∅
  | e :: rest => e ∪ listSupport rest

def greedyMatching : List (Finset V) → List (Finset V)
  | [] => []
  | e :: rest =>
      let selected := greedyMatching rest
      if Disjoint e (listSupport selected) then e :: selected else selected

theorem mem_listSupport {e : Finset V} {L : List (Finset V)} (he : e ∈ L) :
    e ⊆ listSupport L := by
  induction L with
  | nil => simp at he
  | cons head tail ih =>
      simp only [List.mem_cons] at he
      simp only [listSupport]
      rcases he with rfl | he
      · exact Finset.subset_union_left
      · exact (ih he).trans Finset.subset_union_right

theorem greedyMatching_sublist (L : List (Finset V)) : List.Sublist (greedyMatching L) L := by
  induction L with
  | nil => simp [greedyMatching]
  | cons e rest ih =>
      simp only [greedyMatching]
      split
      · exact ih.cons_cons e
      · exact ih.cons e

/-- Symmetric pairwise-disjointness, phrased directly by membership. -/
def ListDisjoint (L : List (Finset V)) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, a ≠ b → Disjoint a b

theorem greedyMatching_pairwise (L : List (Finset V)) : ListDisjoint (greedyMatching L) := by
  induction L with
  | nil => simp [greedyMatching, ListDisjoint]
  | cons e rest ih =>
      simp only [greedyMatching]
      split
      · rename_i hdisjoint
        intro a ha b hb hab
        simp only [List.mem_cons] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact False.elim (hab rfl)
        · exact hdisjoint.mono_right (mem_listSupport hb)
        · exact (hdisjoint.mono_right (mem_listSupport ha)).symm
        · exact ih a ha b hb hab
      · exact ih

theorem greedyMatching_hits
    (L : List (Finset V)) {e : Finset V} (he : e ∈ L) (hne : e.Nonempty) :
    ¬Disjoint e (listSupport (greedyMatching L)) := by
  induction L with
  | nil => simp at he
  | cons head tail ih =>
      simp only [List.mem_cons] at he
      simp only [greedyMatching]
      split
      · rename_i hdisjoint
        simp only [listSupport]
        rcases he with rfl | he
        · obtain ⟨v, hv⟩ := hne
          exact Finset.not_disjoint_iff.mpr ⟨v, hv, Finset.mem_union_left _ hv⟩
        · have hhit := ih he
          exact fun hd => hhit (hd.mono_right Finset.subset_union_right)
      · rename_i hnotdisjoint
        rcases he with rfl | he
        · exact hnotdisjoint
        · exact ih he

theorem listSupport_toFinset (L : List (Finset V)) :
    matchingSupport L.toFinset = listSupport L := by
  induction L with
  | nil => simp [matchingSupport, listSupport]
  | cons e rest ih =>
      simp only [List.toFinset_cons, matchingSupport, Finset.biUnion_insert, listSupport]
      rw [← matchingSupport, ih]
      rfl

/-- The finite greedy construction returns a saturated matching for nonempty clause supports. -/
theorem greedyMatching_saturated (E : Finset (Finset V))
    (hnonempty : ∀ e ∈ E, e.Nonempty) :
    SaturatedMatching E (greedyMatching E.toList).toFinset := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    have helist : e ∈ greedyMatching E.toList := by simpa using he
    have : e ∈ E.toList := (greedyMatching_sublist E.toList).subset helist
    simpa using this
  · intro a ha b hb hab
    have hal : a ∈ greedyMatching E.toList := by simpa using ha
    have hbl : b ∈ greedyMatching E.toList := by simpa using hb
    exact greedyMatching_pairwise E.toList a hal b hbl hab
  · intro e he
    rw [listSupport_toFinset]
    exact greedyMatching_hits E.toList (by simpa using he) (hnonempty e he)

end PallLean.Paper93.DeepMath.PathB.TwoCNFGreedyMatching

#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFGreedyMatching.greedyMatching_pairwise
#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFGreedyMatching.greedyMatching_saturated
