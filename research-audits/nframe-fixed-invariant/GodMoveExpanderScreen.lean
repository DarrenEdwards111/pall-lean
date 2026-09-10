import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinInstance

/-!
# An erasure-resistant edge screen derived from actual graph expansion

The screen records the parity combination of the constraints at a vertex set.
Expansion bounds the Hamming distance between two such screens by the size of
the symmetric difference of their labels. For k-subset labels with 4k at most
the vertex count, deleting fewer than 2c edge coordinates preserves injectivity.

The hypothesis is the existing, graph-dependent `TseitinGraph.HasExpansion c`.
No spectral certificate, label-preservation field, rank bound, or SAT hardness
assumption is supplied. This protects labels already present in a minor; it
does not manufacture computational hardness or a small boundary state space.
-/

namespace GodMoveExpanderScreen

open PallLean.Paper93.DeepMath.PathB
open Finset
open scoped BigOperators symmDiff

variable {V Edge : Type*} [Fintype V] [DecidableEq V]
  [Fintype Edge] [DecidableEq Edge]

/-- The actual number of differing edge coordinates. -/
def edgeDistance (f g : Edge → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun e => f e ≠ g e)).card

/-- Cancellation over F₂ identifies the difference of two screens exactly. -/
theorem combination_symmDiff (G : TseitinGraph V Edge) (S T : Finset V) :
    G.combination (S ∆ T) = G.combination S + G.combination T := by
  funext e
  have hsum (A : Finset V) : G.combination A e =
      ∑ v : V, if v ∈ A then G.constraint v e else 0 := by
    rw [← Finset.sum_filter]
    simp [TseitinGraph.combination]
  simp only [Pi.add_apply, hsum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hS : v ∈ S <;> by_cases hT : v ∈ T <;>
    simp [Finset.mem_symmDiff, hS, hT, ZModModule.add_self]

/-- Hamming distance is the support of the symmetric-difference combination. -/
theorem edgeDistance_eq_support_symmDiff (G : TseitinGraph V Edge) (S T : Finset V) :
    edgeDistance (G.combination S) (G.combination T) =
      (edgeSupport (G.combination (S ∆ T))).card := by
  have hneq : ∀ a b : ZMod 2, a + b ≠ 0 ↔ a ≠ b := by decide
  simp only [edgeDistance, edgeSupport, combination_symmDiff, Pi.add_apply, hneq]

/-- The quantitative separation comes from graph expansion. -/
theorem expansion_le_edgeDistance (G : TseitinGraph V Edge) {c : ℕ}
    (hexp : G.HasExpansion c) (S T : Finset V)
    (hhalf : 2 * (S ∆ T).card ≤ Fintype.card V) :
    c * (S ∆ T).card ≤ edgeDistance (G.combination S) (G.combination T) := by
  rw [edgeDistance_eq_support_symmDiff]
  by_cases hST : S = T
  · subst T
    simp
  · exact G.combination_support_card_ge_of_expansion hexp (S ∆ T)
      (Finset.card_pos.mpr (Finset.symmDiff_nonempty.mpr hST)) hhalf

omit [Fintype V] in
/-- Two different sets of equal size differ at two or more vertices. -/
theorem two_le_symmDiff_card {S T : Finset V} (hcard : S.card = T.card)
    (hne : S ≠ T) : 2 ≤ (S ∆ T).card := by
  have hST : ¬ S ⊆ T := fun h => hne (Finset.eq_of_subset_of_card_le h hcard.ge)
  have hTS : ¬ T ⊆ S := fun h => hne (Finset.eq_of_subset_of_card_le h hcard.le).symm
  obtain ⟨a, haS, haT⟩ := Finset.not_subset.mp hST
  obtain ⟨b, hbT, hbS⟩ := Finset.not_subset.mp hTS
  have hab : a ≠ b := fun h => hbS (h ▸ haS)
  have hsub : ({a, b} : Finset V) ⊆ S ∆ T := by
    intro v hv
    rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hv :
      v = a ∨ v = b) with rfl | rfl
    · exact Finset.mem_symmDiff.mpr (Or.inl ⟨haS, haT⟩)
    · exact Finset.mem_symmDiff.mpr (Or.inr ⟨hbT, hbS⟩)
  simpa only [Finset.card_pair hab] using Finset.card_le_card hsub

/-- All k-subset labels have edge distance at least 2c at this window. -/
theorem two_mul_expansion_le_edgeDistance (G : TseitinGraph V Edge) {c k : ℕ}
    (hexp : G.HasExpansion c) (hwindow : 4 * k ≤ Fintype.card V)
    (S T : Finset V) (hS : S.card = k) (hT : T.card = k) (hne : S ≠ T) :
    2 * c ≤ edgeDistance (G.combination S) (G.combination T) := by
  have hupper : (S ∆ T).card ≤ 2 * k := by
    have h := (Finset.card_le_card (Finset.symmDiff_subset_union (s := S) (t := T))).trans
      (Finset.card_union_le S T)
    omega
  have hlower := two_le_symmDiff_card (hS.trans hT.symm) hne
  have hmul := Nat.mul_le_mul_left c hlower
  have hdist := expansion_le_edgeDistance G hexp S T (by omega)
  omega

/-- Retain the real edge parities outside the erased coordinate set. -/
def screen (G : TseitinGraph V Edge) (erased : Finset Edge) (S : Finset V) :
    {e : Edge // e ∉ erased} → ZMod 2 :=
  fun e => G.combination S e.val

/-- Equal retained screens can differ only on erased coordinates. -/
theorem edgeDistance_le_erased_of_screen_eq (G : TseitinGraph V Edge)
    (erased : Finset Edge) (S T : Finset V)
    (heq : screen G erased S = screen G erased T) :
    edgeDistance (G.combination S) (G.combination T) ≤ erased.card := by
  apply Finset.card_le_card
  intro e he
  by_contra hne
  have heq' := congrFun heq ⟨e, hne⟩
  exact (Finset.mem_filter.mp he).2 heq'

/-- Erasing fewer than 2c edges preserves every k-subset label. -/
theorem screen_injective_on_card (G : TseitinGraph V Edge) {c k : ℕ}
    (hexp : G.HasExpansion c) (hwindow : 4 * k ≤ Fintype.card V)
    (erased : Finset Edge) (herased : erased.card < 2 * c) :
    Set.InjOn (screen G erased) {S : Finset V | S.card = k} := by
  intro S hS T hT heq
  by_contra hne
  have hlo := two_mul_expansion_le_edgeDistance G hexp hwindow S T hS hT hne
  have hhi := edgeDistance_le_erased_of_screen_eq G erased S T heq
  omega

/-- A nonvacuous instance: K4 tolerates three erased edges on singleton labels. -/
theorem K4_singleton_screen_injective (erased : Finset (Fin 6))
    (herased : erased.card < 4) :
    Function.Injective (fun v : Fin 4 => screen K4 erased {v}) := by
  intro v w heq
  have h := screen_injective_on_card K4 K4_hasExpansion
    (k := 1) (by decide) erased herased
    (by simp : ({v} : Finset (Fin 4)).card = 1)
    (by simp : ({w} : Finset (Fin 4)).card = 1) heq
  simpa only [Finset.singleton_inj] using h

end GodMoveExpanderScreen

#print axioms GodMoveExpanderScreen.combination_symmDiff
#print axioms GodMoveExpanderScreen.edgeDistance_eq_support_symmDiff
#print axioms GodMoveExpanderScreen.expansion_le_edgeDistance
#print axioms GodMoveExpanderScreen.two_le_symmDiff_card
#print axioms GodMoveExpanderScreen.two_mul_expansion_le_edgeDistance
#print axioms GodMoveExpanderScreen.edgeDistance_le_erased_of_screen_eq
#print axioms GodMoveExpanderScreen.screen_injective_on_card
#print axioms GodMoveExpanderScreen.K4_singleton_screen_injective
