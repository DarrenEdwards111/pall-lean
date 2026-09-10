import GodMoveRowSpanSeparation

/-!
# Selecting polynomial basis wires through a finite sample matrix

On a separating sample list, spanning and linear independence of numeric
wire columns lift to spanning and linear independence of the actual computed
wire polynomials. The columns use actual Boolean execution; expanded
polynomial coefficients are unnecessary for column selection.
-/

namespace GodMoveSampledWireBasis

open GodMoveBooleanInterpolation GodMoveComputedWireRank GodMoveBooleanWireTable
open GodMoveSamplingBarrier GodMoveRowSpanSeparation GodMoveSampledWireGauge
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer (CGate)
open scoped BigOperators

def wireColumn {n : ℕ} (c : List (CGate n)) (samples : List (Assignment n))
    (i : Fin c.length) : Fin samples.length → ℚ :=
  fun j => wireRow c (samples.get j) i

noncomputable def sampleMap {n : ℕ} (samples : List (Assignment n)) :
    Poly n →ₗ[ℚ] (Fin samples.length → ℚ) :=
  LinearMap.pi (fun j => sampleEval (samples.get j))

@[simp] theorem sampleMap_apply {n : ℕ} (samples : List (Assignment n))
    (p : Poly n) (j : Fin samples.length) :
    sampleMap samples p j = MvPolynomial.eval (booleanPoint (samples.get j)) p := rfl

theorem sampleMap_wirePolynomial {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (i : Fin c.length) :
    sampleMap samples (wirePolynomial c i) = wireColumn c samples i := by
  funext j
  exact (wireRow_eq_normalized_eval c (samples.get j) i).symm

theorem wirePolynomial_mem {n : ℕ} (c : List (CGate n)) (i : Fin c.length) :
    wirePolynomial c i ∈ wireSpace c := by
  rw [wireSpace_eq_span_indexed]
  exact Submodule.subset_span ⟨i, rfl⟩

noncomputable def chosenWire {n : ℕ} (c : List (CGate n))
    (indices : List (Fin c.length)) (j : Fin indices.length) : Poly n :=
  wirePolynomial c (indices.get j)

noncomputable def chosenWireSpace {n : ℕ} (c : List (CGate n))
    (indices : List (Fin c.length)) : Submodule ℚ (Poly n) :=
  Submodule.span ℚ (Set.range (chosenWire c indices))

noncomputable def chosenColumnSpace {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (indices : List (Fin c.length)) :
    Submodule ℚ (Fin samples.length → ℚ) :=
  Submodule.span ℚ (Set.range (fun j : Fin indices.length =>
    wireColumn c samples (indices.get j)))

theorem chosenWireSpace_le {n : ℕ} (c : List (CGate n))
    (indices : List (Fin c.length)) : chosenWireSpace c indices ≤ wireSpace c := by
  apply Submodule.span_le.mpr
  rintro p ⟨j, rfl⟩
  exact wirePolynomial_mem c (indices.get j)

theorem sampleMap_eq_zero_iff {n : ℕ} (samples : List (Assignment n)) (p : Poly n) :
    sampleMap samples p = 0 ↔
      ∀ a ∈ samples, MvPolynomial.eval (booleanPoint a) p = 0 := by
  constructor
  · intro h a ha
    obtain ⟨j, hj, hval⟩ := List.mem_iff_getElem.mp ha
    have he := congrFun h ⟨j, hj⟩
    simpa [sampleMap_apply, hval] using he
  · intro h
    funext j
    exact h _ (List.getElem_mem j.isLt)

/-- Numeric column spanning on separating samples determines exactly the
computed polynomial space. The separation proof is used on the difference
between each wire and the linear combination found from its column. -/
theorem chosenWireSpace_eq_of_columns {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (indices : List (Fin c.length))
    (hsep : SeparatesWires c samples)
    (hcolumns : ∀ i, wireColumn c samples i ∈ chosenColumnSpace c samples indices) :
    chosenWireSpace c indices = wireSpace c := by
  classical
  apply le_antisymm (chosenWireSpace_le c indices)
  rw [wireSpace_eq_span_indexed]
  apply Submodule.span_le.mpr
  rintro p ⟨i, rfl⟩
  obtain ⟨coeff, hcoeff⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hcolumns i)
  let q : Poly n := ∑ j : Fin indices.length, coeff j • chosenWire c indices j
  have hq : q ∈ chosenWireSpace c indices := by
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have heq : sampleMap samples q = sampleMap samples (wirePolynomial c i) := by
    simpa only [q, map_sum, map_smul, chosenWire, sampleMap_wirePolynomial] using hcoeff
  have hdiff : wirePolynomial c i - q = 0 := by
    apply hsep _ ((wireSpace c).sub_mem (wirePolynomial_mem c i)
      (chosenWireSpace_le c indices hq))
    apply (sampleMap_eq_zero_iff samples _).mp
    rw [map_sub, heq, sub_self]
  rw [sub_eq_zero.mp hdiff]
  exact hq

/-- Numeric independence lifts without any separation assumption: a
polynomial linear relation would give the same numeric column relation. -/
theorem chosenWire_linearIndependent {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (indices : List (Fin c.length))
    (hcolumns : LinearIndependent ℚ
      (fun j : Fin indices.length => wireColumn c samples (indices.get j))) :
    LinearIndependent ℚ (chosenWire c indices) := by
  rw [Fintype.linearIndependent_iff] at hcolumns ⊢
  intro coeff hcoeff
  apply hcolumns coeff
  have h := congrArg (sampleMap samples) hcoeff
  simpa only [map_sum, map_smul, map_zero, chosenWire, sampleMap_wirePolynomial] using h

theorem chosenWire_length_eq_rank {n : ℕ} (c : List (CGate n))
    (indices : List (Fin c.length))
    (hspan : chosenWireSpace c indices = wireSpace c)
    (hlin : LinearIndependent ℚ (chosenWire c indices)) :
    indices.length = wireRank c := by
  have h := finrank_span_eq_card hlin
  change Module.finrank ℚ (chosenWireSpace c indices) = _ at h
  change indices.length = Module.finrank ℚ (wireSpace c)
  calc
    _ = Module.finrank ℚ (chosenWireSpace c indices) := by
      simpa only [Fintype.card_fin] using h.symm
    _ = _ := congrArg (fun S : Submodule ℚ (Poly n) => Module.finrank ℚ S) hspan

end GodMoveSampledWireBasis

#print axioms GodMoveSampledWireBasis.sampleMap_wirePolynomial
#print axioms GodMoveSampledWireBasis.chosenWireSpace_le
#print axioms GodMoveSampledWireBasis.chosenWireSpace_eq_of_columns
#print axioms GodMoveSampledWireBasis.chosenWire_linearIndependent
#print axioms GodMoveSampledWireBasis.chosenWire_length_eq_rank
