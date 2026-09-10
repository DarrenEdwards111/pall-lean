import GodMoveComputedWireRank
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATFamilyDenseFloor

/-!
# A genuine linear SAT lower bound for the computed-wire rank

Every input coordinate on which a circuit's output depends forces an actual
variable-read gate. That gate emits `X_i`, and normalization fixes it. Distinct
coordinate polynomials are linearly independent, so the same computed-wire
rank bounded above by the simulator's clock is bounded below by the number
of essential inputs.

The repository's existing faithful SAT decoder witnesses show that every bit
position from 22 onward is essential to the exact length-indexed `SATFamily`.
Consequently EVERY circuit computing `SATFamily N` has wire rank at least
`N - 22`. No derivative-span containment or rank-transport premise is used.

This is only a linear lower bound. Essential-input counting has a ceiling of
`N`, so this argument supplies no superpolynomial obstruction. The generic
statement concerns every SAT circuit representation. For the particular
unrolled machine simulator, all inputs are initialized regardless of the
language, so its input-loading rank alone is already linear; the machine
corollary must not be read as additional hardness of that chosen simulation.
-/

namespace GodMoveComputedWireLowerBound

open MvPolynomial MultilinearSPDP
open GodMoveBooleanInterpolation GodMoveCircuitNormalization
open GodMoveComputedWireRank GodMoveCircuitConnection
open GodMoveCircuitArithmetization (AExpr runArithmetic arithGate)
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer SATFamilyCircuitFloor SATCircuitSeparationBridge
open ComposableMachine ComposablePpolyDischarge

/-- Appending arithmetic gates never removes an already-computed wire value. -/
theorem mem_runArithmetic_of_mem {n : ℕ} (x : Fin n → Poly n)
    (gs : List (AExpr n)) (vals : List (Poly n)) (p : Poly n) (hp : p ∈ vals) :
    p ∈ runArithmetic x vals gs := by
  induction gs generalizing vals with
  | nil => exact hp
  | cons g gs ih =>
      exact ih (vals ++ [g.eval x vals]) (List.mem_append_left _ hp)

/-- A source variable gate emits its coordinate polynomial into the actual wire list. -/
theorem X_mem_rawWires_of_var_mem {n : ℕ} (c : List (CGate n)) (i : Fin n)
    (hi : CGate.var i ∈ c) : (X i : Poly n) ∈ rawWires c := by
  obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp hi
  simp only [rawWires, GodMoveCircuitArithmetization.compile, List.map_append,
    List.map_cons, runArithmetic_append, runArithmetic]
  apply mem_runArithmetic_of_mem
  simp [arithGate, AExpr.eval]

theorem normalize_X {n : ℕ} (i : Fin n) : normalize (X i : Poly n) = X i := by
  apply GodMoveBooleanDifferentiation.normalize_of_isMultilinear
  intro α hα j
  have hαeq : α = Finsupp.single i 1 := by
    simpa only [Finset.mem_singleton] using support_monomial_subset hα
  rw [hαeq]
  by_cases hji : j = i <;> simp [hji]

/-- Normalization leaves the forced variable wire unchanged. -/
theorem X_mem_wireSpace_of_var_mem {n : ℕ} (c : List (CGate n)) (i : Fin n)
    (hi : CGate.var i ∈ c) : (X i : Poly n) ∈ wireSpace c := by
  classical
  apply Submodule.subset_span
  change X i ∈ (normalizedWires c).toFinset
  rw [List.mem_toFinset]
  exact List.mem_map.mpr ⟨X i, X_mem_rawWires_of_var_mem c i hi, normalize_X i⟩

theorem coordinatePolynomials_linearIndependent (n : ℕ) :
    LinearIndependent ℚ (fun i : Fin n => (X i : Poly n)) := by
  have hinj : Function.Injective (fun i : Fin n => Finsupp.single i (1 : ℕ)) := by
    intro i j hij
    have h := congrArg (fun α : Fin n →₀ ℕ => α i) hij
    by_contra hne
    simp [Finsupp.single_eq_of_ne hne] at h
  simpa [MvPolynomial.X] using
    (Finsupp.linearIndependent_single_one ℚ (Fin n →₀ ℕ)).comp
      (fun i : Fin n => Finsupp.single i 1) hinj

/-- All distinct coordinates read by a circuit contribute independent wire directions. -/
theorem varsOf_card_le_wireRank {n : ℕ} (c : List (CGate n)) :
    (varsOf c).card ≤ wireRank c := by
  let rows : ↥(varsOf c) → wireSpace c :=
    fun i => ⟨X i.val, X_mem_wireSpace_of_var_mem c i.val (mem_varsOf.mp i.property)⟩
  have hli : LinearIndependent ℚ rows := by
    apply LinearIndependent.of_comp (wireSpace c).subtype
    exact (coordinatePolynomials_linearIndependent n).comp
      (fun i : ↥(varsOf c) => i.val) Subtype.val_injective
  simpa only [Fintype.card_coe, wireRank] using hli.fintype_card_le_finrank

/-- Semantics alone forces every essential coordinate to be read by the circuit. -/
theorem depSet_subset_varsOf {n : ℕ} (c : List (CGate n))
    (f : Assignment n → Bool) (hcomp : computes c f) : depSet f ⊆ varsOf c := by
  intro i hi
  obtain ⟨x, b, hxb⟩ := mem_depSet.mp hi
  by_contra hnv
  have hvar : CGate.var i ∉ c := fun h => hnv (mem_varsOf.mpr h)
  have hout : output c (Function.update x i b) = output c x := by
    unfold output
    rw [runFrom_update i b x c [] hvar]
  exact hxb (by rw [← hcomp, ← hcomp, hout])

/-- A lower bound on the same actual wire rank, with no assumed algebraic extraction. -/
theorem depSet_card_le_wireRank {n : ℕ} (c : List (CGate n))
    (f : Assignment n → Bool) (hcomp : computes c f) :
    (depSet f).card ≤ wireRank c :=
  (Finset.card_le_card (depSet_subset_varsOf c f hcomp)).trans (varsOf_card_le_wireRank c)

/-- Every circuit computing the exact encoded SAT decision slice has this lower bound. -/
theorem satFamily_wireRank_lower (N : ℕ) (c : List (CGate N))
    (hcomp : computes c (SATFamily N)) : N - 22 ≤ wireRank c :=
  (SATFamilyDenseFloor.depSet_card_ge_dense N).trans
    (depSet_card_le_wireRank c (SATFamily N) hcomp)

/-- An actual globally correct SAT machine inherits the same unconditional linear floor. -/
theorem actualSAT_wireRank_lower (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SeparationTarget.SATLang T) (N : ℕ) :
    N - 22 ≤ wireRank (circuitFor M N (T N)) :=
  satFamily_wireRank_lower N _
    (circuitFor_computes M SeparationTarget.SATLang T hD N)

/-- The dependency argument itself has a linear ceiling, independently of SAT. -/
theorem dependency_count_le_input_count {n : ℕ} (f : Assignment n → Bool) :
    (depSet f).card ≤ n := by
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card (Finset.subset_univ (depSet f))

end GodMoveComputedWireLowerBound

#print axioms GodMoveComputedWireLowerBound.X_mem_rawWires_of_var_mem
#print axioms GodMoveComputedWireLowerBound.X_mem_wireSpace_of_var_mem
#print axioms GodMoveComputedWireLowerBound.coordinatePolynomials_linearIndependent
#print axioms GodMoveComputedWireLowerBound.varsOf_card_le_wireRank
#print axioms GodMoveComputedWireLowerBound.depSet_card_le_wireRank
#print axioms GodMoveComputedWireLowerBound.satFamily_wireRank_lower
#print axioms GodMoveComputedWireLowerBound.actualSAT_wireRank_lower
#print axioms GodMoveComputedWireLowerBound.dependency_count_le_input_count
