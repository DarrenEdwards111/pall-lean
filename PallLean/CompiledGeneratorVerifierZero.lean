import PallLean.CompiledGeneratorVerifierControl

/-!
# CompiledGeneratorVerifierZero

A real verifier-side control theorem for the compiled generator frontier:
if the derivative list hits any variable outside the witness-image used by
`verifierSheetOf`, then the verifier contribution vanishes immediately.
-/

namespace CompiledGeneratorTransportFrontier

open CompiledAssemblyRoadmap
open LatentFullBridge LatentCompiler MultilinearSPDP NPWitness Compiler TuringMachine
open MvPolynomial SPDP

/-- Public generic lemma: derivative at a variable outside the rename-image kills
that renamed polynomial. Duplicated here in non-private form so the verifier-side
control step can use it directly. -/
theorem pderiv_rename_zero_public {n m : ℕ} {F : Type*} [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (v : Fin m) (hv : v ∉ Set.range f)
    (p : MvPolynomial (Fin n) F) :
    MvPolynomial.pderiv v (MvPolynomial.rename f p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.pderiv_C]
  | add p q hp hq =>
    rw [map_add, map_add (MvPolynomial.pderiv v), hp, hq, add_zero]
  | mul_X p j ih =>
    have hne : v ≠ f j := fun h => hv ⟨j, h.symm⟩
    have h1 : MvPolynomial.rename f (p * MvPolynomial.X j) =
      MvPolynomial.rename f p * MvPolynomial.X (f j) := by
      rw [map_mul, MvPolynomial.rename_X]
    rw [h1]
    have hx : MvPolynomial.pderiv v (MvPolynomial.X (f j) : MvPolynomial (Fin m) F) = 0 := by
      rw [MvPolynomial.pderiv_X]
      simp [Pi.single, Function.update, hne.symm]
    rw [MvPolynomial.pderiv_mul, hx, mul_zero, add_zero, ih, zero_mul]

/-- Public generic lemma: if any variable in the derivative list lies outside the
rename-image, the whole iterated derivative of the renamed polynomial is zero. -/
theorem iterDerivList_rename_zero_public {n m : ℕ} {F : Type*} [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (S : List (Fin m)) (hS : ∃ v ∈ S, v ∉ Set.range f)
    (p : MvPolynomial (Fin n) F) :
    iterDerivList S (MvPolynomial.rename f p) = 0 := by
  obtain ⟨v, hv_mem, hv_range⟩ := hS
  induction S generalizing p with
  | nil => simp at hv_mem
  | cons a rest ih =>
    show iterDerivList rest (MvPolynomial.pderiv a (MvPolynomial.rename f p)) = 0
    rcases List.mem_cons.mp hv_mem with rfl | hv_rest
    · rw [pderiv_rename_zero_public f hf v hv_range p]
      unfold iterDerivList
      exact LowDeg.foldl_pderiv_zero rest
    · by_cases ha : a ∈ Set.range f
      · obtain ⟨i, rfl⟩ := ha
        rw [MvPolynomial.pderiv_rename hf i p]
        exact ih (MvPolynomial.pderiv i p) hv_rest
      · rw [pderiv_rename_zero_public f hf a ha p]
        unfold iterDerivList
        exact LowDeg.foldl_pderiv_zero rest

/-- Verifier sheet is killed by any iterated derivative list that hits a variable
outside the witness-image used to build `verifierSheetOf`. -/
theorem iterDerivList_verifierSheet_zero_of_outside_witness_range
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (S : List (Fin (numVars M n (Nat.log 2 n))))
    (hS : ∃ v ∈ S, v ∉ Set.range (witnessInclusion M n h_le)) :
    iterDerivList S (verifierSheetOf ℚ M n h_le) = 0 := by
  unfold verifierSheetOf
  exact iterDerivList_rename_zero_public
    (witnessInclusion M n h_le)
    (witnessInclusion_injective M n h_le)
    S hS (tseitinPoly ℚ n)

/-- Consequently, the verifier contribution to a compiled generator vanishes
whenever the derivative list hits any variable outside the witness-image. -/
theorem compiled_generator_verifier_zero_of_outside_witness_range
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (S : List (Fin (numVars M n (Nat.log 2 n))))
    (m : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hS : ∃ v ∈ S, v ∉ Set.range (witnessInclusion M n h_le)) :
    mlProj (m * iterDerivList S (verifierSheetOf ℚ M n h_le)) = 0 := by
  rw [iterDerivList_verifierSheet_zero_of_outside_witness_range M n h_le S hS, mul_zero, mlProj_zero]

end CompiledGeneratorTransportFrontier
