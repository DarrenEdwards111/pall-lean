import GodMoveFaithfulHandshake

/-!
# Free slack cancels in the canonical Boolean characteristic polynomial

If a Boolean predicate ignores its last input bit, its canonical interpolant
is exactly the variable-renaming of the original interpolant.  The two
assignments of the unused bit contribute complementary factors whose sum
is `X + (1-X) = 1`.  Therefore differentiating in that slack coordinate gives
zero.  The same statement applies to a signed CNF with no occurrence of the
new variable.

Repeated free padding can preserve pre-existing core structure but does not
create dependence on the unused coordinates.  Acceptance multiplicity alone
does not transfer a slack-coordinate minor from a different tableau/selector
polynomial to this canonical characteristic target.  Shifts involving the new
variables can still enlarge shifted row spaces; invariance of the full SPDP
rank is not claimed.  No general compiler impossibility or SAT separation is
claimed.
-/

namespace GodMoveCharacteristicPadding

open MvPolynomial MultilinearSPDP
open GodMoveBooleanInterpolation GodMovePinnedSATQueries GodMoveFaithfulHandshake
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.SATVerifierSpec (evalFormula_congr)
open scoped BigOperators

theorem boolMonomial_snoc {n : ℕ} (a : Assignment n) (b : Bool) :
    Step4Compiler.boolMonomial (Fin.snoc a b) =
      rename Fin.castSucc (Step4Compiler.boolMonomial a) *
        (if b then (X (Fin.last n) : GodMoveBooleanInterpolation.Poly (n + 1))
          else 1 - X (Fin.last n)) := by
  unfold Step4Compiler.boolMonomial
  rw [Fin.prod_univ_castSucc, map_prod]
  cases b <;> simp [apply_ite]

/-- Summing the two unused-bit delta factors gives one exact core factor. -/
theorem boolMonomial_snoc_pair {n : ℕ} (a : Assignment n) :
    Step4Compiler.boolMonomial (Fin.snoc a false) +
      Step4Compiler.boolMonomial (Fin.snoc a true) =
        rename Fin.castSucc (Step4Compiler.boolMonomial a) := by
  rw [boolMonomial_snoc, boolMonomial_snoc]
  simp only [Bool.false_eq_true, ↓reduceIte]
  ring

/-- Exact polynomial cancellation, obtained from the full interpolation sum. -/
theorem interpolate_ignore_last {n : ℕ} (f : Assignment n → Bool) :
    interpolate (fun a : Assignment (n + 1) => f (fun i => a i.castSucc)) =
      rename Fin.castSucc (interpolate f) := by
  classical
  unfold interpolate Step4Compiler.chi_phi
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp]
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Fin.snocEquiv_apply, Fin.snoc_castSucc]
  by_cases ha : f a = true
  · simp only [ha, ↓reduceIte]
    simpa only [add_comm] using boolMonomial_snoc_pair a
  · simp [ha]

/-- The unused coordinate has zero derivative after canonical interpolation. -/
theorem pderiv_interpolate_ignore_last {n : ℕ} (f : Assignment n → Bool) :
    pderiv (Fin.last n)
      (interpolate (fun a : Assignment (n + 1) => f (fun i => a i.castSucc))) = 0 := by
  rw [interpolate_ignore_last]
  apply pderiv_rename_zero Fin.castSucc (Fin.castSucc_injective n)
  rintro ⟨i, hi⟩
  exact Fin.castSucc_ne_last i hi

/-- A bounded signed formula evaluates independently of the new last bit. -/
theorem evalFormula_ignore_last {n : ℕ} (φ : Formula)
    (hvars : VariablesBelow n φ) (a : Assignment (n + 1)) :
    evalFormula (extendAssignment a) φ =
      evalFormula (extendAssignment (fun i : Fin n => a i.castSucc)) φ := by
  apply evalFormula_congr
  intro c hc l hl
  have hi := hvars c hc l hl
  simp [extendAssignment, hi, Nat.lt_succ_of_lt hi]

/-- Adding one genuinely free variable only renames the old characteristic. -/
theorem verifierCharacteristic_succ_eq_rename {n : ℕ} (φ : Formula)
    (hvars : VariablesBelow n φ) :
    verifierCharacteristic (n + 1) φ =
      rename Fin.castSucc (verifierCharacteristic n φ) := by
  unfold verifierCharacteristic
  calc
    interpolate (fun a : Assignment (n + 1) => evalFormula (extendAssignment a) φ) =
        interpolate (fun a : Assignment (n + 1) =>
          evalFormula (extendAssignment (fun i : Fin n => a i.castSucc)) φ) :=
      interpolate_congr (evalFormula_ignore_last φ hvars)
    _ = _ := interpolate_ignore_last (fun a : Assignment n =>
      evalFormula (extendAssignment a) φ)

/-- Free witness padding contributes no derivative in its own coordinate. -/
theorem pderiv_verifierCharacteristic_last_eq_zero {n : ℕ} (φ : Formula)
    (hvars : VariablesBelow n φ) :
    pderiv (Fin.last n) (verifierCharacteristic (n + 1) φ) = 0 := by
  rw [verifierCharacteristic_succ_eq_rename φ hvars]
  apply pderiv_rename_zero Fin.castSucc (Fin.castSucc_injective n)
  rintro ⟨i, hi⟩
  exact Fin.castSucc_ne_last i hi

end GodMoveCharacteristicPadding

#print axioms GodMoveCharacteristicPadding.boolMonomial_snoc
#print axioms GodMoveCharacteristicPadding.boolMonomial_snoc_pair
#print axioms GodMoveCharacteristicPadding.interpolate_ignore_last
#print axioms GodMoveCharacteristicPadding.pderiv_interpolate_ignore_last
#print axioms GodMoveCharacteristicPadding.evalFormula_ignore_last
#print axioms GodMoveCharacteristicPadding.verifierCharacteristic_succ_eq_rename
#print axioms GodMoveCharacteristicPadding.pderiv_verifierCharacteristic_last_eq_zero
