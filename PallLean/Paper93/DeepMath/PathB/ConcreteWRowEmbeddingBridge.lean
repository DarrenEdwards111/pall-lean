import PallLean.Paper93.Direct.PerTypeComposition
import PallLean.Paper93.Spanning.PerDerivativeSpanning

/-!
# ConcreteW row-embedding bridge

This file isolates the exact remaining local closure frontier needed to inhabit
`Direct.CookLevinPerTypeRowEmbeddings_concreteW` for the real Cook-Levin factor
list at Agent J1's concrete `concreteW` family.

No new algebraic shortcut is introduced: the main theorem is the existing H5
composition theorem specialised to
`W := fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound
open PallLean.Paper93
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring (concreteW)

attribute [local instance] Classical.dec

/-- The exact concrete closure package whose discharge would close
`Direct.CookLevinPerTypeRowEmbeddings_concreteW` for the real Cook-Levin object.

The three components are:

* H3: every concrete Cook-Levin factor lies in its `concreteW` type space;
* H4: each concrete type space is closed under bounded iterated derivatives;
* I5: the resulting profile subspace is closed under shift and `mlProj`.
-/
def CookLevinConcreteWRowEmbeddingClosureFrontier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4) :
    Prop :=
  CookLevinFactorMemPerType M n hn htb hns
      (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau) ∧
    DerivClosurePerType (n := n)
      (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau) ∧
    PerTypeShiftMlprojClosure (n := n)
      (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau)

/-- Specialise H5's existing per-type spanning composition to the real
Cook-Levin `concreteW` family.

This is a direct bridge from the concrete H3/H4/I5 closure frontier to
`Direct.CookLevinPerTypeRowEmbeddings_concreteW`. -/
theorem CookLevinPerTypeRowEmbeddings_concreteW_of_closureFrontier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hFrontier :
      CookLevinConcreteWRowEmbeddingClosureFrontier M n hn htb hns hn4) :
    PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
      M n hn htb hns hn4 := by
  rcases hFrontier with ⟨hFactor, hDeriv, hShiftMlproj⟩
  exact cookLevinPerTypeSpanning_discharged
    M n hn htb hns
    (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau)
    hFactor hDeriv hShiftMlproj

/-- Same bridge with the three concrete closure components exposed separately.

This is convenient for call sites that already carry the three H3/H4/I5
frontiers independently. -/
theorem CookLevinPerTypeRowEmbeddings_concreteW_of_H3_H4_I5
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hFactor :
      CookLevinFactorMemPerType M n hn htb hns
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hShiftMlproj :
      PerTypeShiftMlprojClosure (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau)) :
    PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
      M n hn htb hns hn4 :=
  CookLevinPerTypeRowEmbeddings_concreteW_of_closureFrontier
    M n hn htb hns hn4 ⟨hFactor, hDeriv, hShiftMlproj⟩

/-- Universal form: a universal per-type spanning theorem immediately supplies
the direct concrete row-embedding package for every Cook-Levin instance. -/
theorem CookLevinPerTypeRowEmbeddings_concreteW_of_universalSpanning
    (hSpan_universal : CookLevinPerTypeSpanning_universal) :
    ∀ (M : DTM) (n : ℕ) (hn : n ≥ 2)
      (hn4 : n ≥ 4) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4 := by
  intro M n hn hn4 htb hns
  exact hSpan_universal M n hn htb hns
    (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau)

/-- Concrete row embeddings are fully reduced to the three universal H3/H4/I5
closure packages.  This does not prove those packages; it records the exact
remaining theorem-level blockers. -/
theorem CookLevinPerTypeRowEmbeddings_concreteW_of_universal_H3_H4_I5
    (hFactor_universal :
      ∀ (M : DTM) (n : ℕ) (hn : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)),
        CookLevinFactorMemPerType M n hn htb hns W)
    (hDeriv_universal :
      ∀ (n : ℕ)
        (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)),
        DerivClosurePerType (n := n) W)
    (hShiftMlproj_universal :
      ∀ (n : ℕ)
        (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)),
        PerTypeShiftMlprojClosure (n := n) W) :
    ∀ (M : DTM) (n : ℕ) (hn : n ≥ 2)
      (hn4 : n ≥ 4) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4 := by
  intro M n hn hn4 htb hns
  exact CookLevinPerTypeRowEmbeddings_concreteW_of_H3_H4_I5
    M n hn htb hns hn4
    (hFactor_universal M n hn htb hns
      (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hDeriv_universal n
      (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hShiftMlproj_universal n
      (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))

/-- Fully discharged active-type fact already available for the real
Cook-Levin classifier: no compiled factor is classified as `transitionRight`.

This is the dormant fourth branch of the row-embedding dispatch. -/
theorem cookLevin_concreteW_transitionRight_dormant
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (bp : BoundedProfile (Nat.log 2 n)) :
    ∀ i : Fin (cookLevinFactorList M n hn htb hns).length,
      cookLevinConstraintType M n hn htb hns i =
        ConstraintType.transitionRight → False :=
  PallLean.Paper93.Direct.transitionRight_vacuous M n hn htb hns hn4 bp

/-! ## Axiom audit anchors -/

#print axioms CookLevinPerTypeRowEmbeddings_concreteW_of_closureFrontier
#print axioms CookLevinPerTypeRowEmbeddings_concreteW_of_H3_H4_I5
#print axioms CookLevinPerTypeRowEmbeddings_concreteW_of_universalSpanning
#print axioms CookLevinPerTypeRowEmbeddings_concreteW_of_universal_H3_H4_I5
#print axioms cookLevin_concreteW_transitionRight_dormant

end PallLean.Paper93.DeepMath.PathB
