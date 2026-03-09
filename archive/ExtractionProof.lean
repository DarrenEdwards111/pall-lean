/-
  ExtractionProof.lean — Extraction lemmas (no dependency on FullCompiler)
-/
import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness
import PallLean.SheetCoupling
import Mathlib.Tactic

namespace ExtractionProof

open MvPolynomial SPDP Compiler NPWitness TuringMachine Extraction

/-! ## Proved: iterDerivList through rename -/

theorem iterDerivList_map_rename {n m : ℕ} {F : Type*} [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (S : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    iterDerivList (S.map f) (rename f p) =
    rename f (iterDerivList S p) := by
  induction S generalizing p with
  | nil => rfl
  | cons i rest ih =>
    show iterDerivList (rest.map f) (pderiv (f i) (rename f p)) =
      rename f (iterDerivList rest (pderiv i p))
    rw [pderiv_rename hf]; exact ih (pderiv i p)

/-! ## Proved: disjoint-range derivatives kill polynomial -/

theorem iterDerivList_cons_rename_zero {n m : ℕ} {F : Type*} [CommRing F]
    (f : Fin n → Fin m) (v : Fin m) (rest : List (Fin m))
    (hv : v ∉ Set.range f) (p : MvPolynomial (Fin n) F) :
    iterDerivList (v :: rest) (rename f p) = 0 := by
  show iterDerivList rest (pderiv v (rename f p)) = 0
  have : pderiv v (rename f p) = 0 := pderiv_eq_zero_of_notMem_vars
    (fun hmem => hv (let ⟨i, _, hi⟩ := mem_vars_rename f p hmem; ⟨i, hi⟩))
  rw [this]; exact foldl_pderiv_zero rest

end ExtractionProof
