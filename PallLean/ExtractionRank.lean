import PallLean.SPDPDefs
import PallLean.RestrictionRank
import PallLean.RenameRank
import PallLean.PDerivEval
import Mathlib.Tactic
/-!
# Extraction rank inequality — from R1 + R3

Updated for the paper-faithful (κ, ℓ) definition.

Extraction = restriction + injective rename, both rank-nonincreasing.
-/

namespace SPDP.ExtractionRank

open SPDP SPDP.Restriction SPDP.Rename PDerivEval MvPolynomial

variable {F : Type*} [CommRing F] [Nontrivial F]

/-- Iterated variable restriction -/
noncomputable def iterRestrict {n : ℕ}
    (restrictions : List (Fin n × F))
    (p : MvPolynomial (Fin n) F) : MvPolynomial (Fin n) F :=
  restrictions.foldl (fun q ⟨i, c⟩ => evalAt i c q) p

/-- Iterated restriction cannot increase rank -/
theorem rank_iterRestrict_le {n : ℕ} (κ ℓ : ℕ)
    (restrictions : List (Fin n × F))
    (p : MvPolynomial (Fin n) F) :
    spdpRank κ ℓ (iterRestrict restrictions p) ≤ spdpRank κ ℓ p := by
  induction restrictions generalizing p with
  | nil => exact le_refl _
  | cons rc rest ih =>
    calc spdpRank κ ℓ (iterRestrict rest (evalAt rc.1 rc.2 p))
        ≤ spdpRank κ ℓ (evalAt rc.1 rc.2 p) := ih (evalAt rc.1 rc.2 p)
      _ ≤ spdpRank κ ℓ p := restriction_rank_le κ ℓ p rc.1 rc.2

/-- **Cross-ring extraction rank inequality**

If q in n_out variables is obtained from p in n_in variables via
restriction + injective rename, then rank(q) ≤ rank(p). -/
theorem rank_extraction_le {n_in n_out : ℕ} (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n_in) F)
    (q : MvPolynomial (Fin n_out) F)
    (restrictions : List (Fin n_in × F))
    (f : Fin n_out → Fin n_in) (hf : Function.Injective f)
    (h_eq : rename f q = iterRestrict restrictions p) :
    spdpRank κ ℓ q ≤ spdpRank κ ℓ p :=
  calc spdpRank κ ℓ q
      = spdpRank κ ℓ (rename f q) := (rank_rename_eq f hf κ ℓ q).symm
    _ = spdpRank κ ℓ (iterRestrict restrictions p) := by rw [h_eq]
    _ ≤ spdpRank κ ℓ p := rank_iterRestrict_le κ ℓ restrictions p

end SPDP.ExtractionRank
