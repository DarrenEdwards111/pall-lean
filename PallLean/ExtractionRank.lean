import PallLean.SPDPDefs
import PallLean.RestrictionRank
import PallLean.RenameRank
import PallLean.PDerivEval
import Mathlib.Tactic
/-!
# Extraction rank inequality — PROVED from R1 + R3
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
theorem rank_iterRestrict_le {n : ℕ} (κ : ℕ)
    (restrictions : List (Fin n × F))
    (p : MvPolynomial (Fin n) F) :
    spdpRank κ (iterRestrict restrictions p) ≤ spdpRank κ p := by
  induction restrictions generalizing p with
  | nil => exact le_refl _
  | cons rc rest ih =>
    calc spdpRank κ (iterRestrict rest (evalAt rc.1 rc.2 p))
        ≤ spdpRank κ (evalAt rc.1 rc.2 p) := ih (evalAt rc.1 rc.2 p)
      _ ≤ spdpRank κ p := restriction_rank_le κ p rc.1 rc.2

/-- Rename with injective f: rank(p) ≤ rank(rename f p) -/
theorem rank_le_rename (f : Fin n → Fin m) (hf : Function.Injective f)
    (κ : ℕ) (p : MvPolynomial (Fin n) F) :
    spdpRank κ p ≤ spdpRank κ (rename f p) := by
  unfold spdpRank
  have h_le := spdpSubspace_rename_ge f hf κ p
  have h_inj : Function.Injective
      ((rename f : MvPolynomial (Fin n) F →ₐ[F] MvPolynomial (Fin m) F).toLinearMap) :=
    fun _ _ h => MvPolynomial.rename_injective f hf h
  have h_eq := (Submodule.equivMapOfInjective
    (rename f : MvPolynomial (Fin n) F →ₐ[F] MvPolynomial (Fin m) F).toLinearMap
    h_inj (spdpSubspace κ p)).finrank_eq
  rw [h_eq]
  exact Submodule.finrank_mono h_le

/-- **Rename preserves SPDP rank** -/
theorem rank_rename_eq (f : Fin n → Fin m) (hf : Function.Injective f)
    (κ : ℕ) (p : MvPolynomial (Fin n) F) :
    spdpRank κ (rename f p) = spdpRank κ p :=
  le_antisymm (rank_rename_le f hf κ p) (rank_le_rename f hf κ p)

/-- **Cross-ring extraction rank inequality — PROVED**

If q in n_out variables is obtained from p in n_in variables via
restriction + injective rename, then rank(q) ≤ rank(p). -/
theorem rank_extraction_le {n_in n_out : ℕ} (κ : ℕ)
    (p : MvPolynomial (Fin n_in) F)
    (q : MvPolynomial (Fin n_out) F)
    (restrictions : List (Fin n_in × F))
    (f : Fin n_out → Fin n_in) (hf : Function.Injective f)
    (h_eq : rename f q = iterRestrict restrictions p) :
    spdpRank κ q ≤ spdpRank κ p :=
  calc spdpRank κ q
      = spdpRank κ (rename f q) := (rank_rename_eq f hf κ q).symm
    _ = spdpRank κ (iterRestrict restrictions p) := by rw [h_eq]
    _ ≤ spdpRank κ p := rank_iterRestrict_le κ restrictions p

end SPDP.ExtractionRank
