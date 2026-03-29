import PallLean.MultilinearSPDP
import PallLean.Compiler
import Mathlib.Tactic

/-!
# PrivateVars — 4 fresh private variables per clause (Paper §34 Step 1)

Creates a private variable space with 4 vars per clause, a block partition
where each clause's 4 vars are in one block, and the private verifier polynomial.
-/

namespace PrivateVars

open SPDP MultilinearSPDP NPWitness Tseitin MvPolynomial

noncomputable abbrev numCl (n : ℕ) : ℕ := (tseitinAt n).clauses.length

/-- 4 private vars per clause. -/
noncomputable def numPV (n : ℕ) : ℕ := 4 * numCl n

/-- Private variable index: clause c, position j ∈ {0,1,2,3}. Index = 4c+j. -/
noncomputable def privIdx (n : ℕ) (c : Fin (numCl n)) (j : Fin 4) :
    Fin (numPV n) :=
  ⟨4 * c.val + j.val, by show _ < 4 * numCl n; have := c.isLt; have := j.isLt; omega⟩

/-- Block partition: clause c → block c+1. 4 vars per block. -/
noncomputable def pvPartition (n : ℕ) : BlockPartition (numPV n) where
  numBlocks := numCl n + 1
  assign := fun v =>
    have hv := v.isLt
    if h : v.val / 4 < numCl n then
      ⟨v.val / 4 + 1, by omega⟩
    else
      ⟨0, by omega⟩

/-- privIdx maps to the correct block. -/
theorem privIdx_block (n : ℕ) (c : Fin (numCl n)) (j : Fin 4) :
    ∃ (hlt : c.val + 1 < numCl n + 1),
      (pvPartition n).assign (privIdx n c j) = ⟨c.val + 1, hlt⟩ := by
  have hc := c.isLt; have hj := j.isLt
  refine ⟨by omega, ?_⟩
  simp only [pvPartition, privIdx]
  have hdiv : (4 * c.val + j.val) / 4 < numCl n := by omega
  simp [hdiv]; congr 1; omega

/-- Private clause gadget using priv(c, 1..3). -/
noncomputable def pvGadget (F : Type*) [CommRing F] [Nontrivial F]
    (n : ℕ) (c : Fin (numCl n)) :
    MvPolynomial (Fin (numPV n)) F :=
  let cl := (tseitinAt n).clauses.get c
  (1 - if cl.sign1 then X (privIdx n c ⟨1, by omega⟩) else 1 - X (privIdx n c ⟨1, by omega⟩)) *
  (1 - if cl.sign2 then X (privIdx n c ⟨2, by omega⟩) else 1 - X (privIdx n c ⟨2, by omega⟩)) *
  (1 - if cl.sign3 then X (privIdx n c ⟨3, by omega⟩) else 1 - X (privIdx n c ⟨3, by omega⟩))

/-- Private coupled factor: 1 - z'_c × g'_c. -/
noncomputable def pvFactor (F : Type*) [CommRing F] [Nontrivial F]
    (n : ℕ) (c : Fin (numCl n)) :
    MvPolynomial (Fin (numPV n)) F :=
  1 - X (privIdx n c ⟨0, by omega⟩) * pvGadget F n c

/-- Private coupled verifier: ∏_c pvFactor c. -/
noncomputable def pvVerifier (F : Type*) [CommRing F] [Nontrivial F]
    (n : ℕ) : MvPolynomial (Fin (numPV n)) F :=
  Finset.univ.prod (pvFactor F n)

/-- KEY: pvFactor c uses only vars from block c+1 (private copies).
    This enables the Width⇒Rank argument under pvPartition. -/
theorem pvFactor_single_block (F : Type*) [CommRing F] [Nontrivial F]
    (n : ℕ) (c : Fin (numCl n)) :
    ∀ v ∈ (pvFactor F n c).vars,
      ∃ (j : Fin 4), v = privIdx n c j := by
  sorry -- pvFactor uses only X(privIdx c 0), X(privIdx c 1..3) via pvGadget

/-- Block-admissible S hits ≤ 1 var per clause block. -/
theorem pvPartition_single_hit (n : ℕ)
    (S : List (Fin (numPV n)))
    (hadm : isBlockAdmissible (pvPartition n) S)
    (c : Fin (numCl n)) (hc : c.val + 1 < numCl n + 1) :
    (S.filter (fun v => (pvPartition n).assign v = ⟨c.val + 1, hc⟩)).length ≤ 1 :=
  hadm.2 ⟨c.val + 1, hc⟩

end PrivateVars
