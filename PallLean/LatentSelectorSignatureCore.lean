import PallLean.LatentCompiler
import Mathlib.Tactic

/-!
# LatentSelectorSignatureCore

Minimal acyclic selector-signature data shared across latent-route files.
This file intentionally contains only the selector-aware profile-signature
structure and its definitional constructor/lemmas. Any compatibility menus,
canonical-witness packaging, or width-rank-specific reductions stay in
`LatentWidthRankDecomp` until they can be moved without reintroducing cycles.
-/

namespace LatentSelectorSignatureCore

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open LatentCompiler

/-- Coarse latent profile signature recording hit blocks and multiplier degree. -/
structure latentProfileSignature (M : DTM) (n : ℕ) where
  hitBlocks : Finset (Fin (latentBaseVars M n))
  hitCardBound : hitBlocks.card ≤ Nat.log 2 n
  multDeg : ℕ
  multDegBound : multDeg ≤ Nat.log 2 n

/-- The hit blocks visited by a raw witness list. -/
noncomputable def latent_hitBlocks_of_list
    (M : DTM) (n : ℕ)
    (S : List (Fin (latentNumVars M n))) : Finset (Fin (latentBaseVars M n)) :=
  (S.map fun v => (latentPartition M n).assign v).toFinset

/-- The hit-block set is no larger than the originating list. -/
theorem latent_hitBlocks_of_list_card_le_length
    (M : DTM) (n : ℕ)
    (S : List (Fin (latentNumVars M n))) :
    (latent_hitBlocks_of_list M n S).card ≤ S.length := by
  unfold latent_hitBlocks_of_list
  simpa using List.toFinset_card_le (S.map (fun i => (latentPartition M n).assign i))

/-- Build the coarse profile signature attached to generator data `(S,m)`. -/
noncomputable def latent_profile_signature_of_generator_data
    (M : DTM) (n : ℕ)
    (S : List (Fin (latentNumVars M n)))
    (m : MvPolynomial (Fin (latentNumVars M n)) ℚ)
    (hLen : S.length = Nat.log 2 n)
    (hDeg : m.totalDegree ≤ Nat.log 2 n) :
    latentProfileSignature M n := by
  refine
    { hitBlocks := latent_hitBlocks_of_list M n S
      hitCardBound := ?_
      multDeg := m.totalDegree
      multDegBound := hDeg }
  calc
    (latent_hitBlocks_of_list M n S).card ≤ S.length :=
      latent_hitBlocks_of_list_card_le_length M n S
    _ = Nat.log 2 n := hLen

/-- The coarse signature records exactly the multiplier degree coming from the
generator presentation. -/
@[simp] theorem latent_profile_signature_of_generator_data_multDeg
    (M : DTM) (n : ℕ)
    (S : List (Fin (latentNumVars M n)))
    (m : MvPolynomial (Fin (latentNumVars M n)) ℚ)
    (hLen : S.length = Nat.log 2 n)
    (hDeg : m.totalDegree ≤ Nat.log 2 n) :
    (latent_profile_signature_of_generator_data M n S m hLen hDeg).multDeg = m.totalDegree := by
  rfl

/-- The coarse signature hit-set is exactly the block projection of the
 derivative list. -/
@[simp] theorem latent_profile_signature_of_generator_data_hitBlocks
    (M : DTM) (n : ℕ)
    (S : List (Fin (latentNumVars M n)))
    (m : MvPolynomial (Fin (latentNumVars M n)) ℚ)
    (hLen : S.length = Nat.log 2 n)
    (hDeg : m.totalDegree ≤ Nat.log 2 n) :
    (latent_profile_signature_of_generator_data M n S m hLen hDeg).hitBlocks =
      latent_hitBlocks_of_list M n S := by
  rfl

/-- Selector-aware refinement of the coarse profile signature. Besides hit blocks and multiplier
 degree, it also remembers the actual selector support set for the multiplier witness. -/
structure latentSelectorProfileSignature (M : DTM) (n : ℕ) where
  coarse : latentProfileSignature M n
  selSupport : Finset (Fin (latentNumVars M n))

/-- Build the selector-aware profile signature attached to generator data. -/
noncomputable def latent_selector_profile_signature_of_generator_data
    (M : DTM) (n : ℕ)
    (S : List (Fin (latentNumVars M n)))
    (m : MvPolynomial (Fin (latentNumVars M n)) ℚ)
    (hLen : S.length = Nat.log 2 n)
    (hDeg : m.totalDegree ≤ Nat.log 2 n) : latentSelectorProfileSignature M n :=
  { coarse := latent_profile_signature_of_generator_data M n S m hLen hDeg
    selSupport := m.vars }

@[simp] theorem latent_selector_profile_signature_of_generator_data_coarse
    (M : DTM) (n : ℕ)
    (S : List (Fin (latentNumVars M n)))
    (m : MvPolynomial (Fin (latentNumVars M n)) ℚ)
    (hLen : S.length = Nat.log 2 n)
    (hDeg : m.totalDegree ≤ Nat.log 2 n) :
    (latent_selector_profile_signature_of_generator_data M n S m hLen hDeg).coarse =
      latent_profile_signature_of_generator_data M n S m hLen hDeg := by
  rfl

@[simp] theorem latent_selector_profile_signature_of_generator_data_selSupport
    (M : DTM) (n : ℕ)
    (S : List (Fin (latentNumVars M n)))
    (m : MvPolynomial (Fin (latentNumVars M n)) ℚ)
    (hLen : S.length = Nat.log 2 n)
    (hDeg : m.totalDegree ≤ Nat.log 2 n) :
    (latent_selector_profile_signature_of_generator_data M n S m hLen hDeg).selSupport = m.vars := by
  rfl

end LatentSelectorSignatureCore

export LatentSelectorSignatureCore
  ( latentProfileSignature
    latent_hitBlocks_of_list
    latent_hitBlocks_of_list_card_le_length
    latent_profile_signature_of_generator_data
    latent_profile_signature_of_generator_data_multDeg
    latent_profile_signature_of_generator_data_hitBlocks
    latentSelectorProfileSignature
    latent_selector_profile_signature_of_generator_data
    latent_selector_profile_signature_of_generator_data_coarse
    latent_selector_profile_signature_of_generator_data_selSupport )
