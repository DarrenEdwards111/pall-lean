import PallLean.HoloCompilerWitnessFriendly
import PallLean.IdentityMinor
import Mathlib.Tactic

/-!
# DistinctIdentityMinor — Identity minor structure for the distinct-layer product

The witness-friendly verifier sheet `wfVerifierSheet = ∏ᵢ (1 - X_{ver(i)})` has
factors touching distinct blocks under `holoDistinctPartition`. This gives the
identity minor structure needed for exponential SPDP rank.
-/

namespace DistinctIdentityMinor

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open HoloCompilerDistinctPartition
open HoloCompilerWitnessFriendly

/-- verSlot is injective on base indices. -/
theorem verSlot_injective (M : DTM) (n : ℕ) :
    Function.Injective (verSlot M n) := by
  intro a b hab
  simp [verSlot] at hab
  exact Fin.ext (by omega)

/-- The verifier slot list for a set of base indices is block-admissible. -/
theorem verSlotList_admissible (M : DTM) (n : ℕ)
    (S : List (Fin (HoloCompilerDistinct.holoBaseVars M n))) (hnd : S.Nodup) :
    isBlockAdmissible (holoDistinctPartition M n)
      (S.map (fun i => verSlot M n i)) := by
  constructor
  · exact hnd.map (verSlot_injective M n)
  · intro b
    -- assign(verSlot(a)) = ⟨(3*a+1)/3, _⟩ = ⟨a, _⟩
    -- So if two mapped elements land in block b, they came from same base index a
    -- S.Nodup means at most one such a → filter length ≤ 1
    sorry

/-- wfCompiledPoly = wfVerifierSheet + wfMachineSheet. Since derivatives of
wfMachineSheet w.r.t. verifier-slot variables are zero (machine sheet uses
only machine-slot variables, disjoint from verifier slots), the SPDP
generators from verifier-only derivative sets are the same for both. -/
theorem wfCompiledPoly_rank_ge_verifier (M : DTM) (n : ℕ)
    (κ ℓ : ℕ) :
    mlBlockedSpdpRank (holoDistinctPartition M n) κ ℓ (wfVerifierSheet M n) ≤
    mlBlockedSpdpRank (holoDistinctPartition M n) κ ℓ (wfCompiledPoly M n) := by
  -- wfCompiledPoly = wfVerifierSheet + wfMachineSheet
  -- The subspace for the sum ⊇ subspace for each summand
  -- (generators of the sum include generators of each part)
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  intro q ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
  apply Submodule.subset_span
  refine ⟨S, m, hlen, hdeg, hvars, hadm, ?_⟩
  -- q = mlProj(m * ∂^S wfVerifierSheet)
  -- Need: q = mlProj(m * ∂^S wfCompiledPoly)
  -- wfCompiledPoly = wfVerifierSheet + wfMachineSheet
  -- ∂^S is linear: ∂^S wfCompiledPoly = ∂^S wfVerifierSheet + ∂^S wfMachineSheet
  -- ∂^S wfMachineSheet = 0 for verifier-slot S (machine sheet uses disjoint vars)
  -- So ∂^S wfCompiledPoly = ∂^S wfVerifierSheet
  -- But S might not be verifier-slot only...
  sorry

/-- The SPDP subspace of wfVerifierSheet under holoDistinctPartition has
dimension ≥ C(N, κ) where N = holoBaseVars. -/
theorem wfVerifierSheet_rank_lower (M : DTM) (n : ℕ)
    (κ : ℕ) (hκ : κ ≥ 5) (hκ_le : κ ≤ HoloCompilerDistinct.holoBaseVars M n) :
    Nat.choose (HoloCompilerDistinct.holoBaseVars M n) κ ≤
      mlBlockedSpdpRank (holoDistinctPartition M n) κ κ (wfVerifierSheet M n) := by
  sorry

/-- C(N, κ) ≥ n^{κ/4} for appropriate parameters. -/
theorem choose_lower_bound (N κ n : ℕ) (hN : N ≥ n) (hκ : κ ≥ 5) (hκ_le : 4 * κ ≤ N) :
    n ^ (κ / 4) ≤ Nat.choose N κ := by
  sorry

/-- Main theorem: the full chain. -/
theorem wf_extracts_hard_witness_proof (M : DTM) (n : ℕ)
    (hn : n ≥ 32)
    (κ : ℕ) (hκ : κ ≥ 5)
    (hbase : HoloCompilerDistinct.holoBaseVars M n ≥ n)
    (hκ_le : 4 * κ ≤ HoloCompilerDistinct.holoBaseVars M n) :
    n ^ (κ / 4) ≤
      mlBlockedSpdpRank (holoDistinctPartition M n) κ κ (wfCompiledPoly M n) :=
  le_trans
    (le_trans (choose_lower_bound (HoloCompilerDistinct.holoBaseVars M n) κ n hbase hκ hκ_le)
             (wfVerifierSheet_rank_lower M n κ hκ (by omega)))
    (wfCompiledPoly_rank_ge_verifier M n κ κ)

end DistinctIdentityMinor
