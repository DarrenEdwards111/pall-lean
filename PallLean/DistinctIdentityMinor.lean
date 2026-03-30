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
    -- assign(verSlot(a)).val = (3*a+1)/3 = a. So two elements in block b
    -- come from the same base index → filter has ≤ 1 element.
    -- Strategy: filter of nodup list is nodup. Show any two elements in
    -- the filter are equal. Then nodup + all-equal → length ≤ 1.
    have hmap_nd := hnd.map (verSlot_injective M n)
    have hfilt_nd := hmap_nd.filter (fun j => (holoDistinctPartition M n).assign j = b)
    -- Show: if x, y both in filter, then x = y
    -- The filter selects verSlot(a) with a.val = b.val.
    -- S.Nodup + verSlot injective → at most one such a → filter length ≤ 1.
    -- Direct approach: bound by counting preimages
    by_contra hgt
    push_neg at hgt
    -- hgt: 2 ≤ filter length
    set filt := (S.map (fun i => verSlot M n i)).filter
        (fun j => (holoDistinctPartition M n).assign j = b) with hfilt_def
    have hfilt_nd := hmap_nd.filter (fun j => (holoDistinctPartition M n).assign j = b)
    have h0 : 0 < filt.length := by omega
    have h1 : 1 < filt.length := by omega
    -- Get two elements from the filter
    have hx_mem : filt[0] ∈ filt := List.getElem_mem h0
    have hy_mem : filt[1] ∈ filt := List.getElem_mem h1
    rw [List.mem_filter] at hx_mem hy_mem
    obtain ⟨hx_in, hx_bl⟩ := hx_mem
    obtain ⟨hy_in, hy_bl⟩ := hy_mem
    rw [List.mem_map] at hx_in hy_in
    obtain ⟨a, _, ha⟩ := hx_in
    obtain ⟨c, _, hc⟩ := hy_in
    -- Both in block b → verSlot(a).val/3 = b = verSlot(c).val/3 → a = c → filt[0]=filt[1]
    -- This contradicts nodup of filt. (Lean plumbing for Fin arithmetic is involved.)
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
