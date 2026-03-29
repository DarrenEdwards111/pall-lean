import PallLean.Leibniz

/-! # Layer 2: Profile classification of derivative allocations

Given the Layer 1 decomposition of `iterDerivList S (∏ f_i)` into
allocations `α : Fin κ → Fin m`, we classify allocations by their
**profile**: the histogram `p : Fin m → ℕ` where `p(i) = |α⁻¹(i)|`.

Block-admissibility forces `p(i) ≤ width` for each factor i.

## Main results

* `allocProfile` — the profile (derivative count histogram) of an allocation
* `allocProfile_bounded` — block-admissibility bounds profile entries by width
* `profile_image_card_le` — number of bounded profiles ≤ (width+1)^m
-/

namespace SPDP

open MvPolynomial Finset

variable {n : ℕ} {F : Type*} [CommRing F]

/-! ## Profile of an allocation -/

/-- The profile of an allocation α counts how many derivatives are
    assigned to each factor. -/
def allocProfile {κ m : ℕ} (α : DerivAlloc κ m) : Fin m → ℕ :=
  fun i => ((List.finRange κ).filter (fun j => decide (α j = i))).length

/-! ## Profile count bound -/

/-- The number of distinct profiles from allocations, where each entry
    is bounded by w, is at most (w+1)^m.

    Proof: each bounded profile is a function Fin m → Fin (w+1),
    and |Fin m → Fin (w+1)| = (w+1)^m. -/
theorem profile_image_card_le (κ m w : ℕ)
    (hbounded : ∀ (α : DerivAlloc κ m), ∀ i, allocProfile α i ≤ w) :
    (Finset.univ.image (fun α : DerivAlloc κ m =>
      (fun i : Fin m => (⟨allocProfile α i, by have := hbounded α i; omega⟩ : Fin (w + 1))))).card
      ≤ (w + 1) ^ m := by
  calc _ ≤ (Finset.univ : Finset (Fin m → Fin (w + 1))).card :=
          Finset.card_le_univ _
    _ = (w + 1) ^ m := by simp [Fintype.card_fun, Fintype.card_fin]

/-! ## Block-admissibility bounds profile entries -/

/-- If a derivative list S is block-admissible and each factor has
    ≤ width variables, then factor i receives ≤ width derivatives
    in any allocation where all derivatives land in their factor's vars.

    Key insight: block-admissibility means the derivatives in S hit
    distinct blocks. Since factor i touches ≤ width blocks, at most
    width derivatives can land in factor i's variables. -/
theorem allocProfile_le_of_width_bound
    {κ m : ℕ}
    (S : List (Fin n)) (hS : S.length = κ)
    (α : DerivAlloc κ m)
    (factor : Fin m → MvPolynomial (Fin n) F)
    (width : ℕ)
    (hfactor_width : ∀ i, (factor i).vars.card ≤ width)
    (h_relevant : ∀ (j : Fin κ), S.get (j.cast (by omega)) ∈ (factor (α j)).vars)
    (hS_nodup : S.Nodup)
    (i : Fin m) :
    allocProfile α i ≤ width := by
  unfold allocProfile
  -- Step 1: The filter selects indices j where α j = i
  set filtered := (List.finRange κ).filter (fun j => decide (α j = i)) with hfilt_def
  -- Step 2: Map these indices to their S-values (variables being differentiated)
  set mapped := filtered.map (fun j => S.get (j.cast (by omega))) with hmapped_def
  -- Step 3: mapped.length = filtered.length
  have hlen : mapped.length = filtered.length := List.length_map ..
  -- Step 4: mapped is Nodup (S is Nodup, and get is injective on Nodup lists)
  have hmapped_nodup : mapped.Nodup := by
    rw [hmapped_def]
    apply List.Nodup.map
    · intro a b hab
      have h := hS_nodup.get_inj_iff.mp hab
      simp [Fin.ext_iff] at h
      exact Fin.ext h
    · exact List.Nodup.filter _ (List.nodup_finRange κ)
  -- Step 5: All elements of mapped are in (factor i).vars
  have hmapped_sub : ∀ v ∈ mapped, v ∈ (factor i).vars := by
    intro v hv
    rw [hmapped_def] at hv
    simp only [List.mem_map, List.mem_filter, List.mem_finRange] at hv
    obtain ⟨j, hj_mem, hv_eq⟩ := hv
    subst hv_eq
    have hj_eq : α j = i := by
      simp only [hfilt_def, List.mem_filter, List.mem_finRange, decide_eq_true_eq] at hj_mem
      exact hj_mem.2
    have := h_relevant j
    rw [hj_eq] at this
    exact this
  -- Step 6: mapped.toFinset ⊆ (factor i).vars, so |mapped| ≤ |vars| ≤ width
  rw [← hlen]
  have h1 : mapped.toFinset.card ≤ (factor i).vars.card := by
    apply Finset.card_le_card
    intro v hv
    exact hmapped_sub v (List.mem_toFinset.mp hv)
  have h2 : mapped.toFinset.card = mapped.length :=
    List.toFinset_card_of_nodup hmapped_nodup
  linarith [hfactor_width i]

/-! ## Combining Layers 1 and 2

The blocked SPDP rank of a product of m local factors is bounded by
the number of profiles times the maximum per-profile dimension.

From Layer 1: generators lie in span of allocation products.
From Layer 2: allocations group into ≤ (w+1)^m profiles.
Layer 3 (axiomatized): each profile-group has bounded dimension.

The assembly into width_to_rank's bound (m·w)^(3w) uses:
  (w+1)^m profiles × (w+1)^(Σ p(i)) per-profile ≤ (w+1)^(m+mw) ≤ (mw)^(3w)
This is the arithmetic step that was shown FALSE for concrete bounds
in the earlier decomposition attempt. The monolithic width_to_rank
remains the cleanest axiom. -/

end SPDP
