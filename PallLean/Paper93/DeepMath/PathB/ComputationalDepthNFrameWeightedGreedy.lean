import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameRouteSupplyZ

/-!
# N-Frame: the weighted greedy — mass-weighted independent selection

Expander-discharge arc, rung E5-prep (… → `z`-general supply → **weighted greedy**).  The
mass-weighted version of E4's greedy bound: for any symmetric degree-`≤ d` neighbourhood
structure and any weight function, every subset `U` contains an independent subset `I`
carrying a `1/(d+1)` fraction of `U`'s WEIGHT.  This is the selector the global
coordinate pool `P*` needs (design doc, finding (a)): the row-side company/absorber
choices force one shared independent pool across blocks, and the pool must be chosen to
carry a constant fraction of the S-mass, not merely of the coordinate count — the greedy
picks the maximum-weight vertex instead of an arbitrary one, and the same induction
closes.

  `greedy_indep_weighted` — **PROVED, THE WEIGHTED BOUND**:
        `∑_{U} W ≤ (d+1) · ∑_{I} W` with `I ⊆ U` independent.
  `circulant_weighted_select` / `circulant_weighted_priced_select` — **PROVED**: the
        circulant instantiations, companion-validity included.

## Honest scope

Safe under every variant of the E5 design.  The kill-accounting itself remains BLOCKED
on the full-block concentration wall (design doc, finding (b)).  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameWeightedGreedy

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityXCode
open PallLean.Paper93.DeepMath.PathB.NFrameCirculantLayer

variable {v : ℕ}

set_option maxHeartbeats 1600000 in
/-- **THE WEIGHTED GREEDY BOUND (proved)**: for any symmetric neighbourhood structure of
degree `≤ d` and any weight function, every subset `U` contains an independent subset
carrying a `1/(d+1)` fraction of `U`'s weight — multiplicative, division-free. -/
theorem greedy_indep_weighted (nbr : Fin v → Finset (Fin v)) (d : ℕ)
    (W : Fin v → ℕ)
    (hdeg : ∀ j : Fin v, (nbr j).card ≤ d)
    (hsym : ∀ a b : Fin v, a ∈ nbr b → b ∈ nbr a)
    (U : Finset (Fin v)) :
    ∃ I ⊆ U, (∀ a ∈ I, ∀ b ∈ I, a ≠ b → b ∉ nbr a)
      ∧ ∑ x ∈ U, W x ≤ (d + 1) * ∑ x ∈ I, W x := by
  classical
  suffices h : ∀ n : ℕ, ∀ U : Finset (Fin v), U.card ≤ n →
      ∃ I ⊆ U, (∀ a ∈ I, ∀ b ∈ I, a ≠ b → b ∉ nbr a)
        ∧ ∑ x ∈ U, W x ≤ (d + 1) * ∑ x ∈ I, W x by
    exact h U.card U le_rfl
  intro n
  induction n with
  | zero =>
      intro U hU
      have hUe : U = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hU)
      refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
      · intro a ha
        exact absurd ha (Finset.notMem_empty a)
      · rw [hUe, Finset.sum_empty]
        omega
  | succ n ihn =>
      intro U hU
      by_cases hUe : U = ∅
      · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
        · intro a ha
          exact absurd ha (Finset.notMem_empty a)
        · rw [hUe, Finset.sum_empty]
          omega
      · obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image U W
          (Finset.nonempty_iff_ne_empty.mpr hUe)
        set U' := U \ insert u (nbr u) with hU'
        have hsub' : U' ⊆ U := by
          rw [hU']
          exact Finset.sdiff_subset
        have huU' : u ∉ U' := by
          intro hc
          rw [hU', Finset.mem_sdiff] at hc
          exact hc.2 (Finset.mem_insert_self u _)
        have hss : U' ⊂ U :=
          (Finset.ssubset_iff_of_subset hsub').mpr ⟨u, hu, huU'⟩
        have hlt : U'.card < U.card := Finset.card_lt_card hss
        obtain ⟨I', hI'sub, hI'ind, hI'sum⟩ := ihn U' (by omega)
        have huI' : u ∉ I' := fun hc => huU' (hI'sub hc)
        refine ⟨insert u I', ?_, ?_, ?_⟩
        · intro a ha
          rcases Finset.mem_insert.mp ha with rfl | haI'
          · exact hu
          · exact hsub' (hI'sub haI')
        · intro a ha b hb hab
          rcases Finset.mem_insert.mp ha with rfl | haI'
          · rcases Finset.mem_insert.mp hb with rfl | hbI'
            · exact absurd rfl hab
            · have hbU' := hI'sub hbI'
              rw [hU', Finset.mem_sdiff] at hbU'
              intro hbn
              exact hbU'.2 (Finset.mem_insert.mpr (Or.inr hbn))
          · rcases Finset.mem_insert.mp hb with rfl | hbI'
            · have haU' := hI'sub haI'
              rw [hU', Finset.mem_sdiff] at haU'
              intro hun
              exact haU'.2 (Finset.mem_insert.mpr (Or.inr (hsym b a hun)))
            · exact hI'ind a haI' b hbI' hab
        · -- the weight chain
          have hsplit : ∑ x ∈ U ∩ insert u (nbr u), W x + ∑ x ∈ U', W x
              = ∑ x ∈ U, W x := by
            rw [hU']
            exact Finset.sum_inter_add_sum_diff U (insert u (nbr u)) W
          have hheavy : ∑ x ∈ U ∩ insert u (nbr u), W x ≤ (d + 1) * W u := by
            have hbound : ∀ x ∈ U ∩ insert u (nbr u), W x ≤ W u := by
              intro x hx
              exact hmax x (Finset.mem_of_mem_inter_left hx)
            have h1 := Finset.sum_le_card_nsmul (U ∩ insert u (nbr u)) W (W u)
              hbound
            rw [smul_eq_mul] at h1
            have h2 : (U ∩ insert u (nbr u)).card ≤ d + 1 := by
              have h3 : (U ∩ insert u (nbr u)).card
                  ≤ (insert u (nbr u)).card :=
                Finset.card_le_card (Finset.inter_subset_right)
              have h4 := Finset.card_insert_le u (nbr u)
              have h5 := hdeg u
              omega
            calc ∑ x ∈ U ∩ insert u (nbr u), W x
                ≤ (U ∩ insert u (nbr u)).card * W u := h1
              _ ≤ (d + 1) * W u := Nat.mul_le_mul_right (W u) h2
          have hins : ∑ x ∈ insert u I', W x = W u + ∑ x ∈ I', W x :=
            Finset.sum_insert huI'
          calc ∑ x ∈ U, W x
              = ∑ x ∈ U ∩ insert u (nbr u), W x + ∑ x ∈ U', W x :=
                hsplit.symm
            _ ≤ (d + 1) * W u + (d + 1) * ∑ x ∈ I', W x := by omega
            _ = (d + 1) * (W u + ∑ x ∈ I', W x) := by ring
            _ = (d + 1) * ∑ x ∈ insert u I', W x := by rw [hins]

/-- **The weighted circulant selection (proved)**. -/
theorem circulant_weighted_select (v dd : ℕ) (hv : 0 < v) (hddv : dd ≤ v)
    (W : Fin v → ℕ) (U : Finset (Fin v)) :
    ∃ I ⊆ U, (∀ a ∈ I, ∀ b ∈ I, a ≠ b → b ∉ circNbr v hv dd a)
      ∧ ∑ x ∈ U, W x ≤ (2 * dd + 1) * ∑ x ∈ I, W x :=
  greedy_indep_weighted (circNbr v hv dd) (2 * dd) W
    (circNbr_card v hv dd)
    (fun a b hab => circNbr_sym v hv dd hddv b a hab) U

/-- **The weighted priced selection (proved)**: the E5-facing form — a priced pool
carrying a `1/(2·dd+1)` weight fraction, all of whose members' route companions avoid
the pool. -/
theorem circulant_weighted_priced_select (v dd : ℕ) (hv : 0 < v) (hddv : dd < v)
    (W : Fin v → ℕ) (U : Finset (Fin v)) :
    ∃ P ⊆ U, ∑ x ∈ U, W x ≤ (2 * dd + 1) * ∑ x ∈ P, W x
      ∧ ∀ j' ∈ P, ∀ ρ : PinRoute dd, ∀ j'' : Fin v,
          routeCompanion v hv j' ρ = some j'' → j'' ∉ P := by
  obtain ⟨I, hIsub, hIind, hIsum⟩ :=
    circulant_weighted_select v dd hv (le_of_lt hddv) W U
  exact ⟨I, hIsub, hIsum, fun j' hj' ρ j'' h =>
    indep_companion_valid v dd hv hddv I hIind j' hj' ρ j'' h⟩

end PallLean.Paper93.DeepMath.PathB.NFrameWeightedGreedy

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameWeightedGreedy.greedy_indep_weighted
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameWeightedGreedy.circulant_weighted_select
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameWeightedGreedy.circulant_weighted_priced_select
