import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityXDrag

/-!
# N-Frame: the circulant layer — greedy companion-compatible independent sets

Expander-discharge arc, rung E4 (… → extended drag → **circulant layer**).  The graph
layer of the ratified framing: the explicit degree-`2·dd` circulant (already implicit in
`rot`/`PinRoute`), and the GENERIC greedy bound that replaces the spectral long-pole —
every subset `U` of coordinates contains an independent subset `I` with
`|U| ≤ (d+1)·|I|`, for ANY symmetric degree-`≤ d` neighbourhood structure.  Instantiated
at the circulant, this is what lets the designer price a `Θ(v)`-size coordinate set per
block while keeping every priced coordinate's edge companions outside the priced set —
the `hcomp` class of the extended drag — with NO spectral input.

  `circNbr` / `circNbr_card` / `circNbr_sym` / `circNbr_no_self` — the explicit circulant
        neighbourhood: degree `≤ 2·dd`, symmetric, loop-free (all PROVED, elementary
        modular arithmetic).
  `routeCompanion_mem_circNbr` — **PROVED, THE BRIDGE**: every route companion of E3's
        route layer is a circulant neighbour of its pinned coordinate.
  `greedy_indep` — **PROVED, THE GENERIC GREEDY BOUND**: `∃ I ⊆ U` independent with
        `|U| ≤ (d+1)·|I|` (multiplicative, division-free).
  `circulant_indep_select` / `indep_companion_valid` / `circulant_priced_select` —
        **PROVED, THE E5 PAYOFF**: inside ANY surviving column set `U`, a priced set `P`
        with `|U| ≤ (2·dd+1)·|P|` such that EVERY route companion of EVERY member of `P`
        avoids `P` — `hcomp` discharges by choosing priced coordinates inside `P`.

## Honest scope

Elementary counting only — no Ramanujan, no spectral gap; the expansion-quality constants
are the flagship upgrade, not the critical path.  The remaining rung is E5: the
kill-accounting at real balanced cuts (Markov designation, survivor columns, reserve
transversal, `|D| = Θ(T)`), then E6 the `(2+c)N` headline.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameCirculantLayer

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityXCode

variable {v dd : ℕ}

/-! ### Rotation arithmetic -/

theorem rot_rot_cancel' (v : ℕ) (hv : 0 < v) (j : Fin v) (k : ℕ) (hk : k ≤ v) :
    rot v hv (rot v hv j k) (v - k) = j := by
  apply Fin.ext
  show ((j.val + k) % v + (v - k)) % v = j.val
  rw [Nat.mod_add_mod]
  have h1 : j.val + k + (v - k) = j.val + v := by omega
  rw [h1, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt j.isLt

theorem rot_ne_self (v : ℕ) (hv : 0 < v) (j : Fin v) (k : ℕ)
    (hk0 : 0 < k) (hkv : k < v) : rot v hv j k ≠ j := by
  intro hcon
  have hval : (j.val + k) % v = j.val := congrArg Fin.val hcon
  have hj := j.isLt
  by_cases h : j.val + k < v
  · rw [Nat.mod_eq_of_lt h] at hval
    omega
  · have h2 : v ≤ j.val + k := by omega
    rw [Nat.mod_eq_sub_mod h2] at hval
    have h3 : j.val + k - v < v := by omega
    rw [Nat.mod_eq_of_lt h3] at hval
    omega

/-! ### The circulant neighbourhood -/

/-- The degree-`2·dd` circulant neighbourhood of a coordinate: offsets `±1, …, ±dd`. -/
def circNbr (v : ℕ) (hv : 0 < v) (dd : ℕ) (j : Fin v) : Finset (Fin v) :=
  ((Finset.univ : Finset (Fin dd)).image (fun s => rot v hv j (s.val + 1)))
    ∪ ((Finset.univ : Finset (Fin dd)).image (fun s => rot v hv j (v - (s.val + 1))))

/-- **The degree bound (proved)**. -/
theorem circNbr_card (v : ℕ) (hv : 0 < v) (dd : ℕ) (j : Fin v) :
    (circNbr v hv dd j).card ≤ 2 * dd := by
  unfold circNbr
  have h1 : (((Finset.univ : Finset (Fin dd)).image
      (fun s => rot v hv j (s.val + 1)))).card ≤ dd := by
    apply le_trans Finset.card_image_le
    rw [Finset.card_univ, Fintype.card_fin]
  have h2 : (((Finset.univ : Finset (Fin dd)).image
      (fun s => rot v hv j (v - (s.val + 1))))).card ≤ dd := by
    apply le_trans Finset.card_image_le
    rw [Finset.card_univ, Fintype.card_fin]
  have h3 := Finset.card_union_le
    (((Finset.univ : Finset (Fin dd)).image (fun s => rot v hv j (s.val + 1))))
    (((Finset.univ : Finset (Fin dd)).image
      (fun s => rot v hv j (v - (s.val + 1)))))
  omega

/-- **The symmetry (proved)**: circulant adjacency is symmetric. -/
theorem circNbr_sym (v : ℕ) (hv : 0 < v) (dd : ℕ) (hddv : dd ≤ v) (a b : Fin v)
    (h : b ∈ circNbr v hv dd a) : a ∈ circNbr v hv dd b := by
  unfold circNbr at h ⊢
  rcases Finset.mem_union.mp h with h1 | h2
  · obtain ⟨s, -, hs⟩ := Finset.mem_image.mp h1
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨s, Finset.mem_univ s, ?_⟩
    rw [← hs]
    exact rot_rot_cancel' v hv a (s.val + 1) (by
      have := s.isLt
      omega)
  · obtain ⟨s, -, hs⟩ := Finset.mem_image.mp h2
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨s, Finset.mem_univ s, ?_⟩
    rw [← hs]
    exact rot_rot_cancel v hv a (s.val + 1) (by
      have := s.isLt
      omega)

/-- **Loop-freeness (proved)**: for `dd < v` the circulant has no self-loops. -/
theorem circNbr_no_self (v : ℕ) (hv : 0 < v) (dd : ℕ) (hddv : dd < v) (j : Fin v) :
    j ∉ circNbr v hv dd j := by
  intro h
  unfold circNbr at h
  rcases Finset.mem_union.mp h with h1 | h2
  · obtain ⟨s, -, hs⟩ := Finset.mem_image.mp h1
    have := s.isLt
    exact rot_ne_self v hv j (s.val + 1) (by omega) (by omega) hs
  · obtain ⟨s, -, hs⟩ := Finset.mem_image.mp h2
    have := s.isLt
    exact rot_ne_self v hv j (v - (s.val + 1)) (by omega) (by omega) hs

/-- **THE BRIDGE (proved)**: every route companion is a circulant neighbour of its pinned
coordinate. -/
theorem routeCompanion_mem_circNbr (v dd : ℕ) (hv : 0 < v)
    (j : Fin v) (ρ : PinRoute dd) (j'' : Fin v)
    (h : routeCompanion v hv j ρ = some j'') : j'' ∈ circNbr v hv dd j := by
  cases ρ with
  | direct =>
      simp [routeCompanion] at h
  | edgeLo s =>
      have hj'' : rot v hv j (s.val + 1) = j'' := Option.some.inj h
      unfold circNbr
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨s, Finset.mem_univ s, hj''⟩
  | edgeHi s =>
      have hj'' : rot v hv j (v - (s.val + 1)) = j'' := Option.some.inj h
      unfold circNbr
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨s, Finset.mem_univ s, hj''⟩

/-! ### The generic greedy bound -/

set_option maxHeartbeats 1600000 in
/-- **THE GENERIC GREEDY BOUND (proved)**: for any symmetric neighbourhood structure of
degree `≤ d`, every subset `U` contains an independent subset `I` with
`|U| ≤ (d+1)·|I|` — multiplicative, division-free.  No expansion, no spectra. -/
theorem greedy_indep (nbr : Fin v → Finset (Fin v)) (d : ℕ)
    (hdeg : ∀ j : Fin v, (nbr j).card ≤ d)
    (hsym : ∀ a b : Fin v, a ∈ nbr b → b ∈ nbr a)
    (U : Finset (Fin v)) :
    ∃ I ⊆ U, (∀ a ∈ I, ∀ b ∈ I, a ≠ b → b ∉ nbr a)
      ∧ U.card ≤ (d + 1) * I.card := by
  classical
  suffices h : ∀ n : ℕ, ∀ U : Finset (Fin v), U.card ≤ n →
      ∃ I ⊆ U, (∀ a ∈ I, ∀ b ∈ I, a ≠ b → b ∉ nbr a)
        ∧ U.card ≤ (d + 1) * I.card by
    exact h U.card U le_rfl
  intro n
  induction n with
  | zero =>
      intro U hU
      refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
      · intro a ha
        exact absurd ha (Finset.notMem_empty a)
      · rw [Finset.card_empty]
        omega
  | succ n ihn =>
      intro U hU
      by_cases hUe : U = ∅
      · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
        · intro a ha
          exact absurd ha (Finset.notMem_empty a)
        · rw [hUe, Finset.card_empty]
          omega
      · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hUe
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
        obtain ⟨I', hI'sub, hI'ind, hI'card⟩ := ihn U' (by omega)
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
        · have hUsub : U ⊆ U' ∪ insert u (nbr u) := by
            intro a ha
            by_cases h : a ∈ insert u (nbr u)
            · exact Finset.mem_union_right _ h
            · apply Finset.mem_union_left
              rw [hU', Finset.mem_sdiff]
              exact ⟨ha, h⟩
          have h1 := Finset.card_le_card hUsub
          have h2 := Finset.card_union_le U' (insert u (nbr u))
          have h3 := Finset.card_insert_le u (nbr u)
          have h4 := hdeg u
          have hcard' : (insert u I').card = I'.card + 1 :=
            Finset.card_insert_of_notMem huI'
          calc U.card ≤ U'.card + (d + 1) := by omega
            _ ≤ (d + 1) * I'.card + (d + 1) := by omega
            _ = (d + 1) * (I'.card + 1) := by ring
            _ = (d + 1) * (insert u I').card := by rw [hcard']

/-! ### The circulant instantiation — the E5 payoff -/

/-- **The circulant independent selection (proved)**: inside any subset `U`, an
independent set of size `≥ |U|/(2·dd+1)`, multiplicatively. -/
theorem circulant_indep_select (v dd : ℕ) (hv : 0 < v) (hddv : dd ≤ v)
    (U : Finset (Fin v)) :
    ∃ I ⊆ U, (∀ a ∈ I, ∀ b ∈ I, a ≠ b → b ∉ circNbr v hv dd a)
      ∧ U.card ≤ (2 * dd + 1) * I.card :=
  greedy_indep (circNbr v hv dd) (2 * dd)
    (circNbr_card v hv dd)
    (fun a b hab => circNbr_sym v hv dd hddv b a hab) U

/-- **Companion validity from independence (proved)**: if the priced set is independent
in the circulant, every route companion of every member avoids the whole set. -/
theorem indep_companion_valid (v dd : ℕ) (hv : 0 < v) (hddv : dd < v)
    (P : Finset (Fin v))
    (hind : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → b ∉ circNbr v hv dd a)
    (j' : Fin v) (hj' : j' ∈ P)
    (ρ : PinRoute dd) (j'' : Fin v)
    (h : routeCompanion v hv j' ρ = some j'') :
    j'' ∉ P := by
  intro hj''P
  have hmem : j'' ∈ circNbr v hv dd j' :=
    routeCompanion_mem_circNbr v dd hv j' ρ j'' h
  by_cases heq : j'' = j'
  · rw [heq] at hmem
    exact circNbr_no_self v hv dd hddv j' hmem
  · exact hind j' hj' j'' hj''P (fun hc => heq hc.symm) hmem

/-- **THE E5 PAYOFF (proved)**: inside ANY surviving column set `U`, a priced set `P`
carrying a `1/(2·dd+1)` fraction of `U` such that EVERY route companion of EVERY member
of `P` avoids `P` — the `hcomp` class of the extended drag discharges by pricing inside
`P`. -/
theorem circulant_priced_select (v dd : ℕ) (hv : 0 < v) (hddv : dd < v)
    (U : Finset (Fin v)) :
    ∃ P ⊆ U, U.card ≤ (2 * dd + 1) * P.card
      ∧ ∀ j' ∈ P, ∀ ρ : PinRoute dd, ∀ j'' : Fin v,
          routeCompanion v hv j' ρ = some j'' → j'' ∉ P := by
  obtain ⟨I, hIsub, hIind, hIcard⟩ :=
    circulant_indep_select v dd hv (le_of_lt hddv) U
  exact ⟨I, hIsub, hIcard, fun j' hj' ρ j'' h =>
    indep_companion_valid v dd hv hddv I hIind j' hj' ρ j'' h⟩

end PallLean.Paper93.DeepMath.PathB.NFrameCirculantLayer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCirculantLayer.circNbr_card
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCirculantLayer.circNbr_sym
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCirculantLayer.circNbr_no_self
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCirculantLayer.routeCompanion_mem_circNbr
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCirculantLayer.greedy_indep
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCirculantLayer.circulant_indep_select
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCirculantLayer.indep_companion_valid
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCirculantLayer.circulant_priced_select
