import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFramePinSlotAssembly

/-!
# N-Frame: the uniform bound — `coneExcess = Ω(√N)` at every band

Rung 21 of the multi-block arc (… → pin-slot assembly → **uniform bound**).  The closing
composition: per slot the min-form dichotomy gives FULL or SIGN-LIVE, and each of the three
global outcomes is priced:

  `sat3_full_mass_three` — **PROVED**: all three slots nearly full forces
        `3·m·(v−j) ≤ |S|` — the three slot regions are disjoint, so the full masses ADD.
        Three times stronger than the rung-17 escape; vacuous only at the genuine top band,
        where root-like cuts really do have small width.
  `sat3_uniform_window_horn` — **PROVED, the mixed-case killer**: one full slot `t*` plus one
        live sign column `t₀` forces `m ≤ 2j + 48`.  The straddle law converts nearly-full
        into `≥ m − j` blocks FULLY-in; the parametric window (data through the `t*`-swap,
        pins routed to `swapSlotF t* t₀`) then prices an `(m/8) × (m/8)` rectangle at `j`.
  `sat3_uniform_cut_bound` — **PROVED, the assembled cut theorem**: for every cut,
        `|S| ≤ 12j + 3v + 9`  ∨  `3·m·(v−j) ≤ |S|`  ∨  `m ≤ 6j + 48`  ∨  `v ≤ 2j`.
  `sat3_uniform_band_bound` — **PROVED, THE UNIFORM BOUND**: at every band of a minimal SAT
        circuit,
        `T ≤ 12·(CE+1) + 3v + 9  ∨  3·m·(v−(CE+1)) ≤ 2T−2  ∨  m ≤ 6·(CE+1)+48  ∨  v ≤ 2·(CE+1)`.

Every horn lower-bounds `coneExcess` in band parameters: on bands `T ∈ [Θ(v), c·m·v]` with
`c < 3/2` each horn gives `coneExcess = Ω(m) = Ω(√N)` — uniformly, including the heavy bands
where rung 17 degraded, with no `hvars`-style hypotheses beyond the band's existence.

## Honest scope

This closes the pin framework at its ceiling: `coneExcess = Ω(√N)` at every band, hence
`cbudget ≥ 2·live + Ω(√N)`-strength in the restricted wire model.  Beyond `Ω(√N)` — the
`(2+c)·N` question — is blocked by the straddle/pool ceiling established at rung 20: `j`
straddling blocks may lawfully carry `j·v` mass, and no instrument in this framework prices
that configuration beyond `Ω(m)`.  The arc now pivots to composition/hierarchy design
(amplification beyond a single cut) — a design problem, not a Lean problem, until the
mathematics is settled.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The three-slot full mass -/

set_option maxHeartbeats 3200000 in
/-- **The three-slot full mass (proved)**: all slots nearly full forces `3·m·(v−j) ≤ |S|` —
the slot regions are disjoint, so the masses add. -/
theorem sat3_full_mass_three (N : ℕ) {S : Finset (Fin N)} {j : ℕ}
    (hout : ∀ (t : Fin 3) (c : Fin (sat3M N)),
      ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c t w.val (by have := w.isLt; omega) ∉ S)).card ≤ j) :
    3 * (sat3M N * (sat3V N - j)) ≤ S.card := by
  classical
  set img : Fin (sat3M N) × Fin 3 → Finset (Fin N) := fun ct =>
    ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N ct.1 ct.2 w.val (by have := w.isLt; omega) ∈ S)).image
      (fun w : Fin (sat3V N) =>
        sat3Bit N ct.1 ct.2 w.val (by have := w.isLt; omega))
    with himg
  have hdisj : (↑(Finset.univ : Finset (Fin (sat3M N) × Fin 3))
      : Set (Fin (sat3M N) × Fin 3)).PairwiseDisjoint img := by
    intro ct _ ct' _ hne
    show Disjoint (img ct) (img ct')
    apply Finset.disjoint_left.mpr
    intro b hb hb'
    rw [himg] at hb hb'
    obtain ⟨w, -, hw⟩ := Finset.mem_image.mp hb
    obtain ⟨w', -, hw'⟩ := Finset.mem_image.mp hb'
    apply hne
    have h1 : b.val / sat3D N = ct.1.val := by
      rw [← hw]
      exact sat3Bit_clause N ct.1 ct.2 w.val (by have := w.isLt; omega)
    have h2 : b.val / sat3D N = ct'.1.val := by
      rw [← hw']
      exact sat3Bit_clause N ct'.1 ct'.2 w'.val (by have := w'.isLt; omega)
    have hr1 : b.val % sat3D N = ct.2.val * (sat3V N + 1) + w.val := by
      rw [← hw]
      exact sat3Bit_rem N ct.1 ct.2 w.val (by have := w.isLt; omega)
    have hr2 : b.val % sat3D N = ct'.2.val * (sat3V N + 1) + w'.val := by
      rw [← hw']
      exact sat3Bit_rem N ct'.1 ct'.2 w'.val (by have := w'.isLt; omega)
    have hts := slotField_eq ct.2 ct'.2
      (by have := w.isLt; omega) (by have := w'.isLt; omega)
      (hr1.symm.trans hr2)
    apply Prod.ext
    · exact Fin.ext (h1.symm.trans h2)
    · exact hts.1
  have hsub : Finset.univ.biUnion img ⊆ S := by
    intro b hb
    obtain ⟨ct, -, hbc⟩ := Finset.mem_biUnion.mp hb
    rw [himg] at hbc
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hbc
    exact (Finset.mem_filter.mp hw).2
  have hper : ∀ ct : Fin (sat3M N) × Fin 3, sat3V N - j ≤ (img ct).card := by
    intro ct
    have hinj : Set.InjOn (fun w : Fin (sat3V N) =>
        sat3Bit N ct.1 ct.2 w.val (by have := w.isLt; omega))
        ↑((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N ct.1 ct.2 w.val (by have := w.isLt; omega) ∈ S)) := by
      intro w _ w' _ hww
      have hval := congrArg Fin.val hww
      apply Fin.ext
      show w.val = w'.val
      have h1 : ct.1.val * sat3D N + ct.2.val * (sat3V N + 1) + w.val
          = ct.1.val * sat3D N + ct.2.val * (sat3V N + 1) + w'.val := hval
      omega
    have hcard : (img ct).card
        = ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N ct.1 ct.2 w.val (by have := w.isLt; omega) ∈ S)).card := by
      rw [himg]
      exact Finset.card_image_of_injOn hinj
    have hcv := univ_filter_cover_card (fun w : Fin (sat3V N) =>
      sat3Bit N ct.1 ct.2 w.val (by have := w.isLt; omega) ∈ S)
    rw [Fintype.card_fin] at hcv
    have := hout ct.2 ct.1
    omega
  calc 3 * (sat3M N * (sat3V N - j))
      = ∑ _ct : Fin (sat3M N) × Fin 3, (sat3V N - j) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, Fintype.card_fin, smul_eq_mul]
        ring
    _ ≤ ∑ ct : Fin (sat3M N) × Fin 3, (img ct).card :=
        Finset.sum_le_sum (fun ct _ => hper ct)
    _ = (Finset.univ.biUnion img).card := (Finset.card_biUnion hdisj).symm
    _ ≤ S.card := Finset.card_le_card hsub

/-! ### The mixed-case window horn -/

set_option maxHeartbeats 3200000 in
/-- **The mixed-case killer (proved)**: one full slot plus one live sign column forces
`m ≤ 2j + 48` — the straddle law makes `≥ m − j` blocks fully-in, and the parametric window
prices an `(m/8) × (m/8)` rectangle at `j`. -/
theorem sat3_uniform_window_horn (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (tstar t0 : Fin 3)
    (hfull : ∀ c : Fin (sat3M N),
      ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c tstar w.val (by have := w.isLt; omega) ∉ S)).card ≤ j)
    (hlive : ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b t0 (sat3V N) (by omega) ∈ S)).card ≤ j + 2)
    (hvj : 2 * j + 1 ≤ sat3V N) :
    sat3M N ≤ 2 * j + 48 := by
  classical
  by_cases hm48 : sat3M N ≤ 2 * j + 48
  · exact hm48
  push_neg at hm48
  exfalso
  have hmv : sat3M N - 1 ≤ sat3V N := sat3M_pred_le_sat3V N
  -- transfer to the swapped world: data slot 0, pins at ps'
  set S' : Finset (Fin N) := S.image (slotSwapBit N tstar) with hS'
  have hcut' : CutFactorization (sat3Family N) S' j :=
    cut_transport (sat3Family N) (slotSwapBit N tstar)
      (slotSwapBit_invol N tstar) (sat3Family_slotSwap N tstar) hcut
  have hswz : swapSlotF tstar ⟨0, by omega⟩ = tstar := swapSlotF_zero tstar (by omega)
  have hfull' : ∀ c : Fin (sat3M N),
      ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∉ S')).card ≤ j := by
    intro c
    have heq : ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∉ S'))
        = ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c tstar w.val (by have := w.isLt; omega) ∉ S)) := by
      ext w
      rw [Finset.mem_filter, Finset.mem_filter, hS', sat3_bit_mem_swap, hswz]
    rw [heq]
    exact hfull c
  set ps' : Fin 3 := swapSlotF tstar t0 with hps'
  have hQ' : ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ps' (sat3V N) (by omega) ∈ S')).card
      = ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b t0 (sat3V N) (by omega) ∈ S)).card := by
    congr 1
    ext b
    rw [Finset.mem_filter, Finset.mem_filter, hS', sat3_bit_mem_swap, hps',
      swapSlotF_invol]
  -- almost all blocks are fully-in in the swapped world
  have hstraddle := sat3_straddle_census N hv hcut'
  have hAllIncard : sat3M N - j
      ≤ ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        ∀ w : Fin (sat3V N),
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')).card := by
    have hsplit := univ_filter_cover_card (fun c : Fin (sat3M N) =>
      ∀ w : Fin (sat3V N),
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')
    rw [Fintype.card_fin] at hsplit
    have hnotsub : ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        ¬ ∀ w : Fin (sat3V N),
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S'))
        ⊆ ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        (∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S')
        ∧ (∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
          (by have := w.isLt; omega) ∉ S'))) := by
      intro c hc
      have hc2 := (Finset.mem_filter.mp hc).2
      rw [not_forall] at hc2
      obtain ⟨w, hw⟩ := hc2
      have hcv := univ_filter_cover_card (fun w : Fin (sat3V N) =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')
      rw [Fintype.card_fin] at hcv
      have hfc := hfull' c
      have hinpos : 0 < ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')).card := by
        omega
      obtain ⟨w', hw'⟩ := Finset.card_pos.mp hinpos
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ c,
        ⟨w', (Finset.mem_filter.mp hw').2⟩, ⟨w, hw⟩⟩
    have hnotle := (Finset.card_le_card hnotsub).trans hstraddle
    omega
  -- the (m/8) × (m/8) window
  set q : ℕ := sat3M N / 8 with hq
  obtain ⟨C', hC'sub, hC'card⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      ∀ w : Fin (sat3V N),
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S'))
    (n := q) (by omega)
  obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin (sat3V N)))) (n := q)
    (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  have hbu : (C'.biUnion (fun _ => W)).card ≤ q := by
    have h := Finset.card_le_card (Finset.biUnion_subset.mpr
      (fun (c : Fin (sat3M N)) (_ : c ∈ C') => Finset.Subset.refl W))
    omega
  have hQpool : ((((Finset.univ : Finset (Fin (sat3M N))) \ C')).filter (fun b =>
      sat3Bit N b ps' (sat3V N) (by omega) ∈ S')).card ≤ j + 2 := by
    have hQsub : ((((Finset.univ : Finset (Fin (sat3M N))) \ C')).filter (fun b =>
        sat3Bit N b ps' (sat3V N) (by omega) ∈ S')).card
        ≤ ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
        sat3Bit N b ps' (sat3V N) (by omega) ∈ S')).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
    rw [hQ'] at hQsub
    exact hQsub.trans hlive
  have hwin := sat3_pinslot_window N hv hcut' C' ps' (fun _ => W)
    (fun c hc w hw => (Finset.mem_filter.mp (hC'sub hc)).2 w)
    (by omega)
    (by omega)
    (by omega)
  have hsum : ∑ c ∈ C', ((fun _ : Fin (sat3M N) => W) c).card = q * q := by
    rw [Finset.sum_const, smul_eq_mul, hC'card, hWcard]
  rw [hsum] at hwin
  -- q·q ≤ j contradicts m > 2j + 48
  have hq6 : 6 ≤ q := by omega
  have hqq : 6 * q ≤ q * q := Nat.mul_le_mul_right q hq6
  omega

/-! ### The assembled cut theorem -/

set_option maxHeartbeats 1600000 in
/-- **THE ASSEMBLED CUT THEOREM (proved)**: for every cut factorization,
`|S| ≤ 12j + 3v + 9`, or `3·m·(v−j) ≤ |S|`, or `j` is `m`/`v`-scale. -/
theorem sat3_uniform_cut_bound (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j) :
    S.card ≤ 12 * j + 3 * sat3V N + 9
    ∨ 3 * (sat3M N * (sat3V N - j)) ≤ S.card
    ∨ sat3M N ≤ 6 * j + 48
    ∨ sat3V N ≤ 2 * j := by
  classical
  by_cases hvj : 2 * j + 1 ≤ sat3V N
  · by_cases hm6 : 2 * j + 6 ≤ sat3M N
    · have hk : (sat3M N - 2) + 1 ≤ sat3M N := by omega
      rcases sat3_slot_dichotomy N hv hk hcut ⟨0, by omega⟩ hm6 hvj with
        hf0 | ⟨-, hl0⟩
      · rcases sat3_slot_dichotomy N hv hk hcut ⟨1, by omega⟩ hm6 hvj with
          hf1 | ⟨-, hl1⟩
        · rcases sat3_slot_dichotomy N hv hk hcut ⟨2, by omega⟩ hm6 hvj with
            hf2 | ⟨-, hl2⟩
          · -- all full
            refine Or.inr (Or.inl (sat3_full_mass_three N ?_))
            intro t c
            rcases t with ⟨tv, htv⟩
            interval_cases tv
            · exact hf0 c
            · exact hf1 c
            · exact hf2 c
          · -- full at 0, live at 2
            exact Or.inr (Or.inr (Or.inl (by
              have := sat3_uniform_window_horn N hv hcut ⟨0, by omega⟩ ⟨2, by omega⟩
                hf0 hl2 hvj
              omega)))
        · -- full at 0, live at 1
          exact Or.inr (Or.inr (Or.inl (by
            have := sat3_uniform_window_horn N hv hcut ⟨0, by omega⟩ ⟨1, by omega⟩
              hf0 hl1 hvj
            omega)))
      · rcases sat3_slot_dichotomy N hv hk hcut ⟨1, by omega⟩ hm6 hvj with
          hf1 | ⟨-, hl1⟩
        · -- full at 1, live at 0
          exact Or.inr (Or.inr (Or.inl (by
            have := sat3_uniform_window_horn N hv hcut ⟨1, by omega⟩ ⟨0, by omega⟩
              hf1 hl0 hvj
            omega)))
        · rcases sat3_slot_dichotomy N hv hk hcut ⟨2, by omega⟩ hm6 hvj with
            hf2 | ⟨-, hl2⟩
          · -- full at 2, live at 0
            exact Or.inr (Or.inr (Or.inl (by
              have := sat3_uniform_window_horn N hv hcut ⟨2, by omega⟩ ⟨0, by omega⟩
                hf2 hl0 hvj
              omega)))
          · -- all live: budgets + ledger
            rcases sat3_private_budget N hv hcut with h0 | h0
            · rcases sat3_private_budget_slot1 N hv hcut with h1 | h1
              · rcases sat3_private_budget_slot2 N hv hcut with h2 | h2
                · left
                  have hled := sat3_grid_mass_ledger N S
                  omega
                · exact Or.inr (Or.inr (Or.inl (by omega)))
              · exact Or.inr (Or.inr (Or.inl (by omega)))
            · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

/-! ### The uniform band bound -/

/-- **THE UNIFORM BOUND (proved)**: at every band of a minimal SAT circuit, every horn
lower-bounds `coneExcess` in band parameters — `coneExcess = Ω(m) = Ω(√N)` on all bands
`T ∈ [Θ(v), c·m·v]`, `c < 3/2`, uniformly, heavy bands included. -/
theorem sat3_uniform_band_bound (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N))
    (T : ℕ) (hT : 2 ≤ T)
    (hband : 2 * T - 1 ≤ (varsOf cc (cc.length - 1)).card) :
    T ≤ 12 * (coneExcess cc (cc.length - 1) + 1) + 3 * sat3V N + 9
    ∨ 3 * (sat3M N * (sat3V N - (coneExcess cc (cc.length - 1) + 1))) ≤ 2 * T - 2
    ∨ sat3M N ≤ 6 * (coneExcess cc (cc.length - 1) + 1) + 48
    ∨ sat3V N ≤ 2 * (coneExcess cc (cc.length - 1) + 1) := by
  classical
  obtain ⟨S, hT1, hT2, j, hj, hcut⟩ :=
    sat3_balanced_cut N hv hm3 hk cc hcomp hmin T hT hband
  rcases sat3_uniform_cut_bound N hv hcut with h | h | h | h
  · left
    omega
  · right
    left
    have hmono : 3 * (sat3M N * (sat3V N - (coneExcess cc (cc.length - 1) + 1)))
        ≤ 3 * (sat3M N * (sat3V N - j)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hj _))
    omega
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_full_mass_three
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_uniform_window_horn
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_uniform_cut_bound
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_uniform_band_bound
