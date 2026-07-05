import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSlotTOneBit

/-!
# N-Frame: the global interface bound — every two-sided cut pays `Ω(m)`

The final case-count.  `GlobalPACInterfaceBound` becomes a **theorem** (under the exact layout):
every interfaced factorization of `sat3Family` whose two exclusive sides are both nonempty pays an
`Ω(m)` interface —

    `sat3M N ≤ 2 · |A ∩ B| + 4`.

No essentiality hypothesis is needed: under `hDN` every coordinate is a `sat3Bit`.  The proof is the
fusion of the whole Track C arc.  Sign trichotomy first; the aligned-right branch reduces to
aligned-left by swapping the factor roles, so only left-side machinery is consumed.  In the
aligned-left branch the exclusive-right witness `q` is classified by the layout:

* `q` a **selector**: if block `q` has a left selector and some other block has one, anchored
  capture kills `q`; otherwise an entire block's slot-0 pinned selector column is off the left side,
  and the one-bit escape bound plus an interning count give `m ≤ 2|W| + 3`.
* `q` a **sign**: the menu law fires.  Pinned menu offside — same column count.  Free menu offside —
  with anchors, every unpinned slot-`t'` selector of the block is interned (`≥ 2m + 2` of them by
  the layout bound `3m ≤ v`), and without anchors the column count fires again.

  `sat3_three_m_le_sat3V` — the layout bound `3m ≤ v` (extracted from the pinning admissibility).
  `sat3_offside_pinned_count` — **PROVED**: a block with its whole slot-`t` pinned selector column
        off the left side forces `m ≤ 2|W| + 3`.
  `sat3_aligned_left_qkill` — **PROVED, the core**: aligned-left + any exclusive-right coordinate
        forces `m ≤ 2|W| + 4`.
  `sat3_global_interface_bound` — **PROVED, the assembly**: both exclusive sides nonempty forces
        `m ≤ 2|W| + 4`.
  `sat3_GlobalPACInterfaceBound` — **PROVED, the headline**: `GlobalPACInterfaceBound N` holds —
        HAL's `every_adversarial_cut_crosses_many_positive_cells` cash-out, discharged.

## Honest scope

This bounds **coordinate-interfaced factorizations**.  The remaining Track C mountain is the
**wire-frontier → coordinate-interface extraction** (`coneExcess ≤ k` ⇒ such a factorization with
`|A ∩ B|` bounded in `k`), which would convert this into `coneExcess ≥ Ω(m)` and
`cbudget ≥ 2N + Ω(m)`.  Beyond that: dimension hierarchy, observer-captures-P — `P ≠ NP`-strength,
open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- The layout bound `3m ≤ v`, extracted from pinning admissibility. -/
theorem sat3_three_m_le_sat3V (N : ℕ) : 3 * sat3M N ≤ sat3V N := by
  have h1 : sat3M N * sat3D N ≤ N := Nat.div_mul_le_self N (sat3D N)
  have h2 : N < (sat3V N + 1) * (sat3V N + 1) := Nat.lt_succ_sqrt N
  have h3 : sat3M N * 3 * (sat3V N + 1) = sat3M N * sat3D N := by
    show sat3M N * 3 * (sat3V N + 1) = sat3M N * (3 * (sat3V N + 1))
    rw [Nat.mul_assoc]
  have h4 : sat3M N * 3 * (sat3V N + 1) < (sat3V N + 1) * (sat3V N + 1) := by omega
  have h5 : sat3M N * 3 < sat3V N + 1 := lt_of_mul_lt_mul_right h4 (Nat.zero_le _)
  omega

/-- **THE OFFSIDE-COLUMN COUNT (proved)**: a block whose slot-`t` pinned selector column avoids
`A \ B` forces `m ≤ 2|A ∩ B| + 3` — escapes are bounded by the one-bit law, the rest are interned. -/
theorem sat3_offside_pinned_count (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (haligned : ∀ c' : Fin (sat3M N), sat3SignBit N c' ∉ A ∩ B →
      sat3SignBit N c' ∈ A \ B)
    (c : Fin (sat3M N)) (t : Fin 3)
    (hoff : ∀ w₀ : Fin (sat3M N - 2), sat3Bit N c t w₀.val
      (by have := sat3M_pred_le_sat3V N; have := w₀.isLt; omega) ∉ A \ B) :
    sat3M N ≤ 2 * (A ∩ B).card + 3 := by
  classical
  have hesc := sat3_slotT_escape_bound_left N hv hm3 hk op g h A B hg hh hf
    haligned c t
  have hint : ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
      sat3Bit N c t j.val
        (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ A ∩ B)).card
      ≤ (A ∩ B).card := by
    apply Finset.card_le_card_of_injOn
      (fun j : Fin (sat3M N - 2) => sat3Bit N c t j.val
        (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega))
    · intro j hj
      exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
    · intro x hx y hy hxy
      by_contra hne
      exact sat3Bit_ne_of_field N _ _ _ _
        (fun hcon => hne (Fin.ext hcon)) hxy
  have hcover : (Finset.univ : Finset (Fin (sat3M N - 2)))
      ⊆ ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
          sat3Bit N c t j.val
            (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ B \ A))
        ∪ ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
          sat3Bit N c t j.val
            (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ A ∩ B)) := by
    intro j _
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    have hu := sat3_sel_mem_union N hv op g h A B hg hh hf c t
      ⟨j.val, by have := sat3M_pred_le_sat3V N; have := j.isLt; omega⟩
    rw [Finset.mem_union] at hu
    have hoffj := hoff j
    by_cases hA : sat3Bit N c t j.val
        (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ A
    · right
      refine ⟨Finset.mem_univ j, Finset.mem_inter.mpr ⟨hA, ?_⟩⟩
      by_contra hB
      exact hoffj (Finset.mem_sdiff.mpr ⟨hA, hB⟩)
    · left
      refine ⟨Finset.mem_univ j, Finset.mem_sdiff.mpr ⟨?_, hA⟩⟩
      rcases hu with h1 | h1
      · exact absurd h1 hA
      · exact h1
  have hm2 : sat3M N - 2
      ≤ ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
          sat3Bit N c t j.val
            (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ B \ A)).card
        + ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
          sat3Bit N c t j.val
            (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ A ∩ B)).card := by
    calc sat3M N - 2 = (Finset.univ : Finset (Fin (sat3M N - 2))).card := by
          rw [Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.card_le_card hcover
      _ ≤ _ := Finset.card_union_le _ _
  omega

set_option maxHeartbeats 1600000 in
/-- **THE CORE KILL (proved)**: aligned-left plus any exclusive-right coordinate forces
`m ≤ 2|A ∩ B| + 4`. -/
theorem sat3_aligned_left_qkill (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hDN : sat3M N * sat3D N = N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (haligned : ∀ c' : Fin (sat3M N), sat3SignBit N c' ∉ A ∩ B →
      sat3SignBit N c' ∈ A \ B)
    (q : Fin N) (hq : q ∈ B \ A) :
    sat3M N ≤ 2 * (A ∩ B).card + 4 := by
  classical
  have hD0 : 0 < sat3D N := sat3D_pos N
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  have hqlt : q.val < sat3M N * sat3D N := by
    rw [hDN]
    exact q.isLt
  have hcq : q.val / sat3D N < sat3M N := (Nat.div_lt_iff_lt_mul hD0).mpr hqlt
  set cq : Fin (sat3M N) := ⟨q.val / sat3D N, hcq⟩ with hcqdef
  have hrem : q.val % sat3D N < sat3D N := Nat.mod_lt _ hD0
  have hD3 : sat3D N = 3 * (sat3V N + 1) := rfl
  have htq3 : q.val % sat3D N / (sat3V N + 1) < 3 :=
    (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
  set tq : Fin 3 := ⟨q.val % sat3D N / (sat3V N + 1), htq3⟩ with htqdef
  have hfld : q.val % sat3D N % (sat3V N + 1) < sat3V N + 1 :=
    Nat.mod_lt _ (by omega)
  have hqval : q.val = q.val / sat3D N * sat3D N
      + q.val % sat3D N / (sat3V N + 1) * (sat3V N + 1)
      + q.val % sat3D N % (sat3V N + 1) := by
    have hdm1 := Nat.div_add_mod q.val (sat3D N)
    have hdm2 := Nat.div_add_mod (q.val % sat3D N) (sat3V N + 1)
    have hcm1 : sat3D N * (q.val / sat3D N)
        = q.val / sat3D N * sat3D N := Nat.mul_comm _ _
    have hcm2 : (sat3V N + 1) * (q.val % sat3D N / (sat3V N + 1))
        = q.val % sat3D N / (sat3V N + 1) * (sat3V N + 1) := Nat.mul_comm _ _
    omega
  rcases Nat.lt_or_ge (q.val % sat3D N % (sat3V N + 1)) (sat3V N) with hsel | hsg
  · -- q is a SELECTOR
    set jq : Fin (sat3V N) := ⟨q.val % sat3D N % (sat3V N + 1), hsel⟩ with hjqdef
    have hqbit : q = sat3Bit N cq tq jq.val (by have := jq.isLt; omega) := by
      apply Fin.ext
      show q.val = q.val / sat3D N * sat3D N
        + q.val % sat3D N / (sat3V N + 1) * (sat3V N + 1)
        + q.val % sat3D N % (sat3V N + 1)
      exact hqval
    rw [hqbit] at hq
    by_cases hyL : ∃ (ty : Fin 3) (jy : Fin (sat3V N)),
        sat3Bit N cq ty jy.val (by have := jy.isLt; omega) ∈ A \ B
    · by_cases hzL : ∃ (c' : Fin (sat3M N)) (_ : c'.val ≠ cq.val) (tz : Fin 3)
          (jz : Fin (sat3V N)),
          sat3Bit N c' tz jz.val (by have := jz.isLt; omega) ∈ A \ B
      · obtain ⟨ty, jy, hy⟩ := hyL
        obtain ⟨c', hcc, tz, jz, hz⟩ := hzL
        have hyq : sat3Bit N cq ty jy.val (by have := jy.isLt; omega)
            ≠ sat3Bit N cq tq jq.val (by have := jq.isLt; omega) := by
          intro heq
          rw [heq] at hy
          exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_sdiff.mp hy).1
        have hIq : sat3Bit N cq tq jq.val (by have := jq.isLt; omega) ∉ A ∩ B :=
          fun hW => (Finset.mem_sdiff.mp hq).2 (Finset.mem_inter.mp hW).1
        have hcap := sat3_anchored_selector_capture_left N hv op g h A B
          hg hh hf cq tq jq ty jy hyq hy c' hcc tz jz hz hIq
        exact absurd (Finset.mem_sdiff.mp hcap).1 (Finset.mem_sdiff.mp hq).2
      · push_neg at hzL
        have hex : ∃ c'' : Fin (sat3M N), c''.val ≠ cq.val := by
          by_cases h0 : cq.val = 0
          · exact ⟨⟨1, by omega⟩, by
              intro hcon
              have h1 : (1 : ℕ) = cq.val := hcon
              omega⟩
          · exact ⟨⟨0, by omega⟩, by
              intro hcon
              have h1 : (0 : ℕ) = cq.val := hcon
              exact h0 h1.symm⟩
        obtain ⟨c'', hne''⟩ := hex
        have hcount := sat3_offside_pinned_count N hv hm3 hk op g h A B
          hg hh hf haligned c'' ⟨0, by omega⟩
          (fun w₀ => hzL c'' hne'' ⟨0, by omega⟩
            ⟨w₀.val, by have := sat3M_pred_le_sat3V N; have := w₀.isLt; omega⟩)
        omega
    · push_neg at hyL
      have hcount := sat3_offside_pinned_count N hv hm3 hk op g h A B
        hg hh hf haligned cq ⟨0, by omega⟩
        (fun w₀ => hyL ⟨0, by omega⟩
          ⟨w₀.val, by have := sat3M_pred_le_sat3V N; have := w₀.isLt; omega⟩)
      omega
  · -- q is a SIGN
    have hqv : q.val % sat3D N % (sat3V N + 1) = sat3V N := by omega
    have hqbit : q = sat3Bit N cq tq (sat3V N) (by omega) := by
      apply Fin.ext
      show q.val = q.val / sat3D N * sat3D N
        + q.val % sat3D N / (sat3V N + 1) * (sat3V N + 1) + sat3V N
      omega
    rw [hqbit] at hq
    rcases sat3_sign_escape_forces_menu_left N hv hm3 hk op g h A B
      hg hh hf cq tq hq with hfree | hpin
    · by_cases hyL : ∃ (ty : Fin 3) (jy : Fin (sat3V N)),
          sat3Bit N cq ty jy.val (by have := jy.isLt; omega) ∈ A \ B
      · by_cases hzL : ∃ (c' : Fin (sat3M N)) (_ : c'.val ≠ cq.val) (tz : Fin 3)
            (jz : Fin (sat3V N)),
            sat3Bit N c' tz jz.val (by have := jz.isLt; omega) ∈ A \ B
        · -- anchors exist: the whole unpinned slot-t' column of cq is interned
          obtain ⟨ty, jy, hy⟩ := hyL
          obtain ⟨c', hcc, tz, jz, hz⟩ := hzL
          have hext' : ∃ t' : Fin 3, t' ≠ tq := by
            by_cases h0 : tq.val = 0
            · exact ⟨⟨1, by omega⟩, by
                intro hcon
                have h1 : (1 : ℕ) = tq.val := congrArg Fin.val hcon
                omega⟩
            · exact ⟨⟨0, by omega⟩, by
                intro hcon
                have h1 : (0 : ℕ) = tq.val := congrArg Fin.val hcon
                omega⟩
          obtain ⟨t', htt'⟩ := hext'
          have hallint : ∀ jF : Fin (sat3V N), sat3M N - 2 ≤ jF.val →
              sat3Bit N cq t' jF.val (by have := jF.isLt; omega) ∈ A ∩ B := by
            intro jF hjF
            have hoffx := hfree t' htt' jF hjF
            have hu := sat3_sel_mem_union N hv op g h A B hg hh hf cq t' jF
            rw [Finset.mem_union] at hu
            by_cases hxB : sat3Bit N cq t' jF.val
                (by have := jF.isLt; omega) ∈ B \ A
            · exfalso
              have hyx : sat3Bit N cq ty jy.val (by have := jy.isLt; omega)
                  ≠ sat3Bit N cq t' jF.val (by have := jF.isLt; omega) := by
                intro heq
                rw [heq] at hy
                exact (Finset.mem_sdiff.mp hxB).2 (Finset.mem_sdiff.mp hy).1
              have hIx : sat3Bit N cq t' jF.val
                  (by have := jF.isLt; omega) ∉ A ∩ B :=
                fun hW => (Finset.mem_sdiff.mp hxB).2 (Finset.mem_inter.mp hW).1
              have hcapx := sat3_anchored_selector_capture_left N hv op g h A B
                hg hh hf cq t' jF ty jy hyx hy c' hcc tz jz hz hIx
              exact (Finset.mem_sdiff.mp hxB).2 (Finset.mem_sdiff.mp hcapx).1
            · rcases hu with hA | hB
              · refine Finset.mem_inter.mpr ⟨hA, ?_⟩
                by_contra hB
                exact hoffx (Finset.mem_sdiff.mpr ⟨hA, hB⟩)
              · by_cases hA : sat3Bit N cq t' jF.val
                    (by have := jF.isLt; omega) ∈ A
                · exact Finset.mem_inter.mpr ⟨hA, hB⟩
                · exact absurd (Finset.mem_sdiff.mpr ⟨hB, hA⟩) hxB
          have hle : ((Finset.univ : Finset (Fin (sat3V N))).filter
              (fun jF => sat3M N - 2 ≤ jF.val)).card ≤ (A ∩ B).card := by
            apply Finset.card_le_card_of_injOn
              (fun jF : Fin (sat3V N) => sat3Bit N cq t' jF.val
                (by have := jF.isLt; omega))
            · intro jF hjF
              have hm := Finset.mem_filter.mp (Finset.mem_coe.mp hjF)
              exact Finset.mem_coe.mpr (hallint jF hm.2)
            · intro x hx y hy' hxy
              by_contra hne
              exact sat3Bit_ne_of_field N _ _ _ _
                (fun hcon => hne (Fin.ext hcon)) hxy
          have hcover2 : (Finset.univ : Finset (Fin (sat3V N)))
              ⊆ ((Finset.univ : Finset (Fin (sat3V N))).filter
                  (fun jF => sat3M N - 2 ≤ jF.val))
                ∪ Finset.univ.map (Fin.castLEEmb hkv) := by
            intro jF _
            rw [Finset.mem_union]
            by_cases hge : sat3M N - 2 ≤ jF.val
            · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hge⟩)
            · right
              rw [Finset.mem_map]
              refine ⟨⟨jF.val, by omega⟩, Finset.mem_univ _, ?_⟩
              apply Fin.ext
              rfl
          have hvtotal : sat3V N
              ≤ ((Finset.univ : Finset (Fin (sat3V N))).filter
                  (fun jF => sat3M N - 2 ≤ jF.val)).card + (sat3M N - 2) := by
            calc sat3V N = (Finset.univ : Finset (Fin (sat3V N))).card := by
                  rw [Finset.card_univ, Fintype.card_fin]
              _ ≤ _ := Finset.card_le_card hcover2
              _ ≤ _ := Finset.card_union_le _ _
              _ = _ := by
                  rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
          have h3m := sat3_three_m_le_sat3V N
          omega
        · push_neg at hzL
          have hex : ∃ c'' : Fin (sat3M N), c''.val ≠ cq.val := by
            by_cases h0 : cq.val = 0
            · exact ⟨⟨1, by omega⟩, by
                intro hcon
                have h1 : (1 : ℕ) = cq.val := hcon
                omega⟩
            · exact ⟨⟨0, by omega⟩, by
                intro hcon
                have h1 : (0 : ℕ) = cq.val := hcon
                exact h0 h1.symm⟩
          obtain ⟨c'', hne''⟩ := hex
          have hcount := sat3_offside_pinned_count N hv hm3 hk op g h A B
            hg hh hf haligned c'' ⟨0, by omega⟩
            (fun w₀ => hzL c'' hne'' ⟨0, by omega⟩
              ⟨w₀.val, by have := sat3M_pred_le_sat3V N; have := w₀.isLt; omega⟩)
          omega
      · push_neg at hyL
        have hcount := sat3_offside_pinned_count N hv hm3 hk op g h A B
          hg hh hf haligned cq ⟨0, by omega⟩
          (fun w₀ => hyL ⟨0, by omega⟩
            ⟨w₀.val, by have := sat3M_pred_le_sat3V N; have := w₀.isLt; omega⟩)
        omega
    · have hcount := sat3_offside_pinned_count N hv hm3 hk op g h A B
        hg hh hf haligned cq tq hpin
      omega

/-- **THE GLOBAL INTERFACE BOUND (proved)**: both exclusive sides nonempty forces
`m ≤ 2|A ∩ B| + 4` — every genuinely two-sided cut pays `Ω(m)` interface. -/
theorem sat3_global_interface_bound (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hDN : sat3M N * sat3D N = N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (p : Fin N) (hp : p ∈ A \ B) (q : Fin N) (hq : q ∈ B \ A) :
    sat3M N ≤ 2 * (A ∩ B).card + 4 := by
  rcases sat3_sign_alignment_or_interface N hv hm3 hk op g h A B hg hh hf
    with hL | hR | hC
  · exact sat3_aligned_left_qkill N hv hm3 hk hDN op g h A B hg hh hf hL q hq
  · have halR : ∀ c' : Fin (sat3M N), sat3SignBit N c' ∉ B ∩ A →
        sat3SignBit N c' ∈ B \ A := by
      intro c' hc'
      apply hR
      intro hW
      exact hc' (Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hW).2, (Finset.mem_inter.mp hW).1⟩)
    have hswap := sat3_aligned_left_qkill N hv hm3 hk hDN (fun x y => op y x)
      h g B A hh hg hf halR p hp
    have hint : (B ∩ A).card = (A ∩ B).card := by
      rw [Finset.inter_comm]
    omega
  · omega

/-- **THE HEADLINE (proved)**: `GlobalPACInterfaceBound N` holds under the exact layout — HAL's
`every_adversarial_cut_crosses_many_positive_cells` cash-out is a theorem. -/
theorem sat3_GlobalPACInterfaceBound (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hDN : sat3M N * sat3D N = N) :
    GlobalPACInterfaceBound N := by
  intro op g h A B hfac hp hq
  obtain ⟨hg, hh, hf⟩ := hfac
  obtain ⟨p, -, hp⟩ := hp
  obtain ⟨q, -, hq⟩ := hq
  have hb := sat3_global_interface_bound N hv hm3 hk hDN op g h A B
    hg hh hf p hp q hq
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_offside_pinned_count
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_global_interface_bound
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_GlobalPACInterfaceBound
