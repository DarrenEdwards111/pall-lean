import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameInterfacedTwoMass

/-!
# N-Frame: selector-escape counting — escape mass is interface mass

The quantitative rung on top of the interfaced two-mass kill.  In the sign-aligned branch, every
escaped selector `(cIdx, j₀)` (non-interned, on the wrong exclusive side) forces `signBit cIdx` or
the pin sign `signBit (pinClause cIdx j₀)` into the interface.  The charge is countable: for a fixed
sign-clean block, `j₀ ↦ pinClause cIdx j₀` is injective, so distinct escapes charge **distinct**
interned pin signs.

  `sat3_block_escape_bound_left/right` — **PROVED, the per-block bound**: a sign-clean block has at
        most `|A ∩ B|` escaped selectors — its escapes inject into the interface via pin signs.
  `sat3_escape_bound_left/right` — **PROVED, the global bound**: in the aligned branch the total
        escape count over all `(cIdx, j₀)` is at most `2 · m · |A ∩ B|` — fiberwise over blocks:
        an interned-sign block contributes at most `m − 2` escapes and there are at most `|A ∩ B|`
        such blocks; a sign-clean block contributes at most `|A ∩ B|`.
  `sat3_united_mass_quantitative` — **PROVED, the assembly**: for any interfaced factorization of
        `sat3Family`: signs aligned left with escape mass `≤ 2m·|A ∩ B|`, or aligned right likewise,
        or `m ≤ |A ∩ B| + 4`.  **A cut with a small interface admits almost no selector escapes** —
        `|A ∩ B| = 0` forces every slot-2 selector onto the signs' side.

## Honest scope

Named, not claimed: (1) turning escape *density* into a second `Ω(m)` bound needs a lower bound on
how many selectors must sit opposite the signs in a genuinely balanced cut — that is where the
row-count/frontier machinery re-enters; (2) slot-0/1 selectors and the remaining slot-probe
families; (3) `GlobalPACInterfaceBound`; (4) the wire-frontier → coordinate-interface extraction.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **PER-BLOCK ESCAPE BOUND, LEFT (proved)**: a sign-clean block's escapes into `B \ A` inject into
the interface via pin signs. -/
theorem sat3_block_escape_bound_left (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (haligned : ∀ c : Fin (sat3M N), sat3SignBit N c ∉ A ∩ B →
      sat3SignBit N c ∈ A \ B)
    (cIdx : Fin (sat3M N)) (hσ : sat3SignBit N cIdx ∉ A ∩ B) :
    ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j₀ =>
        sat3S2Sel N cIdx ⟨j₀.val, by
          have h1 := sat3M_pred_le_sat3V N; have h2 := j₀.isLt; omega⟩ ∉ A ∩ B ∧
        sat3S2Sel N cIdx ⟨j₀.val, by
          have h1 := sat3M_pred_le_sat3V N; have h2 := j₀.isLt; omega⟩ ∈ B \ A)).card
      ≤ (A ∩ B).card := by
  classical
  apply Finset.card_le_card_of_injOn
    (fun j₀ => sat3SignBit N (sat3PinClause N cIdx hk j₀))
  · intro j₀ hj
    have hjf := Finset.mem_coe.mp hj
    rw [Finset.mem_filter] at hjf
    obtain ⟨-, hτc, hτe⟩ := hjf
    apply Finset.mem_coe.mpr
    by_contra hπc
    have hcap := sat3_aligned_selector_capture_left N hv hm3 hk op g h A B
      hg hh hf haligned cIdx j₀
      (by have h1 := sat3M_pred_le_sat3V N; have h2 := j₀.isLt; omega)
      hσ hπc hτc
    rw [Finset.mem_sdiff] at hcap hτe
    exact hcap.2 hτe.1
  · intro x hx y hy hxy
    by_contra hne
    have hval : (sat3PinClause N cIdx hk x).val
        ≠ (sat3PinClause N cIdx hk y).val :=
      fun hv' => hne (sat3PinClause_val_inj N cIdx hk hv')
    exact sat3_signBit_ne N hval hxy

/-- **PER-BLOCK ESCAPE BOUND, RIGHT (proved)**: mirror of the left bound. -/
theorem sat3_block_escape_bound_right (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (haligned : ∀ c : Fin (sat3M N), sat3SignBit N c ∉ A ∩ B →
      sat3SignBit N c ∈ B \ A)
    (cIdx : Fin (sat3M N)) (hσ : sat3SignBit N cIdx ∉ A ∩ B) :
    ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j₀ =>
        sat3S2Sel N cIdx ⟨j₀.val, by
          have h1 := sat3M_pred_le_sat3V N; have h2 := j₀.isLt; omega⟩ ∉ A ∩ B ∧
        sat3S2Sel N cIdx ⟨j₀.val, by
          have h1 := sat3M_pred_le_sat3V N; have h2 := j₀.isLt; omega⟩ ∈ A \ B)).card
      ≤ (A ∩ B).card := by
  classical
  apply Finset.card_le_card_of_injOn
    (fun j₀ => sat3SignBit N (sat3PinClause N cIdx hk j₀))
  · intro j₀ hj
    have hjf := Finset.mem_coe.mp hj
    rw [Finset.mem_filter] at hjf
    obtain ⟨-, hτc, hτe⟩ := hjf
    apply Finset.mem_coe.mpr
    by_contra hπc
    have hcap := sat3_aligned_selector_capture_right N hv hm3 hk op g h A B
      hg hh hf haligned cIdx j₀
      (by have h1 := sat3M_pred_le_sat3V N; have h2 := j₀.isLt; omega)
      hσ hπc hτc
    rw [Finset.mem_sdiff] at hcap hτe
    exact hcap.2 hτe.1
  · intro x hx y hy hxy
    by_contra hne
    have hval : (sat3PinClause N cIdx hk x).val
        ≠ (sat3PinClause N cIdx hk y).val :=
      fun hv' => hne (sat3PinClause_val_inj N cIdx hk hv')
    exact sat3_signBit_ne N hval hxy

/-- **GLOBAL ESCAPE BOUND, LEFT (proved)**: the total escape count into `B \ A` is at most
`2 · m · |A ∩ B|`. -/
theorem sat3_escape_bound_left (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (haligned : ∀ c : Fin (sat3M N), sat3SignBit N c ∉ A ∩ B →
      sat3SignBit N c ∈ A \ B) :
    ((Finset.univ : Finset (Fin (sat3M N) × Fin (sat3M N - 2))).filter (fun p =>
        sat3S2Sel N p.1 ⟨p.2.val, by
          have h1 := sat3M_pred_le_sat3V N; have h2 := p.2.isLt; omega⟩ ∉ A ∩ B ∧
        sat3S2Sel N p.1 ⟨p.2.val, by
          have h1 := sat3M_pred_le_sat3V N; have h2 := p.2.isLt; omega⟩ ∈ B \ A)).card
      ≤ 2 * sat3M N * (A ∩ B).card := by
  classical
  set E := (Finset.univ : Finset (Fin (sat3M N) × Fin (sat3M N - 2))).filter (fun p =>
      sat3S2Sel N p.1 ⟨p.2.val, by
        have h1 := sat3M_pred_le_sat3V N; have h2 := p.2.isLt; omega⟩ ∉ A ∩ B ∧
      sat3S2Sel N p.1 ⟨p.2.val, by
        have h1 := sat3M_pred_le_sat3V N; have h2 := p.2.isLt; omega⟩ ∈ B \ A)
    with hEdef
  have hfib : E.card = ∑ c ∈ (Finset.univ : Finset (Fin (sat3M N))),
      (E.filter (fun p => p.1 = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_univ p.1)
  -- interned-sign blocks: trivial bound m − 2
  have hfibI : ∀ c : Fin (sat3M N),
      (E.filter (fun p => p.1 = c)).card ≤ sat3M N - 2 := by
    intro c
    have hle : (E.filter (fun p => p.1 = c)).card
        ≤ (Finset.univ : Finset (Fin (sat3M N - 2))).card := by
      apply Finset.card_le_card_of_injOn
        (fun p : Fin (sat3M N) × Fin (sat3M N - 2) => p.2)
      · intro p _
        exact Finset.mem_coe.mpr (Finset.mem_univ _)
      · intro p hp q hq hpq
        have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
        have hq' := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
        exact Prod.ext (hp'.2.trans hq'.2.symm) hpq
    rw [Finset.card_univ, Fintype.card_fin] at hle
    exact hle
  -- sign-clean blocks: the pin-sign injection
  have hfibC : ∀ c : Fin (sat3M N), sat3SignBit N c ∉ A ∩ B →
      (E.filter (fun p => p.1 = c)).card ≤ (A ∩ B).card := by
    intro c hσ
    apply Finset.card_le_card_of_injOn
      (fun p : Fin (sat3M N) × Fin (sat3M N - 2) =>
        sat3SignBit N (sat3PinClause N c hk p.2))
    · intro p hp
      have hpf := Finset.mem_coe.mp hp
      rw [Finset.mem_filter] at hpf
      obtain ⟨hpE, hp1⟩ := hpf
      rw [hEdef, Finset.mem_filter] at hpE
      obtain ⟨-, hτc, hτe⟩ := hpE
      rw [hp1] at hτc hτe
      apply Finset.mem_coe.mpr
      by_contra hπc
      have hcap := sat3_aligned_selector_capture_left N hv hm3 hk op g h A B
        hg hh hf haligned c p.2
        (by have h1 := sat3M_pred_le_sat3V N; have h2 := p.2.isLt; omega)
        hσ hπc hτc
      rw [Finset.mem_sdiff] at hcap hτe
      exact hcap.2 hτe.1
    · intro p hp q hq heq
      have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
      have hq' := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
      have h2 : p.2 = q.2 := by
        by_contra hne2
        have hval : (sat3PinClause N c hk p.2).val
            ≠ (sat3PinClause N c hk q.2).val :=
          fun hv' => hne2 (sat3PinClause_val_inj N c hk hv')
        exact sat3_signBit_ne N hval heq
      exact Prod.ext (hp'.2.trans hq'.2.symm) h2
  -- split the fiber sum over interned vs clean sign blocks
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin (sat3M N)))
    (fun c => sat3SignBit N c ∈ A ∩ B)
    (fun c => (E.filter (fun p => p.1 = c)).card)
  have hb1 : ∑ c ∈ Finset.univ.filter (fun c : Fin (sat3M N) =>
        sat3SignBit N c ∈ A ∩ B),
      (E.filter (fun p => p.1 = c)).card
      ≤ (Finset.univ.filter (fun c : Fin (sat3M N) =>
        sat3SignBit N c ∈ A ∩ B)).card * (sat3M N - 2) := by
    calc ∑ c ∈ Finset.univ.filter (fun c : Fin (sat3M N) =>
          sat3SignBit N c ∈ A ∩ B), (E.filter (fun p => p.1 = c)).card
        ≤ ∑ _c ∈ Finset.univ.filter (fun c : Fin (sat3M N) =>
          sat3SignBit N c ∈ A ∩ B), (sat3M N - 2) :=
          Finset.sum_le_sum (fun c _ => hfibI c)
      _ = _ := by rw [Finset.sum_const, smul_eq_mul]
  have hb2 : ∑ c ∈ Finset.univ.filter (fun c : Fin (sat3M N) =>
        ¬ sat3SignBit N c ∈ A ∩ B),
      (E.filter (fun p => p.1 = c)).card
      ≤ (Finset.univ.filter (fun c : Fin (sat3M N) =>
        ¬ sat3SignBit N c ∈ A ∩ B)).card * (A ∩ B).card := by
    calc ∑ c ∈ Finset.univ.filter (fun c : Fin (sat3M N) =>
          ¬ sat3SignBit N c ∈ A ∩ B), (E.filter (fun p => p.1 = c)).card
        ≤ ∑ c ∈ Finset.univ.filter (fun c : Fin (sat3M N) =>
          ¬ sat3SignBit N c ∈ A ∩ B), (A ∩ B).card :=
          Finset.sum_le_sum (fun c hc =>
            hfibC c (Finset.mem_filter.mp hc).2)
      _ = _ := by rw [Finset.sum_const, smul_eq_mul]
  -- the interned-sign blocks inject into the interface
  have hPle : (Finset.univ.filter (fun c : Fin (sat3M N) =>
      sat3SignBit N c ∈ A ∩ B)).card ≤ (A ∩ B).card := by
    apply Finset.card_le_card_of_injOn (sat3SignBit N)
    · intro c hc
      exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2
    · intro x _ y _ hxy
      by_contra hne
      exact sat3_signBit_ne N (fun hv' => hne (Fin.ext hv')) hxy
  have hQle : (Finset.univ.filter (fun c : Fin (sat3M N) =>
      ¬ sat3SignBit N c ∈ A ∩ B)).card ≤ sat3M N := by
    calc (Finset.univ.filter (fun c : Fin (sat3M N) =>
          ¬ sat3SignBit N c ∈ A ∩ B)).card
        ≤ (Finset.univ : Finset (Fin (sat3M N))).card :=
          Finset.card_filter_le _ _
      _ = sat3M N := by rw [Finset.card_univ, Fintype.card_fin]
  -- assemble the arithmetic
  have e1 : (Finset.univ.filter (fun c : Fin (sat3M N) =>
      sat3SignBit N c ∈ A ∩ B)).card * (sat3M N - 2)
      ≤ (A ∩ B).card * sat3M N :=
    Nat.mul_le_mul hPle (by omega)
  have e2 : (Finset.univ.filter (fun c : Fin (sat3M N) =>
      ¬ sat3SignBit N c ∈ A ∩ B)).card * (A ∩ B).card
      ≤ sat3M N * (A ∩ B).card :=
    Nat.mul_le_mul_right _ hQle
  have e3 : (A ∩ B).card * sat3M N = sat3M N * (A ∩ B).card :=
    Nat.mul_comm _ _
  have e4 : 2 * sat3M N * (A ∩ B).card
      = sat3M N * (A ∩ B).card + sat3M N * (A ∩ B).card := by ring
  omega

/-- **GLOBAL ESCAPE BOUND, RIGHT (proved)**: mirror — total escapes into `A \ B` are at most
`2 · m · |A ∩ B|`. -/
theorem sat3_escape_bound_right (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (haligned : ∀ c : Fin (sat3M N), sat3SignBit N c ∉ A ∩ B →
      sat3SignBit N c ∈ B \ A) :
    ((Finset.univ : Finset (Fin (sat3M N) × Fin (sat3M N - 2))).filter (fun p =>
        sat3S2Sel N p.1 ⟨p.2.val, by
          have h1 := sat3M_pred_le_sat3V N; have h2 := p.2.isLt; omega⟩ ∉ A ∩ B ∧
        sat3S2Sel N p.1 ⟨p.2.val, by
          have h1 := sat3M_pred_le_sat3V N; have h2 := p.2.isLt; omega⟩ ∈ A \ B)).card
      ≤ 2 * sat3M N * (A ∩ B).card := by
  classical
  set E := (Finset.univ : Finset (Fin (sat3M N) × Fin (sat3M N - 2))).filter (fun p =>
      sat3S2Sel N p.1 ⟨p.2.val, by
        have h1 := sat3M_pred_le_sat3V N; have h2 := p.2.isLt; omega⟩ ∉ A ∩ B ∧
      sat3S2Sel N p.1 ⟨p.2.val, by
        have h1 := sat3M_pred_le_sat3V N; have h2 := p.2.isLt; omega⟩ ∈ A \ B)
    with hEdef
  have hfib : E.card = ∑ c ∈ (Finset.univ : Finset (Fin (sat3M N))),
      (E.filter (fun p => p.1 = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_univ p.1)
  have hfibI : ∀ c : Fin (sat3M N),
      (E.filter (fun p => p.1 = c)).card ≤ sat3M N - 2 := by
    intro c
    have hle : (E.filter (fun p => p.1 = c)).card
        ≤ (Finset.univ : Finset (Fin (sat3M N - 2))).card := by
      apply Finset.card_le_card_of_injOn
        (fun p : Fin (sat3M N) × Fin (sat3M N - 2) => p.2)
      · intro p _
        exact Finset.mem_coe.mpr (Finset.mem_univ _)
      · intro p hp q hq hpq
        have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
        have hq' := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
        exact Prod.ext (hp'.2.trans hq'.2.symm) hpq
    rw [Finset.card_univ, Fintype.card_fin] at hle
    exact hle
  have hfibC : ∀ c : Fin (sat3M N), sat3SignBit N c ∉ A ∩ B →
      (E.filter (fun p => p.1 = c)).card ≤ (A ∩ B).card := by
    intro c hσ
    apply Finset.card_le_card_of_injOn
      (fun p : Fin (sat3M N) × Fin (sat3M N - 2) =>
        sat3SignBit N (sat3PinClause N c hk p.2))
    · intro p hp
      have hpf := Finset.mem_coe.mp hp
      rw [Finset.mem_filter] at hpf
      obtain ⟨hpE, hp1⟩ := hpf
      rw [hEdef, Finset.mem_filter] at hpE
      obtain ⟨-, hτc, hτe⟩ := hpE
      rw [hp1] at hτc hτe
      apply Finset.mem_coe.mpr
      by_contra hπc
      have hcap := sat3_aligned_selector_capture_right N hv hm3 hk op g h A B
        hg hh hf haligned c p.2
        (by have h1 := sat3M_pred_le_sat3V N; have h2 := p.2.isLt; omega)
        hσ hπc hτc
      rw [Finset.mem_sdiff] at hcap hτe
      exact hcap.2 hτe.1
    · intro p hp q hq heq
      have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
      have hq' := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
      have h2 : p.2 = q.2 := by
        by_contra hne2
        have hval : (sat3PinClause N c hk p.2).val
            ≠ (sat3PinClause N c hk q.2).val :=
          fun hv' => hne2 (sat3PinClause_val_inj N c hk hv')
        exact sat3_signBit_ne N hval heq
      exact Prod.ext (hp'.2.trans hq'.2.symm) h2
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin (sat3M N)))
    (fun c => sat3SignBit N c ∈ A ∩ B)
    (fun c => (E.filter (fun p => p.1 = c)).card)
  have hb1 : ∑ c ∈ Finset.univ.filter (fun c : Fin (sat3M N) =>
        sat3SignBit N c ∈ A ∩ B),
      (E.filter (fun p => p.1 = c)).card
      ≤ (Finset.univ.filter (fun c : Fin (sat3M N) =>
        sat3SignBit N c ∈ A ∩ B)).card * (sat3M N - 2) := by
    calc ∑ c ∈ Finset.univ.filter (fun c : Fin (sat3M N) =>
          sat3SignBit N c ∈ A ∩ B), (E.filter (fun p => p.1 = c)).card
        ≤ ∑ _c ∈ Finset.univ.filter (fun c : Fin (sat3M N) =>
          sat3SignBit N c ∈ A ∩ B), (sat3M N - 2) :=
          Finset.sum_le_sum (fun c _ => hfibI c)
      _ = _ := by rw [Finset.sum_const, smul_eq_mul]
  have hb2 : ∑ c ∈ Finset.univ.filter (fun c : Fin (sat3M N) =>
        ¬ sat3SignBit N c ∈ A ∩ B),
      (E.filter (fun p => p.1 = c)).card
      ≤ (Finset.univ.filter (fun c : Fin (sat3M N) =>
        ¬ sat3SignBit N c ∈ A ∩ B)).card * (A ∩ B).card := by
    calc ∑ c ∈ Finset.univ.filter (fun c : Fin (sat3M N) =>
          ¬ sat3SignBit N c ∈ A ∩ B), (E.filter (fun p => p.1 = c)).card
        ≤ ∑ c ∈ Finset.univ.filter (fun c : Fin (sat3M N) =>
          ¬ sat3SignBit N c ∈ A ∩ B), (A ∩ B).card :=
          Finset.sum_le_sum (fun c hc =>
            hfibC c (Finset.mem_filter.mp hc).2)
      _ = _ := by rw [Finset.sum_const, smul_eq_mul]
  have hPle : (Finset.univ.filter (fun c : Fin (sat3M N) =>
      sat3SignBit N c ∈ A ∩ B)).card ≤ (A ∩ B).card := by
    apply Finset.card_le_card_of_injOn (sat3SignBit N)
    · intro c hc
      exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2
    · intro x _ y _ hxy
      by_contra hne
      exact sat3_signBit_ne N (fun hv' => hne (Fin.ext hv')) hxy
  have hQle : (Finset.univ.filter (fun c : Fin (sat3M N) =>
      ¬ sat3SignBit N c ∈ A ∩ B)).card ≤ sat3M N := by
    calc (Finset.univ.filter (fun c : Fin (sat3M N) =>
          ¬ sat3SignBit N c ∈ A ∩ B)).card
        ≤ (Finset.univ : Finset (Fin (sat3M N))).card :=
          Finset.card_filter_le _ _
      _ = sat3M N := by rw [Finset.card_univ, Fintype.card_fin]
  have e1 : (Finset.univ.filter (fun c : Fin (sat3M N) =>
      sat3SignBit N c ∈ A ∩ B)).card * (sat3M N - 2)
      ≤ (A ∩ B).card * sat3M N :=
    Nat.mul_le_mul hPle (by omega)
  have e2 : (Finset.univ.filter (fun c : Fin (sat3M N) =>
      ¬ sat3SignBit N c ∈ A ∩ B)).card * (A ∩ B).card
      ≤ sat3M N * (A ∩ B).card :=
    Nat.mul_le_mul_right _ hQle
  have e3 : (A ∩ B).card * sat3M N = sat3M N * (A ∩ B).card :=
    Nat.mul_comm _ _
  have e4 : 2 * sat3M N * (A ∩ B).card
      = sat3M N * (A ∩ B).card + sat3M N * (A ∩ B).card := by ring
  omega

/-- **THE QUANTITATIVE UNITED MASS (proved)**: any interfaced factorization of `sat3Family` has signs
aligned left with escape mass `≤ 2m·|A ∩ B|`, or aligned right likewise, or `m ≤ |A ∩ B| + 4`.
A small interface admits almost no selector escapes. -/
theorem sat3_united_mass_quantitative (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x)) :
    ((∀ c : Fin (sat3M N), sat3SignBit N c ∉ A ∩ B → sat3SignBit N c ∈ A \ B) ∧
      ((Finset.univ : Finset (Fin (sat3M N) × Fin (sat3M N - 2))).filter (fun p =>
          sat3S2Sel N p.1 ⟨p.2.val, by
            have h1 := sat3M_pred_le_sat3V N; have h2 := p.2.isLt; omega⟩ ∉ A ∩ B ∧
          sat3S2Sel N p.1 ⟨p.2.val, by
            have h1 := sat3M_pred_le_sat3V N; have h2 := p.2.isLt; omega⟩ ∈ B \ A)).card
        ≤ 2 * sat3M N * (A ∩ B).card) ∨
    ((∀ c : Fin (sat3M N), sat3SignBit N c ∉ A ∩ B → sat3SignBit N c ∈ B \ A) ∧
      ((Finset.univ : Finset (Fin (sat3M N) × Fin (sat3M N - 2))).filter (fun p =>
          sat3S2Sel N p.1 ⟨p.2.val, by
            have h1 := sat3M_pred_le_sat3V N; have h2 := p.2.isLt; omega⟩ ∉ A ∩ B ∧
          sat3S2Sel N p.1 ⟨p.2.val, by
            have h1 := sat3M_pred_le_sat3V N; have h2 := p.2.isLt; omega⟩ ∈ A \ B)).card
        ≤ 2 * sat3M N * (A ∩ B).card) ∨
    sat3M N ≤ (A ∩ B).card + 4 := by
  rcases sat3_sign_alignment_or_interface N hv hm3 hk op g h A B hg hh hf
    with hL | hR | hC
  · exact Or.inl ⟨hL,
      sat3_escape_bound_left N hv hm3 hk op g h A B hg hh hf hL⟩
  · exact Or.inr (Or.inl ⟨hR,
      sat3_escape_bound_right N hv hm3 hk op g h A B hg hh hf hR⟩)
  · exact Or.inr (Or.inr hC)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_escape_bound_left
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_united_mass_quantitative
