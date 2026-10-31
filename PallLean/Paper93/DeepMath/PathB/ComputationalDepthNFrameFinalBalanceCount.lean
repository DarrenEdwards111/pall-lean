import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSlotSymmetry

/-!
# N-Frame: the final balance case-count — `coneExcess ≥ Ω(m)`

The closing rung of the Track C arc.  With both min forms at every slot, the count closes:

  `sat3_pin_cover` — a pin family sees every block but at most 2, so any block census transfers
        to pin censuses with loss 2.
  `sat3_sign_concentration` — **PROVED, the global sign law**: for each slot `t`, the slot-`t`
        sign column is `(j+2)`-concentrated: at most `j+2` sign bits inside `S`, or all but
        `j+2` inside.  (Otherwise both min forms fire on one block, giving `v ≤ 2j`.)
  `sat3_slot_dichotomy` — **PROVED**: each slot region is nearly-full (every block has ≤ `j`
        slot-`t` selectors outside `S`) or nearly-empty (every block has ≤ `j` inside, and ≤
        `j+2` sign bits inside).
  `sat3_full_mass` / `sat3_empty_mass` — **PROVED, the mass counts**: a nearly-full slot forces
        `|S| ≥ m(v−j)`; three nearly-empty slots force `|S| ≤ 3mj + 3(j+2) + 3v + 3`.
  `sat3_balanced_cut_impossible` — **PROVED, the window contradiction**: no cut factorization
        with balanced `S` in the window between the two masses exists.
  `sat3_final_balance_count` — **PROVED, the circuit cash-out**: for a minimal SAT circuit, the
        balanced wire cut at a window band is impossible unless the windows fail — every
        hypothesis is arithmetic in `coneExcess`.
  `sat3_coneExcess_omega` — **PROVED, the Ω(m) bound**: if the minimal circuit's root reads at
        least half the live grid (`m·v ≤ 2·|varsOf root| + 1`), then
        `m < 32 · (coneExcess + 2)`, i.e. `coneExcess ≥ m/32 − 2 = Ω(m) = Ω(√N)`.

## Honest scope

This discharges the Track C target `coneExcess ≥ Ω(m)` **conditionally on one stated hypothesis**:
`hvars`, that the root cone of a minimal circuit reads at least half of the live `m·v` selector
grid.  This is an evasiveness-flavoured statement about minimal circuits (a minimal circuit
cannot ignore half the instance encoding); it is NOT yet proven in this development and is the
single remaining rung between this file and an unconditional `cbudget ≥ 2N + Ω(m)`-type bound for
the wire model.  It is an explicit hypothesis of one theorem — not an axiom, not a socket.
Everything above it (`sat3_balanced_cut_impossible`, `sat3_final_balance_count`) is unconditional.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Counting helpers -/

/-- Complement cover: the universe splits into a predicate and its negation. -/
theorem univ_filter_cover_card {X : Type*} [Fintype X] [DecidableEq X]
    (P : X → Prop) [DecidablePred P] :
    Fintype.card X ≤ ((Finset.univ : Finset X).filter P).card
      + ((Finset.univ : Finset X).filter (fun x => ¬ P x)).card := by
  classical
  have hcover : (Finset.univ : Finset X)
      ⊆ (Finset.univ.filter P) ∪ (Finset.univ.filter (fun x => ¬ P x)) := by
    intro x _
    by_cases h : P x
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩))
  calc Fintype.card X = (Finset.univ : Finset X).card := Finset.card_univ.symm
    _ ≤ _ := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)

/-- **THE PIN COVER (proved)**: the pin family of any block sees every block but at most 2, so a
block census transfers to the pin census with loss 2. -/
theorem sat3_pin_cover (N : ℕ) (c : Fin (sat3M N))
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (Q : Fin (sat3M N) → Prop) [DecidablePred Q] :
    ((Finset.univ : Finset (Fin (sat3M N))).filter Q).card
      ≤ ((Finset.univ : Finset (Fin (sat3M N - 2))).filter
          (fun p => Q (sat3PinClause N c hk p))).card + 2 := by
  classical
  set I : Finset (Fin (sat3M N)) :=
    Finset.univ.image (sat3PinClause N c hk) with hI
  have hIcard : I.card = sat3M N - 2 := by
    rw [hI, Finset.card_image_of_injective _
        (fun p p' hpp => sat3PinClause_val_inj N c hk (congrArg Fin.val hpp)),
      Finset.card_univ, Fintype.card_fin]
  have hsplit : (Finset.univ.filter Q)
      ⊆ ((Finset.univ.filter Q) ∩ I) ∪ ((Finset.univ : Finset (Fin (sat3M N))) \ I) := by
    intro x hx
    by_cases hxI : x ∈ I
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hx, hxI⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxI⟩))
  have h1 : ((Finset.univ.filter Q) ∩ I).card
      ≤ ((Finset.univ : Finset (Fin (sat3M N - 2))).filter
          (fun p => Q (sat3PinClause N c hk p))).card := by
    apply Finset.card_le_card_of_surjOn (sat3PinClause N c hk)
    intro x hx
    have hx' := Finset.mem_coe.mp hx
    have hxQ := (Finset.mem_filter.mp (Finset.mem_inter.mp hx').1).2
    have hxI := (Finset.mem_inter.mp hx').2
    rw [hI] at hxI
    obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hxI
    refine ⟨p, ?_, hp⟩
    apply Finset.mem_coe.mpr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ p, ?_⟩
    rw [hp]
    exact hxQ
  have h2 : ((Finset.univ : Finset (Fin (sat3M N))) \ I).card ≤ 2 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
      hIcard]
    omega
  have h3 := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  omega

/-! ### The global sign law and the slot dichotomy -/

set_option maxHeartbeats 800000 in
/-- **THE GLOBAL SIGN LAW (proved)**: for each slot, the sign column is `(j+2)`-concentrated on
one side of `S` — otherwise both min forms fire on one block, forcing `v ≤ 2j`. -/
theorem sat3_sign_concentration (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j) (t : Fin 3)
    (hm : 2 * j + 6 ≤ sat3M N) (hvj : 2 * j + 1 ≤ sat3V N) :
    ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      sat3Bit N c t (sat3V N) (by omega) ∈ S)).card ≤ j + 2
    ∨ sat3M N - (j + 2) ≤ ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      sat3Bit N c t (sat3V N) (by omega) ∈ S)).card := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hbig, hsmall⟩ := hcon
  set c0 : Fin (sat3M N) := ⟨0, by omega⟩ with hc0
  -- the pin family of c0 sees the sign census with loss 2, on both sides
  have hpcIn := sat3_pin_cover N c0 hk (fun c' =>
    sat3Bit N c' t (sat3V N) (by omega) ∈ S)
  have hpcOut := sat3_pin_cover N c0 hk (fun c' =>
    sat3Bit N c' t (sat3V N) (by omega) ∉ S)
  have hcovM := univ_filter_cover_card (fun c' : Fin (sat3M N) =>
    sat3Bit N c' t (sat3V N) (by omega) ∈ S)
  rw [Fintype.card_fin] at hcovM
  rcases sat3_min_bound_slot N hv hk hcut c0 t with h1 | h1
  · -- pinIn ≤ j: but the sign-in census is > j+2, so pinIn ≥ j+1
    omega
  · rcases sat3_seldata_bound_slot N hv hk hcut c0 t with h2 | h2
    · -- selOut ≤ j and selIn ≤ j: v ≤ 2j, contradiction
      have hcovV := univ_filter_cover_card (fun w : Fin (sat3V N) =>
        sat3Bit N c0 t w.val (by have := w.isLt; omega) ∈ S)
      rw [Fintype.card_fin] at hcovV
      omega
    · -- pinOut ≤ j: but the sign-out census is ≥ m − (sign-in) > j+2, so pinOut ≥ j+1
      omega

/-- **THE SLOT DICHOTOMY (proved)**: each slot region is nearly-full or nearly-empty in `S`. -/
theorem sat3_slot_dichotomy (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j) (t : Fin 3)
    (hm : 2 * j + 6 ≤ sat3M N) (hvj : 2 * j + 1 ≤ sat3V N) :
    (∀ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c t w.val (by have := w.isLt; omega) ∉ S)).card ≤ j)
    ∨ ((∀ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c t w.val (by have := w.isLt; omega) ∈ S)).card ≤ j)
      ∧ ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c t (sat3V N) (by omega) ∈ S)).card ≤ j + 2) := by
  classical
  rcases sat3_sign_concentration N hv hk hcut t hm hvj with hsm | hbg
  · right
    refine ⟨?_, hsm⟩
    intro c
    have hpcOut := sat3_pin_cover N c hk (fun c' =>
      sat3Bit N c' t (sat3V N) (by omega) ∉ S)
    have hcovM := univ_filter_cover_card (fun c' : Fin (sat3M N) =>
      sat3Bit N c' t (sat3V N) (by omega) ∈ S)
    rw [Fintype.card_fin] at hcovM
    rcases sat3_seldata_bound_slot N hv hk hcut c t with h | h
    · exact h
    · -- pinOut ≤ j: but sign-out ≥ m − (j+2) ≥ j+4, so pinOut ≥ j+2
      omega
  · left
    intro c
    have hpcIn := sat3_pin_cover N c hk (fun c' =>
      sat3Bit N c' t (sat3V N) (by omega) ∈ S)
    rcases sat3_min_bound_slot N hv hk hcut c t with h | h
    · -- pinIn ≤ j: but sign-in ≥ m − (j+2) ≥ j+4, so pinIn ≥ j+2
      omega
    · exact h

/-! ### The mass counts -/

/-- **THE FULL-SLOT MASS (proved)**: a nearly-full slot forces `|S| ≥ m(v−j)`. -/
theorem sat3_full_mass (N : ℕ) {S : Finset (Fin N)} {j : ℕ} (t : Fin 3)
    (hout : ∀ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c t w.val (by have := w.isLt; omega) ∉ S)).card ≤ j) :
    sat3M N * (sat3V N - j) ≤ S.card := by
  classical
  set img : Fin (sat3M N) → Finset (Fin N) := fun c =>
    ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c t w.val (by have := w.isLt; omega) ∈ S)).image
      (fun w : Fin (sat3V N) => sat3Bit N c t w.val (by have := w.isLt; omega))
    with himg
  have hdisj : (↑(Finset.univ : Finset (Fin (sat3M N)))
      : Set (Fin (sat3M N))).PairwiseDisjoint img := by
    intro c _ c' _ hne
    show Disjoint (img c) (img c')
    apply Finset.disjoint_left.mpr
    intro b hb hb'
    rw [himg] at hb hb'
    obtain ⟨w, -, hw⟩ := Finset.mem_image.mp hb
    obtain ⟨w', -, hw'⟩ := Finset.mem_image.mp hb'
    apply hne
    apply Fin.ext
    have h1 : b.val / sat3D N = c.val := by
      rw [← hw]
      exact sat3Bit_clause N c t w.val (by have := w.isLt; omega)
    have h2 : b.val / sat3D N = c'.val := by
      rw [← hw']
      exact sat3Bit_clause N c' t w'.val (by have := w'.isLt; omega)
    omega
  have hsub : Finset.univ.biUnion img ⊆ S := by
    intro b hb
    obtain ⟨c, -, hbc⟩ := Finset.mem_biUnion.mp hb
    rw [himg] at hbc
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hbc
    exact (Finset.mem_filter.mp hw).2
  have hper : ∀ c : Fin (sat3M N), sat3V N - j ≤ (img c).card := by
    intro c
    have hinj : Set.InjOn (fun w : Fin (sat3V N) =>
        sat3Bit N c t w.val (by have := w.isLt; omega))
        ↑((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c t w.val (by have := w.isLt; omega) ∈ S)) := by
      intro w _ w' _ hww
      have hval := congrArg Fin.val hww
      apply Fin.ext
      show w.val = w'.val
      have h1 : c.val * sat3D N + t.val * (sat3V N + 1) + w.val
          = c.val * sat3D N + t.val * (sat3V N + 1) + w'.val := hval
      omega
    have hcard : (img c).card
        = ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c t w.val (by have := w.isLt; omega) ∈ S)).card := by
      rw [himg]
      exact Finset.card_image_of_injOn hinj
    have hcv := univ_filter_cover_card (fun w : Fin (sat3V N) =>
      sat3Bit N c t w.val (by have := w.isLt; omega) ∈ S)
    rw [Fintype.card_fin] at hcv
    have := hout c
    omega
  calc sat3M N * (sat3V N - j)
      = ∑ _c : Fin (sat3M N), (sat3V N - j) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ ≤ ∑ c : Fin (sat3M N), (img c).card :=
        Finset.sum_le_sum (fun c _ => hper c)
    _ = (Finset.univ.biUnion img).card := (Finset.card_biUnion hdisj).symm
    _ ≤ S.card := Finset.card_le_card hsub

set_option maxHeartbeats 1600000 in
/-- **THE EMPTY-SLOT MASS (proved)**: three nearly-empty slots force
`|S| ≤ 3mj + 3(j+2) + 3v + 3`. -/
theorem sat3_empty_mass (N : ℕ) {S : Finset (Fin N)} {j : ℕ}
    (hsel : ∀ (t : Fin 3) (c : Fin (sat3M N)),
      ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c t w.val (by have := w.isLt; omega) ∈ S)).card ≤ j)
    (hsgn : ∀ t : Fin 3,
      ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c t (sat3V N) (by omega) ∈ S)).card ≤ j + 2) :
    S.card ≤ 3 * (sat3M N * j) + 3 * (j + 2) + 3 * sat3V N + 3 := by
  classical
  have hDpos := sat3D_pos N
  set Fsel : Fin 3 → Finset (Fin N) := fun t => S.filter (fun b =>
    b.val / sat3D N < sat3M N ∧ b.val % sat3D N / (sat3V N + 1) = t.val ∧
    b.val % sat3D N % (sat3V N + 1) < sat3V N) with hFsel
  set Fsgn : Fin 3 → Finset (Fin N) := fun t => S.filter (fun b =>
    b.val / sat3D N < sat3M N ∧ b.val % sat3D N / (sat3V N + 1) = t.val ∧
    ¬ (b.val % sat3D N % (sat3V N + 1) < sat3V N)) with hFsgn
  set Ftail : Finset (Fin N) := S.filter (fun b =>
    ¬ (b.val / sat3D N < sat3M N)) with hFtail
  -- reconstruction: a live bit is a layout bit
  have hrec : ∀ b : Fin N, ∀ hdiv : b.val / sat3D N < sat3M N,
      ∀ hsl : b.val % sat3D N / (sat3V N + 1) < 3,
      b = sat3Bit N ⟨b.val / sat3D N, hdiv⟩ ⟨b.val % sat3D N / (sat3V N + 1), hsl⟩
        (b.val % sat3D N % (sat3V N + 1)) (Nat.mod_lt _ (by omega)) := by
    intro b hdiv hsl
    apply Fin.ext
    show b.val = b.val / sat3D N * sat3D N
      + b.val % sat3D N / (sat3V N + 1) * (sat3V N + 1)
      + b.val % sat3D N % (sat3V N + 1)
    have h1 : sat3D N * (b.val / sat3D N) + b.val % sat3D N = b.val :=
      Nat.div_add_mod _ _
    have h2 : (sat3V N + 1) * (b.val % sat3D N / (sat3V N + 1))
        + b.val % sat3D N % (sat3V N + 1) = b.val % sat3D N :=
      Nat.div_add_mod _ _
    have h3 : sat3D N * (b.val / sat3D N) = b.val / sat3D N * sat3D N :=
      Nat.mul_comm _ _
    have h4 : (sat3V N + 1) * (b.val % sat3D N / (sat3V N + 1))
        = b.val % sat3D N / (sat3V N + 1) * (sat3V N + 1) := Nat.mul_comm _ _
    omega
  have hslot3 : ∀ b : Fin N, b.val % sat3D N / (sat3V N + 1) < 3 := by
    intro b
    apply Nat.div_lt_of_lt_mul
    have := Nat.mod_lt b.val hDpos
    have hD : sat3D N = 3 * (sat3V N + 1) := rfl
    omega
  -- per-piece bounds
  have hselbound : ∀ t : Fin 3, (Fsel t).card ≤ sat3M N * j := by
    intro t
    have h1 : (Fsel t).card ≤ ((Finset.univ : Finset (Fin (sat3M N) × Fin (sat3V N))).filter
        (fun cw => sat3Bit N cw.1 t cw.2.val (by have := cw.2.isLt; omega) ∈ S)).card := by
      apply Finset.card_le_card_of_surjOn
        (fun cw : Fin (sat3M N) × Fin (sat3V N) =>
          sat3Bit N cw.1 t cw.2.val (by have := cw.2.isLt; omega))
      intro b hb
      have hb' := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
      obtain ⟨hbS, hdiv, hsl, hfd⟩ := hb'
      have hbit : b = sat3Bit N ⟨b.val / sat3D N, hdiv⟩ t
          (b.val % sat3D N % (sat3V N + 1)) (Nat.mod_lt _ (by omega)) := by
        have ht : (⟨b.val % sat3D N / (sat3V N + 1), hslot3 b⟩ : Fin 3) = t :=
          Fin.ext hsl
        have h0 := hrec b hdiv (hslot3 b)
        rw [ht] at h0
        exact h0
      refine ⟨(⟨b.val / sat3D N, hdiv⟩, ⟨b.val % sat3D N % (sat3V N + 1), hfd⟩), ?_, ?_⟩
      · apply Finset.mem_coe.mpr
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        show sat3Bit N ⟨b.val / sat3D N, hdiv⟩ t (b.val % sat3D N % (sat3V N + 1)) _ ∈ S
        rw [← hbit]
        exact hbS
      · show sat3Bit N ⟨b.val / sat3D N, hdiv⟩ t (b.val % sat3D N % (sat3V N + 1)) _ = b
        rw [← hbit]
    have h2 : ((Finset.univ : Finset (Fin (sat3M N) × Fin (sat3V N))).filter
        (fun cw => sat3Bit N cw.1 t cw.2.val (by have := cw.2.isLt; omega) ∈ S)).card
        ≤ sat3M N * j := by
      rw [Finset.card_eq_sum_card_fiberwise
        (f := fun cw : Fin (sat3M N) × Fin (sat3V N) => cw.1)
        (t := (Finset.univ : Finset (Fin (sat3M N))))
        (fun cw _ => Finset.mem_univ cw.1)]
      calc ∑ c : Fin (sat3M N), (((Finset.univ : Finset (Fin (sat3M N) × Fin (sat3V N))).filter
            (fun cw => sat3Bit N cw.1 t cw.2.val (by have := cw.2.isLt; omega) ∈ S)).filter
            (fun cw => cw.1 = c)).card
          ≤ ∑ _c : Fin (sat3M N), j := by
            apply Finset.sum_le_sum
            intro c _
            have hle : (((Finset.univ : Finset (Fin (sat3M N) × Fin (sat3V N))).filter
                (fun cw => sat3Bit N cw.1 t cw.2.val (by have := cw.2.isLt; omega) ∈ S)).filter
                (fun cw => cw.1 = c)).card
                ≤ ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
                  sat3Bit N c t w.val (by have := w.isLt; omega) ∈ S)).card := by
              apply Finset.card_le_card_of_injOn (fun cw => cw.2)
              · intro cw hcw
                have hcw' := Finset.mem_filter.mp (Finset.mem_coe.mp hcw)
                have hmemS := (Finset.mem_filter.mp hcw'.1).2
                have hc1 := hcw'.2
                apply Finset.mem_coe.mpr
                apply Finset.mem_filter.mpr
                refine ⟨Finset.mem_univ _, ?_⟩
                rw [← hc1]
                exact hmemS
              · intro cw hcw cw' hcw' h2eq
                have hc1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hcw)).2
                have hc1' := (Finset.mem_filter.mp (Finset.mem_coe.mp hcw')).2
                apply Prod.ext
                · rw [hc1, hc1']
                · exact h2eq
            exact hle.trans (hsel t c)
        _ = sat3M N * j := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  have hsgnbound : ∀ t : Fin 3, (Fsgn t).card ≤ j + 2 := by
    intro t
    have h1 : (Fsgn t).card ≤ ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c t (sat3V N) (by omega) ∈ S)).card := by
      apply Finset.card_le_card_of_surjOn
        (fun c : Fin (sat3M N) => sat3Bit N c t (sat3V N) (by omega))
      intro b hb
      have hb' := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
      obtain ⟨hbS, hdiv, hsl, hfd⟩ := hb'
      have hfv : b.val % sat3D N % (sat3V N + 1) = sat3V N := by
        have := Nat.mod_lt (b.val % sat3D N) (y := sat3V N + 1) (by omega)
        omega
      have hbit : b = sat3Bit N ⟨b.val / sat3D N, hdiv⟩ t (sat3V N) (by omega) := by
        apply Fin.ext
        show b.val = b.val / sat3D N * sat3D N + t.val * (sat3V N + 1) + sat3V N
        have h1 : sat3D N * (b.val / sat3D N) + b.val % sat3D N = b.val :=
          Nat.div_add_mod _ _
        have h2 : (sat3V N + 1) * (b.val % sat3D N / (sat3V N + 1))
            + b.val % sat3D N % (sat3V N + 1) = b.val % sat3D N :=
          Nat.div_add_mod _ _
        have h3 : sat3D N * (b.val / sat3D N) = b.val / sat3D N * sat3D N :=
          Nat.mul_comm _ _
        have h4 : (sat3V N + 1) * (b.val % sat3D N / (sat3V N + 1))
            = (sat3V N + 1) * t.val := by rw [hsl]
        have h5 : (sat3V N + 1) * t.val = t.val * (sat3V N + 1) :=
          Nat.mul_comm _ _
        omega
      refine ⟨⟨b.val / sat3D N, hdiv⟩, ?_, ?_⟩
      · apply Finset.mem_coe.mpr
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        show sat3Bit N ⟨b.val / sat3D N, hdiv⟩ t (sat3V N) _ ∈ S
        rw [← hbit]
        exact hbS
      · show sat3Bit N ⟨b.val / sat3D N, hdiv⟩ t (sat3V N) _ = b
        rw [← hbit]
    exact h1.trans (hsgn t)
  have htailbound : Ftail.card ≤ 3 * sat3V N + 3 := by
    have h1 : Ftail.card ≤ (Finset.range (3 * sat3V N + 3)).card := by
      apply Finset.card_le_card_of_injOn (fun b => b.val - sat3M N * sat3D N)
      · intro b hb
        have hb' := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
        have hge : sat3M N * sat3D N ≤ b.val := by
          have hdge : sat3M N ≤ b.val / sat3D N := by omega
          have := Nat.div_mul_le_self b.val (sat3D N)
          have hmm : sat3M N * sat3D N ≤ b.val / sat3D N * sat3D N :=
            Nat.mul_le_mul_right _ hdge
          omega
        have hNd : sat3D N * sat3M N + N % sat3D N = N := Nat.div_add_mod N (sat3D N)
        have hmd : N % sat3D N < sat3D N := Nat.mod_lt _ hDpos
        have hDD : sat3D N = 3 * (sat3V N + 1) := rfl
        have hcm : sat3D N * sat3M N = sat3M N * sat3D N := Nat.mul_comm _ _
        apply Finset.mem_coe.mpr
        apply Finset.mem_range.mpr
        show b.val - sat3M N * sat3D N < 3 * sat3V N + 3
        have hblt := b.isLt
        omega
      · intro b hb b' hb' heq
        have h1 := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
        have h2 := Finset.mem_filter.mp (Finset.mem_coe.mp hb')
        have hge : sat3M N * sat3D N ≤ b.val := by
          have hdge : sat3M N ≤ b.val / sat3D N := by omega
          have := Nat.div_mul_le_self b.val (sat3D N)
          have hmm : sat3M N * sat3D N ≤ b.val / sat3D N * sat3D N :=
            Nat.mul_le_mul_right _ hdge
          omega
        have hge' : sat3M N * sat3D N ≤ b'.val := by
          have hdge : sat3M N ≤ b'.val / sat3D N := by omega
          have := Nat.div_mul_le_self b'.val (sat3D N)
          have hmm : sat3M N * sat3D N ≤ b'.val / sat3D N * sat3D N :=
            Nat.mul_le_mul_right _ hdge
          omega
        have heq' : b.val - sat3M N * sat3D N = b'.val - sat3M N * sat3D N := heq
        apply Fin.ext
        omega
    rw [Finset.card_range] at h1
    exact h1
  -- the cover
  have hcover : S ⊆ ((Fsel ⟨0, by omega⟩ ∪ Fsgn ⟨0, by omega⟩)
      ∪ (Fsel ⟨1, by omega⟩ ∪ Fsgn ⟨1, by omega⟩))
      ∪ ((Fsel ⟨2, by omega⟩ ∪ Fsgn ⟨2, by omega⟩) ∪ Ftail) := by
    intro b hb
    by_cases hdiv : b.val / sat3D N < sat3M N
    · have hsl3 := hslot3 b
      have h012 : b.val % sat3D N / (sat3V N + 1) = 0
          ∨ b.val % sat3D N / (sat3V N + 1) = 1
          ∨ b.val % sat3D N / (sat3V N + 1) = 2 := by
        have hq3 := hslot3 b
        revert hq3
        generalize b.val % sat3D N / (sat3V N + 1) = q
        intro hq3
        omega
      by_cases hfd : b.val % sat3D N % (sat3V N + 1) < sat3V N
      · rcases h012 with h | h | h
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
            (Finset.mem_union.mpr (Or.inl
              (Finset.mem_filter.mpr ⟨hb, hdiv, h, hfd⟩))))))
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
            (Finset.mem_union.mpr (Or.inl
              (Finset.mem_filter.mpr ⟨hb, hdiv, h, hfd⟩))))))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl
            (Finset.mem_union.mpr (Or.inl
              (Finset.mem_filter.mpr ⟨hb, hdiv, h, hfd⟩))))))
      · rcases h012 with h | h | h
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
            (Finset.mem_union.mpr (Or.inr
              (Finset.mem_filter.mpr ⟨hb, hdiv, h, hfd⟩))))))
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
            (Finset.mem_union.mpr (Or.inr
              (Finset.mem_filter.mpr ⟨hb, hdiv, h, hfd⟩))))))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl
            (Finset.mem_union.mpr (Or.inr
              (Finset.mem_filter.mpr ⟨hb, hdiv, h, hfd⟩))))))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨hb, hdiv⟩))))
  -- assemble
  have hc1 := Finset.card_le_card hcover
  have hc2 := Finset.card_union_le
    ((Fsel ⟨0, by omega⟩ ∪ Fsgn ⟨0, by omega⟩)
      ∪ (Fsel ⟨1, by omega⟩ ∪ Fsgn ⟨1, by omega⟩))
    ((Fsel ⟨2, by omega⟩ ∪ Fsgn ⟨2, by omega⟩) ∪ Ftail)
  have hc3 := Finset.card_union_le (Fsel ⟨0, by omega⟩ ∪ Fsgn ⟨0, by omega⟩)
    (Fsel ⟨1, by omega⟩ ∪ Fsgn ⟨1, by omega⟩)
  have hc4 := Finset.card_union_le (Fsel ⟨2, by omega⟩ ∪ Fsgn ⟨2, by omega⟩) Ftail
  have hc5 := Finset.card_union_le (Fsel ⟨0, by omega⟩) (Fsgn ⟨0, by omega⟩)
  have hc6 := Finset.card_union_le (Fsel ⟨1, by omega⟩) (Fsgn ⟨1, by omega⟩)
  have hc7 := Finset.card_union_le (Fsel ⟨2, by omega⟩) (Fsgn ⟨2, by omega⟩)
  have hb0 := hselbound ⟨0, by omega⟩
  have hb1 := hselbound ⟨1, by omega⟩
  have hb2 := hselbound ⟨2, by omega⟩
  have hg0 := hsgnbound ⟨0, by omega⟩
  have hg1 := hsgnbound ⟨1, by omega⟩
  have hg2 := hsgnbound ⟨2, by omega⟩
  omega

/-! ### The window contradiction and the circuit cash-outs -/

/-- **THE WINDOW CONTRADICTION (proved)**: no cut factorization has a balanced `S` strictly
between the empty mass and the full mass. -/
theorem sat3_balanced_cut_impossible (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) {S : Finset (Fin N)} {j T : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (hm : 2 * j + 6 ≤ sat3M N) (hvj : 2 * j + 1 ≤ sat3V N)
    (hlo : T ≤ S.card) (hhi : S.card ≤ 2 * T - 2)
    (hwin1 : 3 * (sat3M N * j) + 3 * (j + 2) + 3 * sat3V N + 3 < T)
    (hwin2 : 2 * T - 2 < sat3M N * (sat3V N - j)) : False := by
  classical
  have hd0 := sat3_slot_dichotomy N hv hk hcut ⟨0, by omega⟩ hm hvj
  have hd1 := sat3_slot_dichotomy N hv hk hcut ⟨1, by omega⟩ hm hvj
  have hd2 := sat3_slot_dichotomy N hv hk hcut ⟨2, by omega⟩ hm hvj
  rcases hd0 with h0 | h0
  · have := sat3_full_mass N ⟨0, by omega⟩ h0
    omega
  rcases hd1 with h1 | h1
  · have := sat3_full_mass N ⟨1, by omega⟩ h1
    omega
  rcases hd2 with h2 | h2
  · have := sat3_full_mass N ⟨2, by omega⟩ h2
    omega
  have hemp := sat3_empty_mass N
    (fun t c => by
      rcases t with ⟨tv, htv⟩
      interval_cases tv
      · exact h0.1 c
      · exact h1.1 c
      · exact h2.1 c)
    (fun t => by
      rcases t with ⟨tv, htv⟩
      interval_cases tv
      · exact h0.2
      · exact h1.2
      · exact h2.2)
  omega

/-- **THE CIRCUIT CASH-OUT (proved)**: for a minimal SAT circuit at a window band, the balanced
wire cut is impossible — every hypothesis is arithmetic in `coneExcess`. -/
theorem sat3_final_balance_count (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N))
    (T : ℕ) (hT : 2 ≤ T)
    (hband : 2 * T - 1 ≤ (varsOf cc (cc.length - 1)).card)
    (hm : 2 * (coneExcess cc (cc.length - 1) + 1) + 6 ≤ sat3M N)
    (hvj : 2 * (coneExcess cc (cc.length - 1) + 1) + 1 ≤ sat3V N)
    (hwin1 : 3 * (sat3M N * (coneExcess cc (cc.length - 1) + 1))
      + 3 * (coneExcess cc (cc.length - 1) + 1 + 2) + 3 * sat3V N + 3 < T)
    (hwin2 : 2 * T - 2 < sat3M N
      * (sat3V N - (coneExcess cc (cc.length - 1) + 1))) : False := by
  obtain ⟨S, hlo, hhi, j, hj, hcut⟩ :=
    sat3_balanced_cut N hv hm3 hk cc hcomp hmin T hT hband
  have hmm : sat3M N * j ≤ sat3M N * (coneExcess cc (cc.length - 1) + 1) :=
    Nat.mul_le_mul_left _ hj
  have hvv : sat3M N * (sat3V N - (coneExcess cc (cc.length - 1) + 1))
      ≤ sat3M N * (sat3V N - j) :=
    Nat.mul_le_mul_left _ (by omega)
  exact sat3_balanced_cut_impossible N hv hk hcut (by omega) (by omega) hlo hhi
    (by omega) (by omega)

/-! ### The Ω(m) bound -/

/-- The reverse layout bound: `v ≤ 3m + 3`. -/
theorem sat3V_le_three_sat3M_add_three (N : ℕ) : sat3V N ≤ 3 * sat3M N + 3 := by
  by_contra hcon
  push_neg at hcon
  have hvv : sat3V N * sat3V N ≤ N := by
    have h := Nat.sqrt_le' N
    rw [pow_two] at h
    exact h
  have hNd : sat3D N * sat3M N + N % sat3D N = N := Nat.div_add_mod N (sat3D N)
  have hmd : N % sat3D N < sat3D N := Nat.mod_lt _ (sat3D_pos N)
  have hDD : sat3D N = 3 * (sat3V N + 1) := rfl
  have hA : (3 * sat3M N + 4) * sat3V N ≤ sat3V N * sat3V N :=
    Nat.mul_le_mul_right _ (by omega)
  have hB : (3 * sat3M N + 4) * sat3V N
      = 3 * (sat3M N * sat3V N) + 4 * sat3V N := by ring
  have hC : sat3D N * sat3M N = 3 * (sat3M N * sat3V N) + 3 * sat3M N := by
    rw [hDD]
    ring
  omega

/-- **THE Ω(m) CONE-EXCESS BOUND (proved, one stated hypothesis)**: if the minimal circuit's root
reads at least half the live selector grid, then `m < 32(coneExcess + 2)`, i.e.
`coneExcess ≥ m/32 − 2 = Ω(m) = Ω(√N)`.  The hypothesis `hvars` (root cone reads half the grid)
is the single remaining unproven rung — an evasiveness statement for minimal circuits. -/
theorem sat3_coneExcess_omega (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N))
    (hvars : sat3M N * sat3V N ≤ 2 * (varsOf cc (cc.length - 1)).card + 1) :
    sat3M N < 32 * (coneExcess cc (cc.length - 1) + 2) := by
  by_contra hbig
  push_neg at hbig
  set E := coneExcess cc (cc.length - 1) with hE
  set j1 := E + 1 with hj1
  set T := 3 * (sat3M N * j1) + 3 * (j1 + 2) + 3 * sat3V N + 4 with hT
  have h3m : 3 * sat3M N ≤ sat3V N := sat3_three_m_le_sat3V N
  have hv3 : sat3V N ≤ 3 * sat3M N + 3 := sat3V_le_three_sat3M_add_three N
  have h96 : 96 * (j1 + 1) ≤ sat3V N := by omega
  have hm64 : 64 ≤ sat3M N := by omega
  have hp1 : 96 * (j1 + 1) * sat3M N ≤ sat3V N * sat3M N :=
    Nat.mul_le_mul_right _ h96
  have hp2 : 96 * (j1 + 1) * sat3M N
      = 96 * (sat3M N * j1) + 96 * sat3M N := by ring
  have hp3 : sat3V N * sat3M N = sat3M N * sat3V N := Nat.mul_comm _ _
  have hj1v : j1 ≤ sat3V N := by omega
  have hsub : sat3M N * (sat3V N - j1) + sat3M N * j1 = sat3M N * sat3V N := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hj1v]
  have hwin2 : 2 * T - 2 < sat3M N * (sat3V N - j1) := by omega
  have hwin1 : 3 * (sat3M N * j1) + 3 * (j1 + 2) + 3 * sat3V N + 3 < T := by omega
  have hT2 : 2 ≤ T := by omega
  have hband : 2 * T - 1 ≤ (varsOf cc (cc.length - 1)).card := by omega
  have hm' : 2 * j1 + 6 ≤ sat3M N := by omega
  have hvj : 2 * j1 + 1 ≤ sat3V N := by omega
  exact sat3_final_balance_count N hv hm3 hk cc hcomp hmin T hT2 hband hm' hvj
    hwin1 hwin2

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_sign_concentration
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_balanced_cut_impossible
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_final_balance_count
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_coneExcess_omega
