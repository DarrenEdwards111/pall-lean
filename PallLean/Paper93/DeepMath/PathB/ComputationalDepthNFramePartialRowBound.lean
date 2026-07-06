import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameAnnulusCapacity

/-!
# N-Frame: the partial-row bound — the honest flat-sat3 consequence

Rung 23 of the multi-block arc (… → annulus capacity → **partial-row bound**).  The rung-20
parametric window is instantiated with PARTIAL rows (`V c := W ∩ S-row(c)` — `hdata` is then
automatic), fed by a two-stage Markov selection (no sorting): any `k` of the `A/2n`-heavy
blocks carry `k·A/2n` mass, else the heavy blocks alone carry `A/2`; repeat on columns.  All
mass inequalities are stated in MULTIPLIED form — no division anywhere.

  `markov_select` — **PROVED, generic**: `∃ C ⊆ U, |C| = k ∧ k·Σ_U f ≤ 2·(|U|·Σ_C f)`.
  `filter_card_sum_comm` — **PROVED**: rectangle mass double-counts across rows and columns.
  `sat3_partialrow_horn` — **PROVED**: with a live sign column, the captured rectangle prices
        `(m/8)·((m/8)·A_{t*}) ≤ 4·(m·(v·j))` — or the pin room is exhausted
        (`m < 3·(m/8) + j + 2`).
  `sat3_partialrow_cut_bound` — **PROVED, the assembled cut theorem**: for every cut,
        `(m/8)·((m/8)·(|S| − (j + 2m + 3v + 5))) ≤ 12·(m·(v·j))`
        ∨ `3·m·(v−j) ≤ |S|`  ∨  `m < 3·(m/8) + j + 2`  ∨  `m < 2j+6`  ∨  `v < 2j+1`.
  `sat3_partialrow_band_bound` — **PROVED, the band form**: the same five horns in
        `coneExcess + 1` at every band of a minimal SAT circuit.

## Honest scope — the visible cap

At heavy bands (`T = Θ(m·v)`) the capture horn forces `j = Θ(N)` and the all-full horn forces
`j ≥ v/3`-scale, so the adversary's ONLY refuge is the explicit `m`-horns: the pin room
(`j ≥ 5m/8`-scale) and the dichotomy threshold (`j ≥ (m−6)/2`).  The binding horn is
`m < 2j + 6`: **`coneExcess ≥ (m − 8)/2` uniformly — three times the rung-21 constant, and
STILL `Θ(√N)`.**  The theorem structure shows exactly why `(2+c)·N` is out of reach for this
instrument: the capture horn is `Θ(N)`-strong only while the `m`-horns do not fire, and the
adversary concedes only `Θ(m)` by firing them.  Every pin instrument is applicability-capped
at the pool scale; amplification beyond `Θ(√N)` requires a diversity channel that survives
total sign poisoning (see `COMPOSITION_DESIGN.md`).  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The Markov selection -/

/-- **The Markov selection (proved)**: some `k`-subset carries a `k/2n` fraction of the mass —
either `k` of the heavy elements do, or the heavy elements alone carry half. -/
theorem markov_select {α : Type*} [DecidableEq α] (U : Finset α) (f : α → ℕ) (k : ℕ)
    (hk : k ≤ U.card) :
    ∃ C, C ⊆ U ∧ C.card = k ∧
      k * (∑ a ∈ U, f a) ≤ 2 * (U.card * ∑ a ∈ C, f a) := by
  classical
  by_cases hn0 : U.card = 0
  · have hk0 : k = 0 := by omega
    refine ⟨∅, Finset.empty_subset U, ?_, ?_⟩
    · rw [Finset.card_empty]
      omega
    · rw [hk0, Nat.zero_mul]
      exact Nat.zero_le _
  set H : Finset α := U.filter (fun a => (∑ b ∈ U, f b) ≤ 2 * U.card * f a) with hH
  have hHsub : H ⊆ U := Finset.filter_subset _ _
  by_cases hbig : k ≤ H.card
  · obtain ⟨C, hCH, hCk⟩ := Finset.exists_subset_card_eq hbig
    refine ⟨C, hCH.trans hHsub, hCk, ?_⟩
    have hper : ∀ a ∈ C, (∑ b ∈ U, f b) ≤ 2 * U.card * f a := by
      intro a ha
      have := hCH ha
      rw [hH, Finset.mem_filter] at this
      exact this.2
    have hsum : ∑ _a ∈ C, (∑ b ∈ U, f b) ≤ ∑ a ∈ C, 2 * U.card * f a :=
      Finset.sum_le_sum hper
    rw [Finset.sum_const, smul_eq_mul, hCk] at hsum
    have hmul : ∑ a ∈ C, 2 * U.card * f a = 2 * (U.card * ∑ a ∈ C, f a) := by
      rw [← Finset.mul_sum]
      ring
    omega
  · push_neg at hbig
    have hcompl : (U \ H).card = U.card - H.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hHsub]
    obtain ⟨D, hDsub, hDcard⟩ := Finset.exists_subset_card_eq
      (s := U \ H) (n := k - H.card) (by omega)
    have hHD : Disjoint H D := Finset.disjoint_left.mpr (fun a haH haD =>
      (Finset.mem_sdiff.mp (hDsub haD)).2 haH)
    refine ⟨H ∪ D,
      Finset.union_subset hHsub (hDsub.trans Finset.sdiff_subset), ?_, ?_⟩
    · rw [Finset.card_union_of_disjoint hHD]
      omega
    · -- the heavy mass alone is at least half
      have hA_split : (∑ a ∈ U \ H, f a) + (∑ a ∈ H, f a) = ∑ a ∈ U, f a :=
        Finset.sum_sdiff hHsub
      have hlightper : ∀ a ∈ U \ H, 2 * U.card * f a ≤ ∑ b ∈ U, f b := by
        intro a ha
        obtain ⟨haU, haH⟩ := Finset.mem_sdiff.mp ha
        by_contra hcon
        push_neg at hcon
        exact haH (by
          rw [hH, Finset.mem_filter]
          exact ⟨haU, by omega⟩)
      have h2' : ∑ a ∈ U \ H, (2 * U.card * f a)
          ≤ (U \ H).card * (∑ b ∈ U, f b) := by
        have h := Finset.sum_le_sum hlightper
        rwa [Finset.sum_const, smul_eq_mul] at h
      have heq2 : ∑ a ∈ U \ H, (2 * U.card * f a)
          = 2 * (U.card * ∑ a ∈ U \ H, f a) := by
        rw [← Finset.mul_sum]
        ring
      have hql : (U \ H).card * (∑ b ∈ U, f b)
          ≤ U.card * (∑ b ∈ U, f b) :=
        Nat.mul_le_mul_right _ (Finset.card_le_card Finset.sdiff_subset)
      have hP : U.card * (∑ a ∈ U, f a)
          = U.card * (∑ a ∈ U \ H, f a) + U.card * (∑ a ∈ H, f a) := by
        rw [← hA_split, Nat.mul_add]
      have hYZ : U.card * (∑ a ∈ H, f a) ≤ U.card * (∑ a ∈ H ∪ D, f a) :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset
          Finset.subset_union_left)
      have hc1 : k * (∑ a ∈ U, f a) ≤ U.card * (∑ a ∈ U, f a) :=
        Nat.mul_le_mul_right _ hk
      omega

/-! ### The rectangle double count -/

theorem filter_card_sum_comm {β γ : Type*} (B : Finset β) (W : Finset γ)
    (p : β → γ → Prop) [∀ b w, Decidable (p b w)] :
    ∑ b ∈ B, (W.filter (fun w => p b w)).card
      = ∑ w ∈ W, (B.filter (fun b => p b w)).card := by
  classical
  have h1 : ∀ b, (W.filter (fun w => p b w)).card
      = ∑ w ∈ W, if p b w then 1 else 0 := by
    intro b
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have h2 : ∀ w, (B.filter (fun b => p b w)).card
      = ∑ b ∈ B, if p b w then 1 else 0 := by
    intro w
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc ∑ b ∈ B, (W.filter (fun w => p b w)).card
      = ∑ b ∈ B, ∑ w ∈ W, if p b w then 1 else 0 :=
        Finset.sum_congr rfl (fun b _ => h1 b)
    _ = ∑ w ∈ W, ∑ b ∈ B, if p b w then 1 else 0 := Finset.sum_comm
    _ = ∑ w ∈ W, (B.filter (fun b => p b w)).card :=
        Finset.sum_congr rfl (fun w _ => (h2 w).symm)

/-! ### The partial-row horn -/

set_option maxHeartbeats 3200000 in
/-- **THE PARTIAL-ROW HORN (proved)**: with a live sign column, the two-stage Markov rectangle
prices `(m/8)·((m/8)·A_{t*}) ≤ 4·(m·(v·j))` — or the pin room is exhausted. -/
theorem sat3_partialrow_horn (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (tstar t0 : Fin 3)
    (hlive : ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b t0 (sat3V N) (by omega) ∈ S)).card ≤ j + 2) :
    (sat3M N / 8) * ((sat3M N / 8) *
        (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c tstar w.val (by have := w.isLt; omega) ∈ S)).card))
      ≤ 4 * (sat3M N * (sat3V N * j))
    ∨ sat3M N < 3 * (sat3M N / 8) + j + 2 := by
  classical
  by_cases hq0 : sat3M N / 8 = 0
  · left
    rw [hq0, Nat.zero_mul]
    exact Nat.zero_le _
  by_cases hroomOK : 3 * (sat3M N / 8) + j + 2 ≤ sat3M N
  swap
  · right
    omega
  left
  have hmv : sat3M N - 1 ≤ sat3V N := sat3M_pred_le_sat3V N
  -- the swapped world: data slot tstar becomes slot 0
  set S' : Finset (Fin N) := S.image (slotSwapBit N tstar) with hS'
  have hcut' : CutFactorization (sat3Family N) S' j :=
    cut_transport (sat3Family N) (slotSwapBit N tstar)
      (slotSwapBit_invol N tstar) (sat3Family_slotSwap N tstar) hcut
  have hswz : swapSlotF tstar ⟨0, by omega⟩ = tstar := swapSlotF_zero tstar (by omega)
  have hf : ∀ c : Fin (sat3M N),
      ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')).card
      = ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c tstar w.val (by have := w.isLt; omega) ∈ S)).card := by
    intro c
    congr 1
    ext w
    rw [Finset.mem_filter, Finset.mem_filter, hS', sat3_bit_mem_swap, hswz]
  set ps' : Fin 3 := swapSlotF tstar t0 with hps'
  have hQ' : ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ps' (sat3V N) (by omega) ∈ S')).card
      = ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b t0 (sat3V N) (by omega) ∈ S)).card := by
    congr 1
    ext b
    rw [Finset.mem_filter, Finset.mem_filter, hS', sat3_bit_mem_swap, hps',
      swapSlotF_invol]
  -- stage 1: block selection
  obtain ⟨C, hCsub, hCcard, hC⟩ := markov_select
    (Finset.univ : Finset (Fin (sat3M N)))
    (fun c : Fin (sat3M N) =>
      ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w : Fin (sat3V N) =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')).card)
    (sat3M N / 8)
    (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  -- stage 2: column selection within C
  obtain ⟨W, hWsub, hWcard, hW⟩ := markov_select
    (Finset.univ : Finset (Fin (sat3V N)))
    (fun w : Fin (sat3V N) => (C.filter (fun c : Fin (sat3M N) =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')).card)
    (sat3M N / 8)
    (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  -- the two double counts
  have hgf : ∑ c ∈ C, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')).card
      = ∑ w : Fin (sat3V N), (C.filter (fun c =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')).card :=
    filter_card_sum_comm C Finset.univ
      (fun (c : Fin (sat3M N)) (w : Fin (sat3V N)) =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')
  have hVW : ∑ c ∈ C, (W.filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')).card
      = ∑ w ∈ W, (C.filter (fun c =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')).card :=
    filter_card_sum_comm C W
      (fun (c : Fin (sat3M N)) (w : Fin (sat3V N)) =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')
  -- the pool bridge for the pin room
  have hQpool : ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
      sat3Bit N b ps' (sat3V N) (by omega) ∈ S')).card ≤ j + 2 := by
    have hQsub : ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
        sat3Bit N b ps' (sat3V N) (by omega) ∈ S')).card
        ≤ ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
        sat3Bit N b ps' (sat3V N) (by omega) ∈ S')).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
    rw [hQ'] at hQsub
    exact hQsub.trans hlive
  have hbu : (C.biUnion (fun c => W.filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S'))).card
      ≤ sat3M N / 8 := by
    have h := Finset.card_le_card (Finset.biUnion_subset.mpr
      (fun (c : Fin (sat3M N)) (_ : c ∈ C) => Finset.filter_subset
        (fun w : Fin (sat3V N) =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S') W))
    omega
  -- the window with partial rows
  have hwin := sat3_pinslot_window N hv hcut' C ps' (fun c =>
      W.filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S'))
    (fun c hc w hw => (Finset.mem_filter.mp hw).2)
    (by omega)
    (by omega)
    (by omega)
  -- chain the three multiplied inequalities
  have hstage2 : (sat3M N / 8) * (∑ c ∈ C, ((Finset.univ :
      Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')).card)
      ≤ 2 * (sat3V N * j) := by
    rw [hgf]
    calc (sat3M N / 8) * (∑ w : Fin (sat3V N), (C.filter (fun c =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')).card)
        ≤ 2 * ((Finset.univ : Finset (Fin (sat3V N))).card
          * ∑ w ∈ W, (C.filter (fun c =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')).card) :=
          hW
      _ = 2 * (sat3V N * ∑ c ∈ C, (W.filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')).card) := by
          rw [Finset.card_univ, Fintype.card_fin, hVW]
      _ ≤ 2 * (sat3V N * j) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (sat3V N) hwin)
  -- stage 1 chained through stage 2
  have hA' : ∑ c : Fin (sat3M N), ((Finset.univ :
      Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')).card
      = ∑ c : Fin (sat3M N), ((Finset.univ :
      Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c tstar w.val (by have := w.isLt; omega) ∈ S)).card :=
    Finset.sum_congr rfl (fun c _ => hf c)
  calc (sat3M N / 8) * ((sat3M N / 8) *
      (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c tstar w.val (by have := w.isLt; omega) ∈ S)).card))
      = (sat3M N / 8) * ((sat3M N / 8) *
        (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')).card)) := by
        rw [hA']
    _ ≤ (sat3M N / 8) * (2 * ((Finset.univ : Finset (Fin (sat3M N))).card
        * ∑ c ∈ C, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')).card)) :=
        Nat.mul_le_mul_left _ hC
    _ = sat3M N * (2 * ((sat3M N / 8) * (∑ c ∈ C, ((Finset.univ :
        Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S')).card))) := by
        rw [Finset.card_univ, Fintype.card_fin]
        ring
    _ ≤ sat3M N * (2 * (2 * (sat3V N * j))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hstage2)
    _ = 4 * (sat3M N * (sat3V N * j)) := by ring

/-! ### The live-slot bound -/

set_option maxHeartbeats 1600000 in
/-- **The live-slot bound (proved)**: a single live sign column prices a third of the grid
mass through the Markov rectangle. -/
theorem sat3_partialrow_live_bound (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (t0 : Fin 3)
    (hlive : ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b t0 (sat3V N) (by omega) ∈ S)).card ≤ j + 2) :
    (sat3M N / 8) * ((sat3M N / 8)
        * (S.card - (j + 2 * sat3M N + 3 * sat3V N + 5)))
      ≤ 12 * (sat3M N * (sat3V N * j))
    ∨ sat3M N < 3 * (sat3M N / 8) + j + 2 := by
  classical
  have hled := sat3_grid_mass_ledger N S
  -- every sign column is at most the block count
  have hQ0 : ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card ≤ sat3M N := by
    have h := Finset.card_filter_le (Finset.univ : Finset (Fin (sat3M N)))
      (fun c => sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hQ1 : ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      sat3Bit N c ⟨1, by omega⟩ (sat3V N) (by omega) ∈ S)).card ≤ sat3M N := by
    have h := Finset.card_filter_le (Finset.univ : Finset (Fin (sat3M N)))
      (fun c => sat3Bit N c ⟨1, by omega⟩ (sat3V N) (by omega) ∈ S)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hQ2 : ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      sat3Bit N c ⟨2, by omega⟩ (sat3V N) (by omega) ∈ S)).card ≤ sat3M N := by
    have h := Finset.card_filter_le (Finset.univ : Finset (Fin (sat3M N)))
      (fun c => sat3Bit N c ⟨2, by omega⟩ (sat3V N) (by omega) ∈ S)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  -- the live column caps the sign total at 2m + j + 2
  have hQsum : ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c ⟨1, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c ⟨2, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      ≤ (j + 2) + 2 * sat3M N := by
    rcases t0 with ⟨tv, htv⟩
    interval_cases tv
    · omega
    · omega
    · omega
  -- the max slot carries a third of the selector mass
  obtain ⟨tstar, h3A⟩ : ∃ t : Fin 3,
      (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
      + (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
      + (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨2, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
      ≤ 3 * (∑ c : Fin (sat3M N), ((Finset.univ :
        Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c t w.val (by have := w.isLt; omega) ∈ S)).card) := by
    by_cases h01 : (∑ c : Fin (sat3M N), ((Finset.univ :
        Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
        ≤ (∑ c : Fin (sat3M N), ((Finset.univ :
        Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
    · by_cases h02 : (∑ c : Fin (sat3M N), ((Finset.univ :
          Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨2, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
          ≤ (∑ c : Fin (sat3M N), ((Finset.univ :
          Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
      · exact ⟨⟨0, by omega⟩, by omega⟩
      · exact ⟨⟨2, by omega⟩, by omega⟩
    · by_cases h12 : (∑ c : Fin (sat3M N), ((Finset.univ :
          Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨2, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
          ≤ (∑ c : Fin (sat3M N), ((Finset.univ :
          Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
      · exact ⟨⟨1, by omega⟩, by omega⟩
      · exact ⟨⟨2, by omega⟩, by omega⟩
  rcases sat3_partialrow_horn N hv hcut tstar t0 hlive with hcap | hroom
  · left
    have hmass : S.card - (j + 2 * sat3M N + 3 * sat3V N + 5)
        ≤ 3 * (∑ c : Fin (sat3M N), ((Finset.univ :
          Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c tstar w.val (by have := w.isLt; omega) ∈ S)).card) := by
      omega
    calc (sat3M N / 8) * ((sat3M N / 8)
        * (S.card - (j + 2 * sat3M N + 3 * sat3V N + 5)))
        ≤ (sat3M N / 8) * ((sat3M N / 8)
          * (3 * (∑ c : Fin (sat3M N), ((Finset.univ :
            Finset (Fin (sat3V N))).filter (fun w =>
            sat3Bit N c tstar w.val (by have := w.isLt; omega) ∈ S)).card))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hmass)
      _ = 3 * ((sat3M N / 8) * ((sat3M N / 8)
          * (∑ c : Fin (sat3M N), ((Finset.univ :
            Finset (Fin (sat3V N))).filter (fun w =>
            sat3Bit N c tstar w.val (by have := w.isLt; omega) ∈ S)).card))) := by
          ring
      _ ≤ 3 * (4 * (sat3M N * (sat3V N * j))) := Nat.mul_le_mul_left 3 hcap
      _ = 12 * (sat3M N * (sat3V N * j)) := by ring
  · right
    exact hroom

/-! ### The assembled cut theorem -/

set_option maxHeartbeats 1600000 in
/-- **THE PARTIAL-ROW CUT BOUND (proved)**: for every cut, the Markov rectangle prices a third
of the balanced mass — or the adversary fires one of the explicit `m`/`v`-scale horns. -/
theorem sat3_partialrow_cut_bound (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j) :
    (sat3M N / 8) * ((sat3M N / 8)
        * (S.card - (j + 2 * sat3M N + 3 * sat3V N + 5)))
      ≤ 12 * (sat3M N * (sat3V N * j))
    ∨ 3 * (sat3M N * (sat3V N - j)) ≤ S.card
    ∨ sat3M N < 3 * (sat3M N / 8) + j + 2
    ∨ sat3M N < 2 * j + 6
    ∨ sat3V N < 2 * j + 1 := by
  classical
  by_cases hvj : 2 * j + 1 ≤ sat3V N
  · by_cases hm : 2 * j + 6 ≤ sat3M N
    · have hk : (sat3M N - 2) + 1 ≤ sat3M N := by omega
      rcases sat3_slot_dichotomy N hv hk hcut ⟨0, by omega⟩ hm hvj with
        hf0 | ⟨-, hl0⟩
      · rcases sat3_slot_dichotomy N hv hk hcut ⟨1, by omega⟩ hm hvj with
          hf1 | ⟨-, hl1⟩
        · rcases sat3_slot_dichotomy N hv hk hcut ⟨2, by omega⟩ hm hvj with
            hf2 | ⟨-, hl2⟩
          · -- all full
            refine Or.inr (Or.inl (sat3_full_mass_three N ?_))
            intro t c
            rcases t with ⟨tv, htv⟩
            interval_cases tv
            · exact hf0 c
            · exact hf1 c
            · exact hf2 c
          · rcases sat3_partialrow_live_bound N hv hcut ⟨2, by omega⟩ hl2 with
              h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inl h))
        · rcases sat3_partialrow_live_bound N hv hcut ⟨1, by omega⟩ hl1 with
            h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inl h))
      · rcases sat3_partialrow_live_bound N hv hcut ⟨0, by omega⟩ hl0 with
          h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))

/-! ### The band form -/

/-- **THE PARTIAL-ROW BAND BOUND (proved)**: the five horns in `coneExcess + 1` at every band
of a minimal SAT circuit.  At heavy bands the capture and all-full horns force `Θ(N)`/`Θ(v)`,
so the binding horn is the explicit `m < 2·(CE+1) + 6`: `coneExcess ≥ (m − 8)/2` uniformly —
three times the rung-21 constant, still `Θ(√N)`, and the horns SHOW the cap. -/
theorem sat3_partialrow_band_bound (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N))
    (T : ℕ) (hT : 2 ≤ T)
    (hband : 2 * T - 1 ≤ (varsOf cc (cc.length - 1)).card) :
    (sat3M N / 8) * ((sat3M N / 8)
        * (T - ((coneExcess cc (cc.length - 1) + 1)
          + 2 * sat3M N + 3 * sat3V N + 5)))
      ≤ 12 * (sat3M N * (sat3V N * (coneExcess cc (cc.length - 1) + 1)))
    ∨ 3 * (sat3M N * (sat3V N - (coneExcess cc (cc.length - 1) + 1))) ≤ 2 * T - 2
    ∨ sat3M N < 3 * (sat3M N / 8) + (coneExcess cc (cc.length - 1) + 1) + 2
    ∨ sat3M N < 2 * (coneExcess cc (cc.length - 1) + 1) + 6
    ∨ sat3V N < 2 * (coneExcess cc (cc.length - 1) + 1) + 1 := by
  classical
  obtain ⟨S, hT1, hT2, j, hj, hcut⟩ :=
    sat3_balanced_cut N hv hm3 hk cc hcomp hmin T hT hband
  rcases sat3_partialrow_cut_bound N hv hcut with h | h | h | h | h
  · left
    have hinner : T - ((coneExcess cc (cc.length - 1) + 1)
        + 2 * sat3M N + 3 * sat3V N + 5)
        ≤ S.card - (j + 2 * sat3M N + 3 * sat3V N + 5) := by
      omega
    calc (sat3M N / 8) * ((sat3M N / 8)
        * (T - ((coneExcess cc (cc.length - 1) + 1)
          + 2 * sat3M N + 3 * sat3V N + 5)))
        ≤ (sat3M N / 8) * ((sat3M N / 8)
          * (S.card - (j + 2 * sat3M N + 3 * sat3V N + 5))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hinner)
      _ ≤ 12 * (sat3M N * (sat3V N * j)) := h
      _ ≤ 12 * (sat3M N * (sat3V N * (coneExcess cc (cc.length - 1) + 1))) :=
          Nat.mul_le_mul_left 12 (Nat.mul_le_mul_left _
            (Nat.mul_le_mul_left _ hj))
  · right
    left
    have hmono : 3 * (sat3M N * (sat3V N - (coneExcess cc (cc.length - 1) + 1)))
        ≤ 3 * (sat3M N * (sat3V N - j)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hj _))
    omega
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.markov_select
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_partialrow_horn
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_partialrow_cut_bound
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_partialrow_band_bound
