import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMultiBlockWindow

/-!
# N-Frame: the multi-block balance census — poison-priced inside mass

Rung 6 of the multi-block arc (patch → context → eval → drag → window → **census**).  The
rebuilt window prices a block set at ONE shared budget `j`, under side conditions (slot-1-clean
blocks, pin-pool room).  The census removes the side conditions by PRICING the adversary's
evasions, and extracts the two regimes the additive drag actually reaches:

  `sat3_multi_clean_census` — **PROVED, the `m·j → j` core**: for slot-1-clean blocks with
        pin-pool room `j + 1 + Q ≤ m − |C|` (and `m − |C| ≤ v`), the TOTAL slot-0 inside mass
        over `C` is at most `j`.  Proof: were it `≥ j + 1`, a sub-pattern tuple of total size
        exactly `j + 1` (a `(j+1)`-subset of the inside sigma-set) would feed the rebuilt
        window and contradict it.  Room costs only `j + 1 + Q` pool blocks — `j`-scale, so the
        census is live precisely when `j ≪ m`.
  `sat3_multi_dirty_le_slot1_mass` — each slot-1-dirty block carries at least one slot-1 bit of
        `S`: the dirty count is priced in `S`-bits.
  `sat3_multi_poison_census` — **PROVED, the unconditional census**: for EVERY cut
        factorization, `A₀ ≤ j + (d₁ + Q + j + 1) · v`, where `A₀` = total slot-0 inside mass,
        `d₁` = slot-1-dirty block count, `Q` = sign-poisoned block count.  Nontrivial whenever
        `j + d₁ + Q ≪ m` (the old census's per-block bound gave only `A₀ ≤ m·j`).
  `sat3_multi_poison_census_mass` — the same with `d₁` relaxed to the slot-1 inside mass `A₁`.
  `sat3_multi_rectangle_census` — **PROVED, the rectangle regime**: clean blocks `C` sharing a
        COMMON inside-position set `W` (with room `|W| + Q ≤ m − |C|`) force `|C| · |W| ≤ j`.
        This is where the additive drag genuinely reaches `Ω(N)`: at `|C|, |W| = Θ(m)` the
        product is `Θ(m²) = Θ(N)`, and `j ≤ coneExcess + 1`.
  `sat3_multi_census_circuit` — **PROVED, the circuit cash-out**: for a minimal SAT circuit, at
        every threshold band there is a balanced `S` with
        `A₀ ≤ (coneExcess + 1) + (A₁ + Q + coneExcess + 2) · v`.

## Honest scope — what the census does and does not reach

The mass census is structurally capped at `Ω(v) = Ω(√N)` cone-excess: bands satisfy `T ≤ N`
and each budget unit prices at most `v + 1` inside bits, so even a poison-free adversary forces
only `j ≥ (T − v)/(v + 1) = O(v)`.  The route to `coneExcess = Ω(N)` (hence a `(2 + c)·N`
cbudget bound in the wire model) is the RECTANGLE regime: `Θ(m)` clean blocks sharing `Θ(m)`
common inside positions give `j ≥ Θ(m²) = Θ(N)`.  Whether every balanced cut of a minimal SAT
circuit must contain such a rectangle (or spread its inside mass so thin that a different count
applies) is the position-spread dichotomy — the named remaining frontier of this arc, analogous
to `hvars` in the single-block census.  It is NOT discharged here.  The adversary's evasions
are priced but not eliminated: one slot-1 poison bit inside `S` ejects one block from the clean
set (up to `v` unpriced slot-0 bits — ratio `v : 1`), one sign bit inside `S` eats one pool
pin.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The `m·j → j` core -/

set_option maxHeartbeats 1600000 in
/-- **THE CLEAN CENSUS (proved)**: slot-1-clean blocks with `j`-scale pin-pool room have TOTAL
slot-0 inside mass at most `j` — one shared budget for the whole set. -/
theorem sat3_multi_clean_census (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (C : Finset (Fin (sat3M N)))
    (hclean1 : ∀ c ∈ C, ∀ w : Fin (sat3V N),
      sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)
    (hkv : sat3M N - C.card ≤ sat3V N)
    (hpool : j + 1 + ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      ≤ sat3M N - C.card) :
    ∑ c ∈ C, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card ≤ j := by
  classical
  by_contra hcon
  push_neg at hcon
  -- the inside sigma-set has more than `j` elements: extract a `(j+1)`-subpattern
  have hDcard : (C.sigma (fun c => (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))).card
      = ∑ c ∈ C, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card :=
    Finset.card_sigma _ _
  have hex : j + 1 ≤ (C.sigma (fun c =>
      (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))).card := by
    omega
  obtain ⟨E, hEsub, hEcard⟩ := Finset.exists_subset_card_eq hex
  -- the subpattern tuple slices `E` back: total size exactly `j + 1`
  have hslice : C.sigma (fun c => sat3TupleOf N (fun c' =>
      (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c' ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)) E c) = E := by
    ext ⟨c, w⟩
    rw [Finset.mem_sigma]
    constructor
    · rintro ⟨hc, hw⟩
      exact (sat3TupleOf_mem N _ E c w (sat3TupleOf_subset N _ E c hw)).mp hw
    · intro hqE
      have hqD := hEsub hqE
      rw [Finset.mem_sigma] at hqD
      exact ⟨hqD.1, (sat3TupleOf_mem N _ E c w hqD.2).mpr hqE⟩
  have hsum : ∑ c ∈ C, (sat3TupleOf N (fun c' =>
      (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c' ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)) E c).card
      = j + 1 := by
    rw [← Finset.card_sigma, hslice, hEcard]
  -- the rebuilt window on the subpattern
  have hroom : (C.biUnion (sat3TupleOf N (fun c' =>
      (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c' ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)) E)).card
      + ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      ≤ sat3M N - C.card := by
    have hbu := Finset.card_biUnion_le (s := C) (t := sat3TupleOf N (fun c' =>
      (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c' ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)) E)
    rw [hsum] at hbu
    omega
  have hwin := sat3_multi_window N hv hcut C
    (sat3TupleOf N (fun c' => (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c' ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)) E)
    (fun c hc w hw => (Finset.mem_filter.mp (sat3TupleOf_subset N _ E c hw)).2)
    (fun c hc c' hc' w hw => hclean1 c hc w)
    hkv hroom
  omega

/-! ### The poison price of a dirty block -/

/-- **The dirty count is priced in `S`-bits (proved)**: every slot-1-dirty block carries at
least one slot-1 selector bit of `S`. -/
theorem sat3_multi_dirty_le_slot1_mass (N : ℕ) (S : Finset (Fin N)) :
    ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
        (by have := w.isLt; omega) ∈ S)).card
    ≤ ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card := by
  classical
  rw [Finset.card_eq_sum_ones]
  calc ∑ _c ∈ (Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S), 1
      ≤ ∑ c ∈ (Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S),
        ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card := by
        apply Finset.sum_le_sum
        intro c hc
        obtain ⟨w, hw⟩ := (Finset.mem_filter.mp hc).2
        exact Finset.card_pos.mpr
          ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩⟩
    _ ≤ ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-! ### The unconditional poison census -/

set_option maxHeartbeats 1600000 in
/-- **THE BALANCE CENSUS (proved)**: over EVERY cut factorization, the total slot-0 inside mass
is priced by one shared budget plus the poison counts:
`A₀ ≤ j + (d₁ + Q + j + 1) · v` — `d₁` dirty blocks (slot-1 poison), `Q` sign-poisoned blocks,
`j + 1` reserved pin blocks. -/
theorem sat3_multi_poison_census (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j) :
    ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
    ≤ j + (((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S)).card
      + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      + j + 1) * sat3V N := by
  classical
  set Dirty : Finset (Fin (sat3M N)) :=
    (Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
        (by have := w.isLt; omega) ∈ S) with hDirty
  set SignIn : Finset (Fin (sat3M N)) :=
    (Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S) with hSignIn
  set Clean : Finset (Fin (sat3M N)) :=
    (Finset.univ : Finset (Fin (sat3M N))) \ Dirty with hClean
  have hCleancard : Clean.card = sat3M N - Dirty.card := by
    rw [hClean, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Fintype.card_fin]
  have hCleanle : Clean.card ≤ sat3M N := by
    have h := Finset.card_le_card (Finset.subset_univ Clean)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hDirtyle : Dirty.card ≤ sat3M N := by
    have h := Finset.card_le_card (Finset.subset_univ Dirty)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hmv : sat3M N - 1 ≤ sat3V N := sat3M_pred_le_sat3V N
  have hIn0le : ∀ c : Fin (sat3M N),
      ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
      ≤ sat3V N := by
    intro c
    have h := Finset.card_filter_le (Finset.univ : Finset (Fin (sat3V N)))
      (fun w => sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  by_cases hbig : j + 1 + SignIn.card + 1 ≤ Clean.card
  · -- the `j`-scale reserve fits: run the clean census on the rest of the clean blocks
    obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq
      (s := Clean) (n := j + 1 + SignIn.card) (by omega)
    set C : Finset (Fin (sat3M N)) := Clean \ R with hC
    have hCcard : C.card = Clean.card - (j + 1 + SignIn.card) := by
      rw [hC, Finset.card_sdiff, Finset.inter_eq_left.mpr hRsub, hRcard]
    have hC1 : 1 ≤ C.card := by omega
    have hpoolC : sat3M N - C.card = Dirty.card + (j + 1 + SignIn.card) := by
      omega
    have hclean1 : ∀ c ∈ C, ∀ w : Fin (sat3V N),
        sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S := by
      intro c hc w hw
      have hcClean : c ∈ Clean := (Finset.mem_sdiff.mp hc).1
      rw [hClean] at hcClean
      have hnd : c ∉ Dirty := (Finset.mem_sdiff.mp hcClean).2
      apply hnd
      rw [hDirty]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, ⟨w, hw⟩⟩
    have hkv : sat3M N - C.card ≤ sat3V N := by omega
    have hQle : ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card ≤ SignIn.card := by
      apply Finset.card_le_card
      intro b hb
      rw [Finset.mem_filter] at hb
      rw [hSignIn]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb.2⟩
    have hpool : j + 1 + ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
        ≤ sat3M N - C.card := by
      omega
    have hcen := sat3_multi_clean_census N hv hcut C hclean1 hkv hpool
    have hsplit : ∑ c ∈ ((Finset.univ : Finset (Fin (sat3M N))) \ C),
        ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
        + ∑ c ∈ C, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
        = ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card :=
      Finset.sum_sdiff (Finset.subset_univ C)
    have hrest : ∑ c ∈ ((Finset.univ : Finset (Fin (sat3M N))) \ C),
        ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
        ≤ (Dirty.card + (j + 1 + SignIn.card)) * sat3V N := by
      calc ∑ c ∈ ((Finset.univ : Finset (Fin (sat3M N))) \ C),
          ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
            sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
          ≤ ∑ _c ∈ ((Finset.univ : Finset (Fin (sat3M N))) \ C), sat3V N :=
            Finset.sum_le_sum (fun c _ => hIn0le c)
        _ = (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card * sat3V N := by
            rw [Finset.sum_const, smul_eq_mul]
        _ = (sat3M N - C.card) * sat3V N := by
            rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
              Fintype.card_fin]
        _ = (Dirty.card + (j + 1 + SignIn.card)) * sat3V N := by
            rw [hpoolC]
    calc ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
        = ∑ c ∈ ((Finset.univ : Finset (Fin (sat3M N))) \ C),
            ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
              sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
          + ∑ c ∈ C, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
              sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card :=
          hsplit.symm
      _ ≤ (Dirty.card + (j + 1 + SignIn.card)) * sat3V N + j :=
          Nat.add_le_add hrest hcen
      _ = (Dirty.card + SignIn.card + j + 1) * sat3V N + j := by
          ring
      _ = j + (Dirty.card + SignIn.card + j + 1) * sat3V N := Nat.add_comm _ _
  · -- the reserve does not fit: the whole grid is inside the poison budget
    push_neg at hbig
    have hA0 : ∑ c : Fin (sat3M N),
        ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
        ≤ sat3M N * sat3V N := by
      calc ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
            sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
          ≤ ∑ _c : Fin (sat3M N), sat3V N :=
            Finset.sum_le_sum (fun c _ => hIn0le c)
        _ = sat3M N * sat3V N := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    calc ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
        ≤ sat3M N * sat3V N := hA0
      _ ≤ (Dirty.card + SignIn.card + j + 1) * sat3V N :=
          Nat.mul_le_mul_right _ (by omega)
      _ ≤ j + (Dirty.card + SignIn.card + j + 1) * sat3V N := Nat.le_add_left _ _

set_option maxHeartbeats 800000 in
/-- **The census, fully `S`-priced (proved)**: `A₀ ≤ j + (A₁ + Q + j + 1) · v` — beyond the
budget terms, every factor on the right counts actual bits of `S`. -/
theorem sat3_multi_poison_census_mass (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j) :
    ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
    ≤ j + ((∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
      + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      + j + 1) * sat3V N := by
  have hcen := sat3_multi_poison_census N hv hcut
  have hd := sat3_multi_dirty_le_slot1_mass N S
  exact le_trans hcen
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) j)

/-! ### The rectangle regime -/

set_option maxHeartbeats 800000 in
/-- **THE RECTANGLE CENSUS (proved)**: clean blocks `C` sharing a COMMON inside-position set
`W` force `|C| · |W| ≤ j` — the regime where the additive drag reaches `Θ(m²) = Θ(N)`. -/
theorem sat3_multi_rectangle_census (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (C : Finset (Fin (sat3M N))) (W : Finset (Fin (sat3V N)))
    (hrect : ∀ c ∈ C, ∀ w ∈ W,
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)
    (hclean1 : ∀ c ∈ C, ∀ w : Fin (sat3V N),
      sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)
    (hkv : sat3M N - C.card ≤ sat3V N)
    (hpool : W.card + ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      ≤ sat3M N - C.card) :
    C.card * W.card ≤ j := by
  classical
  have hroom : (C.biUnion (fun _ => W)).card
      + ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      ≤ sat3M N - C.card := by
    have hbu : (C.biUnion (fun _ => W)).card ≤ W.card :=
      Finset.card_le_card (Finset.biUnion_subset.mpr (fun _ _ => Finset.Subset.refl W))
    omega
  have hwin := sat3_multi_window N hv hcut C (fun _ => W)
    (fun c hc w hw => hrect c hc w hw)
    (fun c hc c' hc' w hw => hclean1 c hc w)
    hkv hroom
  calc C.card * W.card = ∑ _c ∈ C, W.card := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ j := hwin

/-! ### The circuit cash-out -/

/-- **THE CIRCUIT CENSUS (proved)**: for a minimal SAT circuit, at every threshold band there
is a balanced coordinate set `S` whose slot-0 inside mass is priced by `coneExcess + 1` plus
the poison terms. -/
theorem sat3_multi_census_circuit (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N))
    (T : ℕ) (hT : 2 ≤ T)
    (hband : 2 * T - 1 ≤ (varsOf cc (cc.length - 1)).card) :
    ∃ S : Finset (Fin N), T ≤ S.card ∧ S.card ≤ 2 * T - 2 ∧
      ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
      ≤ (coneExcess cc (cc.length - 1) + 1)
        + ((∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
            sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
          + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
            sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
          + coneExcess cc (cc.length - 1) + 2) * sat3V N := by
  obtain ⟨S, hT1, hT2, j, hj, hcut⟩ :=
    sat3_balanced_cut N hv hm3 hk cc hcomp hmin T hT hband
  refine ⟨S, hT1, hT2, ?_⟩
  have hcen := sat3_multi_poison_census_mass N hv hcut
  calc ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
      ≤ j + ((∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
        + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
          sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
        + j + 1) * sat3V N := hcen
    _ ≤ (coneExcess cc (cc.length - 1) + 1)
        + ((∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
            sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
          + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
            sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
          + coneExcess cc (cc.length - 1) + 2) * sat3V N :=
        Nat.add_le_add hj (Nat.mul_le_mul_right _ (by omega))

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_clean_census
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_poison_census
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_rectangle_census
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_census_circuit
