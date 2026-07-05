import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMultiBlockSpread

/-!
# N-Frame: the bulk upgrade — the two-cover census and the local rectangle

Rung 8 of the multi-block arc (… → census → spread → **bulk**).  Rung 6 priced the clean blocks
through ONE window application and paid a `(j + 1 + Q)·v` reserve: the pin blocks' own columns
went unpriced.  The repair is the TWO-COVER: when the pool has room for half the grid
(`2(j + 1 + Q) ≤ m`), split the clean family into two halves — each half is priced at `j` by one
window application while the OTHER half sits in its pin pool.  Nothing is left unpriced:

  `sat3_multi_sign_pool_mono` — pool sign censuses are monotone in the pool.
  `sat3_multi_clean_census'` — the clean census with the `m − |C| ≤ v` side condition
        discharged internally (any nonempty `C` qualifies; empty `C` is trivial).
  `sat3_multi_bulk_clean_census` — **PROVED, the two-cover census**: for ANY slot-1-clean block
        family `B`, if `2(j + 1 + Q) ≤ m` then `Σ_{c ∈ B} In₀(c) ≤ 2·j`.
  `sat3_multi_bulk_poison_census` — **PROVED, the bulk census**: under the same room,
        `A₀ ≤ 2·j + d₁·v` — the rung-6 `(j + Q + j + 1)·v` term is GONE; the only unpriced mass
        is the dirty blocks', and each dirty block costs the adversary an `S`-bit.
  `sat3_multi_rectangle_census_local` — **PROVED, the local rectangle**: the rectangle census
        with cleanliness required only on the `C × W` pairs — a block poisoned OUTSIDE `W` still
        participates.  This is the form in which the rectangle regime survives bulk poisoning.
  `sat3_multi_bulk_census_circuit` — **PROVED, the circuit dichotomy**: for a minimal SAT
        circuit at every band, the balanced `S` satisfies
        `m < 2·(coneExcess + 2 + Q)`  (the pool-exhausted horn: `coneExcess ≳ m/2 − Q`)
        or `A₀ ≤ 2·(coneExcess + 1) + d₁·v`.

Strict improvement over rung 6: `2j ≤ j + (j+1)·v` always, so the bulk census dominates the
poison census wherever both apply, and the pure-`S` floor at bands `T ≥ m` jumps to
`coneExcess ≥ ⌊m/2⌋ − 2 − Q` (rung 6 gave `≈ T/v` there, which vanishes below `T ≈ v`).

## Honest scope — where the `Ω(N)` question now stands

Every pin-based census self-caps at pool scale: each window application spends `j + 1` pins and
there are only `m` blocks, so `j`-bounds through pins cannot exceed `Θ(m) = Θ(√N)`.  Rows
beyond `2^Θ(m)` exist only in the rectangle regime (`Σ_c |V c| = |C|·|W|` with a SHARED position
set), now available in the local form: the adversary can no longer disable it with one poison
bit per block — poison must hit the `C × W` pairs themselves.  The remaining frontier for
`coneExcess = Ω(N)` is therefore sharpened to: does every balanced cut of a minimal SAT circuit
with `A₀ = Θ(N)` slot-0 mass contain a `Θ(m) × Θ(m)` rectangle whose `C × W` slot-1 pairs are
clean and whose pool has room?  Bulk poisoning of whole blocks no longer helps the adversary
(two-cover prices it; local rectangle survives it) — the open combinatorics is the density
extraction itself.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Pool monotonicity -/

theorem sat3_multi_sign_pool_mono (N : ℕ) (S : Finset (Fin N))
    (C : Finset (Fin (sat3M N))) :
    ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
      sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
    ≤ ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card := by
  apply Finset.card_le_card
  intro b hb
  rw [Finset.mem_filter] at hb
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb.2⟩

/-! ### The clean census, side condition discharged -/

/-- The rung-6 clean census with `m − |C| ≤ v` discharged internally: empty `C` is trivial and
nonempty `C` has `m − |C| ≤ m − 1 ≤ v`. -/
theorem sat3_multi_clean_census' (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (C : Finset (Fin (sat3M N)))
    (hclean1 : ∀ c ∈ C, ∀ w : Fin (sat3V N),
      sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)
    (hpool : j + 1 + ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      ≤ sat3M N - C.card) :
    ∑ c ∈ C, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card ≤ j := by
  classical
  by_cases hC : C = ∅
  · rw [hC, Finset.sum_empty]
    exact Nat.zero_le j
  · have h1 : 1 ≤ C.card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hC)
    have hmv : sat3M N - 1 ≤ sat3V N := sat3M_pred_le_sat3V N
    exact sat3_multi_clean_census N hv hcut C hclean1 (by omega) hpool

/-! ### The two-cover census -/

set_option maxHeartbeats 1600000 in
/-- **THE TWO-COVER CENSUS (proved)**: any slot-1-clean block family `B` has total slot-0 inside
mass at most `2·j` once the pool has room for half the grid — each half of `B` is priced at `j`
while the other half serves as its pin pool.  The rung-6 reserve term is gone. -/
theorem sat3_multi_bulk_clean_census (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (B : Finset (Fin (sat3M N)))
    (hcleanB : ∀ c ∈ B, ∀ w : Fin (sat3V N),
      sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)
    (hroom : 2 * (j + 1 + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card) ≤ sat3M N) :
    ∑ c ∈ B, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
    ≤ 2 * j := by
  classical
  have hBle : B.card ≤ sat3M N := by
    have h := Finset.card_le_card (Finset.subset_univ B)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  by_cases hsmall : B.card ≤ sat3M N / 2
  · -- one application suffices
    have hQ := sat3_multi_sign_pool_mono N S B
    have h1 := sat3_multi_clean_census' N hv hcut B hcleanB (by omega)
    omega
  · -- split `B` into two pool-compatible halves
    push_neg at hsmall
    obtain ⟨C₁, hC₁sub, hC₁card⟩ := Finset.exists_subset_card_eq
      (s := B) (n := sat3M N / 2) (by omega)
    have hC₂card : (B \ C₁).card = B.card - sat3M N / 2 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hC₁sub, hC₁card]
    have hQ₁ := sat3_multi_sign_pool_mono N S C₁
    have hQ₂ := sat3_multi_sign_pool_mono N S (B \ C₁)
    have h1 := sat3_multi_clean_census' N hv hcut C₁
      (fun c hc w => hcleanB c (hC₁sub hc) w) (by omega)
    have h2 := sat3_multi_clean_census' N hv hcut (B \ C₁)
      (fun c hc w => hcleanB c (Finset.sdiff_subset hc) w) (by omega)
    have hsplit : ∑ c ∈ (B \ C₁), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
        + ∑ c ∈ C₁, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
        = ∑ c ∈ B, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card :=
      Finset.sum_sdiff hC₁sub
    omega

/-! ### The bulk poison census -/

set_option maxHeartbeats 1600000 in
/-- **THE BULK CENSUS (proved)**: under half-grid pool room, the total slot-0 inside mass is
`A₀ ≤ 2·j + d₁·v` — beyond the doubled budget, only the dirty blocks go unpriced, and each
costs the adversary a slot-1 bit of `S`. -/
theorem sat3_multi_bulk_poison_census (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (hroom : 2 * (j + 1 + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card) ≤ sat3M N) :
    ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
    ≤ 2 * j + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S)).card * sat3V N := by
  classical
  set Dirty : Finset (Fin (sat3M N)) :=
    (Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
        (by have := w.isLt; omega) ∈ S) with hDirty
  set Clean : Finset (Fin (sat3M N)) :=
    (Finset.univ : Finset (Fin (sat3M N))) \ Dirty with hClean
  have hcleanClean : ∀ c ∈ Clean, ∀ w : Fin (sat3V N),
      sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S := by
    intro c hc w hw
    rw [hClean] at hc
    have hnd : c ∉ Dirty := (Finset.mem_sdiff.mp hc).2
    apply hnd
    rw [hDirty]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, ⟨w, hw⟩⟩
  have hbulk := sat3_multi_bulk_clean_census N hv hcut Clean hcleanClean hroom
  have hIn0le : ∀ c : Fin (sat3M N),
      ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
      ≤ sat3V N := by
    intro c
    have h := Finset.card_filter_le (Finset.univ : Finset (Fin (sat3V N)))
      (fun w => sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hUC : (Finset.univ : Finset (Fin (sat3M N))) \ Clean = Dirty := by
    rw [hClean, Finset.sdiff_sdiff_self_left, Finset.univ_inter]
  have hsplit : ∑ c ∈ ((Finset.univ : Finset (Fin (sat3M N))) \ Clean),
      ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
      + ∑ c ∈ Clean, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
      = ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card :=
    Finset.sum_sdiff (Finset.subset_univ Clean)
  have hdirtysum : ∑ c ∈ ((Finset.univ : Finset (Fin (sat3M N))) \ Clean),
      ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
      ≤ Dirty.card * sat3V N := by
    rw [hUC]
    calc ∑ c ∈ Dirty, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
        ≤ ∑ _c ∈ Dirty, sat3V N :=
          Finset.sum_le_sum (fun c _ => hIn0le c)
      _ = Dirty.card * sat3V N := by rw [Finset.sum_const, smul_eq_mul]
  calc ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
      = ∑ c ∈ ((Finset.univ : Finset (Fin (sat3M N))) \ Clean),
          ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
            sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
        + ∑ c ∈ Clean, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
            sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card :=
        hsplit.symm
    _ ≤ Dirty.card * sat3V N + 2 * j := Nat.add_le_add hdirtysum hbulk
    _ = 2 * j + Dirty.card * sat3V N := Nat.add_comm _ _

/-! ### The local rectangle -/

set_option maxHeartbeats 800000 in
/-- **THE LOCAL RECTANGLE CENSUS (proved)**: the rectangle census with slot-1 cleanliness
required only on the `C × W` pairs — a block poisoned outside `W` still participates.  Bulk
per-block poisoning no longer disables the rectangle regime. -/
theorem sat3_multi_rectangle_census_local (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (C : Finset (Fin (sat3M N))) (W : Finset (Fin (sat3V N)))
    (hrect : ∀ c ∈ C, ∀ w ∈ W,
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)
    (hkitW : ∀ c ∈ C, ∀ w ∈ W,
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
    (fun c hc c' hc' w hw => hkitW c hc w hw)
    hkv hroom
  calc C.card * W.card = ∑ _c ∈ C, W.card := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ j := hwin

/-! ### The circuit dichotomy -/

/-- **THE CIRCUIT BULK DICHOTOMY (proved)**: for a minimal SAT circuit, at every threshold band
the balanced `S` has a `j`-exhausted pool (`m < 2·(coneExcess + 2 + Q)`, i.e.
`coneExcess ≳ m/2 − Q`) or bulk-priced slot-0 mass (`A₀ ≤ 2·(coneExcess + 1) + d₁·v`). -/
theorem sat3_multi_bulk_census_circuit (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N))
    (T : ℕ) (hT : 2 ≤ T)
    (hband : 2 * T - 1 ≤ (varsOf cc (cc.length - 1)).card) :
    ∃ S : Finset (Fin N), T ≤ S.card ∧ S.card ≤ 2 * T - 2 ∧
      (sat3M N < 2 * (coneExcess cc (cc.length - 1) + 2
        + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
          sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card)
      ∨ ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
        ≤ 2 * (coneExcess cc (cc.length - 1) + 1)
          + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
            ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
              (by have := w.isLt; omega) ∈ S)).card * sat3V N) := by
  classical
  obtain ⟨S, hT1, hT2, j, hj, hcut⟩ :=
    sat3_balanced_cut N hv hm3 hk cc hcomp hmin T hT hband
  refine ⟨S, hT1, hT2, ?_⟩
  by_cases hroom : 2 * (j + 1 + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card) ≤ sat3M N
  · right
    have hcen := sat3_multi_bulk_poison_census N hv hcut hroom
    calc ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
        ≤ 2 * j + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
            ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
              (by have := w.isLt; omega) ∈ S)).card * sat3V N := hcen
      _ ≤ 2 * (coneExcess cc (cc.length - 1) + 1)
          + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
            ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
              (by have := w.isLt; omega) ∈ S)).card * sat3V N :=
          Nat.add_le_add_right (by omega) _
  · left
    push_neg at hroom
    omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_bulk_clean_census
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_bulk_poison_census
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_rectangle_census_local
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_bulk_census_circuit
