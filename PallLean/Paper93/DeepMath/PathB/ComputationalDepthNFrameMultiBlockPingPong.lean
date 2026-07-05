import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMultiBlockCircuitSide

/-!
# N-Frame: the slot ping-pong closure — the three-slot bulk census

Rung 10 of the multi-block arc (… → bulk → circuit side → **ping-pong**).  The band flight
(rung 9) showed the band mass must flee slot 0 into `A₁`, `A₂`, signs, or slot-1 poison.  This
file closes the chase: the slot swaps (`SlotSymmetry`) carry the bulk census to every slot, so
ALL THREE selector masses are priced and only block-count poison terms remain:

  `sat3_bit_mem_swap` — layout-bit membership under the swap image: slot `s` of the image reads
        slot `swapSlotF t s` of the original.
  `sat3_multi_bulk_census_slot1` — **PROVED**: `A₁ ≤ 2j + d₀·v` (kit at slot 0 after the swap:
        the poison for slot-1 data is the slot-0-dirty count).
  `sat3_multi_bulk_census_slot2` — **PROVED**: `A₂ ≤ 2j + d₁·v` (the `0 ↔ 2` swap fixes slot 1,
        so the kit slot — and the poison — is slot 1 again).
  `sat3_multi_three_slot_census` — **PROVED, the closure**: under pool room at all three sign
        columns, `A₀ + A₁ + A₂ ≤ 6j + (d₀ + 2·d₁)·v`.
  `sat3_multi_band_flight_full` — **PROVED, the closed flight**: at every band of a minimal SAT
        circuit, some sign column exhausts the pool
        (`∃ t, m < 2·(coneExcess + 2 + Q_t)`) or
        `T ≤ 6·(coneExcess + 1) + (d₀ + 2·d₁)·v + Q₀ + Q₁ + Q₂ + 3v + 3`.

After the closure the adversary's ONLY remaining hiding places at a band are block-counted:
sign columns (`Q_t` blocks each) and dirty blocks (`d₀ + 2d₁`, each priced at one `S`-bit in the
opposite slot).  A poison-light cut (`(d₀ + 2d₁)·v + ΣQ ≤ T/2`, say) forces
`coneExcess = Ω(T)` up to the pool cap — i.e. `Ω(m)` at every band `T ≥ Θ(m)`.

## Honest scope

The ping-pong is closed as an ACCOUNTING system, not a contradiction: a fully-dirty adversary
(`d₀ = d₁ = m`) saturates the right-hand side at the grid ceiling, and each dirty block is
priced only once (an `S`-bit in the other slot) while unlocking up to `v` unpriced bits — the
`v : 1` amplification identified at rung 6 is priced, not eliminated.  The remaining fight for
`Ω(N)` is unchanged: the local rectangle extraction (rung 8) against dirty-saturated cuts, now
with the exact ledger of what dirty saturation costs the adversary (`d₀ + 2d₁ = Ω(m)` blocks
carrying cross-slot selector bits at every heavy band — the rectangle's raw material).  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Bit membership under the swap -/

theorem sat3_bit_mem_swap (N : ℕ) (t : Fin 3) (S : Finset (Fin N))
    (c : Fin (sat3M N)) (s : Fin 3) (f : ℕ) (hf : f < sat3V N + 1) :
    sat3Bit N c s f hf ∈ S.image (slotSwapBit N t)
      ↔ sat3Bit N c (swapSlotF t s) f hf ∈ S := by
  rw [mem_image_invol (slotSwapBit N t) (slotSwapBit_invol N t) S,
    slotSwapBit_bit]

/-! ### The slot-1 and slot-2 bulk censuses -/

set_option maxHeartbeats 1600000 in
/-- **The slot-1 bulk census (proved)**: `A₁ ≤ 2j + d₀·v` under pool room at the slot-1 sign
column — the `0 ↔ 1` swap makes slot 0 the kit slot, so slot-1 data is poisoned by
slot-0-dirty blocks. -/
theorem sat3_multi_bulk_census_slot1 (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (hroom : 2 * (j + 1 + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ⟨1, by omega⟩ (sat3V N) (by omega) ∈ S)).card) ≤ sat3M N) :
    ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
    ≤ 2 * j + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        ∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S)).card * sat3V N := by
  classical
  have hcut' : CutFactorization (sat3Family N)
      (S.image (slotSwapBit N ⟨1, by omega⟩)) j :=
    cut_transport (sat3Family N) (slotSwapBit N ⟨1, by omega⟩)
      (slotSwapBit_invol N ⟨1, by omega⟩)
      (sat3Family_slotSwap N ⟨1, by omega⟩) hcut
  have hswap0 : swapSlotF (⟨1, by omega⟩ : Fin 3) ⟨0, by omega⟩ = ⟨1, by omega⟩ :=
    Fin.ext rfl
  have hswap1 : swapSlotF (⟨1, by omega⟩ : Fin 3) ⟨1, by omega⟩ = ⟨0, by omega⟩ :=
    Fin.ext rfl
  have hQ : ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega)
        ∈ S.image (slotSwapBit N ⟨1, by omega⟩))).card
      = ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ⟨1, by omega⟩ (sat3V N) (by omega) ∈ S)).card := by
    congr 1
    ext b
    rw [Finset.mem_filter, Finset.mem_filter, sat3_bit_mem_swap, hswap0]
  have hA : ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega)
        ∈ S.image (slotSwapBit N ⟨1, by omega⟩))).card
      = ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card := by
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    ext w
    rw [Finset.mem_filter, Finset.mem_filter, sat3_bit_mem_swap, hswap0]
  have hD : ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
        (by have := w.isLt; omega)
        ∈ S.image (slotSwapBit N ⟨1, by omega⟩))).card
      = ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      ∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∈ S)).card := by
    congr 1
    ext c
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hu, w, hw⟩
      rw [sat3_bit_mem_swap, hswap1] at hw
      exact ⟨hu, w, hw⟩
    · rintro ⟨hu, w, hw⟩
      refine ⟨hu, w, ?_⟩
      rw [sat3_bit_mem_swap, hswap1]
      exact hw
  have hcen := sat3_multi_bulk_poison_census N hv hcut' (by omega)
  rw [hA, hD] at hcen
  exact hcen

set_option maxHeartbeats 1600000 in
/-- **The slot-2 bulk census (proved)**: `A₂ ≤ 2j + d₁·v` under pool room at the slot-2 sign
column — the `0 ↔ 2` swap fixes slot 1, so the kit slot (and the poison) is slot 1. -/
theorem sat3_multi_bulk_census_slot2 (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (hroom : 2 * (j + 1 + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ⟨2, by omega⟩ (sat3V N) (by omega) ∈ S)).card) ≤ sat3M N) :
    ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨2, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
    ≤ 2 * j + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S)).card * sat3V N := by
  classical
  have hcut' : CutFactorization (sat3Family N)
      (S.image (slotSwapBit N ⟨2, by omega⟩)) j :=
    cut_transport (sat3Family N) (slotSwapBit N ⟨2, by omega⟩)
      (slotSwapBit_invol N ⟨2, by omega⟩)
      (sat3Family_slotSwap N ⟨2, by omega⟩) hcut
  have hswap0 : swapSlotF (⟨2, by omega⟩ : Fin 3) ⟨0, by omega⟩ = ⟨2, by omega⟩ :=
    Fin.ext rfl
  have hswap1 : swapSlotF (⟨2, by omega⟩ : Fin 3) ⟨1, by omega⟩ = ⟨1, by omega⟩ :=
    Fin.ext rfl
  have hQ : ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega)
        ∈ S.image (slotSwapBit N ⟨2, by omega⟩))).card
      = ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ⟨2, by omega⟩ (sat3V N) (by omega) ∈ S)).card := by
    congr 1
    ext b
    rw [Finset.mem_filter, Finset.mem_filter, sat3_bit_mem_swap, hswap0]
  have hA : ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega)
        ∈ S.image (slotSwapBit N ⟨2, by omega⟩))).card
      = ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨2, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card := by
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    ext w
    rw [Finset.mem_filter, Finset.mem_filter, sat3_bit_mem_swap, hswap0]
  have hD : ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
        (by have := w.isLt; omega)
        ∈ S.image (slotSwapBit N ⟨2, by omega⟩))).card
      = ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
        (by have := w.isLt; omega) ∈ S)).card := by
    congr 1
    ext c
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hu, w, hw⟩
      rw [sat3_bit_mem_swap, hswap1] at hw
      exact ⟨hu, w, hw⟩
    · rintro ⟨hu, w, hw⟩
      refine ⟨hu, w, ?_⟩
      rw [sat3_bit_mem_swap, hswap1]
      exact hw
  have hcen := sat3_multi_bulk_poison_census N hv hcut' (by omega)
  rw [hA, hD] at hcen
  exact hcen

/-! ### The three-slot closure -/

set_option maxHeartbeats 800000 in
/-- **THE THREE-SLOT CENSUS (proved)**: under pool room at all three sign columns, every
selector mass is priced — `A₀ + A₁ + A₂ ≤ 6j + (d₀ + 2·d₁)·v`. -/
theorem sat3_multi_three_slot_census (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (hroom0 : 2 * (j + 1 + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card) ≤ sat3M N)
    (hroom1 : 2 * (j + 1 + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ⟨1, by omega⟩ (sat3V N) (by omega) ∈ S)).card) ≤ sat3M N)
    (hroom2 : 2 * (j + 1 + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ⟨2, by omega⟩ (sat3V N) (by omega) ∈ S)).card) ≤ sat3M N) :
    (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
    + (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
    + (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨2, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
    ≤ 6 * j + (((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        ∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S)).card
      + 2 * ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S)).card) * sat3V N := by
  classical
  have h0 := sat3_multi_bulk_poison_census N hv hcut hroom0
  have h1 := sat3_multi_bulk_census_slot1 N hv hcut hroom1
  have h2 := sat3_multi_bulk_census_slot2 N hv hcut hroom2
  have hring : 2 * j + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S)).card * sat3V N
      + (2 * j + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        ∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S)).card * sat3V N)
      + (2 * j + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S)).card * sat3V N)
      = 6 * j + (((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        ∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S)).card
      + 2 * ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S)).card) * sat3V N := by
    ring
  calc (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
      + (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
      + (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨2, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
      ≤ (2 * j + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
          ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
            (by have := w.isLt; omega) ∈ S)).card * sat3V N)
        + (2 * j + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
          ∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
            (by have := w.isLt; omega) ∈ S)).card * sat3V N)
        + (2 * j + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
          ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
            (by have := w.isLt; omega) ∈ S)).card * sat3V N) :=
        Nat.add_le_add (Nat.add_le_add h0 h1) h2
    _ = _ := hring

/-! ### The closed band flight -/

/-- **THE CLOSED BAND FLIGHT (proved)**: at every band of a minimal SAT circuit, some sign
column exhausts the pool, or ALL selector masses are priced and only block-counted poison
remains: `T ≤ 6·(coneExcess + 1) + (d₀ + 2d₁)·v + Q₀ + Q₁ + Q₂ + 3v + 3`. -/
theorem sat3_multi_band_flight_full (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N))
    (T : ℕ) (hT : 2 ≤ T)
    (hband : 2 * T - 1 ≤ (varsOf cc (cc.length - 1)).card) :
    ∃ S : Finset (Fin N), T ≤ S.card ∧ S.card ≤ 2 * T - 2 ∧
      ((∃ t : Fin 3, sat3M N < 2 * (coneExcess cc (cc.length - 1) + 2
        + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
          sat3Bit N b t (sat3V N) (by omega) ∈ S)).card))
      ∨ T ≤ 6 * (coneExcess cc (cc.length - 1) + 1)
          + (((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
            ∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
              (by have := w.isLt; omega) ∈ S)).card
            + 2 * ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
            ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
              (by have := w.isLt; omega) ∈ S)).card) * sat3V N
          + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
            sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
          + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
            sat3Bit N b ⟨1, by omega⟩ (sat3V N) (by omega) ∈ S)).card
          + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
            sat3Bit N b ⟨2, by omega⟩ (sat3V N) (by omega) ∈ S)).card
          + 3 * sat3V N + 3) := by
  classical
  obtain ⟨S, hT1, hT2, j, hj, hcut⟩ :=
    sat3_balanced_cut N hv hm3 hk cc hcomp hmin T hT hband
  refine ⟨S, hT1, hT2, ?_⟩
  by_cases hr0 : 2 * (j + 1 + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card) ≤ sat3M N
  · by_cases hr1 : 2 * (j + 1 + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
        sat3Bit N b ⟨1, by omega⟩ (sat3V N) (by omega) ∈ S)).card) ≤ sat3M N
    · by_cases hr2 : 2 * (j + 1 + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
          sat3Bit N b ⟨2, by omega⟩ (sat3V N) (by omega) ∈ S)).card) ≤ sat3M N
      · right
        have hcen := sat3_multi_three_slot_census N hv hcut hr0 hr1 hr2
        have hled := sat3_grid_mass_ledger N S
        omega
      · push_neg at hr2
        exact Or.inl ⟨⟨2, by omega⟩, by omega⟩
    · push_neg at hr1
      exact Or.inl ⟨⟨1, by omega⟩, by omega⟩
  · push_neg at hr0
    exact Or.inl ⟨⟨0, by omega⟩, by omega⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_bulk_census_slot1
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_bulk_census_slot2
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_three_slot_census
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_band_flight_full
