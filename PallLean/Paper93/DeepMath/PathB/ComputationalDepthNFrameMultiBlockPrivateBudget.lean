import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMultiBlockPrivateWindow

/-!
# N-Frame: the private budget and band flight — everything priced but the signs

Rung 16 of the multi-block arc (… → private window → **private budget**).  The room bill of the
private census carries the `+|C|` private pins, so the rung-8 two-cover becomes a THREE-cover:
parts of size `⌊m/3⌋` satisfy `j + 1 + |Cᵢ| + Q ≤ m − |Cᵢ|` exactly when
`3(j + 1 + Q) + 8 ≤ m`.  The result prices the whole grid with no dirty, stack, or cleanliness
terms:

  `sat3_private_budget` — **PROVED**: `A₀ ≤ 3·j`, or the pool is exhausted
        (`m < 3(j + 1 + Q₀) + 8`).
  `sat3_private_budget_slot1` / `_slot2` — the slot-swapped budgets (`A₁`, `A₂ ≤ 3·j` with the
        `Q₁`/`Q₂` horns) — the transfers are LIGHT now: only a mass and a sign equation, no
        dirty or stack bookkeeping.
  `sat3_private_band_flight` — **PROVED, the flight**: at every band of a minimal SAT circuit,
        `T ≤ 9·(coneExcess + 1) + Q₀ + Q₁ + Q₂ + 3v + 3`
        or some sign column exhausts the pool (`∃ t, m < 3·(coneExcess + 2 + Q_t) + 8`).

## The verdict — the last refuge

Since `Q₀ + Q₁ + Q₂ ≤ 3m`, at bands `T > 9(coneExcess + 1) + 3m + 3v + 3` the first horn is
unsatisfiable and the pool horn is FORCED: `coneExcess ≥ (m − 3·Q_t − 14)/3` for some slot `t`.
The adversary's ONLY remaining escape from `coneExcess = Ω(m)` at heavy bands — and from
`Ω(T)` on the first horn — is SIGN-COLUMN POISON: `Ω(m)` sign bits of one slot inside `S`, at
`o(N)` mass cost.  This refuge is structural for the present gadget family: a pin's
mode-dependent bit IS its sign bit, so a sign-poisoned pool block cannot pin.  Selector mass,
in every slot, at every pair, stacked or not, is now priced at `3j`; the sign columns are the
one unpriced coordinate class.  The next frontier is the sign-data drag — reading sign columns
as row data (the single-block machinery already does this in its min-form arc) lifted
multi-block — after which the route to `coneExcess = Ω(T)` / `(2 + c)·N` either closes or
meets its true obstruction.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The private budget -/

set_option maxHeartbeats 1600000 in
/-- **THE PRIVATE BUDGET (proved)**: the total slot-0 inside mass of the WHOLE grid is at most
`3·j` — no dirty, stack, or cleanliness terms — or the pool is exhausted.  Three-cover: parts
of size `⌊m/3⌋` each priced at `j` by the private clean census. -/
theorem sat3_private_budget (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j) :
    (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card ≤ 3 * j)
    ∨ sat3M N < 3 * (j + 1 + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card) + 8 := by
  classical
  by_cases hroom : 3 * (j + 1 + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card) + 8 ≤ sat3M N
  · left
    have hmv : sat3M N - 1 ≤ sat3V N := sat3M_pred_le_sat3V N
    obtain ⟨C₁, hC₁sub, hC₁card⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin (sat3M N)))) (n := sat3M N / 3)
      (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    obtain ⟨C₂, hC₂sub, hC₂card⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin (sat3M N))) \ C₁) (n := sat3M N / 3)
      (by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
          Fintype.card_fin, hC₁card]
        omega)
    set C₃ : Finset (Fin (sat3M N)) :=
      ((Finset.univ : Finset (Fin (sat3M N))) \ C₁) \ C₂ with hC₃
    have hC₃card : C₃.card = sat3M N - 2 * (sat3M N / 3) := by
      rw [hC₃, Finset.card_sdiff, Finset.inter_eq_left.mpr hC₂sub, hC₂card,
        Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
        Fintype.card_fin, hC₁card]
      omega
    have hsplit1 : ∑ c ∈ ((Finset.univ : Finset (Fin (sat3M N))) \ C₁),
        ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
        + ∑ c ∈ C₁, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
        = ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card :=
      Finset.sum_sdiff hC₁sub
    have hsplit2 : ∑ c ∈ C₃,
        ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
        + ∑ c ∈ C₂, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
        = ∑ c ∈ ((Finset.univ : Finset (Fin (sat3M N))) \ C₁),
        ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card :=
      Finset.sum_sdiff hC₂sub
    have hQ₁ := sat3_multi_sign_pool_mono N S C₁
    have hQ₂ := sat3_multi_sign_pool_mono N S C₂
    have hQ₃ := sat3_multi_sign_pool_mono N S C₃
    have hcen₁ := sat3_private_clean_census N hv hcut C₁
      (by omega) (by omega) (by omega)
    have hcen₂ := sat3_private_clean_census N hv hcut C₂
      (by omega) (by omega) (by omega)
    have hcen₃ := sat3_private_clean_census N hv hcut C₃
      (by omega) (by omega) (by omega)
    omega
  · right
    omega

/-! ### The slot-swapped budgets -/

set_option maxHeartbeats 1600000 in
/-- **The slot-1 private budget (proved)**: `A₁ ≤ 3·j` or the slot-1 sign column exhausts the
pool. -/
theorem sat3_private_budget_slot1 (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j) :
    (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card ≤ 3 * j)
    ∨ sat3M N < 3 * (j + 1 + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
        sat3Bit N b ⟨1, by omega⟩ (sat3V N) (by omega) ∈ S)).card) + 8 := by
  classical
  have hcut' : CutFactorization (sat3Family N)
      (S.image (slotSwapBit N ⟨1, by omega⟩)) j :=
    cut_transport (sat3Family N) (slotSwapBit N ⟨1, by omega⟩)
      (slotSwapBit_invol N ⟨1, by omega⟩)
      (sat3Family_slotSwap N ⟨1, by omega⟩) hcut
  have hswap0 : swapSlotF (⟨1, by omega⟩ : Fin 3) ⟨0, by omega⟩ = ⟨1, by omega⟩ :=
    Fin.ext rfl
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
  have hQ : ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega)
        ∈ S.image (slotSwapBit N ⟨1, by omega⟩))).card
      = ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ⟨1, by omega⟩ (sat3V N) (by omega) ∈ S)).card := by
    congr 1
    ext b
    rw [Finset.mem_filter, Finset.mem_filter, sat3_bit_mem_swap, hswap0]
  rcases sat3_private_budget N hv hcut' with h | h
  · left
    rw [hA] at h
    exact h
  · right
    rw [hQ] at h
    exact h

set_option maxHeartbeats 1600000 in
/-- **The slot-2 private budget (proved)**: `A₂ ≤ 3·j` or the slot-2 sign column exhausts the
pool. -/
theorem sat3_private_budget_slot2 (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j) :
    (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨2, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card ≤ 3 * j)
    ∨ sat3M N < 3 * (j + 1 + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
        sat3Bit N b ⟨2, by omega⟩ (sat3V N) (by omega) ∈ S)).card) + 8 := by
  classical
  have hcut' : CutFactorization (sat3Family N)
      (S.image (slotSwapBit N ⟨2, by omega⟩)) j :=
    cut_transport (sat3Family N) (slotSwapBit N ⟨2, by omega⟩)
      (slotSwapBit_invol N ⟨2, by omega⟩)
      (sat3Family_slotSwap N ⟨2, by omega⟩) hcut
  have hswap0 : swapSlotF (⟨2, by omega⟩ : Fin 3) ⟨0, by omega⟩ = ⟨2, by omega⟩ :=
    Fin.ext rfl
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
  have hQ : ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega)
        ∈ S.image (slotSwapBit N ⟨2, by omega⟩))).card
      = ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
      sat3Bit N b ⟨2, by omega⟩ (sat3V N) (by omega) ∈ S)).card := by
    congr 1
    ext b
    rw [Finset.mem_filter, Finset.mem_filter, sat3_bit_mem_swap, hswap0]
  rcases sat3_private_budget N hv hcut' with h | h
  · left
    rw [hA] at h
    exact h
  · right
    rw [hQ] at h
    exact h

/-! ### The band flight -/

set_option maxHeartbeats 1600000 in
/-- **THE PRIVATE BAND FLIGHT (proved)**: at every band of a minimal SAT circuit,
`T ≤ 9·(coneExcess + 1) + Q₀ + Q₁ + Q₂ + 3v + 3`, or some sign column exhausts the pool.
Since `ΣQ ≤ 3m`, heavy bands force the pool horn: the adversary's last refuge is sign-column
poison. -/
theorem sat3_private_band_flight (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N))
    (T : ℕ) (hT : 2 ≤ T)
    (hband : 2 * T - 1 ≤ (varsOf cc (cc.length - 1)).card) :
    ∃ S : Finset (Fin N), T ≤ S.card ∧ S.card ≤ 2 * T - 2 ∧
      ((∃ t : Fin 3, sat3M N < 3 * (coneExcess cc (cc.length - 1) + 2
        + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
          sat3Bit N b t (sat3V N) (by omega) ∈ S)).card) + 8)
      ∨ T ≤ 9 * (coneExcess cc (cc.length - 1) + 1)
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
  rcases sat3_private_budget N hv hcut with h0 | h0
  · rcases sat3_private_budget_slot1 N hv hcut with h1 | h1
    · rcases sat3_private_budget_slot2 N hv hcut with h2 | h2
      · right
        have hled := sat3_grid_mass_ledger N S
        omega
      · exact Or.inl ⟨⟨2, by omega⟩, by omega⟩
    · exact Or.inl ⟨⟨1, by omega⟩, by omega⟩
  · exact Or.inl ⟨⟨0, by omega⟩, by omega⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_private_budget
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_private_budget_slot1
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_private_budget_slot2
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_private_band_flight
