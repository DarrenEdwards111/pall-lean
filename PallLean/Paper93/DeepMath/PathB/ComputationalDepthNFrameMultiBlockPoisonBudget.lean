import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMultiBlockAlignment

/-!
# N-Frame: the poison-vs-payload budget — pair pricing and the stacked remainder

Rung 12 of the multi-block arc (… → ping-pong → alignment → **budget**).  The question posed at
rung 11: can the adversary afford to thin every admissible window?  The answer, in both
directions:

  `sat3_multi_column_budget` — **PROVED, the pair pricing**: for EVERY position `w`, the
        pair-clean payload of its column is priced — `#{c : slot-0(c,w) ∈ S, slot-1(c,w) ∉ S}
        ≤ j` — or the pool is exhausted outright (`m − 1 − Q₀ ≤ j`, STRONGER than the rung-10
        horn `m/2`).  The column census with `C` := the pair-clean payload blocks kills the
        `m`-amplification: a poison bit at `(c₀, w)` excludes only `c₀` from that column's
        census; every other block at `w` is still extracted.  POISON PRICES 1 : 1 PER PAIR.
  `sat3_multi_payload_split` — payload partitions into pair-clean and pair-stacked:
        `A₀ = Σ_w clean(w) + Σ_w stacked(w)`.
  `sat3_multi_poison_budget` — **PROVED, the budget**: `A₀ ≤ v·j + STACK₀₁` or
        `m − 1 − Q₀ ≤ j`, where `STACK₀₁` counts pairs carrying BOTH slot-0 and slot-1 bits.
  `sat3_multi_poison_budget_slot1` / `_slot2` — the slot-swapped budgets:
        `A₁ ≤ v·j + STACK₀₁` (the stack term is symmetric) and `A₂ ≤ v·j + STACK₂₁`.
  `sat3_multi_stacked_band_flight` — **PROVED, the band verdict**: at every band of a minimal
        SAT circuit, some sign column exhausts the pool at FULL strength
        (`∃ t, m − 1 − Q_t ≤ coneExcess + 1`) or
        `T ≤ 3·v·(coneExcess + 1) + 2·STACK₀₁ + STACK₂₁ + Q₀ + Q₁ + Q₂ + 3v + 3`.

## The verdict on HAL's budget check

Separate poison is now priced bit-for-bit: any adversary sheltering payload with poison at
OTHER pairs pays `1:1` and loses.  But MUTUAL stacking costs zero net: a pair `(c, w)` carrying
slot-0 and slot-1 bits (or all three slots) is simultaneously payload and shelter, in both
directions, across every slot-swapped gadget — the kit needs a free slot at the pair, and mode
dependence forbids baking kits into the rows.  So the inequality does not break the adversary
outright; it corners them exactly: at a heavy band, up to the `3·v·(coneExcess+1)` census term
and the sign/tail ledger, THE CUT MUST BE STACK-SATURATED — `2·STACK₀₁ + STACK₂₁ = Ω(T)` pairs
carrying multiple slots of `S` at the same clause-position pair.  The remaining frontier is one
of: a reader for stacked pairs (a genuinely new gadget — the present kit family cannot see
them), a circuit-side theorem that minimal balanced cuts cannot stack-saturate, or the
averaging diagnostic for the unstacked remainder.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The pair pricing -/

set_option maxHeartbeats 1600000 in
/-- **THE PAIR PRICING (proved)**: every column's pair-clean payload is at most `j`, or the pool
is exhausted at full strength (`m − 1 − Q₀ ≤ j`). -/
theorem sat3_multi_column_budget (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (w : Fin (sat3V N)) :
    ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
      ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)).card ≤ j
    ∨ sat3M N - 1 - ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card ≤ j := by
  classical
  have hmv : sat3M N - 1 ≤ sat3V N := sat3M_pred_le_sat3V N
  by_cases hcase : ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
      ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)).card
      ≤ sat3M N - 1 - ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
  · left
    by_cases hz : ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
        ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)) = ∅
    · rw [hz, Finset.card_empty]
      exact Nat.zero_le j
    · have h1 : 1 ≤ ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
          ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)).card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hz)
      have hQmono := sat3_multi_sign_pool_mono N S
        ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
          ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S))
      have hcen := sat3_multi_column_census N hv hcut
        ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
          ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)) w
        (fun c hc => (Finset.mem_filter.mp hc).2.2)
        (by omega)
        (by omega)
      have hfull : ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
          ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)).filter
          (fun c => sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)
          = ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
          ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)) :=
        Finset.filter_true_of_mem (fun c hc => (Finset.mem_filter.mp hc).2.1)
      rw [hfull] at hcen
      exact hcen
  · right
    push_neg at hcase
    by_cases hz : sat3M N - 1 - ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card = 0
    · omega
    · obtain ⟨C', hC'sub, hC'card⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
          ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S))
        (n := sat3M N - 1 - ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
          sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card)
        (by omega)
      have hQmono := sat3_multi_sign_pool_mono N S C'
      have hcen := sat3_multi_column_census N hv hcut C' w
        (fun c hc => (Finset.mem_filter.mp (hC'sub hc)).2.2)
        (by omega)
        (by omega)
      have hfull : C'.filter (fun c =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S) = C' :=
        Finset.filter_true_of_mem
          (fun c hc => (Finset.mem_filter.mp (hC'sub hc)).2.1)
      rw [hfull, hC'card] at hcen
      exact hcen

/-! ### The payload split -/

set_option maxHeartbeats 800000 in
/-- Payload partitions into pair-stacked and pair-clean:
`A₀ = Σ_w stacked(w) + Σ_w clean(w)`. -/
theorem sat3_multi_payload_split (N : ℕ) (S : Finset (Fin N)) :
    ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
    = (∑ w : Fin (sat3V N), ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
        ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
      + ∑ w : Fin (sat3V N), ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
        ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)).card := by
  classical
  have hdc := sat3_multi_column_double_count N S
    (Finset.univ : Finset (Fin (sat3M N))) (Finset.univ : Finset (Fin (sat3V N)))
  have hsplit : ∀ w : Fin (sat3V N),
      ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
      = ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
        ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
      + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
        ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)).card := by
    intro w
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))
      (p := fun c => sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)
    rw [Finset.filter_filter, Finset.filter_filter] at h
    exact h.symm
  calc ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
      = ∑ w : Fin (sat3V N), ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card := hdc
    _ = ∑ w : Fin (sat3V N),
        (((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
          ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
        + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
          ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)).card) :=
        Finset.sum_congr rfl (fun w _ => hsplit w)
    _ = _ := Finset.sum_add_distrib

/-! ### The budget -/

set_option maxHeartbeats 800000 in
/-- **THE POISON BUDGET (proved)**: `A₀ ≤ v·j + STACK₀₁`, or the pool is exhausted at full
strength.  Separate poison pays 1 : 1; only mutually-stacked pairs escape. -/
theorem sat3_multi_poison_budget (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j) :
    (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
    ≤ sat3V N * j
      + ∑ w : Fin (sat3V N), ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
        ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
    ∨ sat3M N - 1 - ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card ≤ j := by
  classical
  by_cases hpool : sat3M N - 1
      - ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card ≤ j
  · right
    exact hpool
  · left
    have hcol : ∀ w : Fin (sat3V N),
        ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
          sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
          ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)).card ≤ j := by
      intro w
      rcases sat3_multi_column_budget N hv hcut w with h | h
      · exact h
      · exact absurd h hpool
    have hsplit := sat3_multi_payload_split N S
    have hsum : ∑ w : Fin (sat3V N), ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
        ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)).card
        ≤ sat3V N * j := by
      calc ∑ w : Fin (sat3V N), ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
            sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
            ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)).card
          ≤ ∑ _w : Fin (sat3V N), j :=
            Finset.sum_le_sum (fun w _ => hcol w)
        _ = sat3V N * j := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega

/-! ### The slot-swapped budgets -/

set_option maxHeartbeats 1600000 in
/-- **The slot-1 budget (proved)**: `A₁ ≤ v·j + STACK₀₁` (the stack term is symmetric under the
`0 ↔ 1` swap), or the pool is exhausted at the slot-1 sign column. -/
theorem sat3_multi_poison_budget_slot1 (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j) :
    (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
    ≤ sat3V N * j
      + ∑ w : Fin (sat3V N), ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
        ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
    ∨ sat3M N - 1 - ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
        sat3Bit N b ⟨1, by omega⟩ (sat3V N) (by omega) ∈ S)).card ≤ j := by
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
  have hStack : ∑ w : Fin (sat3V N), ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega)
        ∈ S.image (slotSwapBit N ⟨1, by omega⟩)
      ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega)
        ∈ S.image (slotSwapBit N ⟨1, by omega⟩))).card
      = ∑ w : Fin (sat3V N), ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
      ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card := by
    apply Finset.sum_congr rfl
    intro w _
    congr 1
    ext c
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hu, h0, h1⟩
      rw [sat3_bit_mem_swap, hswap0] at h0
      rw [sat3_bit_mem_swap, hswap1] at h1
      exact ⟨hu, h1, h0⟩
    · rintro ⟨hu, h0, h1⟩
      refine ⟨hu, ?_, ?_⟩
      · rw [sat3_bit_mem_swap, hswap0]
        exact h1
      · rw [sat3_bit_mem_swap, hswap1]
        exact h0
  rcases sat3_multi_poison_budget N hv hcut' with h | h
  · left
    rw [hA, hStack] at h
    exact h
  · right
    rw [hQ] at h
    exact h

set_option maxHeartbeats 1600000 in
/-- **The slot-2 budget (proved)**: `A₂ ≤ v·j + STACK₂₁` (the `0 ↔ 2` swap fixes slot 1, so the
stack partner is slot 1), or the pool is exhausted at the slot-2 sign column. -/
theorem sat3_multi_poison_budget_slot2 (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j) :
    (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨2, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
    ≤ sat3V N * j
      + ∑ w : Fin (sat3V N), ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c ⟨2, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
        ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
    ∨ sat3M N - 1 - ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
        sat3Bit N b ⟨2, by omega⟩ (sat3V N) (by omega) ∈ S)).card ≤ j := by
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
  have hStack : ∑ w : Fin (sat3V N), ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega)
        ∈ S.image (slotSwapBit N ⟨2, by omega⟩)
      ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega)
        ∈ S.image (slotSwapBit N ⟨2, by omega⟩))).card
      = ∑ w : Fin (sat3V N), ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      sat3Bit N c ⟨2, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
      ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card := by
    apply Finset.sum_congr rfl
    intro w _
    congr 1
    ext c
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hu, h0, h1⟩
      rw [sat3_bit_mem_swap, hswap0] at h0
      rw [sat3_bit_mem_swap, hswap1] at h1
      exact ⟨hu, h0, h1⟩
    · rintro ⟨hu, h0, h1⟩
      refine ⟨hu, ?_, ?_⟩
      · rw [sat3_bit_mem_swap, hswap0]
        exact h0
      · rw [sat3_bit_mem_swap, hswap1]
        exact h1
  rcases sat3_multi_poison_budget N hv hcut' with h | h
  · left
    rw [hA, hStack] at h
    exact h
  · right
    rw [hQ] at h
    exact h

/-! ### The band verdict -/

set_option maxHeartbeats 1600000 in
/-- **THE BAND VERDICT (proved)**: at every band of a minimal SAT circuit, some sign column
exhausts the pool at full strength, or the cut is stack-saturated up to the census term:
`T ≤ 3·v·(coneExcess + 1) + 2·STACK₀₁ + STACK₂₁ + Q₀ + Q₁ + Q₂ + 3v + 3`. -/
theorem sat3_multi_stacked_band_flight (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N))
    (T : ℕ) (hT : 2 ≤ T)
    (hband : 2 * T - 1 ≤ (varsOf cc (cc.length - 1)).card) :
    ∃ S : Finset (Fin N), T ≤ S.card ∧ S.card ≤ 2 * T - 2 ∧
      ((∃ t : Fin 3, sat3M N - 1
        - ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
          sat3Bit N b t (sat3V N) (by omega) ∈ S)).card
        ≤ coneExcess cc (cc.length - 1) + 1)
      ∨ T ≤ 3 * (sat3V N * (coneExcess cc (cc.length - 1) + 1))
          + 2 * (∑ w : Fin (sat3V N), ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
            sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
            ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
          + (∑ w : Fin (sat3V N), ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
            sat3Bit N c ⟨2, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
            ∧ sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
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
  rcases sat3_multi_poison_budget N hv hcut with h0 | h0
  · rcases sat3_multi_poison_budget_slot1 N hv hcut with h1 | h1
    · rcases sat3_multi_poison_budget_slot2 N hv hcut with h2 | h2
      · right
        have hled := sat3_grid_mass_ledger N S
        have hj' : sat3V N * j ≤ sat3V N * (coneExcess cc (cc.length - 1) + 1) :=
          Nat.mul_le_mul_left _ hj
        omega
      · exact Or.inl ⟨⟨2, by omega⟩, by omega⟩
    · exact Or.inl ⟨⟨1, by omega⟩, by omega⟩
  · exact Or.inl ⟨⟨0, by omega⟩, by omega⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_column_budget
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_poison_budget
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_poison_budget_slot1
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_poison_budget_slot2
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_stacked_band_flight
