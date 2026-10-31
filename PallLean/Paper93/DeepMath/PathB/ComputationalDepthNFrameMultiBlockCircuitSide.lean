import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMultiBlockBulk

/-!
# N-Frame: the circuit side — the grid ledger, gate pricing, and the band flight

Rung 9 of the multi-block arc (… → census → spread → bulk → **circuit side**).  The censuses
bound the slot-0 selector mass `A₀`, but nothing yet forced `A₀` to be LARGE: the band gives
only `|S| ≥ T`, and `S` could sit in slot-1/2 selectors, sign bits, or tail bits.  This file
closes that gap and starts consuming the circuit-specific structure of the cut sets:

  `sat3_grid_mass_ledger` — **PROVED, the ledger**: for ANY `S ⊆ Fin N`,
        `|S| ≤ A₀ + A₁ + A₂ + Q₀ + Q₁ + Q₂ + 3v + 3` —
        every bit of `S` is a slot-`t` selector (counted by `A_t`), a slot-`t` sign (counted by
        `Q_t`), or one of the `< 3v + 3` tail bits.  The partition count that converts band mass
        into census-visible mass.
  `varsOf_card_le_cone` — **PROVED, gate pricing**: `|varsOf c r| ≤ |coneOf c r|` — every
        coordinate of a cut set is witnessed by a distinct cone gate, so cut sets are priced in
        GATES.  (The cut sets of `sat3_balanced_cut` are `varsOf` sets: circuit cuts are not
        arbitrary — their size is circuit length spent.)
  `sat3_band_cone_cost` — **PROVED, the spectrum bone**: at every scale `T` below the root
        support, some wire's cone has at least `T` gates.
  `sat3_multi_band_flight` — **PROVED, the band flight**: for a minimal SAT circuit, at every
        band `T` the balanced `S` has a `j`-exhausted pool
        (`m < 2·(coneExcess + 2 + Q₀)`) or the band mass FLEES slot 0:
        `T ≤ 2·(coneExcess + 1) + d₁·v + A₁ + A₂ + Q₀ + Q₁ + Q₂ + 3v + 3`.
        Every term the mass can flee into is a census-priced or `S`-bit-priced quantity.

## Honest scope

The flight theorem quantifies exactly what the adversary must do at every band: pay
`coneExcess ≳ m/2` (first horn), or carry the band mass in slot-1/2 selectors, sign columns, or
slot-1 poison — each an explicit target for the slot-symmetric censuses (the `SlotSymmetry`
transfer moves the slot-0 machinery to the other slots; the ping-pong between slots remains the
open combinatorial fight, as does the rectangle extraction).  Gate pricing is the first genuine
use of the `varsOf` shape of circuit cuts; the deeper structure — which coordinates a MINIMAL
circuit's balanced cones must share — is untouched.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The grid mass ledger -/

set_option maxHeartbeats 3200000 in
/-- **THE GRID MASS LEDGER (proved)**: every bit of `S` is a slot-`t` selector, a slot-`t`
sign, or a tail bit — `|S| ≤ A₀ + A₁ + A₂ + Q₀ + Q₁ + Q₂ + 3v + 3`. -/
theorem sat3_grid_mass_ledger (N : ℕ) (S : Finset (Fin N)) :
    S.card ≤ (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
      + (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
      + (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨2, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
      + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c ⟨1, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c ⟨2, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      + 3 * sat3V N + 3 := by
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
  -- selector pieces are counted by the raw masses
  have hselbound : ∀ t : Fin 3, (Fsel t).card
      ≤ ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c t w.val (by have := w.isLt; omega) ∈ S)).card := by
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
        ≤ ∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N c t w.val (by have := w.isLt; omega) ∈ S)).card := by
      rw [Finset.card_eq_sum_card_fiberwise
        (f := fun cw : Fin (sat3M N) × Fin (sat3V N) => cw.1)
        (t := (Finset.univ : Finset (Fin (sat3M N))))
        (fun cw _ => Finset.mem_univ cw.1)]
      apply Finset.sum_le_sum
      intro c _
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
    omega
  -- sign pieces are counted by the sign censuses
  have hsgnbound : ∀ t : Fin 3, (Fsgn t).card
      ≤ ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        sat3Bit N c t (sat3V N) (by omega) ∈ S)).card := by
    intro t
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
  -- the tail is short
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

/-! ### Gate pricing of cut sets -/

/-- **Gate pricing (proved)**: every coordinate of a cut set is witnessed by a distinct cone
gate — `|varsOf c r| ≤ |coneOf c r|`.  Circuit cuts pay for their size in gates. -/
theorem varsOf_card_le_cone {n : ℕ} (c : List (CGate n)) (r : ℕ) :
    (varsOf c r).card ≤ (coneOf c r).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun i : Fin n =>
    if h : ∃ p ∈ coneOf c r, c.getD p (CGate.cst false) = CGate.var i
    then h.choose else 0)
  · intro i hi
    have hex : ∃ p ∈ coneOf c r, c.getD p (CGate.cst false) = CGate.var i := by
      have h2 := Finset.mem_coe.mp hi
      unfold varsOf at h2
      exact (Finset.mem_filter.mp h2).2
    show (if h : ∃ p ∈ coneOf c r, c.getD p (CGate.cst false) = CGate.var i
      then h.choose else 0) ∈ ↑(coneOf c r)
    rw [dif_pos hex]
    exact Finset.mem_coe.mpr hex.choose_spec.1
  · intro i hi i' hi' heq
    have hex : ∃ p ∈ coneOf c r, c.getD p (CGate.cst false) = CGate.var i := by
      have h2 := Finset.mem_coe.mp hi
      unfold varsOf at h2
      exact (Finset.mem_filter.mp h2).2
    have hex' : ∃ p ∈ coneOf c r, c.getD p (CGate.cst false) = CGate.var i' := by
      have h2 := Finset.mem_coe.mp hi'
      unfold varsOf at h2
      exact (Finset.mem_filter.mp h2).2
    have heq' : (if h : ∃ p ∈ coneOf c r, c.getD p (CGate.cst false) = CGate.var i
        then h.choose else 0)
        = (if h : ∃ p ∈ coneOf c r, c.getD p (CGate.cst false) = CGate.var i'
        then h.choose else 0) := heq
    rw [dif_pos hex, dif_pos hex'] at heq'
    have h1 := hex.choose_spec.2
    have h2 := hex'.choose_spec.2
    rw [heq'] at h1
    rw [h2] at h1
    exact (CGate.var.inj h1).symm

/-- **The spectrum bone (proved)**: at every scale `T` below the root support, some wire of the
cone has at least `T` gates in its own cone. -/
theorem sat3_band_cone_cost {n : ℕ} (c : List (CGate n)) (r : ℕ) (T : ℕ)
    (hT : 2 ≤ T) (hr : T ≤ (varsOf c r).card) :
    ∃ w ∈ coneOf c r, T ≤ (coneOf c w).card := by
  obtain ⟨w, hw, hT1, -⟩ := balanced_wire_exists c r T hT hr
  exact ⟨w, hw, hT1.trans (varsOf_card_le_cone c w)⟩

/-! ### The band flight -/

/-- **THE BAND FLIGHT (proved)**: at every band of a minimal SAT circuit, the pool is
`j`-exhausted (`coneExcess ≳ m/2 − Q₀`) or the band mass flees slot 0 into census-priced
targets: slot-1/2 selector mass, sign columns, slot-1 poison. -/
theorem sat3_multi_band_flight (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N))
    (T : ℕ) (hT : 2 ≤ T)
    (hband : 2 * T - 1 ≤ (varsOf cc (cc.length - 1)).card) :
    ∃ S : Finset (Fin N), T ≤ S.card ∧ S.card ≤ 2 * T - 2 ∧
      (sat3M N < 2 * (coneExcess cc (cc.length - 1) + 2
        + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
          sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card)
      ∨ T ≤ 2 * (coneExcess cc (cc.length - 1) + 1)
          + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
            ∃ w : Fin (sat3V N), sat3Bit N c ⟨1, by omega⟩ w.val
              (by have := w.isLt; omega) ∈ S)).card * sat3V N
          + (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
            sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
          + (∑ c : Fin (sat3M N), ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
            sat3Bit N c ⟨2, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
          + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
            sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
          + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
            sat3Bit N c ⟨1, by omega⟩ (sat3V N) (by omega) ∈ S)).card
          + ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
            sat3Bit N c ⟨2, by omega⟩ (sat3V N) (by omega) ∈ S)).card
          + 3 * sat3V N + 3) := by
  classical
  obtain ⟨S, hT1, hT2, hdich⟩ :=
    sat3_multi_bulk_census_circuit N hv hm3 hk cc hcomp hmin T hT hband
  refine ⟨S, hT1, hT2, ?_⟩
  rcases hdich with h | h
  · exact Or.inl h
  · right
    have hled := sat3_grid_mass_ledger N S
    omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_grid_mass_ledger
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.varsOf_card_le_cone
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_band_cone_cost
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_band_flight
