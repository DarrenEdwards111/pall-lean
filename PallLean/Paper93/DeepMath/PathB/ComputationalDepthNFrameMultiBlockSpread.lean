import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMultiBlockCensus

/-!
# N-Frame: the position-spread dichotomy — pairwise structure of the inside mass

Rung 7 of the multi-block arc (… → drag → window → census → **spread**).  The rung-6 rectangle
census reaches `Θ(N)` only if the balanced cut carries a large clean rectangle; this file proves
the two halves of the position-spread dichotomy at the PAIR level, and the count that governs
the spread side:

  `sat3_multi_pair_bound` — **PROVED**: for any two distinct slot-1-clean blocks, any `t`
        common inside positions with pin-pool room satisfy `2t ≤ j` — the `|C| = 2` rectangle.
  `sat3_multi_pair_dichotomy` — **PROVED, the dichotomy**: every clean pair has
        `2 · |In₀(c) ∩ In₀(c')| ≤ j`  OR  `2 · (m − 2 − Q_pair) ≤ j` —
        small intersection, or the pin pool itself is already `j`-exhausted.
  `sat3_multi_codegree_count` — **PROVED, the double count**: summed over ordered pairs of
        blocks, the intersection sizes equal the summed off-diagonal degree counts over
        positions — the bipartite incidence count in both orders.
  `sat3_multi_spread_census` — **PROVED, the spread-side count**: when `j` is below pool scale
        (`j + 1 ≤ 2(m − 2 − Q)`), every pair intersects in `≤ j/2` positions, and
        Cauchy–Schwarz turns this into a quadratic mass bound:
        `2·A² ≤ v · |B.offDiag| · j + 2·v·A`
        for the total inside mass `A` of any slot-1-clean block set `B`.

Reading the dichotomy: the adversary must choose.  Concentrate the inside mass on shared
positions and the rectangle census prices `|C|·|W| ≤ j` at product scale; spread it and the
quadratic count caps the mass at `A ≲ v + m·√(v·j)`.  Both horns are now theorems.

## Honest scope

At `A ~ T = Θ(m·v)` the spread census forces only `j = Ω(v) = Ω(√N)` — it independently
confirms the rung-6 ceiling rather than beating it (a random-like `S` with pairwise-small
intersections realizes it, so the pairwise bound alone CANNOT give `Ω(N)`).  What remains for
`coneExcess = Ω(N)` / a `(2+c)·N` cbudget bound is the BULK half of the dichotomy: upgrading
pairwise-small to a global structure theorem — either a `Θ(m) × Θ(m)` clean rectangle exists
(rectangle census fires at `Θ(N)`), or a stronger-than-pairwise count applies — and/or using
circuit-side structure of `S` (a minimal circuit's balanced cut is `varsOf`-shaped, not
random).  That bulk upgrade is the named remaining frontier.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The pair bound -/

set_option maxHeartbeats 800000 in
/-- **The pair bound (proved)**: two distinct clean blocks sharing `t` inside positions with
pin-pool room force `2t ≤ j` — the `|C| = 2` instance of the rectangle census. -/
theorem sat3_multi_pair_bound (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (c c' : Fin (sat3M N)) (hne : c ≠ c')
    (hclean1 : ∀ w : Fin (sat3V N),
      sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)
    (hclean1' : ∀ w : Fin (sat3V N),
      sat3Bit N c' ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)
    (t : ℕ)
    (ht : t ≤ (((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))
      ∩ ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c' ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))).card)
    (hroom : t + (((Finset.univ : Finset (Fin (sat3M N)))
        \ ({c, c'} : Finset (Fin (sat3M N)))).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      ≤ sat3M N - 2) :
    2 * t ≤ j := by
  classical
  obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq ht
  have hcard2 : ({c, c'} : Finset (Fin (sat3M N))).card = 2 := Finset.card_pair hne
  have hmv : sat3M N - 1 ≤ sat3V N := sat3M_pred_le_sat3V N
  have hget := sat3_multi_rectangle_census N hv hcut
    ({c, c'} : Finset (Fin (sat3M N))) W
    (fun b hb w hw => by
      rcases Finset.mem_insert.mp hb with hb | hb
      · rw [hb]
        exact (Finset.mem_filter.mp (Finset.mem_inter.mp (hWsub hw)).1).2
      · rw [Finset.mem_singleton] at hb
        rw [hb]
        exact (Finset.mem_filter.mp (Finset.mem_inter.mp (hWsub hw)).2).2)
    (fun b hb w => by
      rcases Finset.mem_insert.mp hb with hb | hb
      · rw [hb]
        exact hclean1 w
      · rw [Finset.mem_singleton] at hb
        rw [hb]
        exact hclean1' w)
    (by rw [hcard2]; omega)
    (by rw [hcard2, hWcard]; exact hroom)
  rw [hcard2, hWcard] at hget
  exact hget

/-! ### The dichotomy -/

set_option maxHeartbeats 800000 in
/-- **THE POSITION-SPREAD DICHOTOMY (proved, pair form)**: every pair of distinct clean blocks
has small inside intersection (`2·|∩| ≤ j`), or the pin pool is already `j`-exhausted
(`2·(m − 2 − Q_pair) ≤ j`). -/
theorem sat3_multi_pair_dichotomy (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (c c' : Fin (sat3M N)) (hne : c ≠ c')
    (hclean1 : ∀ w : Fin (sat3V N),
      sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)
    (hclean1' : ∀ w : Fin (sat3V N),
      sat3Bit N c' ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S) :
    2 * ((((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))
      ∩ ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c' ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))).card) ≤ j
    ∨ 2 * (sat3M N - 2
      - (((Finset.univ : Finset (Fin (sat3M N)))
          \ ({c, c'} : Finset (Fin (sat3M N)))).filter (fun b =>
          sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card) ≤ j := by
  classical
  by_cases hQ : sat3M N - 2
      ≤ (((Finset.univ : Finset (Fin (sat3M N)))
        \ ({c, c'} : Finset (Fin (sat3M N)))).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
  · right
    omega
  · by_cases hcase : (((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))
      ∩ ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c' ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))).card
      ≤ sat3M N - 2
        - (((Finset.univ : Finset (Fin (sat3M N)))
          \ ({c, c'} : Finset (Fin (sat3M N)))).filter (fun b =>
          sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
    · left
      exact sat3_multi_pair_bound N hv hcut c c' hne hclean1 hclean1' _
        (le_refl _) (by omega)
    · right
      exact sat3_multi_pair_bound N hv hcut c c' hne hclean1 hclean1' _
        (by omega) (by omega)

/-! ### The codegree double count -/

set_option maxHeartbeats 1600000 in
/-- **The codegree double count (proved)**: over ordered pairs of distinct blocks of `B`, the
inside-intersection sizes sum to the same total as the off-diagonal degree counts over
positions. -/
theorem sat3_multi_codegree_count (N : ℕ) (S : Finset (Fin N))
    (B : Finset (Fin (sat3M N))) :
    ∑ p ∈ B.offDiag,
      (((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N p.1 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))
      ∩ ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N p.2 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))).card
    = ∑ w : Fin (sat3V N),
      ((B.filter (fun b => sat3Bit N b ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∈ S)).offDiag).card := by
  classical
  have hL : ∀ p : Fin (sat3M N) × Fin (sat3M N),
      (((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N p.1 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))
      ∩ ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N p.2 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))).card
      = ∑ w : Fin (sat3V N),
        if (sat3Bit N p.1 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
          ∧ sat3Bit N p.2 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)
        then 1 else 0 := by
    intro p
    rw [← Finset.filter_and, Finset.card_filter]
  have hR : ∀ w : Fin (sat3V N),
      ((B.filter (fun b => sat3Bit N b ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∈ S)).offDiag).card
      = ∑ p ∈ B.offDiag,
        if (sat3Bit N p.1 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
          ∧ sat3Bit N p.2 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)
        then 1 else 0 := by
    intro w
    rw [← Finset.card_filter]
    congr 1
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, hs1⟩, ⟨h2, hs2⟩, hpne⟩
      exact ⟨⟨h1, h2, hpne⟩, hs1, hs2⟩
    · rintro ⟨⟨h1, h2, hpne⟩, hs1, hs2⟩
      exact ⟨⟨h1, hs1⟩, ⟨h2, hs2⟩, hpne⟩
  calc ∑ p ∈ B.offDiag,
      (((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N p.1 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))
      ∩ ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N p.2 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))).card
      = ∑ p ∈ B.offDiag, ∑ w : Fin (sat3V N),
        if (sat3Bit N p.1 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
          ∧ sat3Bit N p.2 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)
        then 1 else 0 :=
        Finset.sum_congr rfl (fun p _ => hL p)
    _ = ∑ w : Fin (sat3V N), ∑ p ∈ B.offDiag,
        if (sat3Bit N p.1 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
          ∧ sat3Bit N p.2 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)
        then 1 else 0 :=
        Finset.sum_comm
    _ = ∑ w : Fin (sat3V N),
        ((B.filter (fun b => sat3Bit N b ⟨0, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S)).offDiag).card :=
        Finset.sum_congr rfl (fun w _ => (hR w).symm)

/-! ### The spread census -/

set_option maxHeartbeats 1600000 in
/-- **THE SPREAD CENSUS (proved)**: when `j` is below pool scale, pairwise-small intersections
plus Cauchy–Schwarz cap the total inside mass of any clean block set quadratically:
`2·A² ≤ v · |B.offDiag| · j + 2·v·A`. -/
theorem sat3_multi_spread_census (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (B : Finset (Fin (sat3M N)))
    (hcleanB : ∀ b ∈ B, ∀ w : Fin (sat3V N),
      sat3Bit N b ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)
    (hjs : j + 1 ≤ 2 * (sat3M N - 2
      - ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card)) :
    2 * ((∑ b ∈ B, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N b ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
      * (∑ b ∈ B, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N b ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card))
    ≤ sat3V N * (B.offDiag.card * j)
      + 2 * (sat3V N * ∑ b ∈ B, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N b ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card) := by
  classical
  -- every pair of `B` has small intersection: the dichotomy's second horn is excluded
  have hpair : ∀ p ∈ B.offDiag,
      2 * ((((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N p.1 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))
      ∩ ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N p.2 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))).card) ≤ j := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    have hQmono : (((Finset.univ : Finset (Fin (sat3M N)))
        \ ({p.1, p.2} : Finset (Fin (sat3M N)))).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
        ≤ ((Finset.univ : Finset (Fin (sat3M N))).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card := by
      apply Finset.card_le_card
      intro b hb
      rw [Finset.mem_filter] at hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb.2⟩
    rcases sat3_multi_pair_dichotomy N hv hcut p.1 p.2 hp.2.2
      (hcleanB p.1 hp.1) (hcleanB p.2 hp.2.1) with h | h
    · exact h
    · omega
  -- the pairwise intersections sum below the budget
  have hsumpair : 2 * (∑ p ∈ B.offDiag,
      (((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N p.1 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))
      ∩ ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N p.2 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))).card)
      ≤ B.offDiag.card * j := by
    rw [Finset.mul_sum]
    calc ∑ p ∈ B.offDiag, 2 * (((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N p.1 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))
        ∩ ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N p.2 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))).card
        ≤ ∑ _p ∈ B.offDiag, j := Finset.sum_le_sum hpair
      _ = B.offDiag.card * j := by rw [Finset.sum_const, smul_eq_mul]
  have hdc := sat3_multi_codegree_count N S B
  -- degree sum over positions is the total mass
  have hdegsum : ∑ w : Fin (sat3V N), (B.filter (fun b =>
      sat3Bit N b ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
      = ∑ b ∈ B, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N b ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card := by
    calc ∑ w : Fin (sat3V N), (B.filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
        = ∑ w : Fin (sat3V N), ∑ b ∈ B,
          if sat3Bit N b ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
          then 1 else 0 :=
          Finset.sum_congr rfl (fun w _ => by rw [Finset.card_filter])
      _ = ∑ b ∈ B, ∑ w : Fin (sat3V N),
          if sat3Bit N b ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
          then 1 else 0 :=
          Finset.sum_comm
      _ = ∑ b ∈ B, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N b ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card :=
          Finset.sum_congr rfl (fun b _ => by rw [Finset.card_filter])
  -- the pointwise square identity
  have hsq : ∀ w : Fin (sat3V N),
      (B.filter (fun b => sat3Bit N b ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∈ S)).card
      * (B.filter (fun b => sat3Bit N b ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∈ S)).card
      = ((B.filter (fun b => sat3Bit N b ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∈ S)).offDiag).card
      + (B.filter (fun b => sat3Bit N b ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∈ S)).card := by
    intro w
    rw [Finset.offDiag_card]
    have hd : (B.filter (fun b => sat3Bit N b ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∈ S)).card
        ≤ (B.filter (fun b => sat3Bit N b ⟨0, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S)).card
        * (B.filter (fun b => sat3Bit N b ⟨0, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S)).card := by
      rcases Nat.eq_zero_or_pos (B.filter (fun b =>
          sat3Bit N b ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
        with h0 | hpos
      · rw [h0]
      · exact Nat.le_mul_of_pos_left _ hpos
    exact (Nat.sub_add_cancel hd).symm
  -- summed square identity
  have hsqsum : ∑ w : Fin (sat3V N),
      ((B.filter (fun b => sat3Bit N b ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∈ S)).card
      * (B.filter (fun b => sat3Bit N b ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∈ S)).card)
      = (∑ w : Fin (sat3V N), ((B.filter (fun b =>
          sat3Bit N b ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).offDiag).card)
      + ∑ b ∈ B, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N b ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card := by
    rw [← hdegsum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun w _ => hsq w)
  -- Cauchy–Schwarz
  have hcs : (∑ b ∈ B, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N b ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
      * (∑ b ∈ B, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N b ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
      ≤ sat3V N * ∑ w : Fin (sat3V N),
        ((B.filter (fun b => sat3Bit N b ⟨0, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S)).card
        * (B.filter (fun b => sat3Bit N b ⟨0, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S)).card) := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin (sat3V N))))
      (f := fun w => (B.filter (fun b => sat3Bit N b ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∈ S)).card)
    simp only [pow_two] at h
    rw [Finset.card_univ, Fintype.card_fin, hdegsum] at h
    exact h
  -- assembly
  calc 2 * ((∑ b ∈ B, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N b ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)
      * (∑ b ∈ B, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N b ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card))
      ≤ 2 * (sat3V N * ∑ w : Fin (sat3V N),
        ((B.filter (fun b => sat3Bit N b ⟨0, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S)).card
        * (B.filter (fun b => sat3Bit N b ⟨0, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S)).card)) :=
        Nat.mul_le_mul_left _ hcs
    _ = 2 * (sat3V N * ((∑ w : Fin (sat3V N), ((B.filter (fun b =>
          sat3Bit N b ⟨0, by omega⟩ w.val
            (by have := w.isLt; omega) ∈ S)).offDiag).card)
        + ∑ b ∈ B, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N b ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card)) := by
        rw [hsqsum]
    _ = sat3V N * (2 * ∑ w : Fin (sat3V N), ((B.filter (fun b =>
          sat3Bit N b ⟨0, by omega⟩ w.val
            (by have := w.isLt; omega) ∈ S)).offDiag).card)
        + 2 * (sat3V N * ∑ b ∈ B, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N b ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card) := by
        ring
    _ = sat3V N * (2 * ∑ p ∈ B.offDiag,
          (((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
            sat3Bit N p.1 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))
          ∩ ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
            sat3Bit N p.2 ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))).card)
        + 2 * (sat3V N * ∑ b ∈ B, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N b ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card) := by
        rw [hdc]
    _ ≤ sat3V N * (B.offDiag.card * j)
        + 2 * (sat3V N * ∑ b ∈ B, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N b ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card) :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hsumpair) _

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_pair_bound
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_pair_dichotomy
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_codegree_count
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_spread_census
