import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitSizeT

/-!
# Cook–Levin M2 emitter — E6 step 14: THE BIT-LEVEL SIZE BOUND

The encoded emission's length: every clause of `emittedTotal` has at most `P + card + 4`
literals, every variable index is at most `3(B + P + card + 3)² + 2` (the `3·Nat.pair + k`
encoding at coordinates `t ≤ B + 1`, second coordinate `≤ P + card + 1`), so
`encodeFormulaT (emittedTotal …)` is bounded by the explicit polynomial `emittedBitBound` —
the output-size half of the `PolyBounded` obligations, closed.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitBits

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics
open PallLean.Paper93.DeepMath.PathB.CookLevinTransition
open PallLean.Paper93.DeepMath.PathB.CookLevinWrite
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
open PallLean.Paper93.DeepMath.PathB.CookLevinAssembly
open PallLean.Paper93.DeepMath.PathB.CookLevinConverse
open PallLean.Paper93.DeepMath.PathB.CookLevinReduce
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitHeadFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitDynFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitGlue
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodecT
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSizeT

/-! ## Variable-index bounds -/

theorem pair_le (a b : ℕ) : Nat.pair a b ≤ (a + b + 1) * (a + b + 1) := by
  unfold Nat.pair
  split <;> nlinarith

/-- The uniform variable bound at coordinates `t ≤ T`, second coordinate `≤ C`. -/
def VB (T C : ℕ) : ℕ := 3 * ((T + C + 1) * (T + C + 1)) + 2

theorem cellVar_le {t p T C : ℕ} (ht : t ≤ T) (hp : p ≤ C) : cellVar t p ≤ VB T C := by
  have h1 := pair_le t p
  have h2 : (t + p + 1) * (t + p + 1) ≤ (T + C + 1) * (T + C + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold cellVar VB
  omega

theorem headVar_le {t p T C : ℕ} (ht : t ≤ T) (hp : p ≤ C) : headVar t p ≤ VB T C := by
  have h1 := pair_le t p
  have h2 : (t + p + 1) * (t + p + 1) ≤ (T + C + 1) * (T + C + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold headVar VB
  omega

theorem stateVar_le {t q T C : ℕ} (ht : t ≤ T) (hq : q ≤ C) : stateVar t q ≤ VB T C := by
  have h1 := pair_le t q
  have h2 : (t + q + 1) * (t + q + 1) ≤ (T + C + 1) * (T + C + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold stateVar VB
  omega

/-! ## Clause-shape bounds -/

theorem implClause_bounds (g1 g2 g3 co : Lit) (V : ℕ)
    (h1 : g1.1 ≤ V) (h2 : g2.1 ≤ V) (h3 : g3.1 ≤ V) (h4 : co.1 ≤ V) :
    (implClause g1 g2 g3 co).length ≤ 4 ∧ ∀ l ∈ implClause g1 g2 g3 co, l.1 ≤ V := by
  refine ⟨by simp [implClause], ?_⟩
  intro l hl
  simp only [implClause, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl <;> simpa

theorem atMostOne_mem_shape : ∀ (l : List ℕ), ∀ c ∈ atMostOne l,
    ∃ v ∈ l, ∃ w ∈ l, c = [(v, false), (w, false)]
  | [], c, hc => absurd hc (by simp [atMostOne])
  | v :: vs, c, hc => by
    rw [atMostOne, List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
      exact ⟨v, List.mem_cons_self, w, List.mem_cons_of_mem _ hw, rfl⟩
    · obtain ⟨v', hv', w', hw', rfl⟩ := atMostOne_mem_shape vs c hc
      exact ⟨v', List.mem_cons_of_mem _ hv', w', List.mem_cons_of_mem _ hw', rfl⟩

/-- One-hot over range-mapped variables: every clause is short and its variables bounded. -/
theorem oneHot_range_bounds (f : ℕ → ℕ) (n V L : ℕ) (hn : n ≤ L) (hL2 : 2 ≤ L)
    (hf : ∀ i < n, f i ≤ V) :
    ∀ c ∈ oneHot ((List.range n).map f), c.length ≤ L ∧ ∀ l ∈ c, l.1 ≤ V := by
  intro c hc
  rw [oneHot, List.mem_cons] at hc
  rcases hc with rfl | hc
  · constructor
    · rw [atLeastOne, List.length_map, List.length_map, List.length_range]
      exact hn
    · intro l hl
      rw [atLeastOne] at hl
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hl
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
      exact hf i (List.mem_range.mp hi)
  · obtain ⟨v, hv, w, hw, rfl⟩ := atMostOne_mem_shape _ c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
    refine ⟨by simp only [List.length_cons, List.length_nil]; omega, ?_⟩
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact hf i (List.mem_range.mp hi)
    · exact hf j (List.mem_range.mp hj)

/-! ## The sweep -/

/-- **Every emitted clause is short with bounded variables**: at most `P + card + 4` literals,
variables at most `VB (B + 1) (P + card + 1)`. -/
theorem emittedTotal_clause_bounds (M : Machine) (x : List Bool) (P B : ℕ) :
    ∀ c ∈ emittedTotal M x P B,
      c.length ≤ P + Fintype.card M.State + 4
      ∧ ∀ l ∈ c, l.1 ≤ VB (B + 1) (P + Fintype.card M.State + 1) := by
  set s := Fintype.card M.State with hs
  set V := VB (B + 1) (P + s + 1) with hV
  have hdyn : ∀ (t : ℕ), t ≤ B → ∀ (q : Fin s) (p : ℕ), p ≤ P + 1 → ∀ (b : Bool),
      ∀ c ∈ dynamicsClause M t q p b,
        c.length ≤ P + s + 4 ∧ ∀ l ∈ c, l.1 ≤ V := by
    intro t ht q p hp b c hc
    rw [dynamicsClause] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    have hq : q.val ≤ P + s + 1 := by have := q.isLt; omega
    have hns : nextStateIdx M q p b ≤ P + s + 1 := by
      have : nextStateIdx M q p b < s := by
        rw [nextStateIdx]
        exact Fin.isLt _
      omega
    have hnh : nextHead M q p b ≤ P + s + 1 := by
      have h1 : nextHead M q p b ≤ p + 1 := by
        rw [nextHead, stepStateHead]
        split
        · omega
        · rw [moveHead]
          split
          · omega
          · split
            · omega
            · split <;> omega
      omega
    rcases hc with rfl | rfl
    · refine (implClause_bounds _ _ _ _ V ?_ ?_ ?_ ?_).imp (fun h => by omega) id
      · exact stateVar_le (by omega) hq
      · exact headVar_le (by omega) (by omega)
      · exact cellVar_le (by omega) (by omega)
      · exact stateVar_le (by omega) hns
    · refine (implClause_bounds _ _ _ _ V ?_ ?_ ?_ ?_).imp (fun h => by omega) id
      · exact stateVar_le (by omega) hq
      · exact headVar_le (by omega) (by omega)
      · exact cellVar_le (by omega) (by omega)
      · exact headVar_le (by omega) hnh
  intro c hc
  rw [emittedTotal, emittedFormula] at hc
  simp only [List.mem_append] at hc
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
  · -- cell fixes
    rw [cellFixes, fixBits] at hc
    obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hpr
    refine ⟨by simp only [List.length_cons, List.length_nil]; omega, ?_⟩
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    subst hl
    exact cellVar_le (by omega) (by rw [List.mem_range] at hp; omega)
  · -- tape family
    rw [tapeFamily, bigAnd] at hc
    obtain ⟨F, hF, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hF
    rw [List.mem_range] at ht
    rw [bigAnd] at hc
    obtain ⟨F', hF', hc⟩ := List.mem_flatten.mp hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hF'
    rw [List.mem_range] at hp
    rw [cellCopyClause, guardedIff] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    all_goals {
      refine ⟨by simp only [List.length_cons, List.length_nil]; omega, ?_⟩
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl
      · exact headVar_le (by omega) (by omega)
      · exact cellVar_le (by omega) (by omega)
      · exact cellVar_le (by omega) (by omega)
    }
  · -- write family
    rw [writeFamily, bigAnd] at hc
    obtain ⟨F, hF, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hF
    rw [List.mem_range] at ht
    rw [bigAnd] at hc
    obtain ⟨F', hF', hc⟩ := List.mem_flatten.mp hc
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hF'
    rw [bigAnd] at hc
    obtain ⟨F'', hF'', hc⟩ := List.mem_flatten.mp hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hF''
    rw [List.mem_range] at hp
    rw [bigAnd] at hc
    obtain ⟨F3, hF3, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hF3
    rw [writeClause] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    refine (implClause_bounds _ _ _ _ V ?_ ?_ ?_ ?_).imp (fun h => by omega) id
    · exact stateVar_le (by omega) (by have := q.isLt; omega)
    · exact headVar_le (by omega) (by omega)
    · exact cellVar_le (by omega) (by omega)
    · exact cellVar_le (by omega) (by omega)
  · -- dynamics A
    rw [dynAFormula, bigAnd] at hc
    obtain ⟨F, hF, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hF
    rw [List.mem_range] at ht
    rw [bigAnd] at hc
    obtain ⟨F', hF', hc⟩ := List.mem_flatten.mp hc
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hF'
    rw [bigAnd] at hc
    obtain ⟨F'', hF'', hc⟩ := List.mem_flatten.mp hc
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hF''
    rw [List.mem_range] at hk
    rw [List.mem_append] at hc
    have hb : ∀ (b : Bool), c ∈ dynQBF M t q b k →
        c.length ≤ P + s + 4 ∧ ∀ l ∈ c, l.1 ≤ V := by
      intro b hcb
      by_cases h0 : mvN M q.val b = 0
      · rw [dynQBF, if_pos h0] at hcb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hcb
        have hq : q.val ≤ P + s + 1 := by have := q.isLt; omega
        rcases hcb with rfl | rfl
        · refine (implClause_bounds _ _ _ _ V ?_ ?_ ?_ ?_).imp (fun h => by omega) id
          · exact stateVar_le (by omega) hq
          · exact headVar_le (by omega) (by omega)
          · exact cellVar_le (by omega) (by omega)
          · exact stateVar_le (by omega) (by
              have : nextStateIdx M q k b < s := by
                rw [nextStateIdx]; exact Fin.isLt _
              omega)
        · refine (implClause_bounds _ _ _ _ V ?_ ?_ ?_ ?_).imp (fun h => by omega) id
          · exact stateVar_le (by omega) hq
          · exact headVar_le (by omega) (by omega)
          · exact cellVar_le (by omega) (by omega)
          · exact headVar_le (by omega) (by
              rw [(nextHead_of_mv M q b (k + 1)).1 h0]
              omega)
      · rw [dynQBF, if_neg h0] at hcb
        exact hdyn t (by omega) q k (by omega) b c hcb
    rcases hc with hc | hc
    · exact hb false hc
    · exact hb true hc
  · -- head loop
    rw [bigAnd] at hc
    obtain ⟨F, hF, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hF
    rw [List.mem_range] at ht
    rw [(headOneHotEmit_perm t P).mem_iff, headOneHot] at hc
    exact oneHot_range_bounds (headVar t) (P + 1) V (P + s + 4) (by omega) (by omega)
      (fun i hi => headVar_le (by omega) (by omega)) c hc
  · -- state loop
    rw [bigAnd] at hc
    obtain ⟨F, hF, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hF
    rw [List.mem_range] at ht
    rw [stateOneHot] at hc
    exact oneHot_range_bounds (stateVar t) s V (P + s + 4) (by omega) (by omega)
      (fun i hi => stateVar_le (by omega) (by omega)) c hc
  · -- dynamics B
    rw [dynBFormula, bigAnd] at hc
    obtain ⟨F, hF, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hF
    rw [List.mem_range] at ht
    rw [bigAnd] at hc
    obtain ⟨F', hF', hc⟩ := List.mem_flatten.mp hc
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hF'
    rw [List.mem_append] at hc
    have hb : ∀ (b : Bool), c ∈ leftFq M t q b →
        c.length ≤ P + s + 4 ∧ ∀ l ∈ c, l.1 ≤ V := by
      intro b hcb
      by_cases h0 : mvN M q.val b = 0
      · rw [leftFq, if_pos h0] at hcb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hcb
        subst hcb
        refine (implClause_bounds _ _ _ _ V ?_ ?_ ?_ ?_).imp (fun h => by omega) id
        · exact stateVar_le (by omega) (by have := q.isLt; omega)
        · exact headVar_le (by omega) (by omega)
        · exact cellVar_le (by omega) (by omega)
        · exact headVar_le (by omega) (by
            rw [nextHead_left_zero M q b h0]
            omega)
      · rw [leftFq, if_neg h0] at hcb
        exact absurd hcb List.not_mem_nil
    rcases hc with hc | hc
    · exact hb false hc
    · exact hb true hc
  · -- state top
    rw [stateOneHot] at hc
    exact oneHot_range_bounds (stateVar B) s V (P + s + 4) (by omega) (by omega)
      (fun i hi => stateVar_le (by omega) (by omega)) c hc
  · -- head top
    rw [(headOneHotEmit_perm B P).mem_iff, headOneHot] at hc
    exact oneHot_range_bounds (headVar B) (P + 1) V (P + s + 4) (by omega) (by omega)
      (fun i hi => headVar_le (by omega) (by omega)) c hc
  · -- accept
    rw [acceptFormula] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    constructor
    · rw [atLeastOne, List.length_map, List.length_map]
      have h1 : (acceptStates M).length ≤ s := by
        rw [acceptStates]
        exact le_trans (List.length_filter_le _ _) (le_of_eq (List.length_finRange))
      omega
    · intro l hl
      rw [atLeastOne] at hl
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hl
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hv
      exact stateVar_le (by omega) (by have := q.isLt; omega)
  · -- init units
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨by simp only [List.length_cons, List.length_nil]; omega, ?_⟩
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      exact stateVar_le (by omega) (by have := Fin.isLt (Fintype.equivFin M.State M.start); omega)
    · refine ⟨by simp only [List.length_cons, List.length_nil]; omega, ?_⟩
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      exact headVar_le (by omega) (by omega)

/-! ## The bit-level bound -/

theorem flatten_map_length_le {α β : Type} (l : List α) (f : α → List β) (K : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ K) : ((l.map f).flatten).length ≤ l.length * K := by
  rw [List.length_flatten, List.map_map]
  have hb : (l.map (List.length ∘ f)).sum ≤ (l.map (List.length ∘ f)).length • K := by
    apply List.sum_le_card_nsmul
    intro y hy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
    exact h a ha
  rwa [List.length_map, smul_eq_mul] at hb

/-- The explicit bit-length polynomial for the coded emission. -/
def emittedBitBound (P B s : ℕ) : ℕ :=
  emittedSizeBound P B s
    * ((P + s + 4 + 1)
      + (P + s + 4) * (2 * (3 * ((B + 1 + (P + s + 1) + 1) * (B + 1 + (P + s + 1) + 1)) + 2) + 6))
    + 1

/-- **The coded emission's bit length is polynomially bounded.** -/
theorem encodeFormulaT_emitted_le (M : Machine) (x : List Bool) (P B : ℕ) :
    (encodeFormulaT (emittedTotal M x P B)).length
      ≤ emittedBitBound P B (Fintype.card M.State) := by
  set s := Fintype.card M.State with hs
  set V := VB (B + 1) (P + s + 1) with hVdef
  set L := P + s + 4 with hL
  set K := (L + 1) + L * (2 * V + 6) with hK
  have hclause : ∀ c ∈ emittedTotal M x P B, (encodeClause' c).length ≤ K := by
    intro c hc
    obtain ⟨hlen, hvars⟩ := emittedTotal_clause_bounds M x P B c hc
    have h1 := encodeClause'_length_le c V hvars
    have h2 : c.length * (2 * V + 6) ≤ L * (2 * V + 6) :=
      Nat.mul_le_mul_right _ hlen
    omega
  have hflat := flatten_map_length_le (emittedTotal M x P B) encodeClause' K hclause
  have hsz := emittedTotal_length_le M x P B
  have h3 : (emittedTotal M x P B).length * K ≤ emittedSizeBound P B s * K :=
    Nat.mul_le_mul_right _ hsz
  rw [encodeFormulaT, List.length_append, List.length_cons, List.length_nil]
  have hb : emittedBitBound P B s = emittedSizeBound P B s * K + 1 := by
    rw [hK, hL, hVdef]
    rfl
  omega

/-- **Polynomial output size at the reduction parameters.** -/
theorem encodeFormulaT_emittedReduction_le (M : Machine) (x : List Bool) (clock : ℕ) :
    (encodeFormulaT (emittedReduction M x clock)).length
      ≤ emittedBitBound (x.length + clock) clock (Fintype.card M.State) :=
  encodeFormulaT_emitted_le M x (x.length + clock) clock

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitBits
