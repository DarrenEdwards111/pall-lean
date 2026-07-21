import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTwelveGateShape

/-!
# Brick 2b of the `SlackComposes` m = 2 attack: the fanout dichotomy

The 12-edge double count over the 11 non-root wires of a hypothetical 12-gate
circuit for `AEm 2`: six genuine binary gates contribute exactly 12 in-range
edges, every non-root wire is read at least once, so **exactly one wire `s` is
read twice and every other wire exactly once**.  Assembled with brick 2a into
`TwelveShape` / `twelve_shape` — the full shape theorem.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

open Classical in
/-- The number of gates reading wire `q`. -/
noncomputable def rdCount (c : List (CGate (3 * 2))) (q : ℕ) : ℕ :=
  ((Finset.range 12).filter (fun w => q ∈ gateReads (c.getD w (.cst false)))).card

/-- The reader-count sum equals the edge count, which is exactly 12. -/
theorem rdCount_sum (c : List (CGate (3 * 2))) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) :
    ∑ q ∈ Finset.range 11, rdCount c q = 12 := by
  classical
  have hdich := twelve_gate_dichotomy c hcomp hlen
  -- the edge set
  set E : Finset (ℕ × ℕ) := (Finset.range 12 ×ˢ Finset.range 11).filter
    (fun p => p.2 ∈ gateReads (c.getD p.1 (.cst false))) with hEdef
  -- fiber over the reader: |E| = Σ over gates of reads-card
  have hfib1 : E.card = ∑ w ∈ Finset.range 12,
      (E.filter (fun p => p.1 = w)).card := by
    refine Finset.card_eq_sum_card_fiberwise ?_
    intro p hp
    simp only [Finset.mem_coe, hEdef, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact hp.1.1
  have hfibgate : ∀ w ∈ Finset.range 12,
      (E.filter (fun p => p.1 = w)).card
        = (gateReads (c.getD w (.cst false))).card := by
    intro w hw
    rw [Finset.mem_range] at hw
    have hfeq : E.filter (fun p => p.1 = w)
        = (gateReads (c.getD w (.cst false))).image (fun t => (w, t)) := by
      ext p
      rw [Finset.mem_filter, hEdef, Finset.mem_filter, Finset.mem_product,
        Finset.mem_image]
      constructor
      · rintro ⟨⟨⟨-, -⟩, hr⟩, hfst⟩
        exact ⟨p.2, hfst ▸ hr, by rw [← hfst]⟩
      · rintro ⟨t, ht, hpt⟩
        rcases hdich w hw with ⟨i, hg⟩ | ⟨op, j, k, hg, hj, hk, hjk⟩
        · rw [hg] at ht
          exact absurd ht (by simp [gateReads])
        · rw [hg] at ht
          have ht2 : t = j ∨ t = k := by
            rcases Finset.mem_insert.mp ht with h | h
            · exact Or.inl h
            · exact Or.inr (Finset.mem_singleton.mp h)
          have htlt : t < 11 := by
            rcases ht2 with h | h <;> omega
          refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
          · rw [← hpt]
            exact Finset.mem_range.mpr (by omega)
          · rw [← hpt]
            exact Finset.mem_range.mpr htlt
          · rw [← hpt, hg]
            exact ht
          · rw [← hpt]
    rw [hfeq]
    exact Finset.card_image_of_injective _ (fun a b hab => by
      have := congrArg Prod.snd hab
      exact this)
  -- reads-card sums to 12: six var gates (0 each) + six genuine bins (2 each)
  have hvarsCard : ((Finset.range 12).filter
      (fun w => ∃ i : Fin (3 * 2), c.getD w (.cst false) = CGate.var i)).card = 6 := by
    have hv := twelve_varsEq c hcomp hlen
    have hall := twelve_cone_all c hcomp hlen
    have hd : (depSet (AEm 2)).card = 6 := by
      rw [depSet_AEm, Finset.card_univ, Fintype.card_fin]
    have hcv : coneVars c = (Finset.range 12).filter
        (fun w => ∃ i : Fin (3 * 2), c.getD w (.cst false) = CGate.var i) := by
      rw [coneVars, hall]
    rw [← hcv, hv, hd]
  have hsplitc : ((Finset.range 12).filter
      (fun w => ∃ i : Fin (3 * 2), c.getD w (.cst false) = CGate.var i)).card
      + ((Finset.range 12).filter
        (fun w => ¬ ∃ i : Fin (3 * 2), c.getD w (.cst false) = CGate.var i)).card
      = 12 := by
    rw [Finset.card_filter_add_card_filter_not (s := Finset.range 12)
      (p := fun w => ∃ i : Fin (3 * 2), c.getD w (.cst false) = CGate.var i),
      Finset.card_range]
  have hsum12 : ∑ w ∈ Finset.range 12,
      (gateReads (c.getD w (.cst false))).card = 12 := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range 12)
      (fun w => ∃ i : Fin (3 * 2), c.getD w (.cst false) = CGate.var i)]
    have hz : ∑ w ∈ (Finset.range 12).filter
        (fun w => ∃ i : Fin (3 * 2), c.getD w (.cst false) = CGate.var i),
        (gateReads (c.getD w (.cst false))).card = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      rw [Finset.mem_filter] at hw
      obtain ⟨-, i, hi⟩ := hw
      rw [hi]
      rfl
    have h2 : ∑ w ∈ (Finset.range 12).filter
        (fun w => ¬ ∃ i : Fin (3 * 2), c.getD w (.cst false) = CGate.var i),
        (gateReads (c.getD w (.cst false))).card
        = 2 * ((Finset.range 12).filter
          (fun w => ¬ ∃ i : Fin (3 * 2), c.getD w (.cst false) = CGate.var i)).card := by
      rw [Finset.sum_congr rfl (fun w hw => ?_), Finset.sum_const, smul_eq_mul,
        Nat.mul_comm]
      rw [Finset.mem_filter] at hw
      rcases hdich w (Finset.mem_range.mp hw.1) with hvar | ⟨op, j, k, hg, hj, hk, hjk⟩
      · exact absurd hvar hw.2
      · rw [hg]
        show ({j, k} : Finset ℕ).card = 2
        rw [Finset.card_insert_of_notMem (by
          rw [Finset.mem_singleton]
          exact hjk), Finset.card_singleton]
    rw [hz, h2]
    omega
  -- fiber over the wire: |E| = Σ rdCount
  have hfib2 : E.card = ∑ q ∈ Finset.range 11,
      (E.filter (fun p => p.2 = q)).card := by
    refine Finset.card_eq_sum_card_fiberwise ?_
    intro p hp
    simp only [Finset.mem_coe, hEdef, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact hp.1.2
  have hfibq : ∀ q ∈ Finset.range 11,
      (E.filter (fun p => p.2 = q)).card = rdCount c q := by
    intro q hq
    rw [Finset.mem_range] at hq
    have hfeq : E.filter (fun p => p.2 = q)
        = ((Finset.range 12).filter
          (fun w => q ∈ gateReads (c.getD w (.cst false)))).image (fun w => (w, q)) := by
      ext p
      rw [Finset.mem_filter, hEdef, Finset.mem_filter, Finset.mem_product,
        Finset.mem_image]
      constructor
      · rintro ⟨⟨⟨hw12, -⟩, hr⟩, hsnd⟩
        refine ⟨p.1, Finset.mem_filter.mpr ⟨hw12, hsnd ▸ hr⟩, ?_⟩
        rw [← hsnd]
      · rintro ⟨w, hw, hpw⟩
        rw [Finset.mem_filter] at hw
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
        · rw [← hpw]
          exact hw.1
        · rw [← hpw]
          exact Finset.mem_range.mpr hq
        · rw [← hpw]
          exact hw.2
        · rw [← hpw]
    rw [hfeq, rdCount]
    exact Finset.card_image_of_injective _ (fun a b hab => congrArg Prod.fst hab)
  rw [Finset.sum_congr rfl hfibq] at hfib2
  rw [Finset.sum_congr rfl hfibgate] at hfib1
  rw [← hfib2, hfib1, hsum12]

/-- Every non-root wire is read. -/
theorem rdCount_pos (c : List (CGate (3 * 2))) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) (q : ℕ) (hq : q < 11) : 1 ≤ rdCount c q := by
  classical
  have hall := twelve_cone_all c hcomp hlen
  have hqc : q ∈ cone c := by
    rw [hall]
    exact Finset.mem_range.mpr (by omega)
  obtain ⟨hqlt, hqic⟩ := mem_cone.mp hqc
  cases hqic with
  | root => omega
  | step hw hjm hjw =>
    rename_i w'
    refine Finset.card_pos.mpr ⟨w', Finset.mem_filter.mpr ⟨?_, hjm⟩⟩
    have := inCone_lt (by omega) hw
    exact Finset.mem_range.mpr (by omega)

/-- The `TwelveShape` record: the forced anatomy of a 12-gate circuit for `AEm 2`. -/
structure TwelveShape (c : List (CGate (3 * 2))) (s r₁ r₂ : ℕ) : Prop where
  cone_all : cone c = Finset.range 12
  dichotomy : ∀ p, p < 12 → (∃ i : Fin (3 * 2), c.getD p (.cst false) = CGate.var i)
    ∨ ∃ op j k, c.getD p (.cst false) = CGate.bin op j k ∧ j < p ∧ k < p ∧ j ≠ k
  var_inj : ∀ w₁ w₂ (i : Fin (3 * 2)), w₁ < 12 → w₂ < 12 →
    c.getD w₁ (.cst false) = CGate.var i → c.getD w₂ (.cst false) = CGate.var i →
    w₁ = w₂
  s_lt : s < 11
  r₁_lt : r₁ < 12
  r₂_lt : r₂ < 12
  r_ne : r₁ ≠ r₂
  r₁_reads : s ∈ gateReads (c.getD r₁ (.cst false))
  r₂_reads : s ∈ gateReads (c.getD r₂ (.cst false))
  s_only : ∀ r, r < 12 → s ∈ gateReads (c.getD r (.cst false)) → r = r₁ ∨ r = r₂
  others_one : ∀ q, q < 11 → q ≠ s → ∀ w₁ w₂, w₁ < 12 → w₂ < 12 →
    q ∈ gateReads (c.getD w₁ (.cst false)) → q ∈ gateReads (c.getD w₂ (.cst false)) →
    w₁ = w₂
  all_read : ∀ q, q < 11 → ∃ w, w < 12 ∧ q ∈ gateReads (c.getD w (.cst false))

/-- **THE SHAPE THEOREM (proved)**: a 12-gate circuit for `AEm 2` has exactly one
doubly-read wire; everything else is a read-once forest of var gates and genuine
binary gates. -/
theorem twelve_shape (c : List (CGate (3 * 2))) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) : ∃ s r₁ r₂, TwelveShape c s r₁ r₂ := by
  classical
  have hsum := rdCount_sum c hcomp hlen
  have hpos : ∀ q ∈ Finset.range 11, 1 ≤ rdCount c q := fun q hq =>
    rdCount_pos c hcomp hlen q (Finset.mem_range.mp hq)
  -- some wire is read twice
  have hex2 : ∃ s ∈ Finset.range 11, 2 ≤ rdCount c s := by
    by_contra hno
    push_neg at hno
    have hle : ∑ q ∈ Finset.range 11, rdCount c q ≤ 11 := by
      calc ∑ q ∈ Finset.range 11, rdCount c q
          ≤ ∑ _q ∈ Finset.range 11, 1 :=
            Finset.sum_le_sum (fun q hq => by
              have := hno q hq
              omega)
        _ = 11 := by simp
    omega
  obtain ⟨s, hs11, hs2⟩ := hex2
  have hs11' := Finset.mem_range.mp hs11
  -- the erased sum
  have herase : ∑ q ∈ (Finset.range 11).erase s, rdCount c q + rdCount c s
      = 12 := by
    rw [Finset.sum_erase_add _ _ hs11]
    exact hsum
  have herase_ge : 10 ≤ ∑ q ∈ (Finset.range 11).erase s, rdCount c q := by
    calc (10 : ℕ) = ((Finset.range 11).erase s).card := by
          rw [Finset.card_erase_of_mem hs11, Finset.card_range]
      _ = ∑ _q ∈ (Finset.range 11).erase s, 1 := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
      _ ≤ ∑ q ∈ (Finset.range 11).erase s, rdCount c q :=
          Finset.sum_le_sum (fun q hq => hpos q (Finset.mem_erase.mp hq).2)
  have hs_eq2 : rdCount c s = 2 := by omega
  have hothers : ∀ q, q < 11 → q ≠ s → rdCount c q = 1 := by
    intro q hq hqs
    by_contra hne1
    have hq2 : 2 ≤ rdCount c q := by
      have := hpos q (Finset.mem_range.mpr hq)
      omega
    have hstrict : ∑ _q ∈ (Finset.range 11).erase s, 1
        < ∑ q ∈ (Finset.range 11).erase s, rdCount c q := by
      refine Finset.sum_lt_sum (fun q' hq' => hpos q' (Finset.mem_erase.mp hq').2)
        ⟨q, Finset.mem_erase.mpr ⟨hqs, Finset.mem_range.mpr hq⟩, by omega⟩
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_one, Finset.card_erase_of_mem hs11,
      Finset.card_range] at hstrict
    omega
  -- unpack the two readers
  obtain ⟨r₁, r₂, hr_ne, hpair⟩ := Finset.card_eq_two.mp hs_eq2
  have hr₁mem : r₁ ∈ (Finset.range 12).filter
      (fun w => s ∈ gateReads (c.getD w (.cst false))) := by
    rw [hpair]
    exact Finset.mem_insert_self _ _
  have hr₂mem : r₂ ∈ (Finset.range 12).filter
      (fun w => s ∈ gateReads (c.getD w (.cst false))) := by
    rw [hpair]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [Finset.mem_filter, Finset.mem_range] at hr₁mem hr₂mem
  refine ⟨s, r₁, r₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact twelve_cone_all c hcomp hlen
  · exact twelve_gate_dichotomy c hcomp hlen
  · intro w₁ w₂ i h₁ h₂ hg₁ hg₂
    exact twelve_var_inj c hcomp hlen h₁ h₂ hg₁ hg₂
  · exact hs11'
  · exact hr₁mem.1
  · exact hr₂mem.1
  · exact hr_ne
  · exact hr₁mem.2
  · exact hr₂mem.2
  · intro r hr hread
    have : r ∈ ({r₁, r₂} : Finset ℕ) := by
      rw [← hpair, Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr hr, hread⟩
    rcases Finset.mem_insert.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mp h)
  · intro q hq hqs w₁ w₂ h₁ h₂ hg₁ hg₂
    have hcard := hothers q hq hqs
    refine Finset.card_le_one.mp (le_of_eq hcard) w₁ ?_ w₂ ?_
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h₁, hg₁⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h₂, hg₂⟩
  · intro q hq
    have hpos := rdCount_pos c hcomp hlen q hq
    rw [rdCount] at hpos
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one hpos)
    rw [Finset.mem_filter, Finset.mem_range] at hw
    exact ⟨w, hw.1, hw.2⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.twelve_shape
