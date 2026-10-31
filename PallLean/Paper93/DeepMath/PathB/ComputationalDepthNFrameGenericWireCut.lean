import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityHeadline

/-!
# N-Frame: the generic wire cut — balanced cuts for any root-shaped family

Work package 3 (… → parity headline → **generic wire cut**).  Reading the sat3 proof for the
mirror revealed the better theorem: once the ROOT SHAPE is a hypothesis, nothing
family-specific remains — the wire-cut factorization and the balanced-cut extraction hold for
ANY function.  This discharges the parity headline's `hj` condition given only the parity
family's root-shape fact (the one remaining mechanical mirror), and serves every future
family for free.

  `wire_cut_factorization_of_root_shape` — **PROVED, GENERIC**: for any minimal circuit
        computing `f` whose root is a binary gate, every wire below the root induces a cut
        factorization of `f` over its cone's variable support with trace width
        `≤ coneExcess + 1`.
  `balanced_cut_of_root_shape` — **PROVED, GENERIC**: at every band `T` within the root's
        support, a balanced coordinate set `S` (`T ≤ |S| ≤ 2T−2`) with a cut factorization of
        width `≤ coneExcess + 1`.

## Honest scope

The root-shape hypothesis for `parityFamilyBits` (the analogue of `sat3_root_shape`: a
minimal circuit's root gate is binary with distinct children — dischargeable from two
essential variables by mirroring the sat3 not-unary machinery) is the remaining input, named
condition (iii/iv) of the headline.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

set_option maxHeartbeats 1600000 in
/-- **THE GENERIC WIRE CUT (proved)**: with a binary root, every wire below the root induces
a cut factorization over its cone's variable support, priced at the exit trace. -/
theorem wire_cut_factorization_of_root_shape {n : ℕ} (f : (Fin n → Bool) → Bool)
    (c : List (CGate n)) (hcomp : computes c f) (hmin : c.length = cbudget f)
    (hroot : ∃ (op : Bool → Bool → Bool) (LL RR : ℕ),
      c.getD (c.length - 1) (CGate.cst false) = CGate.bin op LL RR
      ∧ LL < c.length - 1 ∧ RR < c.length - 1 ∧ LL ≠ RR)
    (w : ℕ) (hw : w < c.length - 1) :
    CutFactorization f (varsOf c w) (wireExits c w).card
    ∧ (wireExits c w).card ≤ coneExcess c (c.length - 1) + 1 := by
  classical
  obtain ⟨opR, LL, RR, hrootg, hLlt, hRlt, hLR⟩ := hroot
  refine ⟨⟨fun z e => (runFrom z [] c).getD
      (((wireExits c w).equivFin.symm e).val) false, ?_, ?_⟩,
    wireExits_card_le f c hcomp hmin w hw⟩
  · -- the trace is determined by the S-part
    intro z z' hzz
    funext e
    apply varsOf_agree_wire c (((wireExits c w).equivFin.symm e).val) z z'
    intro i hi
    apply hzz
    have hprop := ((wireExits c w).equivFin.symm e).2
    have hmemw : (((wireExits c w).equivFin.symm e).val) ∈ coneOf c w :=
      (Finset.mem_filter.mp hprop).1
    exact varsOf_mono c _ w hmemw hi
  · -- equal traces separate: the root value ignores the S-part beyond the trace
    intro x y y' hφeq
    have hsepPf : ∀ q ∈ coneOf c (c.length - 1), q ∉ coneOf c w →
        ∀ u ∈ childrenOf c q, u ∈ coneOf c w → u ∈ wireExits c w := by
      intro q hq hqT u huch huT
      exact Finset.mem_filter.mpr ⟨huT, Or.inr ⟨q, Finset.mem_range.mpr
        (by have := cone_le c (c.length - 1) q hq; omega), hqT, huch⟩⟩
    have hFvalPf : ∀ p ∈ wireExits c w,
        (runFrom (mixOn (varsOf c w)ᶜ x y) [] c).getD p false
          = (runFrom (mixOn (varsOf c w)ᶜ x y') [] c).getD p false := by
      intro p hp
      have hpmem : p ∈ coneOf c w := (Finset.mem_filter.mp hp).1
      have h1 : (runFrom (mixOn (varsOf c w)ᶜ x y) [] c).getD p false
          = (runFrom y [] c).getD p false := by
        apply varsOf_agree_wire
        intro i hi
        have hiS : i ∈ varsOf c w := varsOf_mono c p w hpmem hi
        show (if i ∈ (varsOf c w)ᶜ then x i else y i) = y i
        rw [if_neg (fun hc => (Finset.mem_compl.mp hc) hiS)]
      have h2 : (runFrom (mixOn (varsOf c w)ᶜ x y') [] c).getD p false
          = (runFrom y' [] c).getD p false := by
        apply varsOf_agree_wire
        intro i hi
        have hiS : i ∈ varsOf c w := varsOf_mono c p w hpmem hi
        show (if i ∈ (varsOf c w)ᶜ then x i else y' i) = y' i
        rw [if_neg (fun hc => (Finset.mem_compl.mp hc) hiS)]
      rw [h1, h2]
      have hidx := congrFun hφeq ((wireExits c w).equivFin ⟨p, hp⟩)
      simp only [Equiv.symm_apply_apply] at hidx
      exact hidx
    have hfrontPf : ∀ q ∈ coneOf c (c.length - 1), q ∉ coneOf c w →
        ∀ i, c.getD q (CGate.cst false) = CGate.var i →
        mixOn (varsOf c w)ᶜ x y i = mixOn (varsOf c w)ᶜ x y' i := by
      intro q hq hqT i hgate
      have hiNS : i ∉ varsOf c w := by
        intro hiS
        obtain ⟨-, p, hpw, hgate'⟩ := Finset.mem_filter.mp hiS
        have hple : p ≤ w := cone_le c w p hpw
        have hqle : q ≤ c.length - 1 := cone_le c (c.length - 1) q hq
        have hqlt : q < c.length - 1 := by
          rcases Nat.lt_or_eq_of_le hqle with h | h
          · exact h
          · exfalso
            rw [h, hrootg] at hgate
            cases hgate
        have hpq : p = q := by
          rcases Nat.lt_trichotomy p q with hlt | heq | hgt
          · exact (var_gate_unique f c hcomp hmin i p q hlt
              hqlt hgate' hgate).elim
          · exact heq
          · exact (var_gate_unique f c hcomp hmin i q p hgt
              (by omega) hgate hgate').elim
        apply hqT
        rw [← hpq]
        exact hpw
      show (if i ∈ (varsOf c w)ᶜ then x i else y i)
        = (if i ∈ (varsOf c w)ᶜ then x i else y' i)
      rw [if_pos (Finset.mem_compl.mpr hiNS), if_pos (Finset.mem_compl.mpr hiNS)]
    have hrootnot : c.length - 1 ∉ coneOf c w := by
      intro hc
      have := cone_le c w (c.length - 1) hc
      omega
    have hmain := sep_frontier_val_agree c (c.length - 1) (coneOf c w)
      (wireExits c w) hsepPf (mixOn (varsOf c w)ᶜ x y) (mixOn (varsOf c w)ᶜ x y')
      hFvalPf hfrontPf (c.length - 1) (cone_self c (c.length - 1)) hrootnot
    calc f (mixOn (varsOf c w)ᶜ x y)
        = (runFrom (mixOn (varsOf c w)ᶜ x y) [] c).getD (c.length - 1) false :=
          (hcomp _).symm
      _ = (runFrom (mixOn (varsOf c w)ᶜ x y') [] c).getD (c.length - 1) false :=
          hmain
      _ = f (mixOn (varsOf c w)ᶜ x y') := hcomp _

/-- **THE GENERIC BALANCED CUT (proved)**: at every band within the root's support, a
balanced coordinate set with a cut factorization of width `≤ coneExcess + 1`. -/
theorem balanced_cut_of_root_shape {n : ℕ} (f : (Fin n → Bool) → Bool)
    (c : List (CGate n)) (hcomp : computes c f) (hmin : c.length = cbudget f)
    (hroot : ∃ (op : Bool → Bool → Bool) (LL RR : ℕ),
      c.getD (c.length - 1) (CGate.cst false) = CGate.bin op LL RR
      ∧ LL < c.length - 1 ∧ RR < c.length - 1 ∧ LL ≠ RR)
    (T : ℕ) (hT : 2 ≤ T)
    (hband : 2 * T - 1 ≤ (varsOf c (c.length - 1)).card) :
    ∃ S : Finset (Fin n), T ≤ S.card ∧ S.card ≤ 2 * T - 2
    ∧ ∃ j : ℕ, j ≤ coneExcess c (c.length - 1) + 1 ∧ CutFactorization f S j := by
  obtain ⟨w, hwcone, hw1, hw2⟩ :=
    balanced_wire_exists c (c.length - 1) T hT (by omega)
  have hwlt : w < c.length - 1 := by
    have hle := cone_le c (c.length - 1) w hwcone
    rcases Nat.lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      rw [h] at hw2
      omega
  obtain ⟨hcut, hcard⟩ :=
    wire_cut_factorization_of_root_shape f c hcomp hmin hroot w hwlt
  exact ⟨varsOf c w, hw1, hw2, (wireExits c w).card, hcard, hcut⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.wire_cut_factorization_of_root_shape
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.balanced_cut_of_root_shape
