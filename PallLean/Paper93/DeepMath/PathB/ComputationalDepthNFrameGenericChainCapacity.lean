import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameAnnulusCapacity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameGenericRootShape

/-!
# N-Frame: the generic chain capacity — rung 22 for any root-shaped family

Expander-discharge arc, rung E5 (concentration channel).  Reading `exit_value_separation`
(rung 22) for the mirror revealed the same fact as the wire cut: once the ROOT SHAPE is a
hypothesis, the k-scale nested-chain capacity holds for ANY family.  This lifts rung 22 off
`sat3Family` and instantiates it at the parity family via `parity_root_shape`, giving the
**concentration channel's upper-bound machinery**: any row family pairwise distinguished at
some scale of a nested chain of `k+1` cuts is bounded by `2^{coneExcess + k + 1}`.

  `exit_value_separation_of_root_shape` — **PROVED, GENERIC**: agreement on a wire's exit
        values forces agreement of the family value under any fixed outer completion.
  `chain_capacity_excess_of_root_shape` — **PROVED, GENERIC**: `|Y| ≤ 2^{CE + k + 1}` for
        any nested chain and any pairwise-distinguished-at-some-scale family.
  `parity_chain_capacity_excess` — **PROVED**: the parity instantiation, at the standard
        codebook, via `parity_root_shape`.

## Honest scope — what this channel can and cannot do (E5′ finding)

This is the concentration channel's UPPER bound; it is TRUE and safe.  But the E5′ paper
round establishes that this channel is **witness-dimension bottlenecked**: for the parity
family the row family `Y` is distinguished only through the shared `v`-dimensional witness
space, so `log|Y| = O(v)` at concentration — hence `CE ≥ log|Y| − k = O(v) = O(√N)` when
`v = Θ(√N)`, NOT `Θ(N)`.  The concentration channel therefore CANNOT deliver `(2+c)N` on
its own; the two-channel dichotomy reduces `(2+c)N` to a spread-forcing (anti-alignment)
statement for minimal parity circuits, which is unresolved.  See `PROBE_PORT_FAMILY.md`
§E5′.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityLayout
open PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook
open PallLean.Paper93.DeepMath.PathB.NFrameParityStdCode

set_option maxHeartbeats 1600000 in
/-- **GENERIC EXIT-VALUE SEPARATION (proved)**: for any family with a binary root, if two
rows agree on a wire's exit values then the family agrees under any fixed outer
completion. -/
theorem exit_value_separation_of_root_shape {n : ℕ} (f : (Fin n → Bool) → Bool)
    (c : List (CGate n)) (hcomp : computes c f) (hmin : c.length = cbudget f)
    (hroot : ∃ (op : Bool → Bool → Bool) (LL RR : ℕ),
      c.getD (c.length - 1) (CGate.cst false) = CGate.bin op LL RR
      ∧ LL < c.length - 1 ∧ RR < c.length - 1 ∧ LL ≠ RR)
    (w : ℕ) (hw : w < c.length - 1)
    (x y y' : Fin n → Bool)
    (hexit : ∀ p ∈ wireExits c w,
      (runFrom y [] c).getD p false = (runFrom y' [] c).getD p false) :
    f (mixOn (varsOf c w)ᶜ x y) = f (mixOn (varsOf c w)ᶜ x y') := by
  classical
  obtain ⟨opR, LL, RR, hroot, hLlt, hRlt, hLR⟩ := hroot
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
    exact hexit p hp
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
          rw [h, hroot] at hgate
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

set_option maxHeartbeats 1600000 in
/-- **GENERIC k-SCALE CAPACITY (proved)**: any row family pairwise distinguished at some
scale of a nested chain injects into the union of exit values. -/
theorem chain_capacity_of_root_shape {n : ℕ} (f : (Fin n → Bool) → Bool)
    (c : List (CGate n)) (hcomp : computes c f) (hmin : c.length = cbudget f)
    (hroot : ∃ (op : Bool → Bool → Bool) (LL RR : ℕ),
      c.getD (c.length - 1) (CGate.cst false) = CGate.bin op LL RR
      ∧ LL < c.length - 1 ∧ RR < c.length - 1 ∧ LL ≠ RR)
    (k : ℕ) (ws : ℕ → ℕ)
    (hlt : ∀ i, i ≤ k → ws i < c.length - 1)
    (hchain : ∀ i, i < k → ws i ∈ coneOf c (ws (i + 1)))
    (Y : Finset (Fin n → Bool))
    (hdist : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → ∃ i, i ≤ k ∧ ∃ x,
      f (mixOn (varsOf c (ws i))ᶜ x y) ≠ f (mixOn (varsOf c (ws i))ᶜ x y')) :
    Y.card ≤ 2 ^ ((wireExits c (ws 0)).card
      + ∑ i ∈ Finset.range k,
          ((wireExits c (ws (i + 1))) \ (coneOf c (ws i))).card) := by
  classical
  set U : Finset ℕ := (Finset.range (k + 1)).biUnion (fun i => wireExits c (ws i))
    with hU
  set Φ : (Fin n → Bool) → (↥U → Bool) := fun y u =>
    (runFrom y [] c).getD u.val false with hΦ
  have hinj : Set.InjOn Φ ↑Y := by
    intro y hy y' hy' heq
    by_contra hne
    obtain ⟨i, hik, x, hx⟩ := hdist y (Finset.mem_coe.mp hy) y'
      (Finset.mem_coe.mp hy') hne
    apply hx
    apply exit_value_separation_of_root_shape f c hcomp hmin hroot (ws i)
      (hlt i hik) x y y'
    intro p hp
    have hpU : p ∈ U := by
      rw [hU]
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr (by omega), hp⟩
    exact congrFun heq ⟨p, hpU⟩
  have hYle : Y.card ≤ 2 ^ U.card := by
    have hmaps : ∀ y ∈ Y, Φ y ∈ (Finset.univ : Finset (↥U → Bool)) :=
      fun y _ => Finset.mem_univ _
    have hcard := Finset.card_le_card_of_injOn Φ hmaps hinj
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_coe] at hcard
    exact hcard
  have hUcard := chain_union_card c k ws hchain
  calc Y.card ≤ 2 ^ U.card := hYle
    _ ≤ 2 ^ ((wireExits c (ws 0)).card
        + ∑ i ∈ Finset.range k,
            ((wireExits c (ws (i + 1))) \ (coneOf c (ws i))).card) :=
      Nat.pow_le_pow_right (by omega) hUcard

/-- **GENERIC CHAIN CAPACITY, EXCESS FORM (proved)**: `k+1` nested scales cost
`coneExcess + k + 1` trace bits total, for any root-shaped family. -/
theorem chain_capacity_excess_of_root_shape {n : ℕ} (f : (Fin n → Bool) → Bool)
    (c : List (CGate n)) (hcomp : computes c f) (hmin : c.length = cbudget f)
    (hroot : ∃ (op : Bool → Bool → Bool) (LL RR : ℕ),
      c.getD (c.length - 1) (CGate.cst false) = CGate.bin op LL RR
      ∧ LL < c.length - 1 ∧ RR < c.length - 1 ∧ LL ≠ RR)
    (k : ℕ) (ws : ℕ → ℕ)
    (hlt : ∀ i, i ≤ k → ws i < c.length - 1)
    (hchain : ∀ i, i < k → ws i ∈ coneOf c (ws (i + 1)))
    (Y : Finset (Fin n → Bool))
    (hdist : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → ∃ i, i ≤ k ∧ ∃ x,
      f (mixOn (varsOf c (ws i))ᶜ x y) ≠ f (mixOn (varsOf c (ws i))ᶜ x y')) :
    Y.card ≤ 2 ^ (coneExcess c (c.length - 1) + (k + 1)) := by
  calc Y.card
      ≤ 2 ^ ((wireExits c (ws 0)).card
        + ∑ i ∈ Finset.range k,
            ((wireExits c (ws (i + 1))) \ (coneOf c (ws i))).card) :=
        chain_capacity_of_root_shape f c hcomp hmin hroot k ws hlt hchain Y hdist
    _ ≤ 2 ^ (coneExcess c (c.length - 1) + (k + 1)) :=
        Nat.pow_le_pow_right (by omega)
          (chain_exit_ledger f c hcomp hmin k ws hlt hchain)

/-- **THE PARITY CHAIN CAPACITY (proved)**: the concentration channel's upper bound for the
standard-codebook parity family — `|Y| ≤ 2^{coneExcess + k + 1}` over any nested chain.
Witness-dimension bottlenecked (E5′): `log|Y| = O(v)`, so this yields `CE = O(v)` at
concentration, not `Θ(N)`. -/
theorem parity_chain_capacity_excess {v m N : ℕ} (hv : 0 < v) (hm : 0 < m)
    (hfit : m * stdL v ≤ N)
    (c : List (CGate N))
    (hcomp : computes c (parityFamilyBits (stdCode v hv) hfit))
    (hmin : c.length = cbudget (parityFamilyBits (stdCode v hv) hfit))
    (k : ℕ) (ws : ℕ → ℕ)
    (hlt : ∀ i, i ≤ k → ws i < c.length - 1)
    (hchain : ∀ i, i < k → ws i ∈ coneOf c (ws (i + 1)))
    (Y : Finset (Fin N → Bool))
    (hdist : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → ∃ i, i ≤ k ∧ ∃ x,
      parityFamilyBits (stdCode v hv) hfit (mixOn (varsOf c (ws i))ᶜ x y)
        ≠ parityFamilyBits (stdCode v hv) hfit (mixOn (varsOf c (ws i))ᶜ x y')) :
    Y.card ≤ 2 ^ (coneExcess c (c.length - 1) + (k + 1)) :=
  chain_capacity_excess_of_root_shape
    (parityFamilyBits (stdCode v hv) hfit) c hcomp hmin
    (PallLean.Paper93.DeepMath.PathB.NFrameParityEssStd.parity_root_shape
      hv hm hfit c hcomp hmin) k ws hlt hchain Y hdist

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.exit_value_separation_of_root_shape
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.chain_capacity_of_root_shape
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.chain_capacity_excess_of_root_shape
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.parity_chain_capacity_excess
