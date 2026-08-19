import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingFixedTermLinearGap

/-!
# Simultaneous fixed-size circuit switching gap

This file composes the corrected bounded-term theorem across a finite bottom layer.  The bad event
is the actual union of the genuine canonical-depth bad sets of all gates.  Thus a restriction outside
it semantically collapses every gate at once, while every restriction inside it remains fully charged.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCircuitLinearGap

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermFamily
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingFixedTermLinearGap
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellBuckets
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellAveraging
open PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting

/-- The genuine circuit bad set: at least one bottom DNF has canonical depth at least `threshold`. -/
def circuitBad {n G : ℕ} (gates : Fin G → List (Clause n)) (K threshold : ℕ) :
    Finset (Restriction n) :=
  Finset.univ.biUnion fun g => boundedTermBad (gates g) K threshold

theorem mem_circuitBad_iff {n G : ℕ} (gates : Fin G → List (Clause n))
    (K threshold : ℕ) (ρ : Restriction n) :
    ρ ∈ circuitBad gates K threshold ↔ ∃ g, ρ ∈ boundedTermBad (gates g) K threshold := by
  simp [circuitBad]

theorem circuitBad_stars {n G : ℕ} (gates : Fin G → List (Clause n))
    (K threshold : ℕ) (ρ : Restriction n) (hρ : ρ ∈ circuitBad gates K threshold) :
    SwitchingCounting.stars ρ = K := by
  obtain ⟨g, hg⟩ := (mem_circuitBad_iff gates K threshold ρ).mp hρ
  exact (mem_boundedTermBad_iff (gates g) K threshold ρ).mp hg |>.1

/-- Outside the union bad set, every bottom gate simultaneously has the sound shallow-CNF collapse. -/
theorem circuit_good_semanticCollapse {n G : ℕ} (gates : Fin G → List (Clause n))
    (K threshold : ℕ) (ρ : Restriction n) (hstars : SwitchingCounting.stars ρ = K)
    (hgood : ρ ∉ circuitBad gates K threshold) :
    ∀ g,
      (∀ x, DTree.agreeRestriction ρ x →
          cnfValue (dtreeToCNF (toDTree (canonicalDT (gates g) K ρ))) x =
            DTree.dnfValue (gates g) x) ∧
      (∀ C ∈ dtreeToCNF (toDTree (canonicalDT (gates g) K ρ)),
          C.lits.length < threshold) := by
  intro g
  apply boundedTerm_good_semanticCollapse (gates g) K threshold ρ hstars
  intro hg
  exact hgood ((mem_circuitBad_iff gates K threshold ρ).mpr ⟨g, hg⟩)

/-- Union bound for the actual simultaneous canonical-depth bad event. -/
theorem circuitBad_card_le_shellSum {n G w m : ℕ} [NeZero w] [NeZero m]
    (gates : Fin G → List (Clause n)) (K threshold : ℕ)
    (hw : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ w)
    (hm : ∀ g, (gates g).length ≤ m) :
    (circuitBad gates K threshold).card ≤
      G * (∑ t ∈ Finset.Icc threshold K,
        n.choose (K - t) * 2 ^ (n - (K - t)) * (2 * w * m) ^ t) := by
  classical
  calc
    (circuitBad gates K threshold).card
        ≤ ∑ g : Fin G, (boundedTermBad (gates g) K threshold).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ _g : Fin G, (∑ t ∈ Finset.Icc threshold K,
          n.choose (K - t) * 2 ^ (n - (K - t)) * (2 * w * m) ^ t) :=
      Finset.sum_le_sum fun g _ => boundedTermBad_card_le_shellSum (gates g) K threshold (hw g) (hm g)
    _ = G * (∑ t ∈ Finset.Icc threshold K,
          n.choose (K - t) * 2 ^ (n - (K - t)) * (2 * w * m) ^ t) := by simp

/-- The gate union factor is absorbed by scaling the ambient density by `G`. -/
theorem circuit_shellBudget (G m r : ℕ) (hG : 0 < G) (hm : 0 < m) (hr : 0 < r) :
    G * (∑ t ∈ Finset.Icc (10 * r) (20 * r),
        (1000 * (G * m) * r).choose (20 * r - t) *
          2 ^ (1000 * (G * m) * r - (20 * r - t)) * (2 * 2 * m) ^ t)
        * 2 ^ (9 * r + 1)
      ≤ (1000 * (G * m) * r).choose (20 * r) *
          2 ^ (1000 * (G * m) * r - 20 * r) := by
  have hdom :
      G * (∑ t ∈ Finset.Icc (10 * r) (20 * r),
        (1000 * (G * m) * r).choose (20 * r - t) *
          2 ^ (1000 * (G * m) * r - (20 * r - t)) * (4 * m) ^ t)
      ≤ ∑ t ∈ Finset.Icc (10 * r) (20 * r),
        (1000 * (G * m) * r).choose (20 * r - t) *
          2 ^ (1000 * (G * m) * r - (20 * r - t)) * (4 * (G * m)) ^ t := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    have ht1 : 1 ≤ t := by
      have := (Finset.mem_Icc.mp ht).1
      omega
    have hpow : G * (4 * m) ^ t ≤ (4 * (G * m)) ^ t := by
      calc
        G * (4 * m) ^ t ≤ G ^ t * (4 * m) ^ t := by
          gcongr
          exact Nat.le_pow (by omega)
        _ = (4 * (G * m)) ^ t := by rw [← mul_pow]; congr 1; ring
    let A := (1000 * (G * m) * r).choose (20 * r - t) *
      2 ^ (1000 * (G * m) * r - (20 * r - t))
    calc
      G * (A * (4 * m) ^ t) = A * (G * (4 * m) ^ t) := by ring
      _ ≤ A * (4 * (G * m)) ^ t := Nat.mul_le_mul_left A hpow
  calc
    G * (∑ t ∈ Finset.Icc (10 * r) (20 * r),
        (1000 * (G * m) * r).choose (20 * r - t) *
          2 ^ (1000 * (G * m) * r - (20 * r - t)) * (2 * 2 * m) ^ t)
        * 2 ^ (9 * r + 1)
      ≤ (∑ t ∈ Finset.Icc (10 * r) (20 * r),
        (1000 * (G * m) * r).choose (20 * r - t) *
          2 ^ (1000 * (G * m) * r - (20 * r - t)) * (2 * 2 * (G * m)) ^ t)
          * 2 ^ (9 * r + 1) := by
            rw [show 2 * 2 * m = 4 * m by ring,
              show 2 * 2 * (G * m) = 4 * (G * m) by ring]
            exact Nat.mul_le_mul_right _ hdom
    _ ≤ (1000 * (G * m) * r).choose (20 * r) *
          2 ^ (1000 * (G * m) * r - 20 * r) :=
      fixedTermLinearGap_shellBudget (G * m) r (Nat.mul_pos hG hm) hr

/-- **Circuit-level composition.** One deterministic free-coordinate bucket simultaneously handles
all `G` bottom DNFs, retains every exceptional restriction, and has a linear exponent gap. -/
theorem circuitLinearGap_selectedBucket_activeGap
    (G m r : ℕ) [NeZero G] [NeZero m] [NeZero r]
    (gates : Fin G → List (Clause (1000 * (G * m) * r)))
    (hw : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ 2)
    (hm : ∀ g, (gates g).length ≤ m) :
    ∃ i : Fin ((1000 * (G * m) * r).choose (20 * r)),
      goodBadWork (1000 * (G * m) * r) (1000 * (G * m) * r - 20 * r)
        (2 ^ (1000 * (G * m) * r - 20 * r))
        (concreteBadCount (K := 20 * r) (circuitBad gates (20 * r) (10 * r)) i)
        (10 * r - 1) ≤ 2 ^ (1000 * (G * m) * r - 9 * r) := by
  let n := 1000 * (G * m) * r
  have hG := NeZero.pos G
  have hmpos := NeZero.pos m
  have hr := NeZero.pos r
  have hGm : 0 < G * m := Nat.mul_pos hG hmpos
  have hcoef20 : 20 ≤ 1000 * (G * m) := by nlinarith
  have hcoef30 : 30 ≤ 1000 * (G * m) := by nlinarith
  have hKn : 20 * r ≤ n := by
    dsimp [n]
    exact Nat.mul_le_mul_right r hcoef20
  have hsaveK : 9 * r + 1 + 20 * r ≤ n := by
    dsimp [n]
    calc
      9 * r + 1 + 20 * r ≤ 30 * r := by omega
      _ ≤ (1000 * (G * m)) * r := Nat.mul_le_mul_right r hcoef30
  have hsN : 9 * r + 1 ≤ n := by omega
  have hstars : ∀ ρ ∈ circuitBad gates (20 * r) (10 * r),
      SwitchingCounting.stars ρ = 20 * r :=
    fun ρ hρ => circuitBad_stars gates (20 * r) (10 * r) ρ hρ
  have hcard := circuitBad_card_le_shellSum gates (20 * r) (10 * r) hw hm
  have htail : (circuitBad gates (20 * r) (10 * r)).card * 2 ^ (9 * r + 1)
      ≤ n.choose (20 * r) * 2 ^ (n - 20 * r) := by
    apply le_trans (Nat.mul_le_mul_right _ hcard)
    simpa [n] using circuit_shellBudget G m r hG hmpos hr
  have hsum := sum_concreteBadCount (Bad := circuitBad gates (20 * r) (10 * r)) hstars
  apply aggregateTail_to_selectedBucket_activeGap n (n.choose (20 * r))
    (n - 20 * r) (9 * r) (10 * r - 1)
  · exact Nat.choose_pos hKn
  · omega
  · exact Nat.sub_le n (20 * r)
  · exact hsN
  · rw [hsum]
    exact htail
  · have hwork {N R : ℕ} (hR : 0 < R) (h : 20 * R ≤ N) :
        (N - 20 * R) + (10 * R - 1) ≤ N - 9 * R - 1 := by omega
    exact hwork hr hKn

end PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCircuitLinearGap

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCircuitLinearGap.circuit_good_semanticCollapse
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCircuitLinearGap.circuit_shellBudget
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCircuitLinearGap.circuitLinearGap_selectedBucket_activeGap
