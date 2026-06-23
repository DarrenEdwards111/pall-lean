import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ExactGateDegree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3DegreeComposition

/-!
# Exact bounded-fan-in degree: `toPoly` degree `≤ w^depth`, no approximation (PROVED)

The depth assembly of the exact per-gate degree laws.  `ACC0AdditiveDegree` (AND) and `ACC0ExactGateDegree`
(OR, MOD) gave the exact per-gate degree recurrences; `Layer3.ApproxDegreeData.approxDegree_le` lifts
*unconditional* per-gate bounds across depth — but the **exact** `toPoly`'s AND/OR degree is the fan-in,
so those bounds hold only under a fan-in cap.  This file builds the **bounded-fan-in variant**: a
`FaninLe`-threaded mutual recursion giving

  `toPoly_totalDegree_le_of_faninLe` — `FaninLe w C ⇒ (toPoly p C).totalDegree ≤ w ^ depth C`,

the **exact** (no RS approximation) degree bound.  For constant depth `d` and `w = polylog`, this is
degree `polylog` exactly — hence quasipolynomial monomial support — for every bounded-fan-in ACC⁰[p]
circuit.  This is the regime where the exact-vs-quasipoly tension does **not** bite: bounded fan-in keeps
the exact polynomial low-degree.

`FaninLe w` bounds every `AND`/`OR`/`MOD` fan-in by `w` and every `MOD` modulus `q` by `w+1` (so the
`q-1` factor is `≤ w`); then every gate multiplies the degree by `≤ w`, giving `w^depth`.

## What is proved (clean axioms, no `sorry`)

* `FaninLe` — the bounded-fan-in (and bounded-`MOD`-modulus) predicate.
* `toPoly_totalDegree_le_of_faninLe` — exact `toPoly` degree `≤ w^depth` under `FaninLe w`.

## Honest scope

The **exact** quasipoly degree for **bounded fan-in**.  Unbounded fan-in is the genuine no-go
(`ACC0ExactDegreeNoGo`: exact AND/OR degree `=` fan-in); the unbounded quasipoly route needs RS
approximation (`toApprox`) or the Beigel–Tarui integer construction (open).  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ExactBoundedDegree

open scoped Classical
open MvPolynomial
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0AdditiveDegree (toPoly_andGate_totalDegree_le)
open PallLean.Paper93.DeepMath.PathB.ACC0ExactGateDegree
  (toPoly_orGate_totalDegree_le toPoly_modGate_totalDegree_le)

variable {n : ℕ}

/-- **Bounded fan-in (and bounded `MOD` modulus) predicate.**  Every `AND`/`OR`/`MOD` has fan-in `≤ w`,
and every `MOD` modulus `q ≤ w+1` (so `q-1 ≤ w`). -/
def FaninLe (w : ℕ) : BoolCircuitSyntax n → Prop
  | .const _ => True
  | .input _ => True
  | .not C => FaninLe w C
  | .andGate Cs => Cs.length ≤ w ∧ ∀ c ∈ Cs, FaninLe w c
  | .orGate Cs => Cs.length ≤ w ∧ ∀ c ∈ Cs, FaninLe w c
  | .modGate q _ Cs => q ≤ w + 1 ∧ Cs.length ≤ w ∧ ∀ c ∈ Cs, FaninLe w c

mutual

/-- **Exact bounded-fan-in degree (proved): `deg(toPoly C) ≤ w^depth` under `FaninLe w`.** -/
theorem toPoly_totalDegree_le_of_faninLe (p w : ℕ) (hw : 1 ≤ w) :
    (C : BoolCircuitSyntax n) → FaninLe w C → (toPoly p C).totalDegree ≤ w ^ C.depth
  | .const b, _ => by
      simp [toPoly, BoolCircuitSyntax.depth, totalDegree_C]
  | .input i, _ => by
      simp only [toPoly, BoolCircuitSyntax.depth, pow_zero]
      exact (isHomogeneous_X _ i).totalDegree_le
  | .not C, h => by
      simp only [FaninLe] at h
      have ih := toPoly_totalDegree_le_of_faninLe p w hw C h
      have hnd : (toPoly p (.not C)).totalDegree ≤ (toPoly p C).totalDegree := by
        show ((1 : MvPolynomial (Fin n) (ZMod p)) - toPoly p C).totalDegree ≤ _
        refine le_trans (totalDegree_sub _ _) ?_
        rw [totalDegree_one]; omega
      refine le_trans hnd (le_trans ih (Nat.pow_le_pow_right hw ?_))
      simp only [BoolCircuitSyntax.depth]; omega
  | .andGate Cs, h => by
      simp only [FaninLe] at h
      obtain ⟨hlen, hch⟩ := h
      have hbound : ∀ x ∈ Cs.map (fun c => (toPoly p c).totalDegree),
          x ≤ w ^ Cs.foldl (fun m c => max m (BoolCircuitSyntax.depth c)) 0 := by
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨c, hc, rfl⟩ := hx
        exact le_trans (toPolyList_totalDegree_le_of_faninLe p w hw Cs hch c hc)
          (Nat.pow_le_pow_right hw (le_foldl_max (fun c => BoolCircuitSyntax.depth c) Cs 0 hc))
      have hd : BoolCircuitSyntax.depth (.andGate Cs)
          = Cs.foldl (fun m c => max m (BoolCircuitSyntax.depth c)) 0 + 1 := by
        simp only [BoolCircuitSyntax.depth]
      calc (toPoly p (.andGate Cs)).totalDegree
          ≤ (Cs.map (fun c => (toPoly p c).totalDegree)).sum := toPoly_andGate_totalDegree_le p Cs
        _ ≤ (Cs.map (fun c => (toPoly p c).totalDegree)).length
              • (w ^ Cs.foldl (fun m c => max m (BoolCircuitSyntax.depth c)) 0) :=
            List.sum_le_card_nsmul _ _ hbound
        _ = Cs.length * w ^ Cs.foldl (fun m c => max m (BoolCircuitSyntax.depth c)) 0 := by
            rw [List.length_map, smul_eq_mul]
        _ ≤ w * w ^ Cs.foldl (fun m c => max m (BoolCircuitSyntax.depth c)) 0 :=
            Nat.mul_le_mul_right _ hlen
        _ = w ^ BoolCircuitSyntax.depth (.andGate Cs) := by rw [hd, pow_succ']
  | .orGate Cs, h => by
      simp only [FaninLe] at h
      obtain ⟨hlen, hch⟩ := h
      have hbound : ∀ x ∈ Cs.map (fun c => (toPoly p c).totalDegree),
          x ≤ w ^ Cs.foldl (fun m c => max m (BoolCircuitSyntax.depth c)) 0 := by
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨c, hc, rfl⟩ := hx
        exact le_trans (toPolyList_totalDegree_le_of_faninLe p w hw Cs hch c hc)
          (Nat.pow_le_pow_right hw (le_foldl_max (fun c => BoolCircuitSyntax.depth c) Cs 0 hc))
      have hd : BoolCircuitSyntax.depth (.orGate Cs)
          = Cs.foldl (fun m c => max m (BoolCircuitSyntax.depth c)) 0 + 1 := by
        simp only [BoolCircuitSyntax.depth]
      calc (toPoly p (.orGate Cs)).totalDegree
          ≤ (Cs.map (fun c => (toPoly p c).totalDegree)).sum := toPoly_orGate_totalDegree_le p Cs
        _ ≤ (Cs.map (fun c => (toPoly p c).totalDegree)).length
              • (w ^ Cs.foldl (fun m c => max m (BoolCircuitSyntax.depth c)) 0) :=
            List.sum_le_card_nsmul _ _ hbound
        _ = Cs.length * w ^ Cs.foldl (fun m c => max m (BoolCircuitSyntax.depth c)) 0 := by
            rw [List.length_map, smul_eq_mul]
        _ ≤ w * w ^ Cs.foldl (fun m c => max m (BoolCircuitSyntax.depth c)) 0 :=
            Nat.mul_le_mul_right _ hlen
        _ = w ^ BoolCircuitSyntax.depth (.orGate Cs) := by rw [hd, pow_succ']
  | .modGate q r Cs, h => by
      simp only [FaninLe] at h
      obtain ⟨hq, hlen, hch⟩ := h
      have hbound : ∀ c ∈ Cs,
          (toPoly p c).totalDegree ≤ w ^ Cs.foldl (fun m c => max m (BoolCircuitSyntax.depth c)) 0 :=
        fun c hc => le_trans (toPolyList_totalDegree_le_of_faninLe p w hw Cs hch c hc)
          (Nat.pow_le_pow_right hw (le_foldl_max (fun c => BoolCircuitSyntax.depth c) Cs 0 hc))
      have hd : BoolCircuitSyntax.depth (.modGate q r Cs)
          = Cs.foldl (fun m c => max m (BoolCircuitSyntax.depth c)) 0 + 1 := by
        simp only [BoolCircuitSyntax.depth]
      calc (toPoly p (.modGate q r Cs)).totalDegree
          ≤ (q - 1) * w ^ Cs.foldl (fun m c => max m (BoolCircuitSyntax.depth c)) 0 :=
            toPoly_modGate_totalDegree_le p q r Cs _ hbound
        _ ≤ w * w ^ Cs.foldl (fun m c => max m (BoolCircuitSyntax.depth c)) 0 :=
            Nat.mul_le_mul_right _ (by omega)
        _ = w ^ BoolCircuitSyntax.depth (.modGate q r Cs) := by rw [hd, pow_succ']

/-- List companion of `toPoly_totalDegree_le_of_faninLe`. -/
theorem toPolyList_totalDegree_le_of_faninLe (p w : ℕ) (hw : 1 ≤ w) :
    (Cs : List (BoolCircuitSyntax n)) → (∀ c ∈ Cs, FaninLe w c) →
      ∀ c ∈ Cs, (toPoly p c).totalDegree ≤ w ^ c.depth
  | [], _ => fun c hc => absurd hc (by simp)
  | c0 :: cs, h => fun c hc => by
      rcases List.mem_cons.mp hc with rfl | hmem
      · exact toPoly_totalDegree_le_of_faninLe p w hw c (h c (by simp))
      · exact toPolyList_totalDegree_le_of_faninLe p w hw cs (fun c' hc' => h c' (by simp [hc'])) c hmem

end

/-!
**Exact bounded-fan-in degree proved.**  `deg(toPoly C) ≤ w^depth C` under `FaninLe w`, no approximation
— exact polylog degree (hence quasipoly support) for bounded-fan-in constant-depth ACC⁰[p].  Unbounded
fan-in is the no-go; the unbounded quasipoly route is RS approximation or the open Beigel–Tarui integer
construction.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ExactBoundedDegree

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExactBoundedDegree.toPoly_totalDegree_le_of_faninLe
