import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ExactGateDegree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3DegreeComposition

/-!
# Exact degree `≤ w^depth` with **unbounded MOD fan-in** — the realistic ACC⁰[p] (PROVED)

A strict generalisation of `ACC0ExactBoundedDegree`.  There the exact degree bound required *every* gate
(including `MOD`) to have fan-in `≤ w`.  But a `MOD_q` gate has exact degree `q−1` (Fermat) **regardless
of fan-in** — the `MOD` case of the recursion never used the fan-in bound.  So we may **drop it**: only
`AND`/`OR` need bounded fan-in; `MOD` gates may have **unbounded** fan-in.

  `FaninLeAndOr w` — `AND`/`OR` fan-in `≤ w`, `MOD` modulus `q ≤ w+1`, but **no** bound on `MOD` fan-in.
  `toPoly_totalDegree_le_of_faninLeAndOr` — `FaninLeAndOr w C ⇒ (toPoly p C).totalDegree ≤ w ^ depth C`.

This is the realistic ACC⁰[p] model — `MOD` gates are typically unbounded fan-in.  So the exact (no RS
approximation) polylog-degree representation holds for **unbounded-MOD-fan-in, bounded-AND/OR-fan-in,
constant-depth** ACC⁰[p].

## What is proved (clean axioms, no `sorry`)

* `FaninLeAndOr` — bounded `AND`/`OR` fan-in; `MOD` fan-in unbounded.
* `toPoly_totalDegree_le_of_faninLeAndOr` — exact degree `≤ w^depth` under `FaninLeAndOr w`.

## Honest scope

Exact polylog degree for bounded-`AND`/`OR`-fan-in (unbounded `MOD` fan-in) constant-depth ACC⁰[p].
Unbounded `AND`/`OR` fan-in is the genuine no-go (`ACC0ExactDegreeNoGo`: exact `AND`/`OR` degree `=`
fan-in); the unbounded-`AND`/`OR` quasipoly route needs RS approximation or the Beigel–Tarui integer
construction (open).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ExactBoundedAndOr

open scoped Classical
open MvPolynomial
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0AdditiveDegree (toPoly_andGate_totalDegree_le)
open PallLean.Paper93.DeepMath.PathB.ACC0ExactGateDegree
  (toPoly_orGate_totalDegree_le toPoly_modGate_totalDegree_le)

variable {n : ℕ}

/-- **Bounded `AND`/`OR` fan-in; `MOD` fan-in unbounded.**  `AND`/`OR` fan-in `≤ w`; `MOD` modulus
`q ≤ w+1` (so `q-1 ≤ w`) with **no** fan-in bound. -/
def FaninLeAndOr (w : ℕ) : BoolCircuitSyntax n → Prop
  | .const _ => True
  | .input _ => True
  | .not C => FaninLeAndOr w C
  | .andGate Cs => Cs.length ≤ w ∧ ∀ c ∈ Cs, FaninLeAndOr w c
  | .orGate Cs => Cs.length ≤ w ∧ ∀ c ∈ Cs, FaninLeAndOr w c
  | .modGate q _ Cs => q ≤ w + 1 ∧ ∀ c ∈ Cs, FaninLeAndOr w c

mutual

/-- **Exact degree `≤ w^depth` with unbounded `MOD` fan-in (proved).** -/
theorem toPoly_totalDegree_le_of_faninLeAndOr (p w : ℕ) (hw : 1 ≤ w) :
    (C : BoolCircuitSyntax n) → FaninLeAndOr w C → (toPoly p C).totalDegree ≤ w ^ C.depth
  | .const b, _ => by
      simp [toPoly, BoolCircuitSyntax.depth, totalDegree_C]
  | .input i, _ => by
      simp only [toPoly, BoolCircuitSyntax.depth, pow_zero]
      exact (isHomogeneous_X _ i).totalDegree_le
  | .not C, h => by
      simp only [FaninLeAndOr] at h
      have ih := toPoly_totalDegree_le_of_faninLeAndOr p w hw C h
      have hnd : (toPoly p (.not C)).totalDegree ≤ (toPoly p C).totalDegree := by
        show ((1 : MvPolynomial (Fin n) (ZMod p)) - toPoly p C).totalDegree ≤ _
        refine le_trans (totalDegree_sub _ _) ?_
        rw [totalDegree_one]; omega
      refine le_trans hnd (le_trans ih (Nat.pow_le_pow_right hw ?_))
      simp only [BoolCircuitSyntax.depth]; omega
  | .andGate Cs, h => by
      simp only [FaninLeAndOr] at h
      obtain ⟨hlen, hch⟩ := h
      have hbound : ∀ x ∈ Cs.map (fun c => (toPoly p c).totalDegree),
          x ≤ w ^ Cs.foldl (fun m c => max m (BoolCircuitSyntax.depth c)) 0 := by
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨c, hc, rfl⟩ := hx
        exact le_trans (toPolyList_totalDegree_le_of_faninLeAndOr p w hw Cs hch c hc)
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
      simp only [FaninLeAndOr] at h
      obtain ⟨hlen, hch⟩ := h
      have hbound : ∀ x ∈ Cs.map (fun c => (toPoly p c).totalDegree),
          x ≤ w ^ Cs.foldl (fun m c => max m (BoolCircuitSyntax.depth c)) 0 := by
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨c, hc, rfl⟩ := hx
        exact le_trans (toPolyList_totalDegree_le_of_faninLeAndOr p w hw Cs hch c hc)
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
      simp only [FaninLeAndOr] at h
      obtain ⟨hq, hch⟩ := h
      have hbound : ∀ c ∈ Cs,
          (toPoly p c).totalDegree ≤ w ^ Cs.foldl (fun m c => max m (BoolCircuitSyntax.depth c)) 0 :=
        fun c hc => le_trans (toPolyList_totalDegree_le_of_faninLeAndOr p w hw Cs hch c hc)
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

/-- List companion. -/
theorem toPolyList_totalDegree_le_of_faninLeAndOr (p w : ℕ) (hw : 1 ≤ w) :
    (Cs : List (BoolCircuitSyntax n)) → (∀ c ∈ Cs, FaninLeAndOr w c) →
      ∀ c ∈ Cs, (toPoly p c).totalDegree ≤ w ^ c.depth
  | [], _ => fun c hc => absurd hc (by simp)
  | c0 :: cs, h => fun c hc => by
      rcases List.mem_cons.mp hc with rfl | hmem
      · exact toPoly_totalDegree_le_of_faninLeAndOr p w hw c (h c (by simp))
      · exact toPolyList_totalDegree_le_of_faninLeAndOr p w hw cs
          (fun c' hc' => h c' (by simp [hc'])) c hmem

end

/-!
**Exact degree with unbounded `MOD` fan-in proved.**  `deg(toPoly C) ≤ w^depth` under `FaninLeAndOr w`
(bounded `AND`/`OR`, unbounded `MOD`) — the realistic ACC⁰[p].  The `MOD` factor `q-1` is fan-in
independent (Fermat), so `MOD` gates need no fan-in cap.  Unbounded `AND`/`OR` is the no-go; unbounded
quasipoly there is RS approximation or the open Beigel–Tarui integer.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ExactBoundedAndOr

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExactBoundedAndOr.toPoly_totalDegree_le_of_faninLeAndOr
