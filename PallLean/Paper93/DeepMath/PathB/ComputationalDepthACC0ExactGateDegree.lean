import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0AdditiveDegree

/-!
# Exact per-gate degree laws for `OR` and `MOD` (PROVED)

`ACC0AdditiveDegree` proved the **exact** `AND`-gate degree law (`toPoly_andGate_totalDegree_le`:
`AND` degree `≤ ∑` child degrees).  This file completes the per-gate exact degree laws for the other two
unbounded gate types of `toPoly` — **no approximation**:

  `toPoly_orGate_totalDegree_le` — `OR` degree `≤ ∑` child degrees (De Morgan: `1 − ∏(1 − qᵢ)`).
  `toPoly_modGate_totalDegree_le` — `MOD_q` degree `≤ (q−1)·D` when all children have degree `≤ D`
  (Fermat form `1 − (∑ qᵢ − r)^{q−1}`): the `MOD` gate multiplies degree by only `q−1`, **independent of
  fan-in** — the key fact distinguishing ACC⁰ from AC⁰.

Together with the `AND` law these are the exact per-gate degree recurrences.  For **bounded fan-in** they
give the exact (not RS-approximate) polylog degree across constant depth — the regime where the
exact-vs-quasipoly tension does not bite.  The full depth-assembled bounded-fan-in bound (a bounded-fan-in
variant of `Layer3.ApproxDegreeData.approxDegree_le`) is the next step and is **not** built here.

## What is proved (clean axioms, no `sorry`)

* `list_sum_totalDegree_le_of` — list-sum degree `≤ D` when each summand has degree `≤ D`.
* `toPoly_orGate_totalDegree_le` — exact `OR`-gate degree `≤ ∑` child degrees.
* `toPoly_modGate_totalDegree_le` — exact `MOD`-gate degree `≤ (q−1)·D`, fan-in-independent factor.

## Honest scope

Per-gate exact degree laws only.  `MOD` is exact + degree `q−1` regardless of fan-in (Fermat); `AND`/`OR`
have exact degree `= fan-in` (so unbounded fan-in is the no-go, `ACC0ExactDegreeNoGo`).  The full
bounded-fan-in depth assembly, and the unbounded quasipoly route (Beigel–Tarui integer), are not here.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ExactGateDegree

open scoped Classical
open MvPolynomial
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0AdditiveDegree (toPolyList_eq_map)

variable {n : ℕ}

/-- **A list sum's degree is `≤ D` when every summand has degree `≤ D` (proved).** -/
theorem list_sum_totalDegree_le_of {p : ℕ} (L : List (MvPolynomial (Fin n) (ZMod p))) (D : ℕ)
    (h : ∀ q ∈ L, q.totalDegree ≤ D) : L.sum.totalDegree ≤ D := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.sum_cons]
    exact le_trans (totalDegree_add _ _)
      (max_le (h a (by simp)) (ih (fun q hq => h q (by simp [hq]))))

/-- **Exact `OR`-gate degree law (proved): `≤ ∑` child degrees.** -/
theorem toPoly_orGate_totalDegree_le (p : ℕ) (cs : List (BoolCircuitSyntax n)) :
    (toPoly p (BoolCircuitSyntax.orGate cs)).totalDegree
      ≤ (cs.map (fun c => (toPoly p c).totalDegree)).sum := by
  show ((1 : MvPolynomial (Fin n) (ZMod p))
      - ((toPolyList p cs).map (fun q => 1 - q)).prod).totalDegree ≤ _
  refine le_trans (totalDegree_sub _ _) (max_le (by rw [totalDegree_one]; exact Nat.zero_le _) ?_)
  refine le_trans (totalDegree_list_prod _) ?_
  rw [toPolyList_eq_map, List.map_map, List.map_map]
  refine List.sum_le_sum (fun c _ => ?_)
  refine le_trans (totalDegree_sub _ _) ?_
  rw [totalDegree_one]; omega

/-- **Exact `MOD`-gate degree law (proved): `≤ (q−1)·D` for children of degree `≤ D`.**  The factor
`q−1` is independent of fan-in (Fermat). -/
theorem toPoly_modGate_totalDegree_le (p q r : ℕ) (cs : List (BoolCircuitSyntax n)) (D : ℕ)
    (h : ∀ c ∈ cs, (toPoly p c).totalDegree ≤ D) :
    (toPoly p (BoolCircuitSyntax.modGate q r cs)).totalDegree ≤ (q - 1) * D := by
  show ((1 : MvPolynomial (Fin n) (ZMod p))
      - ((toPolyList p cs).sum - C ((r : ZMod p))) ^ (q - 1)).totalDegree ≤ _
  refine le_trans (totalDegree_sub _ _) (max_le (by rw [totalDegree_one]; exact Nat.zero_le _) ?_)
  refine le_trans (totalDegree_pow _ _) (Nat.mul_le_mul_left _ ?_)
  refine le_trans (totalDegree_sub _ _)
    (max_le ?_ (by rw [totalDegree_C]; exact Nat.zero_le _))
  rw [toPolyList_eq_map]
  exact list_sum_totalDegree_le_of _ D
    (fun s hs => by simp only [List.mem_map] at hs; obtain ⟨c, hc, rfl⟩ := hs; exact h c hc)

/-!
**Per-gate exact degree laws proved.**  With the existing `AND` law, the exact per-gate degree
recurrences are complete: `AND`/`OR` multiply degree by the fan-in; `MOD` by only `q−1` (fan-in
independent, Fermat).  The full bounded-fan-in depth-assembled bound and the unbounded quasipoly
(Beigel–Tarui integer) route are the remaining steps, not here.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ExactGateDegree

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExactGateDegree.toPoly_orGate_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExactGateDegree.toPoly_modGate_totalDegree_le
