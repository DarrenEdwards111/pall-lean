import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4CircuitReal
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Layer 3 — structural depth lift of the per-gate degree recurrence

The per-gate degree recurrence (`ComputationalDepthLayer3AC0pApprox.lean`,
`genOrApprox_totalDegree_le`) says a gate approximant over children of degree `≤ D` has degree
`≤ (p-1)·t·D` — each gate multiplies the degree by `K := (p-1)·t`.  This file performs the **structural
lift** over `BoolCircuitSyntax`: any approximant map `A` obeying that per-gate recurrence has
\[
  \deg(A\,C) \;\le\; K^{\operatorname{depth} C},
\]
the Razborov–Smolensky `((p-1)·t)^d` degree for a depth-`d` circuit (leaves degree `≤ 1`).

The statement is *abstract* in the approximant: the hypotheses (`ApproxDegreeData`) are exactly the
per-gate degree bounds, which the concrete `genOrApprox`-based approximant satisfies
(`genOrApprox_totalDegree_le`, with `K = (p-1)·t`, the `not` gate degree-preserving, and the leaves
`X i` / `C b` of degree `≤ 1`).  The engine is the `foldl`-max induction `foldl_max_pow_le`, matching
the `foldl`-max in `BoolCircuitSyntax.depth`.

No lower bound, no capstone; far below P vs NP.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer3

open MvPolynomial

/-- **`foldl`-max power bound.**  If `f c ≤ K^(g c)` pointwise on a list (and `K ≥ 1`), the running
maximum of `f` is bounded by `K` raised to the running maximum of `g`.  This matches the `foldl`-max
shape of `BoolCircuitSyntax.depth` and drives the depth lift. -/
theorem foldl_max_pow_le {α : Type*} (K : ℕ) (hK : 1 ≤ K) (f g : α → ℕ) :
    ∀ (L : List α) (a b : ℕ), a ≤ K ^ b → (∀ c ∈ L, f c ≤ K ^ g c) →
      L.foldl (fun m c => max m (f c)) a ≤ K ^ (L.foldl (fun m c => max m (g c)) b)
  | [], a, b, hab, _ => by simpa using hab
  | c :: cs, a, b, hab, hfg => by
      simp only [List.foldl_cons]
      apply foldl_max_pow_le K hK f g cs
      · exact max_le (le_trans hab (Nat.pow_le_pow_right hK (le_max_left b (g c))))
          (le_trans (hfg c (by simp)) (Nat.pow_le_pow_right hK (le_max_right b (g c))))
      · exact fun c' hc' => hfg c' (by simp [hc'])

/-- Hypotheses making an approximant map `A : BoolCircuitSyntax n → MvPolynomial (Fin n) (ZMod p)` obey
the **per-gate degree recurrence** with factor `K` (`K = (p-1)·t` for the Razborov OR/AND-approximant;
the MOD gate has degree `p-1 ≤ K`; leaves have degree `≤ 1`).  `genOrApprox_totalDegree_le` supplies the
gate bounds for the concrete approximant. -/
structure ApproxDegreeData (p n : ℕ) where
  /-- the approximant polynomial of each subcircuit -/
  A : BoolCircuitSyntax n → MvPolynomial (Fin n) (ZMod p)
  /-- the per-gate degree-multiplication factor `(p-1)·t` -/
  K : ℕ
  hK : 1 ≤ K
  hconst : ∀ b, (A (.const b)).totalDegree ≤ 1
  hinput : ∀ i, (A (.input i)).totalDegree ≤ 1
  hnot : ∀ C, (A (.not C)).totalDegree ≤ (A C).totalDegree
  hand : ∀ Cs, (A (.andGate Cs)).totalDegree
    ≤ K * Cs.foldl (fun m c => max m (A c).totalDegree) 0
  hor : ∀ Cs, (A (.orGate Cs)).totalDegree
    ≤ K * Cs.foldl (fun m c => max m (A c).totalDegree) 0
  hmod : ∀ q r Cs, (A (.modGate q r Cs)).totalDegree
    ≤ K * Cs.foldl (fun m c => max m (A c).totalDegree) 0

namespace ApproxDegreeData

variable {p n : ℕ}

mutual

/-- **The depth lift.**  Under the per-gate recurrence, `deg(A C) ≤ K^(depth C)` — the Smolensky
`((p-1)·t)^d` degree for a depth-`d` circuit. -/
theorem approxDegree_le (d : ApproxDegreeData p n) :
    (C : BoolCircuitSyntax n) → (d.A C).totalDegree ≤ d.K ^ C.depth
  | .const b => by simpa using d.hconst b
  | .input i => by simpa using d.hinput i
  | .not C => by
      refine le_trans (le_trans (d.hnot C) (approxDegree_le d C)) (Nat.pow_le_pow_right d.hK ?_)
      simp only [BoolCircuitSyntax.depth]; omega
  | .andGate Cs => by
      have hfold := foldl_max_pow_le d.K d.hK (fun c => (d.A c).totalDegree)
        (fun c => c.depth) Cs 0 0 (Nat.zero_le _) (fun c hc => approxDegreeList_le d Cs c hc)
      have hd : (BoolCircuitSyntax.andGate Cs).depth
          = Cs.foldl (fun m c => max m c.depth) 0 + 1 := by simp only [BoolCircuitSyntax.depth]
      calc (d.A (.andGate Cs)).totalDegree
          ≤ d.K * Cs.foldl (fun m c => max m (d.A c).totalDegree) 0 := d.hand Cs
        _ ≤ d.K * d.K ^ (Cs.foldl (fun m c => max m c.depth) 0) := Nat.mul_le_mul_left _ hfold
        _ = d.K ^ (BoolCircuitSyntax.andGate Cs).depth := by rw [hd, pow_succ, Nat.mul_comm]
  | .orGate Cs => by
      have hfold := foldl_max_pow_le d.K d.hK (fun c => (d.A c).totalDegree)
        (fun c => c.depth) Cs 0 0 (Nat.zero_le _) (fun c hc => approxDegreeList_le d Cs c hc)
      have hd : (BoolCircuitSyntax.orGate Cs).depth
          = Cs.foldl (fun m c => max m c.depth) 0 + 1 := by simp only [BoolCircuitSyntax.depth]
      calc (d.A (.orGate Cs)).totalDegree
          ≤ d.K * Cs.foldl (fun m c => max m (d.A c).totalDegree) 0 := d.hor Cs
        _ ≤ d.K * d.K ^ (Cs.foldl (fun m c => max m c.depth) 0) := Nat.mul_le_mul_left _ hfold
        _ = d.K ^ (BoolCircuitSyntax.orGate Cs).depth := by rw [hd, pow_succ, Nat.mul_comm]
  | .modGate q r Cs => by
      have hfold := foldl_max_pow_le d.K d.hK (fun c => (d.A c).totalDegree)
        (fun c => c.depth) Cs 0 0 (Nat.zero_le _) (fun c hc => approxDegreeList_le d Cs c hc)
      have hd : (BoolCircuitSyntax.modGate q r Cs).depth
          = Cs.foldl (fun m c => max m c.depth) 0 + 1 := by simp only [BoolCircuitSyntax.depth]
      calc (d.A (.modGate q r Cs)).totalDegree
          ≤ d.K * Cs.foldl (fun m c => max m (d.A c).totalDegree) 0 := d.hmod q r Cs
        _ ≤ d.K * d.K ^ (Cs.foldl (fun m c => max m c.depth) 0) := Nat.mul_le_mul_left _ hfold
        _ = d.K ^ (BoolCircuitSyntax.modGate q r Cs).depth := by rw [hd, pow_succ, Nat.mul_comm]

/-- List companion of `approxDegree_le` (mirrors the `toPoly`/`toPolyList` mutual recursion). -/
theorem approxDegreeList_le (d : ApproxDegreeData p n) :
    (Cs : List (BoolCircuitSyntax n)) → ∀ c ∈ Cs, (d.A c).totalDegree ≤ d.K ^ c.depth
  | [] => fun c hc => absurd hc (by simp)
  | c0 :: cs => fun c hc => by
      rcases List.mem_cons.mp hc with rfl | hmem
      · exact approxDegree_le d c
      · exact approxDegreeList_le d cs c hmem

end

end ApproxDegreeData

end PallLean.Paper93.DeepMath.PathB.Layer3

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.foldl_max_pow_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.ApproxDegreeData.approxDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.ApproxDegreeData.approxDegreeList_le
