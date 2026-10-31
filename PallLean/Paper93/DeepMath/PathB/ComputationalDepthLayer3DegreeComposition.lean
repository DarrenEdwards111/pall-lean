import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4CircuitReal
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pApprox
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

/-! ## The concrete `genOrApprox`-based approximant and its `((p-1)t)^depth` degree

We now build a *concrete* approximant `toApprox` (with a per-fan-in random-form oracle `R`), wire it
through the circuit recursion (mutual with `toApproxList`, mirroring `toPoly`/`toPolyList`), and discharge
the `ApproxDegreeData` per-gate degree hypotheses — so `approxDegree_le` gives the closed bound
`deg(toApprox C) ≤ ((p-1)·t)^(depth C)`.  Each `∨`/`∧` gate uses `genOrApprox` over the children's
approximants; the `MOD` gate uses the Fermat indicator at exponent `p-1`; leaves are `X i` / `C b`.
(The form-sharing across equal-fan-in gates is a *degree-only* simplification — degree is independent of
the forms; independence for the agreement/error bound is the separate, deferred piece.) -/

section ConcreteApprox

open MvPolynomial

variable {n : ℕ}

/-- foldl-max is `≥` its initial value (max only grows). -/
theorem foldl_max_ge_init {α : Type*} (f : α → ℕ) :
    ∀ (L : List α) (a : ℕ), a ≤ L.foldl (fun m x => max m (f x)) a
  | [], a => le_refl a
  | x :: xs, a => le_trans (le_max_left a (f x)) (foldl_max_ge_init f xs (max a (f x)))

/-- Every list element's `f`-value is `≤` the running foldl-max. -/
theorem le_foldl_max {α : Type*} (f : α → ℕ) :
    ∀ (L : List α) (a : ℕ) {c : α}, c ∈ L → f c ≤ L.foldl (fun m x => max m (f x)) a
  | [], _, _, hc => absurd hc (by simp)
  | x :: xs, a, c, hc => by
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hc with rfl | hmem
      · exact le_trans (le_max_right a (f c)) (foldl_max_ge_init f xs (max a (f c)))
      · exact le_foldl_max f xs (max a (f x)) hmem

/-- The total degree of a list-sum of polynomials is bounded by any common bound on its entries. -/
theorem list_sum_totalDegree_le {p N : ℕ} (D : ℕ) :
    ∀ (l : List (MvPolynomial (Fin N) (ZMod p))), (∀ q ∈ l, q.totalDegree ≤ D) →
      l.sum.totalDegree ≤ D
  | [], _ => by simpa using Nat.zero_le D
  | q :: qs, h => by
      rw [List.sum_cons]
      refine le_trans (totalDegree_add _ _) (max_le (h q (by simp)) ?_)
      exact list_sum_totalDegree_le D qs (fun q' hq' => h q' (by simp [hq']))

/-! The concrete probabilistic approximant `toApprox`: `∨`/`∧` gates → `genOrApprox` over children;
`MOD` gate → Fermat indicator at exponent `p-1`; leaves → `X i` / `C b`. -/
mutual
noncomputable def toApprox (p t : ℕ) (R : (k : ℕ) → Fin t → Fin k → ZMod p) :
    BoolCircuitSyntax n → MvPolynomial (Fin n) (ZMod p)
  | .const b => C (boolToZMod p b)
  | .input i => X i
  | .not c => 1 - toApprox p t R c
  | .andGate cs =>
      genOrApprox p (R (toApproxList p t R cs).length) (toApproxList p t R cs).get
  | .orGate cs =>
      genOrApprox p (R (toApproxList p t R cs).length) (toApproxList p t R cs).get
  | .modGate _ r cs =>
      1 - ((toApproxList p t R cs).sum - C (r : ZMod p)) ^ (p - 1)
noncomputable def toApproxList (p t : ℕ) (R : (k : ℕ) → Fin t → Fin k → ZMod p) :
    List (BoolCircuitSyntax n) → List (MvPolynomial (Fin n) (ZMod p))
  | [] => []
  | c :: cs => toApprox p t R c :: toApproxList p t R cs
end

/-- `toApproxList` is the pointwise `map` of `toApprox`. -/
theorem toApproxList_eq_map (p t : ℕ) (R : (k : ℕ) → Fin t → Fin k → ZMod p) :
    ∀ (cs : List (BoolCircuitSyntax n)), toApproxList p t R cs = cs.map (toApprox p t R)
  | [] => by simp [toApproxList]
  | c :: cs => by simp [toApproxList, List.map_cons, toApproxList_eq_map p t R cs]

/-- Each child approximant's degree is `≤` the running foldl-max over the child list. -/
theorem toApprox_mem_le_foldl (p t : ℕ) (R : (k : ℕ) → Fin t → Fin k → ZMod p)
    (cs : List (BoolCircuitSyntax n)) {q : MvPolynomial (Fin n) (ZMod p)}
    (hq : q ∈ toApproxList p t R cs) :
    q.totalDegree ≤ cs.foldl (fun m c => max m (toApprox p t R c).totalDegree) 0 := by
  rw [toApproxList_eq_map, List.mem_map] at hq
  obtain ⟨c, hc, rfl⟩ := hq
  exact le_foldl_max (fun c => (toApprox p t R c).totalDegree) cs 0 hc

/-- **The `genOrApprox`-based approximant satisfies the per-gate degree recurrence** with factor
`K = (p-1)·t`, packaged as `ApproxDegreeData`. -/
noncomputable def toApproxData (p t : ℕ) [Fact p.Prime] (ht : 1 ≤ t)
    (R : (k : ℕ) → Fin t → Fin k → ZMod p) : ApproxDegreeData p n where
  A := toApprox p t R
  K := (p - 1) * t
  hK := by
    have h2 := (Fact.out (p := p.Prime)).two_le
    have : 1 * 1 ≤ (p - 1) * t := Nat.mul_le_mul (by omega) ht
    simpa using this
  hconst := fun b => by simp only [toApprox, totalDegree_C]; exact Nat.zero_le 1
  hinput := fun i => by simp only [toApprox, totalDegree_X]; exact le_refl 1
  hnot := fun C => by
    simp only [toApprox]
    refine le_trans (totalDegree_sub _ _) ?_
    rw [totalDegree_one, Nat.zero_max]
  hand := fun cs => by
    simp only [toApprox]
    refine le_trans (genOrApprox_totalDegree_le p _ _
      (cs.foldl (fun m c => max m (toApprox p t R c).totalDegree) 0)
      (fun j => toApprox_mem_le_foldl p t R cs (List.get_mem _ j))) ?_
    exact le_of_eq (by ring)
  hor := fun cs => by
    simp only [toApprox]
    refine le_trans (genOrApprox_totalDegree_le p _ _
      (cs.foldl (fun m c => max m (toApprox p t R c).totalDegree) 0)
      (fun j => toApprox_mem_le_foldl p t R cs (List.get_mem _ j))) ?_
    exact le_of_eq (by ring)
  hmod := fun q r cs => by
    simp only [toApprox]
    set D := cs.foldl (fun m c => max m (toApprox p t R c).totalDegree) 0 with hD
    have hsub : ((toApproxList p t R cs).sum - C (r : ZMod p)).totalDegree ≤ D := by
      refine le_trans (totalDegree_sub _ _) ?_
      rw [totalDegree_C, Nat.max_zero]
      exact list_sum_totalDegree_le D _ (fun q' hq' => toApprox_mem_le_foldl p t R cs hq')
    have h1 : (1 - ((toApproxList p t R cs).sum - C (r : ZMod p)) ^ (p - 1)).totalDegree
        ≤ (p - 1) * D := by
      refine le_trans (totalDegree_sub _ _) ?_
      rw [totalDegree_one, Nat.zero_max]
      exact le_trans (totalDegree_pow _ _) (Nat.mul_le_mul_left _ hsub)
    exact le_trans h1 (le_trans (Nat.le_mul_of_pos_right _ ht) (le_of_eq (by ring)))

/-- **Concrete `((p-1)·t)^depth` degree bound.**  The `genOrApprox`-based approximant of any circuit `C`
has total degree at most `((p-1)·t)^(depth C)` — the Razborov–Smolensky degree, now for a concrete
approximant rather than an abstract hypothesis. -/
theorem toApprox_totalDegree_le (p t : ℕ) [Fact p.Prime] (ht : 1 ≤ t)
    (R : (k : ℕ) → Fin t → Fin k → ZMod p) (C : BoolCircuitSyntax n) :
    (toApprox p t R C).totalDegree ≤ ((p - 1) * t) ^ C.depth :=
  (toApproxData p t ht R).approxDegree_le C

end ConcreteApprox

end PallLean.Paper93.DeepMath.PathB.Layer3

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.foldl_max_pow_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.ApproxDegreeData.approxDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.ApproxDegreeData.approxDegreeList_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.toApprox_totalDegree_le
