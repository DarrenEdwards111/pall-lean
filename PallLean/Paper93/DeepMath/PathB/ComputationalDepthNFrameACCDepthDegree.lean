import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameACCBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameFpDegree

/-!
# The depth-`d` degree bound over `ACCCircuit`

The gate recurrences (`NFrameFpDegree.modp_low_degree_representation`, `NFrameFpANDOR.orComp/andComp_
totalDegree_le`) each show a single `AC⁰[p]` gate multiplies the `F_p` degree by `≤ p-1`, *independent of
fan-in*.  This file assembles them over the actual `ACCCircuit` inductive (`NFrameACCBridge`) into a single
theorem: a depth-`d` circuit has a degree-`≤ (p-1)^d` `F_p` polynomial skeleton.

`rsPoly p C` is the **Razborov–Smolensky single-form skeleton** of `C`: every gate becomes one linear-power
`(Σ children)^{p-1}`, so `rsPoly_totalDegree_le` gives `totalDegree (rsPoly p C) ≤ (p-1)^{depth C}` by induction
on the circuit.  For constant depth this is quasi-polynomial in `p`, matching the classical `AC⁰[p]`
degree/depth trade-off — the degree side of the ACC-upper bound, now over the real circuit structure.

## Honest scope

This is the **degree** side: `rsPoly` witnesses the RS degree structure and `rsPoly_totalDegree_le` bounds it by
`(p-1)^{depth}` over `ACCCircuit`.  It is not an *exact* computation of the circuit — the single-form skeleton is
only approximately correct (correctness needs the amplification/error analysis of `NFrameFpAmplify`), and it
applies to the matching prime `p` only (composite / mixed `MOD` is the wall, `NFrameCompositeMODWall`).  No ACC⁰
lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACCDepthDegree

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.NFrameACCBridge
open PallLean.Paper93.DeepMath.PathB.NFrameFpDegree

/-! ## Two combinatorial helpers -/

/-- An element's value is `≤` the running `foldr max`. -/
theorem le_foldr_max {α : Type*} (f : α → Nat) (l : List α) (x : α) (hx : x ∈ l) :
    f x ≤ (l.map f).foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp hx with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- The total degree of a list-sum is bounded by a common bound on the summands. -/
theorem totalDegree_list_sum_le {n : Nat} {p : Nat}
    (l : List (MvPolynomial (Fin n) (ZMod p))) (D : Nat) (h : ∀ q ∈ l, q.totalDegree ≤ D) :
    (l.sum).totalDegree ≤ D := by
  induction l with
  | nil => simpa using Nat.zero_le D
  | cons a t ih =>
    rw [List.sum_cons]
    exact le_trans (MvPolynomial.totalDegree_add _ _)
      (max_le (h a (by simp)) (ih (fun q hq => h q (by simp [hq]))))

/-! ## The Razborov–Smolensky degree skeleton -/

/-- The RS single-form skeleton of an `ACC⁰` circuit over `F_p`: every gate is one linear-power. -/
noncomputable def rsPoly (p : Nat) {n : Nat} : ACCCircuit n → MvPolynomial (Fin n) (ZMod p)
  | .input i => X i
  | .const b => C (if b then (1 : ZMod p) else 0)
  | .not c => 1 - rsPoly p c
  | .and l => 1 - ((l.map (rsPoly p)).sum) ^ (p - 1)
  | .or l => ((l.map (rsPoly p)).sum) ^ (p - 1)
  | .mod _ l => 1 - ((l.map (rsPoly p)).sum) ^ (p - 1)

/-- The list-sum of children skeletons has degree `≤ (p-1)^{max child depth}`. -/
theorem sum_deg_le (p : Nat) [Fact p.Prime] {n : Nat} (l : List (ACCCircuit n))
    (ih : ∀ c ∈ l, (rsPoly p c).totalDegree ≤ (p - 1) ^ ACCCircuit.depth c) :
    ((l.map (rsPoly p)).sum).totalDegree ≤ (p - 1) ^ ((l.map ACCCircuit.depth).foldr max 0) := by
  apply totalDegree_list_sum_le
  intro q hq
  rw [List.mem_map] at hq
  obtain ⟨c, hc, rfl⟩ := hq
  have h2 : 1 ≤ p - 1 := by have := (Fact.out : p.Prime).two_le; omega
  exact le_trans (ih c hc) (Nat.pow_le_pow_right h2 (le_foldr_max ACCCircuit.depth l c hc))

/-! ## The depth-`d` degree bound -/

/-- **The depth-`d` degree bound.**  Over `F_p` (`p` prime), the RS skeleton of a depth-`d` `ACC⁰` circuit has
total degree `≤ (p-1)^d` — every gate multiplies the degree by `≤ p-1`, independent of fan-in. -/
theorem rsPoly_totalDegree_le (p : Nat) [Fact p.Prime] {n : Nat} :
    ∀ C : ACCCircuit n, (rsPoly p C).totalDegree ≤ (p - 1) ^ ACCCircuit.depth C
  | .input i => by simp [rsPoly, ACCCircuit.depth, MvPolynomial.totalDegree_X]
  | .const b => by cases b <;> simp [rsPoly, ACCCircuit.depth]
  | .not c => by
      have ih := rsPoly_totalDegree_le p c
      have hp : 1 ≤ p - 1 := by have := (Fact.out : p.Prime).two_le; omega
      have hstep : (1 - rsPoly p c).totalDegree ≤ (rsPoly p c).totalDegree :=
        le_trans (MvPolynomial.totalDegree_sub _ _)
          (max_le (by rw [MvPolynomial.totalDegree_one]; exact Nat.zero_le _) le_rfl)
      show (rsPoly p (.not c)).totalDegree ≤ (p - 1) ^ ACCCircuit.depth (.not c)
      simp only [rsPoly, ACCCircuit.depth]
      exact le_trans hstep (le_trans ih (Nat.pow_le_pow_right hp (Nat.le_succ _)))
  | .and l => by
      have hs := sum_deg_le p l (fun c _ => rsPoly_totalDegree_le p c)
      simp only [rsPoly, ACCCircuit.depth]
      calc (1 - ((l.map (rsPoly p)).sum) ^ (p - 1)).totalDegree
          ≤ (((l.map (rsPoly p)).sum) ^ (p - 1)).totalDegree :=
            le_trans (MvPolynomial.totalDegree_sub _ _)
              (max_le (by rw [MvPolynomial.totalDegree_one]; exact Nat.zero_le _) le_rfl)
        _ ≤ (p - 1) * ((l.map (rsPoly p)).sum).totalDegree := MvPolynomial.totalDegree_pow _ _
        _ ≤ (p - 1) * (p - 1) ^ ((l.map ACCCircuit.depth).foldr max 0) :=
            Nat.mul_le_mul (le_refl _) hs
        _ = (p - 1) ^ ((l.map ACCCircuit.depth).foldr max 0 + 1) := by rw [pow_succ]; ring
  | .or l => by
      have hs := sum_deg_le p l (fun c _ => rsPoly_totalDegree_le p c)
      simp only [rsPoly, ACCCircuit.depth]
      calc (((l.map (rsPoly p)).sum) ^ (p - 1)).totalDegree
          ≤ (p - 1) * ((l.map (rsPoly p)).sum).totalDegree := MvPolynomial.totalDegree_pow _ _
        _ ≤ (p - 1) * (p - 1) ^ ((l.map ACCCircuit.depth).foldr max 0) :=
            Nat.mul_le_mul (le_refl _) hs
        _ = (p - 1) ^ ((l.map ACCCircuit.depth).foldr max 0 + 1) := by rw [pow_succ]; ring
  | .mod m l => by
      have hs := sum_deg_le p l (fun c _ => rsPoly_totalDegree_le p c)
      simp only [rsPoly, ACCCircuit.depth]
      calc (1 - ((l.map (rsPoly p)).sum) ^ (p - 1)).totalDegree
          ≤ (((l.map (rsPoly p)).sum) ^ (p - 1)).totalDegree :=
            le_trans (MvPolynomial.totalDegree_sub _ _)
              (max_le (by rw [MvPolynomial.totalDegree_one]; exact Nat.zero_le _) le_rfl)
        _ ≤ (p - 1) * ((l.map (rsPoly p)).sum).totalDegree := MvPolynomial.totalDegree_pow _ _
        _ ≤ (p - 1) * (p - 1) ^ ((l.map ACCCircuit.depth).foldr max 0) :=
            Nat.mul_le_mul (le_refl _) hs
        _ = (p - 1) ^ ((l.map ACCCircuit.depth).foldr max 0 + 1) := by rw [pow_succ]; ring
  termination_by C => sizeOf C
  decreasing_by
    all_goals simp_wf
    all_goals (first | omega | (rename_i hc; have := List.sizeOf_lt_of_mem hc; omega))

end PallLean.Paper93.DeepMath.PathB.NFrameACCDepthDegree

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACCDepthDegree.rsPoly_totalDegree_le
