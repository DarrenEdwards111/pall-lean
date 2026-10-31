import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameACCBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameFpDegree

/-!
# A syntactic degree bound of a polynomial skeleton over `ACCCircuit` — **SYNTACTIC DEGREE ONLY**

This file proves a *single* fact: a particular, syntactically-defined polynomial `rsPoly p C` has
`totalDegree ≤ (p-1)^{depth C}`.  It does **NOT** prove that `rsPoly p C` computes or approximates the circuit
`C`.  It is degree bookkeeping for a recursive expression — **not** a Razborov–Smolensky approximation theorem,
and it must not be read as one.  (An earlier version of this docstring over-claimed it as "the AC⁰[p]
degree/depth trade-off"; that was wrong.)

## Why it is not a semantic (`AC⁰[p]`) statement

`rsPoly` is a degree skeleton with three deliberate non-semantic simplifications:

1. **The AND clause is semantically wrong.**  It uses `1 - (Σ childᵢ)^{p-1}`, which detects whether the sum of
   the true children is `≡ 0 mod p` — not AND.  On the all-false input the sum is `0` and it returns `1`, while
   AND returns `0`.  The correct dual form is `1 - (Σ wᵢ(1 - Pᵢ))^{p-1}` (with weights) — see
   `NFrameFpANDOR.andComp` / `andComp_eval_eq`.
2. **The MOD clause ignores its modulus.**  `.mod m l` discards `m` and always emits the `MOD_p` Fermat
   detector.  For a gate labelled `MOD_m` with `m ≠ p` this polynomial has no semantic relation to the gate.  A
   real `AC⁰[p]` statement must restrict to circuits whose MOD gates all use `p` (a datatype `AC0pCircuit p` or a
   predicate `AllModulus p C`).
3. **No weights / randomness.**  Every linear form uses coefficient `1`, so even the OR clause fails on nonzero
   patterns whose Hamming weight is `≡ 0 mod p`.  The correct RS construction picks random weights and amplifies
   (`NFrameFpAmplify.or_amplified_error_bound`).

## What is actually true

`rsPoly_totalDegree_le` : `totalDegree (rsPoly p C) ≤ (p-1)^{depth C}` — a valid, machine-checked *degree*
inequality for this specific expression.  Note that `(p-1)^{depth}`, for fixed `p` and `depth`, is a
**constant** (it does not grow with the input length `n`); it is *not* "quasi-polynomial in `n`".

## The genuine theorem this is NOT yet

To turn this into a real ACC-upper result one must: define `AC0pCircuit p` (or work under `AllModulus p C`); make
`rsPoly` depend on gate-wise random / amplification seeds; use the correct complement form for AND; use the MOD
detector only when the gate modulus is exactly `p`; prove a **pointwise error** theorem (each gate correct off a
`p^{-t}` fraction); and then derive a circuit error `≤ size · p^{-t}` by a union bound.  Until that semantic
theorem exists, this file combines degree inequalities only, not correctness.

## Honest scope

Recursive degree bookkeeping for one expression.  **No** correctness, **no** approximation, **no** `AC⁰[p]`
statement, no ACC⁰ lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
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

/-- A **degree skeleton** of an `ACC⁰` circuit over `F_p`: every gate becomes one linear-power.  This is a
degree witness ONLY — it does not compute the circuit (the AND clause is semantically wrong and the MOD clause
discards its modulus; see the module docstring). -/
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

/-- **Syntactic degree bound (NOT a correctness theorem).**  The specific polynomial skeleton `rsPoly p C` has
total degree `≤ (p-1)^{depth C}`.  This bounds the degree of the *expression* only; `rsPoly` does not compute or
approximate `C` (its AND clause is semantically wrong and its MOD clause ignores the modulus — see the module
docstring).  `(p-1)^{depth}` is a constant for fixed `p`, `depth`. -/
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
