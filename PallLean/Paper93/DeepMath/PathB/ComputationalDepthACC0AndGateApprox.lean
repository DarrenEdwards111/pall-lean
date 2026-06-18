import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MultilinearBasis

/-!
# Polynomial approximation of a single AND gate — the base case of the Razborov–Smolensky method

The first rung of the `PolynomialMethodApproximation` socket (entry 264): how a single gate is represented/approximated
by a polynomial over `F`.  This file formalizes the genuinely-provable algebraic substrate — the **Fermat indicator**
and the **exact monomial representations** of AND and OR — and isolates the probabilistic low-degree boosting as the one
named open ingredient.

**The algebraic engine (Fermat).**  Over `F_p` (`p` prime), `y^{p-1} = [y ≠ 0]` (Fermat's little theorem).  This is the
indicator that the entire polynomial method is built on: it turns a *sum* of literals into a `0/1` value of degree
`p-1`, *independent of the fan-in*.

**Exact representations.**  `AND_n(x) = ∏ᵢ xᵢ` (degree `n`) and `OR_n(x) = 1 − ∏ᵢ(1 − xᵢ)` (degree `n`) hold exactly
over any field on the Boolean cube.  The AND monomial is `mlMon univ` from entry 265, so the AND indicator lies in the
degree-`≤ n` submodule `lowDegreeSubmodule n n`.

**The clause indicator (degree `p-1`, fan-in-free).**  `1 − (∑_{i∈S} xᵢ)^{p-1}` detects whether the `S`-sum vanishes
mod `p` — a degree-`p-1` polynomial regardless of `|S|`.  This is the RS building block whose *randomized boosting*
(over random subsets, to dodge mod-`p` cancellation) yields the low-degree approximation; that probabilistic step is the
open socket.

## What is proved (clean axioms, no `sorry`)

* **`fermat_indicator`** (PROVED) — `y^{p-1} = if y = 0 then 0 else 1` over `F_p` (`ZMod.pow_card_sub_one_eq_one`).
* **`andExact`** (PROVED) — `∏ᵢ (if xᵢ then 1 else 0) = if (∀ i, xᵢ) then 1 else 0`: the exact AND monomial.
* **`orExact`** (PROVED) — `1 − ∏ᵢ (1 − [xᵢ]) = if (∃ i, xᵢ) then 1 else 0`: the exact OR (De Morgan).
* **`clauseIndicator`** (PROVED) — `1 − (∑_{i∈S} [xᵢ])^{p-1} = if (∑_{i∈S} [xᵢ]) = 0 then 1 else 0`: the degree-`p-1`
  Fermat clause indicator (fan-in-free).
* **`andIndicator_eq_mlMon`** / **`andIndicator_mem_lowDegree`** (PROVED) — the AND indicator *is* the monomial
  `mlMon univ`, hence lies in `lowDegreeSubmodule n n` (entry 265): the exact (degree `n`) representation lands in the
  framework's degree-`≤ n` space.
* **`and_exact_is_zeroError_approximation`** (PROVED) — the exact representation witnesses
  `RandomizedLowDegreeApproximation F n n 0` (degree `n`, zero error): the socket is non-vacuous at `(D=n, k=0)`.

## The open ingredient (named socket)

* **`RandomizedLowDegreeApproximation F n D k`** — a degree-`≤ D` polynomial agreeing with `AND_n` on all but `≤ k`
  inputs.  The exact case is `D = n, k = 0` (proved).  The RS content — achieving `D ≪ n` with `k ≤ ε·2ⁿ` via random
  restriction + boosting of the Fermat clause indicators — is the genuine open analytic step (the single-gate base case
  of `PolynomialMethodApproximation`).  Not faked.

## Honest scope

This formalizes the algebraic substrate of the polynomial method for one gate — Fermat indicator, exact AND/OR monomials,
the degree-`p-1` clause indicator, the AND indicator's membership in the degree-`≤ n` submodule — and a proved
zero-error (degree-`n`) approximation instance.  It does **not** prove the low-degree (`D ≪ n`) probabilistic
approximation, which is the open socket.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0AndGateApprox

open PallLean.Paper93.DeepMath.PathB.ACC0MultilinearBasis (mlMon lowDegreeSubmodule)

/-! ## The Fermat indicator — the algebraic engine -/

/-- **The Fermat indicator (PROVED).**  Over `F_p` (`p` prime), `y^{p-1} = [y ≠ 0]`: `0` if `y = 0`, else `1`
(Fermat's little theorem).  The degree-`p-1` engine of the polynomial method. -/
theorem fermat_indicator {p : ℕ} [Fact p.Prime] (y : ZMod p) :
    y ^ (p - 1) = if y = 0 then 0 else 1 := by
  by_cases h : y = 0
  · subst h
    rw [if_pos rfl, zero_pow (show p - 1 ≠ 0 by have := (Fact.out : p.Prime).two_le; omega)]
  · rw [if_neg h, ZMod.pow_card_sub_one_eq_one h]

/-! ## Exact monomial representations of AND and OR -/

variable {F : Type} [Field F]

/-- **The exact AND monomial (PROVED).**  `∏ᵢ (if xᵢ then 1 else 0) = if (∀ i, xᵢ) then 1 else 0`: the AND of `n`
literals is the degree-`n` monomial. -/
theorem andExact {n : ℕ} (x : Fin n → Bool) :
    (∏ i, (if x i then (1 : F) else 0)) = if (∀ i, x i = true) then 1 else 0 := by
  by_cases h : ∀ i, x i = true
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i _
    rw [h i, if_pos rfl]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    cases hx : x i
    · rfl
    · exact absurd hx hi

/-- **The exact OR (PROVED).**  `1 − ∏ᵢ (1 − [xᵢ]) = if (∃ i, xᵢ) then 1 else 0` (De Morgan): the OR of `n` literals,
degree `n`. -/
theorem orExact {n : ℕ} (x : Fin n → Bool) :
    1 - (∏ i, (1 - (if x i then (1 : F) else 0))) = if (∃ i, x i = true) then 1 else 0 := by
  by_cases h : ∃ i, x i = true
  · rw [if_pos h]
    obtain ⟨i, hi⟩ := h
    have hz : (∏ i, (1 - (if x i then (1 : F) else 0))) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [hi, if_pos rfl, sub_self]
    rw [hz, sub_zero]
  · rw [if_neg h]
    push_neg at h
    have ho : (∏ i, (1 - (if x i then (1 : F) else 0))) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      cases hx : x i
      · rw [if_neg (by simp), sub_zero]
      · exact absurd hx (h i)
    rw [ho, sub_self]

/-! ## The Fermat clause indicator (degree `p-1`, fan-in-free) -/

/-- **The clause indicator (PROVED).**  `1 − (∑_{i∈S} [xᵢ])^{p-1} = if (∑_{i∈S} [xᵢ]) = 0 then 1 else 0`: a
degree-`p-1` polynomial (independent of `|S|`) detecting whether the `S`-sum of literals vanishes mod `p`.  The RS
building block. -/
theorem clauseIndicator {p : ℕ} [Fact p.Prime] {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    1 - (∑ i ∈ S, (if x i then (1 : ZMod p) else 0)) ^ (p - 1)
      = if (∑ i ∈ S, (if x i then (1 : ZMod p) else 0)) = 0 then 1 else 0 := by
  rw [fermat_indicator]
  by_cases h : (∑ i ∈ S, (if x i then (1 : ZMod p) else 0)) = 0
  · rw [if_pos h, if_pos h, sub_zero]
  · rw [if_neg h, if_neg h, sub_self]

/-! ## The AND indicator lands in the degree-`≤ n` submodule (entry 265) -/

/-- **The AND indicator is the monomial `mlMon univ` (PROVED).** -/
theorem andIndicator_eq_mlMon {n : ℕ} :
    (fun x : Fin n → Bool => if (∀ i, x i = true) then (1 : F) else 0)
      = mlMon (F := F) Finset.univ := by
  funext x
  simp only [mlMon]
  exact (andExact x).symm

/-- **The AND indicator lies in `lowDegreeSubmodule n n` (PROVED).**  The exact (degree-`n`) AND representation is the
monomial `mlMon univ`, a generator of the degree-`≤ n` submodule (entry 265). -/
theorem andIndicator_mem_lowDegree {n : ℕ} :
    mlMon (F := F) (Finset.univ : Finset (Fin n)) ∈ lowDegreeSubmodule (F := F) n n := by
  apply Submodule.subset_span
  exact ⟨⟨Finset.univ, by simp⟩, rfl⟩

/-! ## The randomized low-degree approximation socket -/

/-- **Randomized low-degree approximation (the open RS ingredient).**  There is a degree-`≤ D` polynomial `q` (an
element of `lowDegreeSubmodule n D`) agreeing with `AND_n` on all but `≤ k` inputs.  The exact case is `D = n, k = 0`
(`and_exact_is_zeroError_approximation`); the RS content is achieving `D ≪ n` with `k ≤ ε·2ⁿ` via random restriction +
boosting of the Fermat clause indicators — the genuine open analytic step. -/
def RandomizedLowDegreeApproximation (F : Type) [Field F] (n D k : ℕ) : Prop :=
  ∃ q ∈ lowDegreeSubmodule (F := F) n D, ∃ bad : Finset (Fin n → Bool),
    bad.card ≤ k ∧ ∀ x ∉ bad, q x = (if (∀ i, x i = true) then (1 : F) else 0)

/-- **The exact representation is a zero-error degree-`n` approximation (PROVED).**  Witnessing
`RandomizedLowDegreeApproximation F n n 0` with `q = mlMon univ` and `bad = ∅`: the socket is non-vacuous at the
exact endpoint.  The open content is shrinking `D` far below `n` at the cost of a small error budget `k`. -/
theorem and_exact_is_zeroError_approximation {n : ℕ} :
    RandomizedLowDegreeApproximation F n n 0 := by
  refine ⟨mlMon (F := F) Finset.univ, andIndicator_mem_lowDegree, ∅, by simp, ?_⟩
  intro x _
  exact congrFun (andIndicator_eq_mlMon (F := F)).symm x

/-!
**The rung.**  The algebraic substrate of the polynomial method for one gate is now proved: the Fermat indicator
(`fermat_indicator`), the exact AND/OR monomials (`andExact`, `orExact`), the degree-`p-1` clause indicator
(`clauseIndicator`), and the AND indicator's membership in the degree-`≤ n` submodule (`andIndicator_mem_lowDegree`),
with a proved zero-error degree-`n` approximation.  The remaining open step — the *low-degree* (`D ≪ n`) probabilistic
approximation `RandomizedLowDegreeApproximation F n D k` with `D` polylogarithmic and `k ≤ ε·2ⁿ`, built by random
restriction + boosting of the clause indicators — is the single-gate base case of `PolynomialMethodApproximation`, the
open Razborov–Smolensky core (entry-238 `CarryRefinementCrossing`).  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0AndGateApprox

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AndGateApprox.fermat_indicator
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AndGateApprox.andExact
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AndGateApprox.orExact
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AndGateApprox.clauseIndicator
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AndGateApprox.andIndicator_mem_lowDegree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AndGateApprox.and_exact_is_zeroError_approximation
