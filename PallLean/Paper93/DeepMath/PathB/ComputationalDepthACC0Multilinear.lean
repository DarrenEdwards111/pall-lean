import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SumCheck
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Arithmetization

/-!
# Low-degree arithmetization — the multilinear extension (proved), discharging `LowDegArithmetization`

Entry 226 (`…ACC0Arithmetization`) proved that arithmetization *computes the accepting count* (`scSum (arith) =
#accepting`) but left **`LowDegArithmetization`** — that the Boolean predicate has a *low-degree* polynomial agreeing
with it on the hypercube — as a named socket.  This file **constructs that polynomial explicitly** (the multilinear
extension) and proves both halves: it agrees with the predicate on the hypercube *and* has total degree `≤ m`.  This
discharges `LowDegArithmetization` with a concrete low-degree witness, completing the BFL arithmetization on the
sum-check side and feeding the entry-227 Schwartz–Zippel degree bound.

The construction.  For a Boolean predicate `f : (Fin m → Bool) → Bool`, the **multilinear extension** is
`mle f (x) = ∑_{a ∈ {0,1}^m} f(a) · ∏_i χ(x_i, a_i)`, where the coordinate factor `χ(x_i, a_i) = x_i` if `a_i = 1` and
`1 - x_i` if `a_i = 0`.  Each `∏_i χ(x_i, a_i)` is multilinear (degree `≤ 1` per variable, `≤ m` total), and on a
Boolean point `b` the product `∏_i χ(boolToR(b_i), a_i)` is the *equality indicator* `[a = b]`, so `mle f (boolToR ∘ b)
= f(b)` — the unique multilinear polynomial agreeing with `f` on the cube.

## What is proved (clean axioms, no `sorry`)

* **`chi` / `chiP`** — the coordinate factor as a ring value and as an `MvPolynomial` (`X i` or `1 - X i`).
* **`chi_boolToR`** (PROVED) — `chi (boolToR bi) ai = [ai = bi]` (the single-coordinate equality indicator).
* **`prod_chi_eq`** (PROVED) — `∏_i chi (boolToR (b i)) (a i) = [a = b]` (the full equality indicator).
* **`mleB_agrees`** (PROVED) — `mleB f (boolToR ∘ b) = boolToR (f b)`: the MLE agrees with `f` on the hypercube.
* **`chiP_degree`** / **`prod_chiP_degree`** / **`mleP_degree`** (PROVED, `[Nontrivial R]`) — total degree `≤ 1`, `≤ m`,
  `≤ m`: the MLE is genuinely low-degree (multilinear).
* **`mleP_eval`** (PROVED) — `eval x (mleP f) = mleB f x`: the `MvPolynomial` `mleP f` *is* the function-level MLE, so
  the *same* object is low-degree (`mleP_degree`) and agrees on the cube (`mleB_agrees`).
* **`mleP_arithmetizes`** (PROVED, `[Nontrivial R]`) — discharges entry-226 `LowDegArithmetization f (eval · (mleP f))`:
  the MLE evaluation is a low-degree arithmetization of `f`.

## Honest scope

This proves the **multilinear extension** completely: agreement with the predicate on the hypercube (`mleB_agrees`,
discharging entry-226 `LowDegArithmetization`) and total degree `≤ m` (`mleP_degree`, the genuine low-degree property
that the entry-227 Schwartz–Zippel bound consumes), tied together by `mleP_eval` (the polynomial *is* the function-level
MLE).  This is the complete, exact arithmetization of a Boolean predicate — no socket remains for the MLE itself.  What
this does *not* do: connect to the *specific* `NEXP` certificate-acceptance predicate (that the predicate `f` is the
verifier of a `NEXP` machine, with `m` polynomial in the machine's running time) — that wiring is the residual
`NexpArithmetization` content at the machine level.  This proves the multilinear extension and its degree bound, not the
machine-level certificate encoding.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset MvPolynomial

namespace PallLean.Paper93.DeepMath.PathB.ACC0Multilinear

open PallLean.Paper93.DeepMath.PathB.ACC0SumCheck (boolToR)
open PallLean.Paper93.DeepMath.PathB.ACC0Arithmetization (LowDegArithmetization)

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The coordinate factor of the multilinear extension, as a ring value: `χ(xi, ai) = xi` if `ai = true`, `1 - xi` if
`ai = false`. -/
def chi (xi : R) (ai : Bool) : R := if ai then xi else 1 - xi

/-- The coordinate factor as an `MvPolynomial`: `X i` if `ai = true`, `1 - X i` if `ai = false`. -/
noncomputable def chiP (i : Fin m) (ai : Bool) : MvPolynomial (Fin m) R :=
  if ai then X i else 1 - X i

/-- **The single-coordinate equality indicator (PROVED).**  Evaluated at a Boolean point, `chi (boolToR bi) ai` is `1`
if `ai = bi` and `0` otherwise. -/
theorem chi_boolToR (bi ai : Bool) : chi (boolToR bi) ai = (if ai = bi then (1 : R) else 0) := by
  unfold chi boolToR
  cases ai <;> cases bi <;> simp

/-- **The full equality indicator (PROVED).**  The product of coordinate factors over a Boolean point is the equality
indicator: `∏_i chi (boolToR (b i)) (a i) = [a = b]` — `1` if `a = b`, else `0` (some coordinate factor vanishes). -/
theorem prod_chi_eq (a b : Fin m → Bool) :
    ∏ i, chi (boolToR (b i)) (a i) = (if a = b then (1 : R) else 0) := by
  simp only [chi_boolToR]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- **The multilinear extension as a function** `(Fin m → R) → R`: `mleB f x = ∑_a f(a) · ∏_i χ(x_i, a_i)`. -/
def mleB (f : (Fin m → Bool) → Bool) (x : Fin m → R) : R :=
  ∑ a : Fin m → Bool, (boolToR (f a) : R) * ∏ i, chi (x i) (a i)

/-- **The multilinear extension as an `MvPolynomial`**: `mleP f = ∑_a C (f a) · ∏_i χP(i, a_i)`. -/
noncomputable def mleP (f : (Fin m → Bool) → Bool) : MvPolynomial (Fin m) R :=
  ∑ a : Fin m → Bool, C (boolToR (f a) : R) * ∏ i, chiP i (a i)

/-- **The MLE agrees with the predicate on the hypercube (PROVED).**  `mleB f (boolToR ∘ b) = boolToR (f b)`: only the
`a = b` term of the sum survives (the equality indicator `prod_chi_eq`), leaving `f(b)`. -/
theorem mleB_agrees (f : (Fin m → Bool) → Bool) (b : Fin m → Bool) :
    mleB f (fun i => boolToR (b i)) = (boolToR (f b) : R) := by
  unfold mleB
  rw [Finset.sum_eq_single b]
  · rw [prod_chi_eq]; simp
  · intro a _ hab; rw [prod_chi_eq, if_neg hab, mul_zero]
  · intro hb; exact absurd (Finset.mem_univ b) hb

/-- **Each coordinate factor is degree `≤ 1` (PROVED).**  `(chiP i ai).totalDegree ≤ 1` (it is `X i` or `1 - X i`). -/
theorem chiP_degree [Nontrivial R] (i : Fin m) (ai : Bool) :
    (chiP i ai : MvPolynomial (Fin m) R).totalDegree ≤ 1 := by
  unfold chiP
  cases ai
  · show (1 - X i : MvPolynomial (Fin m) R).totalDegree ≤ 1
    calc (1 - X i : MvPolynomial (Fin m) R).totalDegree
        ≤ max (1 : MvPolynomial (Fin m) R).totalDegree (X i : MvPolynomial (Fin m) R).totalDegree :=
          totalDegree_sub _ _
      _ ≤ 1 := by rw [totalDegree_one, totalDegree_X]; omega
  · show (X i : MvPolynomial (Fin m) R).totalDegree ≤ 1
    exact le_of_eq (totalDegree_X i)

/-- **Each monomial is degree `≤ m` (PROVED).**  `(∏_i chiP i (a i)).totalDegree ≤ m` — a product of `m` degree-`≤ 1`
factors. -/
theorem prod_chiP_degree [Nontrivial R] (a : Fin m → Bool) :
    (∏ i, chiP i (a i) : MvPolynomial (Fin m) R).totalDegree ≤ m := by
  calc (∏ i, chiP i (a i) : MvPolynomial (Fin m) R).totalDegree
      ≤ ∑ i, (chiP i (a i) : MvPolynomial (Fin m) R).totalDegree := totalDegree_finset_prod _ _
    _ ≤ ∑ _i : Fin m, 1 := Finset.sum_le_sum (fun i _ => chiP_degree i (a i))
    _ = m := by simp

/-- **The MLE is low-degree: total degree `≤ m` (PROVED).**  `(mleP f).totalDegree ≤ m` — a sum of (constant ×
degree-`≤ m`) terms.  This is the genuine multilinearity / low-degree property feeding sum-check soundness. -/
theorem mleP_degree [Nontrivial R] (f : (Fin m → Bool) → Bool) :
    (mleP f : MvPolynomial (Fin m) R).totalDegree ≤ m := by
  unfold mleP
  apply le_trans (totalDegree_finset_sum _ _)
  apply Finset.sup_le
  intro a _
  calc (C (boolToR (f a) : R) * ∏ i, chiP i (a i)).totalDegree
      ≤ (C (boolToR (f a) : R)).totalDegree
          + (∏ i, chiP i (a i) : MvPolynomial (Fin m) R).totalDegree := totalDegree_mul _ _
    _ ≤ 0 + m := by rw [totalDegree_C]; exact Nat.add_le_add_left (prod_chiP_degree a) 0
    _ = m := by simp

/-- The polynomial coordinate factor evaluates to the ring coordinate factor: `eval x (chiP i ai) = chi (x i) ai`. -/
theorem chiP_eval (x : Fin m → R) (i : Fin m) (ai : Bool) :
    eval x (chiP i ai) = chi (x i) ai := by
  unfold chiP chi
  cases ai <;> simp

/-- **The `MvPolynomial` MLE *is* the function-level MLE (PROVED).**  `eval x (mleP f) = mleB f x` — so the single
object `mleP f` is both low-degree (`mleP_degree`) and agrees with `f` on the hypercube (`mleB_agrees`). -/
theorem mleP_eval (f : (Fin m → Bool) → Bool) (x : Fin m → R) :
    eval x (mleP f) = mleB f x := by
  unfold mleP mleB
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_mul, eval_C, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact chiP_eval x i (a i)

/-- **The MLE evaluation agrees with the predicate on the hypercube (PROVED).**  `eval (boolToR ∘ b) (mleP f) =
boolToR (f b)` — combining `mleP_eval` and `mleB_agrees`. -/
theorem mleP_eval_agrees (f : (Fin m → Bool) → Bool) (b : Fin m → Bool) :
    eval (fun i => boolToR (b i)) (mleP f) = (boolToR (f b) : R) := by
  rw [mleP_eval, mleB_agrees]

/-- **Discharges entry-226 `LowDegArithmetization` (PROVED).**  The MLE evaluation `g x = eval x (mleP f)` is an
arithmetization of `f` agreeing with it on the hypercube — and (by `mleP_degree`) it is the *low-degree* one.  This
supplies the concrete low-degree polynomial the entry-226 socket required. -/
theorem mleP_arithmetizes (f : (Fin m → Bool) → Bool) :
    LowDegArithmetization f (fun x => eval x (mleP f) : (Fin m → R) → R) :=
  fun b => mleP_eval_agrees f b

end PallLean.Paper93.DeepMath.PathB.ACC0Multilinear

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Multilinear.mleB_agrees
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Multilinear.mleP_degree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Multilinear.mleP_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Multilinear.mleP_arithmetizes
