import Mathlib

/-!
# Hard math (Beigel–Tarui, gate-degree rung) — Boolean gates are low-degree (proved)

The genuinely open content of the Beigel–Tarui `SYM∘AND` size bound is the *degree* of the gate polynomials: the corpus's
`compositeBT_representation` derives the quasipolynomial monomial count from `hgu`/`hgb` — the hypotheses that the unary and
binary gate polynomials have total degree `≤ δ`.  This brick discharges that residual content for the **Boolean gates**: every
unary Boolean function has an exact multilinear polynomial of total degree `≤ 1`, and every binary Boolean function one of
total degree `≤ 2` (`gateUnary_degree`, `gateBinary_degree`), and these polynomials are *eval-correct* — they agree with the
gate on Boolean inputs (`gateUnary_eval`, `gateBinary_eval`).

So the `δ = 2` gate-degree input to Beigel–Tarui is genuinely established for all `AND/OR/NOT`-style (binary) gates.  The
remaining high-degree content is the `MOD_m` gate (the Toda low-degree polynomial / probabilistic-polynomial construction),
the genuinely hard combinatorics — classical, known, **not** P≠NP-strength.

## What is proved (clean axioms, no `sorry`)

* **`gateUnary`** / **`gateBinary`** — the exact multilinear interpolation of any unary/binary Boolean function.
* **`gateUnary_degree`** (PROVED) — `totalDegree (gateUnary f) ≤ 1`.
* **`gateBinary_degree`** (PROVED) — `totalDegree (gateBinary g) ≤ 2`.
* **`gateUnary_eval`** / **`gateBinary_eval`** (PROVED) — eval-correctness on Boolean inputs.

## Honest scope

This is the Boolean-gate degree rung of Beigel–Tarui (the `δ = 2` input for `compositeBT_representation`).  The `MOD_m`
gate's polylog degree (the hard Toda part) and the unconditional `NEXP ⊄ ACC⁰` (P≠NP-strength) are **not** done here.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0GatePolyDegree

open MvPolynomial

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- The Boolean value `0/1` in `R`. -/
def bval (b : Bool) : R := if b then 1 else 0

/-- The 1-variable selector: `chiU true = X₀`, `chiU false = 1 − X₀`. -/
noncomputable def chiU (b : Bool) : MvPolynomial (Fin 1) R := if b then X 0 else 1 - X 0

/-- The 2-variable selector on coordinate `i`. -/
noncomputable def chiB (b : Bool) (i : Fin 2) : MvPolynomial (Fin 2) R := if b then X i else 1 - X i

theorem chiU_degree (b : Bool) : (chiU b : MvPolynomial (Fin 1) R).totalDegree ≤ 1 := by
  rw [chiU]; split
  · simp [totalDegree_X]
  · refine le_trans (totalDegree_sub _ _) ?_; simp [totalDegree_one, totalDegree_X]

theorem chiB_degree (b : Bool) (i : Fin 2) : (chiB b i : MvPolynomial (Fin 2) R).totalDegree ≤ 1 := by
  rw [chiB]; split
  · simp [totalDegree_X]
  · refine le_trans (totalDegree_sub _ _) ?_; simp [totalDegree_one, totalDegree_X]

/-- The exact multilinear polynomial of a unary Boolean function. -/
noncomputable def gateUnary (f : Bool → Bool) : MvPolynomial (Fin 1) R :=
  C (bval (f false)) * chiU false + C (bval (f true)) * chiU true

/-- The exact multilinear polynomial of a binary Boolean function. -/
noncomputable def gateBinary (g : Bool → Bool → Bool) : MvPolynomial (Fin 2) R :=
  C (bval (g false false)) * (chiB false 0 * chiB false 1)
    + C (bval (g false true)) * (chiB false 0 * chiB true 1)
    + C (bval (g true false)) * (chiB true 0 * chiB false 1)
    + C (bval (g true true)) * (chiB true 0 * chiB true 1)

/-- **Every unary Boolean gate polynomial has total degree `≤ 1` (PROVED).** -/
theorem gateUnary_degree (f : Bool → Bool) : (gateUnary f : MvPolynomial (Fin 1) R).totalDegree ≤ 1 := by
  refine le_trans (totalDegree_add _ _) (max_le ?_ ?_) <;>
    · refine le_trans (totalDegree_mul _ _) ?_
      refine le_trans (add_le_add (totalDegree_C _).le (chiU_degree _)) ?_
      simp

/-- **Every binary Boolean gate polynomial has total degree `≤ 2` (PROVED).** -/
theorem gateBinary_degree (g : Bool → Bool → Bool) :
    (gateBinary g : MvPolynomial (Fin 2) R).totalDegree ≤ 2 := by
  have hterm : ∀ (b0 b1 : Bool) (c : R),
      (C c * (chiB b0 0 * chiB b1 1) : MvPolynomial (Fin 2) R).totalDegree ≤ 2 := by
    intro b0 b1 c
    refine le_trans (totalDegree_mul _ _) ?_
    refine le_trans (add_le_add (totalDegree_C _).le (totalDegree_mul _ _)) ?_
    have := chiB_degree (R := R) b0 0
    have := chiB_degree (R := R) b1 1
    omega
  unfold gateBinary
  refine le_trans (totalDegree_add _ _) (max_le ?_ (hterm _ _ _))
  refine le_trans (totalDegree_add _ _) (max_le ?_ (hterm _ _ _))
  refine le_trans (totalDegree_add _ _) (max_le (hterm _ _ _) (hterm _ _ _))

omit [Nontrivial R] in
/-- **The unary gate polynomial is eval-correct on Boolean inputs (PROVED).** -/
theorem gateUnary_eval (f : Bool → Bool) (b : Bool) :
    eval (fun _ => (bval b : R)) (gateUnary f) = bval (f b) := by
  simp only [gateUnary, chiU, bval, map_add, map_mul, eval_C, map_sub, map_one, eval_X]
  cases b <;> simp

omit [Nontrivial R] in
/-- **The binary gate polynomial is eval-correct on Boolean inputs (PROVED).** -/
theorem gateBinary_eval (g : Bool → Bool → Bool) (b0 b1 : Bool) :
    eval (fun i => (bval (if i = 0 then b0 else b1) : R)) (gateBinary g) = bval (g b0 b1) := by
  simp only [gateBinary, chiB, bval, map_add, map_mul, eval_C, map_sub, map_one, eval_X]
  cases b0 <;> cases b1 <;> simp

/-!
**Boolean gates are low-degree, proved.**  The unary/binary Boolean gate polynomials are degree `≤ 1`/`≤ 2` and eval-correct —
the `δ = 2` gate-degree input to Beigel–Tarui (`compositeBT_representation`'s `hgu`/`hgb`).  Remaining (open, not faked): the
`MOD_m` gate's polylog degree (the Toda construction) and the unconditional `NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0GatePolyDegree

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GatePolyDegree.gateBinary_degree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GatePolyDegree.gateBinary_eval
