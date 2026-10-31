import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymAndForm

/-!
# Brick (count-symEval) — AC⁰[p] value as a count-based symmetric function (proved)

The count-based `symEval` repackaging of the `AC⁰[p]` `SYM∘AND` form.  Replicating each `AND`-gate `monoAND(e.support)` of
the representation by its coefficient (`(coeff e (reprP C)).val` copies), the **plain count** of accepting gates is
`repCount`, a symmetric statistic; reading it mod `p` recovers the circuit value: `eval C x = decide((repCount … : ZMod p) =
1)`.  This is exactly the count-based `symEval` shape `h(count of accepting AND-gates)` — the symmetric reader `h(c) =
decide((c : ZMod p) = 1)` over the replicated `AND`-gate family.

This converts the `F_p`-linear `SYM∘AND` form (Brick SYM∘AND form) into the count-based form: the circuit's output depends
only on *how many* of the (replicated) `AND`-gates accept, exactly as the tree's `symEval`/`HasExactSymAndForm` requires.

## What is proved (clean axioms, no `sorry`)

* **`repCount`** — the count of accepting gates in the coefficient-replicated `AND`-gate family (a `ℕ` statistic).
* **`repCount_cast`** (PROVED) — `(repCount P x : ZMod p) = eval (bv ∘ x) P`.
* **`reprP_symEval`** (PROVED) — `ModpOnly p C → ACC0Circuit.eval C x = decide((repCount (reprP p C) x : ZMod p) = 1)` —
  the circuit value as a count-based symmetric function.

## Honest scope

This is the count-based symmetric representation for `AC⁰[p]` (`repCount` = plain count of replicated `AND`-gates, read mod
`p`).  It uses `repCount` (the count statistic) rather than instantiating the tree's `Fin m → Finset` `gateCount` literally
(an equivalent re-indexing).  It does **not** handle `MOD_q`(`q≠p`)/prime-power gates (RS/A.3 obstruction) nor the Williams
cash-out.  General YBT remains open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SymEvalRepack

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitRepr (bv)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (reprP ModpOnly reprP_eval)
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)
open PallLean.Paper93.DeepMath.PathB.ACC0SymAndForm (andVal andVal_eq_bv_monoAND eval_eq_sum_andTerms)

variable {n p : ℕ} [Fact p.Prime]

/-- The count of accepting gates in the coefficient-replicated `AND`-gate family of `P`. -/
def repCount (P : MvPolynomial (Fin n) (ZMod p)) (x : Fin n → Bool) : ℕ :=
  ∑ e ∈ P.support, (coeff e P).val * (if monoAND e.support x then 1 else 0)

/-- **The replicated count, read mod `p`, is the polynomial's value (PROVED).** -/
theorem repCount_cast (P : MvPolynomial (Fin n) (ZMod p)) (x : Fin n → Bool) :
    ((repCount P x : ℕ) : ZMod p) = eval (fun i => (bv (x i) : ZMod p)) P := by
  rw [eval_eq_sum_andTerms, repCount, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [Nat.cast_mul]
  congr 1
  · exact ZMod.natCast_zmod_val _
  · rw [andVal_eq_bv_monoAND]
    cases hm : monoAND e.support x <;> simp [bv]

/-- **The `AC⁰[p]` circuit value as a count-based symmetric function (PROVED): the count-based `symEval` form.** -/
theorem reprP_symEval (C : ACC0Circuit n) (x : Fin n → Bool) (h : ModpOnly p C) :
    ACC0CircuitModel.eval C x = decide ((repCount (reprP p C) x : ZMod p) = 1) := by
  have hcast : ((repCount (reprP p C) x : ℕ) : ZMod p) = bv (ACC0CircuitModel.eval C x) := by
    rw [repCount_cast, reprP_eval C x h]
  rw [hcast]
  cases hb : ACC0CircuitModel.eval C x with
  | true => simp [bv]
  | false => simp [bv, zero_ne_one]

/-!
**The count-based symEval repackaging, proved.**  An `AC⁰[p]` circuit's output is a function of the plain count of accepting
gates in the coefficient-replicated `AND`-gate family, read mod `p` (`reprP_symEval`) — the count-based `symEval` shape.
Remaining (open, not faked): the literal `Fin m → Finset` re-indexing, `MOD_q`/prime-power gates, the Williams cash-out.
Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0SymEvalRepack

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymEvalRepack.repCount_cast
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymEvalRepack.reprP_symEval
