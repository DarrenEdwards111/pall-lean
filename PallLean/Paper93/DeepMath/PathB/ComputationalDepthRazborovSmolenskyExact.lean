import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyError

/-!
# Beigel–Tarui, rung 19: the assembled polynomial is exact for the canonical subsets (soundness)

Rungs 16–18 built the whole-circuit RS-substituted polynomial `arithApprox subsets f`, bounded its degree
(`((#subsets)(p-1))^depth`), and showed it computes `f.eval` off a union of per-gate bad sets.  This file proves the
machinery is **sound and non-vacuous**: with the *canonical* subset choice `[{0},{1}]` (the two singletons) **every gate's
bad set is empty**, so `arithApprox [{0},{1}] f` computes `f.eval` **exactly** — zero error, on every input.

  `badSet_singletons_empty` — **PROVED**: `badSet [{0},{1}] g = ∅` for every gate `g`.  For an `OR` gate the singleton
        `{i}` fires exactly when input `i` is `true`, so a `true` `OR` always fires some singleton (never all-fails);
        dually for `AND` via De Morgan.  So the "all-fail" event is impossible with the singletons present.
  `arithApprox_exact` / `eval_arithApprox_exact` — **PROVED**: `arithApproxVal [{0},{1}] f (embed∘x) = embed (f.eval x)`
        for all `x`, and the same for the polynomial `eval` — the assembled polynomial is an *exact* arithmetisation.
  `arithApprox_singletons_error_zero` — **PROVED**: the error set is `∅`.

## Honest scope — why this is soundness, not the degree win

This shows the rung 16–18 construction is correct and non-vacuous: a concrete subset choice makes the assembled
polynomial compute the formula exactly.  It is *not* the Razborov–Smolensky degree win, and here is the honest reason:
these gates are **binary** (`Fin 2`), and a 2-input gate needs no approximation — the singletons compute it exactly, at
degree `(2(p-1))^depth`, which is **not** an asymptotic improvement over rung 6's exact arithmetisation (`2^depth`).  The
genuine RS `2^{-t}` error / degree-`t(p-1)` tradeoff is a property of **unbounded fan-in** gates: for a single `OR` of
`n` variables, rung 8's `exists_low_error_orApprox` already gives a `t`-subset approximator erring on only `≤ 2^{n-t}`
inputs — that *is* the per-gate quantitative bound.  Turning that per-gate `2^{-t}` bound into a whole-circuit bound
requires unbounded-fan-in gates and a correlated-inputs analysis of how sub-circuit errors combine — the deep remaining
Beigel–Tarui content, of which this binary-gate arc (rungs 16–19) is the *exact-computation* skeleton.  The
composite-`MOD_m` case remains the proven two-fields barrier.  Nothing here is the Beigel–Tarui reduction in full,
`NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

open MvPolynomial
open scoped Classical
open PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase (BForm subforms embed)

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- **The canonical subsets kill every bad set (proved)**: with the two singletons `[{0},{1}]`, no gate ever all-fails,
so its bad set is empty.  (`OR` gate: a `true` output means some input `i` is `true`, and singleton `{i}` then fires;
`AND` gate: dually via De Morgan.) -/
theorem badSet_singletons_empty (g : BForm n) :
    badSet (p := p) [{0}, {1}] g = ∅ := by
  cases g with
  | var i => rfl
  | bnot a => rfl
  | bor a b =>
      rw [badSet, Finset.filter_eq_empty_iff]
      rintro x - ⟨hor, hall⟩
      have h0 := hall {0} (by simp)
      have h1 := hall {1} (by simp)
      simp only [Finset.sum_singleton, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      have ha : a.eval x = false := by
        by_contra h; rw [Bool.not_eq_false] at h; rw [h] at h0; simp [embed] at h0
      have hb : b.eval x = false := by
        by_contra h; rw [Bool.not_eq_false] at h; rw [h] at h1; simp [embed] at h1
      rw [ha, hb] at hor; simp at hor
  | band a b =>
      rw [badSet, Finset.filter_eq_empty_iff]
      rintro x - ⟨hand, hall⟩
      have h0 := hall {0} (by simp)
      have h1 := hall {1} (by simp)
      simp only [Finset.sum_singleton, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      have ha : a.eval x = true := by
        by_contra h; rw [Bool.not_eq_true] at h; rw [h] at h0; simp [embed] at h0
      have hb : b.eval x = true := by
        by_contra h; rw [Bool.not_eq_true] at h; rw [h] at h1; simp [embed] at h1
      rw [ha, hb] at hand; simp at hand

/-- **Exact computation (proved)**: with the canonical singletons, the assembled evaluator equals the clean embed of the
Boolean value on *every* input (the bad sets are all empty, so rung 18's correctness applies unconditionally). -/
theorem arithApprox_exact (f : BForm n) (x : Fin n → Bool) :
    arithApproxVal (p := p) [{0}, {1}] f (fun i => embed (x i)) = embed (f.eval x) :=
  arithApprox_correct [{0}, {1}] x f
    (fun g _ => by rw [badSet_singletons_empty]; exact Finset.notMem_empty x)

/-- **Exact computation, polynomial form (proved)**: the substituted **polynomial** with the canonical singletons is an
exact arithmetisation of the formula on Boolean inputs. -/
theorem eval_arithApprox_exact (f : BForm n) (x : Fin n → Bool) :
    (eval (fun i => embed (x i))) (arithApprox (p := p) [{0}, {1}] f) = embed (f.eval x) := by
  rw [eval_arithApprox]; exact arithApprox_exact f x

/-- **Zero error (proved)**: with the canonical singletons the assembled polynomial's error set is empty. -/
theorem arithApprox_singletons_error_zero (f : BForm n) :
    (Finset.univ.filter (fun x =>
        (eval (fun i => embed (x i))) (arithApprox (p := p) [{0}, {1}] f) ≠ embed (f.eval x))) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro x _
  rw [not_ne_iff]
  exact eval_arithApprox_exact f x

end PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.badSet_singletons_empty
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.eval_arithApprox_exact
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.arithApprox_singletons_error_zero
