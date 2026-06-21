import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymEvalRepack

/-!
# Brick (Fin m symEval) — the literal `Fin m → Finset` `symEval` form for AC⁰[p] (proved)

The final re-indexing: realising the count statistic `repCount` (Brick count-symEval) as the tree's literal `Fin m`
`gateCount`, giving the exact `HasExactSymAndForm` shape `eval C = symEval (monoAND ∘ mono) h` for `AC⁰[p]` circuits.

The general combinator `weightedCount_realizable` shows any coefficient-weighted sum of `AND`-indicators is the plain
`gateCount` of a `Fin m` family obtained by replicating each `AND`-gate by its weight (`m = ∑ w`).  Specialised to `reprP`,
`reprP_hasSymAndForm` produces, for an `AC⁰[p]` circuit `C` under the size budget, the literal
`∃ m mono h, eval C = symEval (monoAND ∘ mono) h ∧ m+1 < 2^n` — the `HasExactSymAndForm` object.

## What is proved (clean axioms, no `sorry`)

* **`weightedCount_realizable`** (PROVED) — `∃ m mono, m = ∑ w ∧ ∀ y, gateCount(monoAND∘mono) y = ∑ e∈S, w e · [monoAND e.support y]`.
* **`reprP_hasSymAndForm`** (PROVED) — `ModpOnly p C → (∑ … +1 < 2^n) → ∃ m mono h, eval C = symEval(monoAND∘mono) h ∧ m+1 < 2^n`.

## Honest scope

This completes the literal `Fin m` `symEval` form for `AC⁰[p]`.  It does **not** handle `MOD_q`(`q≠p`)/prime-power gates
(RS/A.3 obstruction — no clean `F_p` object), nor the Williams cash-out (`RSRep`/counting/williams/hierarchy, P≠NP-strength).
General YBT and `NEXP ⊄ ACC⁰` remain open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SymEvalFinM

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (reprP ModpOnly)
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver (gateCount symEval)
open PallLean.Paper93.DeepMath.PathB.ACC0SymEvalRepack (repCount reprP_symEval)

variable {n p : ℕ} [Fact p.Prime]

/-- **A weighted sum of `AND`-indicators is a plain `gateCount` of a replicated `Fin m` family (PROVED).** -/
theorem weightedCount_realizable (S : Finset (Fin n →₀ ℕ)) (w : (Fin n →₀ ℕ) → ℕ) :
    ∃ (m : ℕ) (mono : Fin m → Finset (Fin n)),
      m = (∑ e ∈ S, w e) ∧
      ∀ y : Fin n → Bool,
        (∑ j : Fin m, if monoAND (mono j) y then (1 : ℕ) else 0)
          = ∑ e ∈ S, w e * (if monoAND e.support y then (1 : ℕ) else 0) := by
  classical
  let Idx := (e : ↥S) × Fin (w e.val)
  let eqv : Fin (Fintype.card Idx) ≃ Idx := (Fintype.equivFin Idx).symm
  refine ⟨Fintype.card Idx, fun j => ((eqv j).1.val).support, ?_, fun y => ?_⟩
  · rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact Finset.sum_coe_sort S w
  · calc (∑ j : Fin (Fintype.card Idx), if monoAND (((eqv j).1.val).support) y then (1 : ℕ) else 0)
        = ∑ i : Idx, if monoAND ((i.1.val).support) y then (1 : ℕ) else 0 :=
          Equiv.sum_comp eqv (fun i => if monoAND ((i.1.val).support) y then (1 : ℕ) else 0)
      _ = ∑ e : ↥S, ∑ _k : Fin (w e.val), if monoAND ((e.val).support) y then (1 : ℕ) else 0 := by
            rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
      _ = ∑ e : ↥S, w e.val * (if monoAND ((e.val).support) y then (1 : ℕ) else 0) := by
            refine Finset.sum_congr rfl (fun e _ => ?_)
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ = ∑ e ∈ S, w e * (if monoAND e.support y then (1 : ℕ) else 0) :=
            Finset.sum_coe_sort S (fun e => w e * (if monoAND e.support y then (1 : ℕ) else 0))

/-- **The `HasExactSymAndForm` object for `AC⁰[p]` (PROVED): `eval C = symEval (monoAND ∘ mono) h`.** -/
theorem reprP_hasSymAndForm (C : ACC0Circuit n) (h : ModpOnly p C)
    (hbudget : (∑ e ∈ (reprP p C).support, (coeff e (reprP p C)).val) + 1 < 2 ^ n) :
    ∃ (m : ℕ) (mono : Fin m → Finset (Fin n)) (hh : ℕ → Bool),
      (ACC0CircuitModel.eval C = symEval (fun j x => monoAND (mono j) x) hh) ∧ m + 1 < 2 ^ n := by
  obtain ⟨m, mono, hm, hgc⟩ :=
    weightedCount_realizable (reprP p C).support (fun e => (coeff e (reprP p C)).val)
  have hgce : ∀ x, gateCount (fun j x => monoAND (mono j) x) x = repCount (reprP p C) x := by
    intro x
    simp only [gateCount, repCount]
    exact hgc x
  refine ⟨m, mono, fun c => decide ((c : ZMod p) = 1), ?_, by rw [hm]; exact hbudget⟩
  funext x
  simp only [symEval]
  rw [hgce x]
  exact reprP_symEval C x h

/-!
**The literal `Fin m` `symEval` form, proved.**  Every `AC⁰[p]` circuit (under the size budget) satisfies the exact
`HasExactSymAndForm` shape `eval C = symEval (monoAND ∘ mono) h` with `m+1 < 2^n` — the YBT/RS representation completed for
`AC⁰[p]` as a concrete object.  Remaining (open, not faked): `MOD_q`(`q≠p`)/prime-power gates and the Williams cash-out.  Not
a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0SymEvalFinM

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymEvalFinM.weightedCount_realizable
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymEvalFinM.reprP_hasSymAndForm
