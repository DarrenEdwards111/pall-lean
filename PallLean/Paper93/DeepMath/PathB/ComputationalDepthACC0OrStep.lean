import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CompositionCorrect
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0InputSmallError

/-!
# The `OR`/`AND` inductive step of the depth induction (assembled)

This assembles the `OR` layer of the Razborov–Smolensky depth induction from the pieces:

* degree composition (`…ACC0LayerCompose`: `compPoly_totalDegree_le`),
* per-point composition (`…ACC0CompositionCorrect`: `eval_compPoly_of_subgates`),
* the input-space per-gate error (`…ACC0InputSmallError`: `exists_small_errSetV`, `errSetV_eq`).

The crux is the **error containment**: the composed approximant errs at an input `x` only if *some* subgate
approximant errs at `x` **or** the gate's own boosting errs on the subgate-value vector `v(x)`:

```
errSet(compPoly P σ, OR(h))  ⊆  (⋃_i errSet(P_i, h_i))  ∪  errSetV v σ .
```

Counting (`card_union_le` + `card_biUnion_le`) gives `error ≤ k·E + |errSetV v σ|`, and `exists_small_errSetV` makes
the gate term small.  Degree composes to `≤ t·D`.  That is one `OR` layer; the `AND` layer is `¬ OR ¬` (`and_step`,
via the negation of the subgate approximants).

## What is proved (clean axioms, no `sorry`)

* `or_step` — for subgates `h_i` with degree-`≤D` error-`≤E` approximants `P_i`, there is `Q` (= `compPoly`) and an
  error budget `Eg` with `Q.totalDegree ≤ t·D`, `errCard(Q, OR(h)) ≤ k·E + Eg`, and `(2^k)^t·Eg ≤ 2^n·(2^{k-1})^t`
  (the gate error is `≤ 2^{-t}` fraction).
* `and_step` — the dual: `errCard(Q, AND(h)) ≤ k·E + Eg` with the same degree and gate-error bounds, via `OR`-duality
  on the negated subgates and `1 − ·`.

## Honest scope

This is the `OR`/`AND` inductive step over a `Fin k`-indexed family of subgates — the genuine mathematical content of
one layer.  Threading it through the `Circ` datatype (`…ACC0CircuitApprox`, the `List`-to-`Fin` packaging), iterating
to the depth-`d` bounds (`degree ≤ t^d`, `error ≤ size·2^{-t}`), and handling `MOD` (prime-power only — composite
`MOD` is the genuine open barrier) is the rest of the Beigel–Tarui/Yao front half, **Wall 1**.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md` and `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0OrStep

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0BasisBridge
open PallLean.Paper93.DeepMath.PathB.ACC0SmallErrorForm
open PallLean.Paper93.DeepMath.PathB.ACC0LayerCompose
open PallLean.Paper93.DeepMath.PathB.ACC0CompositionCorrect
open PallLean.Paper93.DeepMath.PathB.ACC0InputSmallError

variable {n k t : ℕ}

/-- The error set of a polynomial `P` against a Boolean function `f` (the inputs where they disagree). -/
noncomputable def perr (P : MvPolynomial (Fin n) (ZMod 2)) (f : (Fin n → Bool) → Bool) :
    Finset (Fin n → Bool) :=
  Finset.univ.filter (fun x => MvPolynomial.eval (fun j => boolToZMod 2 (x j)) P ≠ boolToZMod 2 (f x))

/-- **The `OR` inductive step (proved).**  Subgates `h_i` with degree-`≤D`, error-`≤E` approximants `P_i` compose to
an `OR`-gate approximant of degree `≤ t·D` and error `≤ k·E + Eg`, where the gate error budget `Eg` satisfies
`(2^k)^t · Eg ≤ 2^n · (2^{k-1})^t` (i.e. `≤ 2^{-t}` fraction). -/
theorem or_step (h : Fin k → (Fin n → Bool) → Bool) (P : Fin k → MvPolynomial (Fin n) (ZMod 2))
    (D E : ℕ) (hdeg : ∀ i, (P i).totalDegree ≤ D) (herr : ∀ i, (perr (P i) (h i)).card ≤ E) :
    ∃ (Q : MvPolynomial (Fin n) (ZMod 2)) (Eg : ℕ),
      Q.totalDegree ≤ t * D
        ∧ (perr Q (fun x => orTarget (fun i => h i x))).card ≤ k * E + Eg
        ∧ (Fintype.card (Finset (Fin k))) ^ t * Eg
            ≤ Fintype.card (Fin n → Bool) * (2 ^ (k - 1)) ^ t := by
  obtain ⟨σ, hσ⟩ := exists_small_errSetV (X := Fin n → Bool) (k := k) (t := t) (fun x i => h i x)
  refine ⟨compPoly P σ, (errSetV (fun x i => h i x) σ).card,
    compPoly_totalDegree_le P hdeg σ, ?_, hσ⟩
  -- error containment: gate error ⊆ (⋃_i subgate errors) ∪ gate-boosting error
  have hsub : perr (compPoly P σ) (fun x => orTarget (fun i => h i x))
      ⊆ (Finset.univ.biUnion (fun i => perr (P i) (h i))) ∪ errSetV (fun x i => h i x) σ := by
    intro x hx
    rw [perr, Finset.mem_filter] at hx
    rw [Finset.mem_union]
    by_contra hcon
    push_neg at hcon
    obtain ⟨hbu, herv⟩ := hcon
    have hsub_correct : ∀ i, MvPolynomial.eval (fun j => boolToZMod 2 (x j)) (P i)
        = boolToZMod 2 (h i x) := by
      intro i
      by_contra hne
      exact hbu (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
        Finset.mem_filter.mpr ⟨Finset.mem_univ x, hne⟩⟩)
    have hQ := eval_compPoly_of_subgates x P h hsub_correct σ
    rw [errSetV_eq, Finset.mem_filter, not_and] at herv
    have heq := not_not.mp (herv (Finset.mem_univ x))
    exact hx.2 (by rw [hQ, heq])
  refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _) ?_)
  have hbu : (Finset.univ.biUnion (fun i => perr (P i) (h i))).card ≤ k * E := by
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_sum (fun i _ => herr i)) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

/-- The `AND` target over a value vector. -/
def andTarget (w : Fin k → Bool) : Bool := decide (∀ j, w j = true)

/-- `AND = ¬ OR ¬` (proved): `andTarget w = !(orTarget (¬w))`. -/
theorem andTarget_eq (w : Fin k → Bool) : andTarget w = !(orTarget (fun j => !(w j))) := by
  unfold andTarget orTarget
  rw [← decide_not]
  apply decide_eq_decide.mpr
  simp only [not_exists]
  constructor
  · intro hall j
    rw [hall j]; decide
  · intro hne j
    have hj := hne j
    cases hw : w j <;> simp_all

/-- The error set is preserved under negation (proved): `perr (1 − P) (¬f) = perr P f`. -/
theorem perr_not_eq (P : MvPolynomial (Fin n) (ZMod 2)) (f : (Fin n → Bool) → Bool) :
    perr (1 - P) (fun x => !(f x)) = perr P f := by
  apply Finset.filter_congr
  intro x _
  rw [MvPolynomial.eval_sub, map_one]
  have hbn : boolToZMod 2 (!(f x)) = 1 - boolToZMod 2 (f x) := by cases f x <;> decide
  rw [hbn]
  exact (by decide : ∀ u v : ZMod 2, (1 - u ≠ 1 - v) ↔ (u ≠ v))
    (MvPolynomial.eval (fun j => boolToZMod 2 (x j)) P) (boolToZMod 2 (f x))

/-- **The `AND` inductive step (proved), via `OR`-duality.**  Same degree/error bounds as `or_step`, obtained by
applying `or_step` to the negated subgates `¬h_i` (with approximants `1 − P_i`) and negating the result. -/
theorem and_step (h : Fin k → (Fin n → Bool) → Bool) (P : Fin k → MvPolynomial (Fin n) (ZMod 2))
    (D E : ℕ) (hdeg : ∀ i, (P i).totalDegree ≤ D) (herr : ∀ i, (perr (P i) (h i)).card ≤ E) :
    ∃ (Q : MvPolynomial (Fin n) (ZMod 2)) (Eg : ℕ),
      Q.totalDegree ≤ t * D
        ∧ (perr Q (fun x => andTarget (fun i => h i x))).card ≤ k * E + Eg
        ∧ (Fintype.card (Finset (Fin k))) ^ t * Eg
            ≤ Fintype.card (Fin n → Bool) * (2 ^ (k - 1)) ^ t := by
  obtain ⟨Q', Eg, hdegQ', herrQ', hgate⟩ := or_step (t := t) (fun i x => !(h i x)) (fun i => 1 - P i) D E
    (fun i => le_trans (MvPolynomial.totalDegree_sub _ _)
      (by rw [MvPolynomial.totalDegree_one]; exact max_le (Nat.zero_le D) (hdeg i)))
    (fun i => by
      show (perr (1 - P i) (fun x => !(h i x))).card ≤ E
      rw [perr_not_eq]; exact herr i)
  refine ⟨1 - Q', Eg, ?_, ?_, hgate⟩
  · exact le_trans (MvPolynomial.totalDegree_sub _ _)
      (by rw [MvPolynomial.totalDegree_one]; exact max_le (Nat.zero_le _) hdegQ')
  · have hkey : (fun x => andTarget (fun i => h i x))
        = (fun x => !(orTarget (fun i => !(h i x)))) := by
      funext x; exact andTarget_eq (fun i => h i x)
    rw [hkey, perr_not_eq]
    exact herrQ'

end PallLean.Paper93.DeepMath.PathB.ACC0OrStep

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0OrStep.or_step
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0OrStep.and_step
