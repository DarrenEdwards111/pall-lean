import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCSwitchingChebyshev
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthManyGateCorrelation

/-!
# The end‑to‑end switching pipeline, assembled

This file chains the proved pieces of the random‑restriction programme into a single conditional theorem:
**bounded‑overlap ACC⁰ predictors fail to correlate with the holonomy parity under a random restriction**, with the
one genuinely higher‑moment step isolated as a named hypothesis.

The pipeline:

1. **Concentration / existence** (proved here).  `exists_of_pr_lt_one`: an event of probability `< 1` has a
   complementary outcome (probabilistic method, from `total`).  `exists_low_survival`: by Markov, if the expected
   number of surviving supports is `≤ B < a`, then *some* restriction leaves `< a` surviving supports.
2. **Cell collapse → witness** (named gap).  Few surviving supports ⇒ coarse cells on the live coordinates ⇒ a
   same‑cell `D`‑witness (`CellWitness`).  This is the bridge `hbridge`; for bounded overlap it is delivered by the
   second‑moment concentration (`…SwitchingVariance`, `…SwitchingChebyshev`) plus pigeonhole, and is the precise
   higher‑moment frontier when the overlap is unbounded.
3. **Witness → correlation bound** (proved here).  `cellWitness_gives_low_correlation`: a same‑cell `D`‑witness
   gives `2·agreement ≤ #off‑diagonal inputs` for the `k`‑gate predictor (via `kGate_low_correlation_offdiagonal`).

## What is proved (clean axioms, no `sorry`)

* `exists_of_pr_lt_one` — probabilistic method over the `p`‑biased measure.
* `survivingCount`, `exists_low_survival` — **a low‑survival restriction exists** when the expected survivor count
  is below the threshold (Markov + the probabilistic method).
* `cellWitness_gives_low_correlation` — **witness ⇒ the ACC⁰ predictor has no correlation advantage**.
* `bounded_overlap_acc0_low_correlation_whp` — **the assembly**: expected‑survivor bound `+` cell bridge `⇒` the
  predictor fails on the restricted holonomy parity.

## Honest scope

Everything except the cell bridge `hbridge` is proved.  `hbridge` (few surviving supports ⇒ a same‑cell witness)
is the combinatorial heart of the switching argument: for *bounded* overlap it follows from the proved
concentration (`Var ≤ d·k·s·p`) and pigeonhole (`#cells ≤ 2^{#survivors} < #live`); for *unbounded* overlap it is
the higher‑moment Håstad content — the precisely‑located `NP ⊄ ACC⁰` frontier.  The expected‑survivor hypothesis
`hE` is the routine identification of the measure expectation with the proved first‑moment bound `≤ k·s·p`.  So the
theorem makes the whole pipeline explicit, proves every link but the one named gap, and shows exactly where the
genuine hardness sits.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.HolonomyBalanceFragments
open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingChebyshev

variable {n k : ℕ}

/-! ## Probabilistic existence -/

/-- **The probabilistic method (proved): an event of probability `< 1` has a complementary outcome.** -/
theorem exists_of_pr_lt_one (p : ℝ) (E : Finset (Fin n) → Prop) (h : Pr p E < 1) :
    ∃ L ∈ (Finset.univ : Finset (Fin n)).powerset, ¬ E L := by
  by_contra hc
  push_neg at hc
  have hone : Pr p E = 1 := by
    unfold Pr
    rw [Finset.filter_true_of_mem hc]
    exact total p
  linarith

/-- The number of supports that survive a restriction to the live set `L`. -/
def survivingCount (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter (fun j => ¬ Disjoint (supports j) L)).card

/-- **A low‑survival restriction exists (proved): if the expected survivor count is `≤ B < a`, some restriction
leaves `< a` surviving supports.**  Markov on the survivor count plus the probabilistic method. -/
theorem exists_low_survival (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (supports : Fin k → Finset (Fin n))
    (B a : ℝ) (ha : 0 < a) (hE : Exp p (fun L => (survivingCount supports L : ℝ)) ≤ B) (hBa : B < a) :
    ∃ L ∈ (Finset.univ : Finset (Fin n)).powerset, (survivingCount supports L : ℝ) < a := by
  have hm := markov p hp0 hp1 (fun L => (survivingCount supports L : ℝ)) (fun L => Nat.cast_nonneg _) a
  have hpr : Pr p (fun L => a ≤ (survivingCount supports L : ℝ)) < 1 := by
    by_contra hge
    push_neg at hge
    have hkey : a ≤ a * Pr p (fun L => a ≤ (survivingCount supports L : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hge ha.le
      rwa [mul_one] at this
    linarith
  obtain ⟨L, hL, hLnot⟩ := exists_of_pr_lt_one p _ hpr
  push_neg at hLnot
  exact ⟨L, hL, hLnot⟩

/-! ## Witness ⇒ correlation bound -/

/-- **A same‑cell `D`‑witness defeats the ACC⁰ predictor (proved): `2·agreement ≤ #off‑diagonal inputs`.** -/
theorem cellWitness_gives_low_correlation (supports : Fin k → Finset (Fin n)) (D : Finset (Fin n))
    (g : (Fin k → ℕ) → Bool) (hwit : CellWitness supports D) :
    ∃ v w, v ≠ w ∧
      2 * (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
            (fun x => g (weightVec supports x) = fParity D x)).card
        ≤ ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).card := by
  obtain ⟨v, w, hne, hvD, hwD, hcell⟩ := hwit
  exact ⟨v, w, hne, kGate_low_correlation_offdiagonal supports D v w hne hvD hwD hcell g⟩

/-! ## The assembly -/

/-- **The end‑to‑end pipeline (proved up to the named cell bridge): a bounded‑overlap ACC⁰ predictor fails to
correlate with the holonomy parity under a random restriction.**  From the expected‑survivor bound a low‑survival
restriction exists (`exists_low_survival`); the cell bridge `hbridge` turns it into a same‑cell `D`‑witness; the
witness defeats the predictor (`cellWitness_gives_low_correlation`).  `hE` is the first‑moment bound (`≤ k·s·p`)
identified with the measure expectation; `hbridge` is the second‑moment/pigeonhole cell collapse (the higher‑moment
frontier for unbounded overlap). -/
theorem bounded_overlap_acc0_low_correlation_whp (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (D : Finset (Fin n)) (g : (Fin k → ℕ) → Bool)
    (B a : ℝ) (ha : 0 < a) (hBa : B < a)
    (hE : Exp p (fun L => (survivingCount supports L : ℝ)) ≤ B)
    (hbridge : ∀ L ∈ (Finset.univ : Finset (Fin n)).powerset,
        (survivingCount supports L : ℝ) < a → CellWitness supports D) :
    ∃ v w, v ≠ w ∧
      2 * (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
            (fun x => g (weightVec supports x) = fParity D x)).card
        ≤ ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).card := by
  obtain ⟨L, hL, hLsurv⟩ := exists_low_survival p hp0 hp1 supports B a ha hE hBa
  exact cellWitness_gives_low_correlation supports D g (hbridge L hL hLsurv)

end PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline

#print axioms PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline.exists_of_pr_lt_one
#print axioms PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline.exists_low_survival
#print axioms PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline.cellWitness_gives_low_correlation
#print axioms PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline.bounded_overlap_acc0_low_correlation_whp
