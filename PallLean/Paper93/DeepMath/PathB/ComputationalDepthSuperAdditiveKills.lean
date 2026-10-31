import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSuperAdditiveNarrow

/-!
# Targeted super-additive candidate kills

`SuperAdditiveNarrow` showed the capped class `PolySizeDominated` is a rich algebra.  This file
cashes that out on **concrete natural candidate measures** — the kind one might hope is a
super-additive witness — and proves each is capped, hence *not* a witness (its hardness reduces to
time).  These are the measures that "look" super-additive (they aggregate across configurations)
but are secretly bounded by a polynomial in the row count or trace size:

* `distinctRows` — the number of distinct configurations (`≤ rows`);
* `repetitions` — the number of repeated configurations (`≤ rows`);
* `rowContent` — the total tape content (`≤ traceSize`);
* `pairwiseRows` — a pairwise aggregate `rows²`;
* `distinctRowsSq` — distinct-row count squared (a product of two capped measures).

`natural_candidates_capped` bundles them; `natural_candidates_not_witnesses` states each fails the
witness's `¬ PolySizeDominated` clause.  The surviving crux is thereby confirmed to lie outside
every such natural aggregate: it needs correlation super-polynomial in the configuration count.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SuperAdditiveKills

open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics (NPObs)
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge (InvHard)
open PallLean.Paper93.DeepMath.PathB.SeparationNoGo (InvGenSound)
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.PolyCeiling
open PallLean.Paper93.DeepMath.PathB.SuperAdditiveNarrow

/-- **A capped measure is not a super-additive witness's measure.**  Its hardness reduces to time;
it cannot satisfy the witness's `¬ PolySizeDominated` clause. -/
theorem psd_not_witness (SATV : NPObs) (μ : List (List Bool) → ℕ) (hpsd : PolySizeDominated μ) :
    ¬ (InvGenSound (traceInv μ) ∧ ¬ PolySizeDominated μ ∧ InvHard SATV (traceInv μ)) :=
  fun ⟨_, hnp, _⟩ => hnp hpsd

/-! ## Candidate measures -/

/-- Number of distinct configurations in the trace. -/
def distinctRows (tr : List (List Bool)) : ℕ := tr.dedup.length

theorem distinctRows_capped : PolySizeDominated distinctRows :=
  polySizeDominated_of_sizeDominated _ fun tr =>
    (List.Sublist.length_le (List.dedup_sublist tr)).trans (rows_le_traceSize tr)

/-- Number of repeated configurations. -/
def repetitions (tr : List (List Bool)) : ℕ := tr.length - tr.dedup.length

theorem repetitions_capped : PolySizeDominated repetitions :=
  polySizeDominated_of_sizeDominated _ fun tr => (Nat.sub_le _ _).trans (rows_le_traceSize tr)

/-- Total tape content across the trace. -/
def rowContent (tr : List (List Bool)) : ℕ := (tr.map List.length).sum

theorem rowContent_capped : PolySizeDominated rowContent :=
  polySizeDominated_of_sizeDominated _ fun tr => by rw [traceSize]; exact Nat.le_add_right _ _

/-- A pairwise aggregate over configurations: `rows²`. -/
def pairwiseRows (tr : List (List Bool)) : ℕ := tr.length * tr.length

theorem pairwiseRows_capped : PolySizeDominated pairwiseRows := by
  apply rowCount_poly_polySizeDominated pairwiseRows 1 2
  intro tr
  show tr.length * tr.length ≤ 1 * (tr.length + 1) ^ 2
  rw [one_mul, pow_two]
  exact Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)

/-- Distinct-configuration count squared — a product of two capped measures. -/
def distinctRowsSq (tr : List (List Bool)) : ℕ := distinctRows tr * distinctRows tr

theorem distinctRowsSq_capped : PolySizeDominated distinctRowsSq :=
  polySizeDominated_mul distinctRows distinctRows distinctRows_capped distinctRows_capped

/-! ## The kills -/

/-- **Every one of these natural candidates is capped.** -/
theorem natural_candidates_capped :
    PolySizeDominated distinctRows ∧ PolySizeDominated repetitions
      ∧ PolySizeDominated rowContent ∧ PolySizeDominated pairwiseRows
      ∧ PolySizeDominated distinctRowsSq :=
  ⟨distinctRows_capped, repetitions_capped, rowContent_capped, pairwiseRows_capped,
    distinctRowsSq_capped⟩

/-- **None of these natural candidates is a super-additive witness.**  Each fails the witness's
`¬ PolySizeDominated` clause, so its hardness (if any) reduces to time — no content beyond it. -/
theorem natural_candidates_not_witnesses (SATV : NPObs) :
    (¬ (InvGenSound (traceInv distinctRows) ∧ ¬ PolySizeDominated distinctRows
        ∧ InvHard SATV (traceInv distinctRows)))
    ∧ (¬ (InvGenSound (traceInv repetitions) ∧ ¬ PolySizeDominated repetitions
        ∧ InvHard SATV (traceInv repetitions)))
    ∧ (¬ (InvGenSound (traceInv rowContent) ∧ ¬ PolySizeDominated rowContent
        ∧ InvHard SATV (traceInv rowContent)))
    ∧ (¬ (InvGenSound (traceInv pairwiseRows) ∧ ¬ PolySizeDominated pairwiseRows
        ∧ InvHard SATV (traceInv pairwiseRows)))
    ∧ (¬ (InvGenSound (traceInv distinctRowsSq) ∧ ¬ PolySizeDominated distinctRowsSq
        ∧ InvHard SATV (traceInv distinctRowsSq))) :=
  ⟨psd_not_witness SATV _ distinctRows_capped,
    psd_not_witness SATV _ repetitions_capped,
    psd_not_witness SATV _ rowContent_capped,
    psd_not_witness SATV _ pairwiseRows_capped,
    psd_not_witness SATV _ distinctRowsSq_capped⟩

end PallLean.Paper93.DeepMath.PathB.SuperAdditiveKills
