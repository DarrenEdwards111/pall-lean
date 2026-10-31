import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceMeasureSchema

/-!
# S2: the trace schema is complete — and `traceSize` is time in disguise

**Step 5, brick S2.**  Two theorems pin the search space exactly.

**Completeness** (`traceSchema_complete`): a size-dominated trace measure witnessing the
route *exists* if and only if the separation is true.  So restricting the search to
size-dominated trace measures loses no generality whatsoever — the space provably
contains a witness whenever any proof exists at all.  The witness used is `traceSize`
itself, via:

* `minHalt_eq_minTimeInv` — for a *decider*, the minimal uniform halting time equals the
  minimal uniform correct-halting time (halting forces the stable — hence correct —
  answer, by `solvedAt_of_halts`);
* `rows_le_traceInv` — the worst-case trace size dominates the row count
  `minHalt + 1`;
* `traceSize_hard_iff_sep` — hardness of `traceInv traceSize` is *equivalent* to the
  separation: forward is the S1 route, backward chains the row count through
  `minHalt = minTimeInv` into `minTimeInv_hard_iff_sep`.

**The no-gain reading** (the honest side of the same coin): `traceSize` is time in
disguise — its hardness is the separation verbatim, with zero attack-surface gain,
exactly the `minTimeInv` pattern.  So the search criterion is now sharp: a *contentful*
candidate `μ` must be superpolynomial on every SAT-decider's traces for reasons visible
in poly-scale structure (rank, expansion, proof-space of the rows) rather than by total
bulk — while staying size-dominated so S1's transfer theorem keeps it generically sound.
Candidates for S3's audit: the Tseitin proof-space observer measure and SPDP/cube rank
read off trace rows; the space-measure kill (max row length cannot be hard, because
brute force decides SAT in poly space) additionally needs a concrete brute-force decider
machine — a named engineering item, not fenced here.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TraceSchemaComplete

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge
open PallLean.Paper93.DeepMath.PathB.SeparationNoGo
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-- **For a decider, halting is deciding**: the minimal uniform halting time equals the
minimal uniform correct-halting time.  Once halted everywhere, the answers are the
stable — hence correct — ones. -/
theorem minHalt_eq_minTimeInv (SATV : NPObs) {M : Machine} {T : ℕ → ℕ}
    (hD : Decides M (acceptBool SATV) T) (n : ℕ) :
    minHalt M n = minTimeInv SATV M n := by
  have hsolvedT : SolvedAt SATV M n (T n) := by
    intro x hx
    obtain ⟨hh, hc⟩ := hD x
    rw [hx] at hh hc
    exact ⟨hh, hc⟩
  have hexS : ∃ t, SolvedAt SATV M n t := ⟨T n, hsolvedT⟩
  have hexH : ∃ t, HaltsAllAt M n t := ⟨T n, fun x hx => (hsolvedT x hx).1⟩
  have h1 : minHalt M n ≤ minTimeInv SATV M n := by
    show (if h : ∃ t, HaltsAllAt M n t then Nat.find h else 0) ≤ _
    rw [dif_pos hexH]
    show Nat.find hexH ≤ (if h : ∃ t, SolvedAt SATV M n t then Nat.find h else 0)
    rw [dif_pos hexS]
    exact Nat.find_le fun x hx => (Nat.find_spec hexS x hx).1
  have h2 : minTimeInv SATV M n ≤ minHalt M n := by
    show (if h : ∃ t, SolvedAt SATV M n t then Nat.find h else 0) ≤ _
    rw [dif_pos hexS]
    show Nat.find hexS ≤ (if h : ∃ t, HaltsAllAt M n t then Nat.find h else 0)
    rw [dif_pos hexH]
    exact Nat.find_le (solvedAt_of_halts SATV M hsolvedT fun x hx =>
      Nat.find_spec hexH x hx)
  omega

/-- The worst-case trace size dominates the row count. -/
theorem rows_le_traceInv (M : Machine) (n : ℕ) :
    minHalt M n + 1 ≤ traceInv traceSize M n := by
  have hle := Finset.le_sup (f := fun v : Fin n → Bool =>
    traceSize (traceObj M (minHalt M n) (List.ofFn v)))
    (Finset.mem_univ (fun _ : Fin n => false))
  refine le_trans ?_ hle
  unfold traceSize traceObj
  simp only [List.length_map, List.length_range]
  omega

/-- **`traceSize` is time in disguise**: hardness of the worst-case trace size is the
separation, verbatim.  Forward is the S1 route; backward, a poly bound on trace size
bounds the row count `minHalt + 1`, which for a decider *is* `minTimeInv + 1` — whose
poly-boundedness contradicts `minTimeInv`'s hardness under the separation. -/
theorem traceSize_hard_iff_sep (SATV : NPObs) :
    InvHard SATV (traceInv traceSize) ↔ ¬ PolyCollapse SATV := by
  constructor
  · intro hH
    exact traceMeasure_route SATV traceSize sizeDominated_traceSize hH
  · intro hsep M T hD hPB
    have h1 : PolyBounded (minTimeInv SATV M) := by
      refine polyBounded_of_le (fun n => ?_) hPB
      rw [← minHalt_eq_minTimeInv SATV hD n]
      have := rows_le_traceInv M n
      omega
    exact (minTimeInv_hard_iff_sep SATV).mpr hsep M T hD h1

/-- **THE SCHEMA IS COMPLETE.**  A size-dominated trace measure witnessing the route
exists iff the separation is true: restricting step 5's search to size-dominated trace
measures loses nothing.  (And, as always, the ∃-form is separation-equivalent — the
content lives only in a *concrete* `μ` whose hardness admits a non-diagonal proof; the
completeness witness `traceSize` is precisely the contentless one.) -/
theorem traceSchema_complete (SATV : NPObs) :
    (∃ μ, SizeDominated μ ∧ InvHard SATV (traceInv μ)) ↔ ¬ PolyCollapse SATV := by
  constructor
  · rintro ⟨μ, hμ, hH⟩
    exact traceMeasure_route SATV μ hμ hH
  · intro hsep
    exact ⟨traceSize, sizeDominated_traceSize, (traceSize_hard_iff_sep SATV).mpr hsep⟩

end PallLean.Paper93.DeepMath.PathB.TraceSchemaComplete
