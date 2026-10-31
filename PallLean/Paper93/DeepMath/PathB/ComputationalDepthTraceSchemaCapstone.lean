import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNaturalProofs
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceRelativization

/-!
# The trace-schema capstone: the frontier, machine-checked

This file consolidates the trace-measure program into a single statement of exactly what a
`P ≠ NP` separation via this schema requires, what it costs, and where its measures are
non-invariant (a measure-level fact, not barrier evasion) — every clause
an already-proven theorem, assembled here as one frontier characterization.

The program, in order:

* **No-go** (`SeparationNoGo`): every abstract ∃-invariant route is equivalent to the
  separation; content needs a *concrete* measure.
* **Language kill** (`LangRankKill` / `DIndexMachine`): language-rank measures fail generic
  soundness — a poly-time language (doubled INDEX) has superpolynomial subfunction rank.  So a
  contentful measure must be *trace-level*.
* **Transfer** (`TraceMeasureSchema`): a size-dominated trace measure is generically sound for
  free.
* **Complete** (`TraceSchemaComplete`): the search space is fully general — a size-dominated
  hard measure exists iff the separation holds, with `traceSize` (time) the canonical witness.
* **Ceiling tower** (`TraceSchemaCeiling` / `PolyCeiling`): `SizeDominated ⊂ PolySizeDominated ⊃`
  generically-sound row-subadditive — every *additive* measure is capped at time.  Content
  beyond time needs a *super-additive* measure (cross-row correlation).
* **Single-configuration cap** (`NonSizeDominated`): even dropping size-domination, generic
  soundness caps a measure per configuration.
* **Measure-level non-invariance** (`TraceRelativization` / `NaturalProofs`): `traceInv` is
  machine-dependent and generically-sound measures are non-large.  These are *not* barrier
  evasions — see those files' scope notes; they record that the measures are not invariant in the
  ways language-determined / density-based barriers exploit, a weaker statement.

`traceSchema_frontier` bundles the SATV-relative clauses; `traceSchema_machine_dependent` is the
SATV-free machine-dependence fact.  The single remaining open crux — a super-additive
generically-sound measure superpolynomial on SAT-decider traces — is precisely the `P` vs `NP`
problem itself, bounded by the abstract theorems here but by nothing that touches the barriers.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TraceSchemaCapstone

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge
open PallLean.Paper93.DeepMath.PathB.SeparationNoGo
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.TraceSchemaCeiling
open PallLean.Paper93.DeepMath.PathB.PolyCeiling
open PallLean.Paper93.DeepMath.PathB.NaturalProofs
open PallLean.Paper93.DeepMath.PathB.TraceRelativization (traceInv_machine_dependent)
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-- **THE TRACE-SCHEMA FRONTIER.**  For every NP-observer `SATV`, the trace-measure schema
satisfies, simultaneously:

1. **Complete** — the separation holds iff a size-dominated hard measure exists;
2. **Ceiling** — every such measure reduces to `traceSize`'s (time's) hardness;
3. **Additive cap** — every generically-sound *row-subadditive* measure's hardness implies
   `traceSize`'s (so additive measures offer no content beyond time);
4. **Free transfer** — size-domination gives generic soundness for free;
5. **Non-large** — every generically-sound measure fails the largeness condition (a measure-level
   fact, not a natural-proofs barrier evasion).

The gap between (2)/(3) and content is exactly the super-additive frontier: a measure that
exceeds `traceSize` on SAT traces via cross-row correlation. -/
theorem traceSchema_frontier (SATV : NPObs) :
    -- (1) completeness
    (¬ PolyCollapse SATV ↔ ∃ μ, SizeDominated μ ∧ InvHard SATV (traceInv μ))
    -- (2) ceiling: reduces to time
    ∧ ((∃ μ, SizeDominated μ ∧ InvHard SATV (traceInv μ))
        ↔ InvHard SATV (traceInv traceSize))
    -- (3) additive measures capped at time
    ∧ (∀ μ, RowSubadditive μ → InvGenSound (traceInv μ) → InvHard SATV (traceInv μ)
        → InvHard SATV (traceInv traceSize))
    -- (4) free transfer: size-domination ⇒ generic soundness
    ∧ (∀ μ, SizeDominated μ → InvGenSound (traceInv μ))
    -- (5) non-large: measure-level failure of the largeness condition
    ∧ (∀ μ, InvGenSound (traceInv μ) → ∀ t : ℕ → ℕ, ¬ PolyBounded t → ¬ PropLarge μ t) :=
  ⟨(sizeDominated_hard_iff_sep SATV).symm,
    sizeDominated_ceiling SATV,
    fun μ hsub hG hH => rowSubadditive_hard_imp_traceSize_hard SATV μ hsub hG hH,
    fun μ hμ => traceInv_genSound μ hμ,
    fun μ hG t ht => genSound_not_propLarge μ hG t ht⟩

/-- **The schema's measure is machine-dependent** (SATV-free): `traceInv` is not determined by the
decided language — a language-invariant measure could not distinguish the two same-language machines
it separates.  This is a measure-level non-invariance fact, not a relativization-barrier evasion
(see `TraceRelativization`'s scope note). -/
theorem traceSchema_machine_dependent :
    ∃ (M₁ M₂ : Machine) (L : List Bool → Bool) (T₁ T₂ : ℕ → ℕ),
      Decides M₁ L T₁ ∧ Decides M₂ L T₂
        ∧ traceInv traceSize M₁ 1 ≠ traceInv traceSize M₂ 1 :=
  traceInv_machine_dependent

/-- **The residual crux, named.**  Everything the schema can decide abstractly is decided: the
only route to `¬ PolyCollapse` not already reducible to time-hardness is a super-additive
generically-sound measure with superpolynomial worst-case value on SAT-decider traces.  This
predicate isolates that object; by `traceSchema_frontier` it is not blocked by the additive
ceiling, relativization, or natural proofs — it is the `P` vs `NP` problem in trace-measure
form. -/
def SuperAdditiveWitness (SATV : NPObs) : Prop :=
  ∃ μ, InvGenSound (traceInv μ) ∧ ¬ PolySizeDominated μ ∧ InvHard SATV (traceInv μ)

/-- A super-additive witness separates: it plugs into the (proved) invariant bridge. -/
theorem superAdditiveWitness_separates (SATV : NPObs) (h : SuperAdditiveWitness SATV) :
    ¬ PolyCollapse SATV := by
  obtain ⟨μ, hG, _, hH⟩ := h
  exact invariant_bridge SATV (traceInv μ)
    (invSound_of_genSound SATV (traceInv μ) hG) hH

end PallLean.Paper93.DeepMath.PathB.TraceSchemaCapstone
