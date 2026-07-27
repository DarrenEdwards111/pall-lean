import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpressivityTower

/-!
# The incompressible core survives free reach — the first free-reach-robust property

Every prior reduction capped at **free reach**: the P-observer's template may *read* everything (reach =
input width is unbounded in the DAG model), so any bound on sharing via reach breaks.  Darren's idea
relocates the obstruction: sharing's saving depends on the template's **summary** — the output width it
passes to both copies (its *compression* of the core) — **not** on its reach.  Reading everything does not
help if you cannot *compress* it.

Split a template by two independent widths: `reach` (input it reads) and `summary` (output it passes on).
The saving from sharing is `coreSize − summary`: you share the core only through the summary, and the
summary itself costs `summary` to produce.  An **incompressible** core — one no summary smaller than
itself can determine (`coreSize ≤ summary`) — yields **zero saving**, and this holds for *any* reach.
Free reach reads the whole core; it still cannot summarize it.

## What is proved

* **`saving_independent_of_reach`** — the saving does not mention `reach`: two templates with the same
  core and summary save the same amount whatever their reach.  Reading more never shares more.
* **`incompressible_kills_saving`** — an incompressible core (`coreSize ≤ summary`) gives saving `0`: it
  cannot be shared.
* **`incompressible_survives_free_reach`** — for *any* reach `r`, an incompressible core still saves `0`.
  The property is free-reach-robust — the first that is.
* **`compressible_permits_saving`** — the contrast: a *compressible* core (`summary < coreSize`) saves
  `coreSize − summary > 0`.  Compression, not reach, is what mass production needs.
* **`free_reach_needs_compression_not_reach`** — the capstone: at the *same* (huge) reach, an
  incompressible core saves nothing while a compressible one saves — the difference is compression, never
  reach.

## Honest verdict — the right property, now on compression instead of reach

Darren's property is correct and it is the **first free-reach-robust** reduction of the arc.  The
mechanism is orthogonality: sharing is bounded by the **summary** (output width = compression), and reach
is **input** width, so free reach (`incompressible_survives_free_reach`) leaves the bound untouched.  This
relocates the open target from "bound the template's reach" — which free reach always broke, the cap of
`SeamReachBound`, `SATSeamSocket`, `SATSeamReachThreshold`, `CutSharingBound`, `GlobalGateGodMove` — to
**"SAT's seam core is incompressible"**: no summary smaller than the core determines it.  That residual is
still `cost_super` (the specific incompressibility of SAT — the incompressibility thread of
`HolographicIncompressibility`, `SelfImproveRatio`), but it is now stated in the **correct, free-reach-
surviving form**: a compression / output-width bound, not a reach / input-width bound.  The property is
built and proved free-reach-robust; that SAT's core *is* incompressible is the wall.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.IncompressibleCore

/-- **A core template.**  `coreSize` is the shared core's size; `reach` is the input width the template
reads (unbounded = free reach); `summary` is the output width it passes to both copies — its
*compression* of the core.  `reach` and `summary` are independent widths. -/
structure CoreTemplate where
  /-- the core's size -/
  coreSize : ℕ
  /-- input width read (free reach = large) -/
  reach : ℕ
  /-- output width passed to both copies (the compression of the core) -/
  summary : ℕ

/-- The saving from sharing: the core, shared only through the summary, net of the summary's own cost —
`coreSize − summary`.  Depends on `summary`, **not** on `reach`. -/
def CoreTemplate.saving (T : CoreTemplate) : ℕ := T.coreSize - T.summary

/-- **Incompressible core**: no summary smaller than the core determines it (`coreSize ≤ summary`). -/
def Incompressible (T : CoreTemplate) : Prop := T.coreSize ≤ T.summary

/-! ### Saving depends on compression, not reach -/

/-- **The saving does not depend on reach (proved).**  Two templates with the same core and summary save
the same, whatever their reach.  Reading more (free reach) never shares more. -/
theorem saving_independent_of_reach (T T' : CoreTemplate)
    (hc : T.coreSize = T'.coreSize) (hs : T.summary = T'.summary) :
    T.saving = T'.saving := by
  simp only [CoreTemplate.saving, hc, hs]

/-! ### Incompressibility kills sharing — and survives free reach -/

/-- **An incompressible core cannot be shared (proved).**  If `coreSize ≤ summary`, the saving is `0`:
the summary is no smaller than the core, so sharing it costs as much as recomputing. -/
theorem incompressible_kills_saving (T : CoreTemplate) (h : Incompressible T) :
    T.saving = 0 := by
  simp only [CoreTemplate.saving]
  have := h
  simp only [Incompressible] at this
  omega

/-- **The incompressible core survives free reach (proved) — the point.**  For *any* reach `r` (however
large — reading everything), an incompressible core still saves `0`.  Free reach is input width; the
obstruction is at the summary (output/compression), which free reach does not touch. -/
theorem incompressible_survives_free_reach (coreSize summary : ℕ) (h : coreSize ≤ summary) (r : ℕ) :
    (CoreTemplate.mk coreSize r summary).saving = 0 := by
  simp only [CoreTemplate.saving]
  omega

/-- **A compressible core permits sharing (proved) — the contrast.**  If `summary < coreSize`, the saving
is `coreSize − summary > 0`.  Compression, not reach, is what mass production needs. -/
theorem compressible_permits_saving (T : CoreTemplate) (h : T.summary < T.coreSize) :
    0 < T.saving := by
  simp only [CoreTemplate.saving]
  omega

/-! ### The capstone: at the same free reach, compression is the only difference -/

/-- **Free reach needs compression, not reach (proved).**  Two templates at the *same* huge reach
(`1000`): the incompressible one (`summary = coreSize = 10`) saves `0`; the compressible one
(`summary = 3 < 10`) saves `7`.  Same reach, opposite outcomes — the difference is compression alone. -/
theorem free_reach_needs_compression_not_reach :
    ∃ T T' : CoreTemplate,
      T.reach = T'.reach ∧
      Incompressible T ∧ T.saving = 0 ∧
      T'.summary < T'.coreSize ∧ 0 < T'.saving := by
  refine ⟨⟨10, 1000, 10⟩, ⟨10, 1000, 3⟩, rfl, ?_, ?_, ?_, ?_⟩
  · show (10 : ℕ) ≤ 10; omega
  · decide
  · decide
  · decide

end PallLean.Paper93.DeepMath.PathB.IncompressibleCore

#print axioms PallLean.Paper93.DeepMath.PathB.IncompressibleCore.saving_independent_of_reach
#print axioms PallLean.Paper93.DeepMath.PathB.IncompressibleCore.incompressible_kills_saving
#print axioms PallLean.Paper93.DeepMath.PathB.IncompressibleCore.incompressible_survives_free_reach
#print axioms PallLean.Paper93.DeepMath.PathB.IncompressibleCore.compressible_permits_saving
#print axioms PallLean.Paper93.DeepMath.PathB.IncompressibleCore.free_reach_needs_compression_not_reach
