import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMCSP

/-!
# N-Frame: scoping the thermodynamic cubic-graph boundary invariant (book1 pillar 3)

This scopes the candidate from `nframe-book1` (Fig 7.3 "SPDP event horizon", §9.4 four pillars): a finite observer has a
bounded thermodynamic / curvature boundary, and a function is P-reachable iff it admits an **observer embedding** (a
bounded-degree "cubic-graph" boundary) of *low boundary dimension*.  The invariant is

  `thermoBoundary f` = the least boundary dimension over admissible observer embeddings computing `f`.

**What is genuinely better than raw degree / sensitivity.**  This is a *locality / process* measure, not a truth-table
property.  It plausibly rates the two functions that broke the earlier candidates *both low*: the full-AND (a small local
structure) and parity (a simple local automaton).  So it can pass anti-inversion screens 1–2 that sensitivity failed, and
it is observer/embedding-based rather than a bare large constructive truth-table property — the right *class* of refined
invariant.  Credit where due: this is closer to what an N-Frame boundary invariant should be.

**Where it stands against the barriers (the honest test).**  `thermoBoundary` is exactly a *minimum-description-size*
invariant with `size = boundaryDim` — so it is a direct instance of the MCSP framework, and inherits its verdict:

  `thermoBoundary_gap_iff_not_lowBoundary` — **PROVED (universal embeddings)**: `s < thermoBoundary f ↔ f ∉ lowBoundary s`.
        If admissible embeddings can represent every function, the "SPDP rank exceeds threshold" gap **is** class
        non-membership — book1's separation, restated.  Circular (the MCSP trap), by the proved theorem.
  `thermoBoundary_useful` — **PROVED**: usefulness holds, but (by the above) definitionally.
  `thermoBoundary_separation` — **PROVED (conditional)**: for a *restricted* admissible class, capture (book1 **pillar 3**:
        every P-function has a low-boundary embedding) + gap (book1 **pillar 4**: the target does not) ⇒ separation.  Both
        premises are named hypotheses — *undischarged*.

## Honest scope — the right class of candidate, the same two open pillars

Mapping book1's four pillars to what is proved vs assumed here:
* **Pillar 3 (capture): every P-computation has low thermodynamic boundary dimension** — this is `thermoBoundary_separation`'s
  hypothesis, *assumed not derived*.  It is the load-bearing "P-observer ⇒ low boundary" bridge, equal in strength to the
  separation.
* **Pillar 4 (gap): permanent / diagonal families have super-polynomial boundary/SPDP rank** — the *diagonal* version was
  disproved in this repo (`rk χ_φ ≪ #SAT`); the *permanent* version is genuine depth-3/4 SPDP but barriered short of
  VP-vs-VNP, so it does not reach the `P/poly` scale (cf. the magnitude increment: the raw invariant caps at linear).
* **Pillar 2 (barrier evasion):** if `boundaryDim` is efficiently computable and large it is a *natural* property (blocked
  by Razborov–Rudich); the universal (min-over-all-embeddings) form is MCSP-circular above; and book1's SRCD "God Move"
  diagonalisation was proved in this repo *equivalent* to the separation, not a proof of it.

So the thermodynamic cubic-boundary invariant is the **right class** of refined candidate — more plausible than raw degree
or sensitivity, correcting more inversions — but its two load-bearing halves are precisely book1's assumed pillar 3 and
barriered/disproved pillar 4, and the universal form collapses to the circularity trap.  This file formalises exactly
that; it does **not** discharge either pillar.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameThermoBoundary

open PallLean.Paper93.DeepMath.PathB.NFrameAntiNatural (BoolFn FnProperty Useful)
open PallLean.Paper93.DeepMath.PathB.NFrameMCSP (mcsp sizeClass mcsp_gap_iff_not_sizeClass mcsp_useful)

variable {n : ℕ} {Embedding : Type*}
  (semantics : Embedding → BoolFn n) (boundaryDim : Embedding → ℕ)

/-- The candidate invariant: the least boundary dimension over admissible observer embeddings computing `f` (book1's SPDP
event-horizon codimension). -/
noncomputable def thermoBoundary (f : BoolFn n) : ℕ := mcsp semantics boundaryDim f

/-- The "low thermodynamic boundary" observer class at budget `s` — book1's P-reachable region inside the collapse
surface. -/
def lowBoundary (s : ℕ) : FnProperty n := sizeClass semantics boundaryDim s

/-- **The circularity, for universal embeddings (proved).**  If admissible observer embeddings can represent every
function, then the boundary-dimension *gap* `s < thermoBoundary f` is *identical* to non-membership `f ∉ lowBoundary s`.
book1's "SPDP rank exceeds the codimension-pruned threshold" is then verbatim "the target is outside the P-reachable
region" — the separation restated, with no independent leverage. -/
theorem thermoBoundary_gap_iff_not_lowBoundary
    (hcover : ∀ f, ∃ e, semantics e = f) (s : ℕ) (f : BoolFn n) :
    s < thermoBoundary semantics boundaryDim f ↔ ¬ lowBoundary semantics boundaryDim s f :=
  mcsp_gap_iff_not_sizeClass semantics boundaryDim hcover s f

/-- **Usefulness (proved).**  The high-boundary property certifies non-membership — but definitionally, by the circularity
above. -/
theorem thermoBoundary_useful (hcover : ∀ f, ∃ e, semantics e = f) (s : ℕ) :
    Useful (fun f => s < thermoBoundary semantics boundaryDim f) (lowBoundary semantics boundaryDim s) :=
  mcsp_useful semantics boundaryDim hcover s

/-- **The book1 beam (proved, conditional on both pillars).**  For a restricted observer/computation class `Pclass`,
book1's **pillar 3** (capture: every `Pclass` function has a low-boundary embedding) and **pillar 4** (gap: the target's
boundary dimension exceeds the budget) together separate the target from `Pclass`.  Both premises are the undischarged,
`P ≠ NP`-strength content — this file supplies only the (trivial) beam over them. -/
theorem thermoBoundary_separation (Pclass : FnProperty n) {s : ℕ} {tgt : BoolFn n}
    (pillar3_capture : ∀ f, Pclass f → thermoBoundary semantics boundaryDim f ≤ s)
    (pillar4_gap : s < thermoBoundary semantics boundaryDim tgt) :
    ¬ Pclass tgt :=
  fun h => absurd (pillar3_capture tgt h) (not_le.mpr pillar4_gap)

end PallLean.Paper93.DeepMath.PathB.NFrameThermoBoundary

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameThermoBoundary.thermoBoundary_gap_iff_not_lowBoundary
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameThermoBoundary.thermoBoundary_separation
