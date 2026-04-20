/-
  PallLean.Supplementary — Paper §28.3 explanatory formalization
  ===============================================================

  ## Purpose

  This directory collects Lean formalization of paper §28.3 (N-Frame
  Lagrangian: analytic reformulation of the hard bound). Per the paper's
  own Remark 60:

    > "Remark 60 (Editorial note). This subsection is explanatory; all
    >  quantitative lower bounds we use are already supplied by §§14.1
    >  and 14.3."

  ## Status

  **SUPPLEMENTARY — not on the critical path to `P_ne_NP_unconditional`.**

  The material here provides a rigorous Lean realization of the paper's
  amplituhedron-type positive geometry: PSD operator infrastructure,
  determinantal barrier, totally positive Grassmannian, Plücker coordinates,
  positroid combinatorics, spectral log-det formulas. Together these
  implement the variational / geometric picture described in §28.3.

  However, the **load-bearing** chain for Theorem 207 (Global God-Move
  ⇒ P ≠ NP) uses:

    - §§14.1, 14.3 — resource-bounded separation + observer-classical
      bridge (via BP→SPDP pipeline)
    - §40 — Formal Proof Architecture (Theorems 203, 209, 217,
      Lemmas 211-214, Width⇒Rank theorem)

  Not the Lagrangian of §28.3.

  ## Files

  - `AmplituhedronPSD.lean` — PSD operators, determinantal barrier,
    totally positive Grassmannian, Plücker coordinates, positroid
    combinatorics, spectral log-det formula (22 sections, axiom-free)

  ## Relationship to the critical path

  The on-chain proof (see `PallLean/PaperFaithfulSeparation.lean`)
  depends on a single project-specific axiom
  `GlobalGodMoveGauge.exists_rank_sandwich_for_sat_decider`, which can
  be discharged by formalizing the §40 pipeline. The amplituhedron
  material here MOTIVATES the gauge Π⋆ geometrically (as the unique
  holographic projection realizing rank minimization under the positive-
  geometry interpretation) but does NOT directly discharge the axiom.

  ## N-Frame as conceptual glue

  This supplementary layer is still useful as a **unifying geometry** for
  the paper's recurring two-view pattern. One can read the current Lean
  obstruction as follows:

  - the **fine-grained / microscopic** view resolves multiplicative
    interaction structure, so identity minors survive and the NP-side
    product-form rank lower bound is visible;
  - the **coarse-grained / effective** view resolves only bounded-locality
    structure, so SoS/locality collapse and low effective rank become
    visible on the P-side;
  - the missing bridge in the current formalization is not a new global
    philosophy, but a concrete compiler/extraction theorem showing how
    these two views arise from one compiled object in the exact algebraic
    form required by the proof.

  In that sense, §28.3 is best treated as a conceptual scaffold for the
  slogan:

    "same object, different effective geometry."

  This helps explain why product-form NP rigidity, P-side locality
  collapse, and observer/coarse-graining arguments keep reappearing across
  different routes, even though the actual load-bearing closure still has
  to be supplied by explicit §40 compiler/extraction theorems.

  Items in this directory are preserved as paper-faithful explanatory
  infrastructure: they make the §28.3 variational picture precise,
  align Lean's formal development with the paper's geometric story, and
  provide a natural home for future notes/theorem schemas expressing the
  "same object, different geometry" interpretation.
-/

import PallLean.Supplementary.AmplituhedronPSD
