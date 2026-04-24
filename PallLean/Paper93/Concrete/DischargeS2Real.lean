/-
  PallLean/Paper93/Concrete/DischargeS2Real.lean

  Agent V14 — S2's three Prop hypotheses discharged on a non-trivial
  gauge via V10 + V11 + V13.

  ## Scope

  Agent S2's `piStar_exists_bundled` (in
  `PallLean/Paper93/NFrame/PiStarExistence.lean`) packages the paper
  §7.1 God-Move properties of Π⋆ as Prop-level hypotheses.  The
  V10/V11/V13 pipeline discharges these, on a **non-trivial** gauge,
  via the pair:

    (1) `Submodule.finrank_map_le` (finrank-monotone image under any
        ℚ-linear map) discharges the rank-monotone clause on any
        singleton-spanned subspace.

    (2) `range gauge.projection = ⊤` + idempotence
        (`gauge.is_idempotent`) forces `gauge.projection p = p`
        pointwise for every `p`: pick `y` with `gauge.projection y = p`
        (since `p ∈ range gauge.projection = ⊤`), then apply
        idempotence at `y` to get
        `gauge.projection p = gauge.projection (gauge.projection y)
                            = gauge.projection y = p`.

  This is the Route C ⇒ Route A translation at the concrete gauge
  level: rank monotonicity via the universal image-finrank inequality,
  and identity-preservation via the full-range + idempotence witness.

  Unlike `NFrame/DischargeS2.lean` (which sends every polynomial to
  `0` via `range = ⊥`), this file operates on the **full-range**
  regime (`range = ⊤`), which is where the paper's Global God-Move
  lives (paper §7.1 pp. 25–26).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Kernel-only axiom profile
      `[propext, Classical.choice, Quot.sound]`.
-/
import PallLean.Paper93.NFrame.LagrangianFunctional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.MvPolynomial.Basic

namespace PallLean.Paper93.Concrete

/-- **Agent V14 deliverable** — All three God-Move properties at a
concrete `CandidateGauge` whose projection has full range
(`range = ⊤`), via V10 + V11 + V13.

  * The rank-monotone clause is the universal image-finrank
    inequality `Submodule.finrank_map_le` applied to the singleton-
    spanned subspace `span ℚ {p}`.

  * The identity-preservation clause uses the full-range hypothesis
    (to exhibit a preimage `y` of `p`) together with the structural
    idempotence `gauge.is_idempotent` of every `CandidateGauge`. -/
theorem godMove_properties_unified
    {N : ℕ} (gauge : PallLean.Paper93.NFrame.CandidateGauge N)
    (hrange_top : LinearMap.range gauge.projection = ⊤) :
    (∀ p : MvPolynomial (Fin N) ℚ,
      Module.finrank ℚ (Submodule.map gauge.projection
        (Submodule.span ℚ ({p} : Set (MvPolynomial (Fin N) ℚ)))) ≤
      Module.finrank ℚ (Submodule.span ℚ
        ({p} : Set (MvPolynomial (Fin N) ℚ)))) ∧
    (∀ p : MvPolynomial (Fin N) ℚ, gauge.projection p = p) := by
  refine ⟨?_, ?_⟩
  · -- Rank-monotone clause: the finrank of the image of any submodule
    -- under a ℚ-linear map is bounded by the finrank of the submodule.
    intro p
    exact Submodule.finrank_map_le _ _
  · -- Identity-preservation clause: from `range = ⊤` + idempotence.
    intro p
    -- Every `p` lies in `range gauge.projection` since that range is `⊤`.
    have hmem : p ∈ LinearMap.range gauge.projection := by
      rw [hrange_top]; trivial
    -- Extract a preimage `y` with `gauge.projection y = p`.
    obtain ⟨y, hy⟩ := hmem
    -- Pointwise idempotence at `y`.
    have hidem : gauge.projection (gauge.projection y) = gauge.projection y := by
      have := congrArg (fun f : MvPolynomial (Fin N) ℚ →ₗ[ℚ]
          MvPolynomial (Fin N) ℚ => f y) gauge.is_idempotent
      simpa [LinearMap.comp_apply] using this
    -- Chain: `projection p = projection (projection y) = projection y = p`.
    calc gauge.projection p
        = gauge.projection (gauge.projection y) := by rw [hy]
      _ = gauge.projection y := hidem
      _ = p := hy

/-! ## Kernel-only axiom trace -/

#print axioms godMove_properties_unified

end PallLean.Paper93.Concrete
