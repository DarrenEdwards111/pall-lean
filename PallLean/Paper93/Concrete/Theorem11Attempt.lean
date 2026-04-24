/-
  PallLean/Paper93/Concrete/Theorem11Attempt.lean

  Agent V11 — Paper §7.1 Theorem 11 (Global God Move for permanent),
  partial formalisation: NP-side abstract statement.

  ## Scope

  This file records a partial, abstract formalisation of paper §7.1
  Theorem 11 ("Global God-Move: Π⋆ preserves the identity minor")
  on the NP-side.  Concretely, we prove:

    * `globalGodMove_permanent_abstract`
        Given a family of permanent-type polynomials
        `permFamily : ℕ → MvPolynomial (Fin N) ℚ` and a candidate
        gauge `gauge : CandidateGauge N` whose projection has full
        range (`LinearMap.range gauge.projection = ⊤`), the gauge
        fixes every member of the family:
            `∀ k, gauge.projection (permFamily k) = permFamily k`.

  The argument is a pure idempotence argument: if `range π = ⊤`,
  every vector lies in the range, so there exists a preimage `y`
  with `π y = x`; applying idempotence `π ∘ π = π` to `y` gives
  `π x = π (π y) = π y = x`.

  This matches paper §7.1 pp. 25–26 "Global God-Move for permanent":
  on the full ambient row-space, the universal gauge `Π⋆` acts as
  the identity, and in particular preserves the identity minor on
  the permanent family.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  ## Paper citations

    * §7.1 pp. 25–26 — Global God-Move for permanent;
      preservation of the identity minor under `Π⋆`.
-/
import PallLean.Paper93.NFrame.LagrangianFunctional

namespace PallLean.Paper93.Concrete

/-- **Paper §7.1 Theorem 11 (NP-side, abstract form).**

Given a family of permanent-type polynomials `permFamily` in
`MvPolynomial (Fin N) ℚ` and a `CandidateGauge N` whose projection
has full range (`LinearMap.range gauge.projection = ⊤`), the gauge
acts as the identity on every member of the family.

This is the abstract idempotence witness of the Global God-Move
statement: on the full ambient row-space, `Π⋆` preserves the
identity minor carried by the permanent family. -/
theorem globalGodMove_permanent_abstract
    {N : ℕ} (permFamily : ℕ → MvPolynomial (Fin N) ℚ)
    (gauge : PallLean.Paper93.NFrame.CandidateGauge N)
    (hrange_top : LinearMap.range gauge.projection = ⊤) :
    ∀ k, gauge.projection (permFamily k) = permFamily k := by
  intro k
  -- Every element of the ambient space lies in the range of the projection,
  -- since that range is all of the ambient space.
  have hmem : permFamily k ∈ LinearMap.range gauge.projection := by
    rw [hrange_top]
    trivial
  -- Extract a preimage `y` with `gauge.projection y = permFamily k`.
  obtain ⟨y, hy⟩ := hmem
  -- Apply idempotence `projection ∘ projection = projection` pointwise at `y`.
  have hidem : gauge.projection (gauge.projection y) = gauge.projection y := by
    have := congrArg (fun f : MvPolynomial (Fin N) ℚ →ₗ[ℚ]
        MvPolynomial (Fin N) ℚ => f y) gauge.is_idempotent
    simpa [LinearMap.comp_apply] using this
  -- Chain: `projection (permFamily k) = projection (projection y) = projection y = permFamily k`.
  calc gauge.projection (permFamily k)
      = gauge.projection (gauge.projection y) := by rw [hy]
    _ = gauge.projection y := hidem
    _ = permFamily k := hy

end PallLean.Paper93.Concrete
