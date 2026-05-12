/-
  PallLean/Paper93/Paper283/PiStarFromStationarity.lean

  Paper §28.3 — Connection of stationarity of `S_NF` (the Φ-side
  Euler–Lagrange condition and the A-side principal-minor positivity
  condition) to the existence of the universal observer gauge Π⋆.

  ## Scope (X12)

  This file provides a Prop-level bridge between the two stationarity
  witnesses formalised earlier in `Paper93/Paper283/`:

    * `StationaryPhi α β G χ Φ` — stub of paper §28.3 line 6878
      `α · L_{Gn} · Φ = (β/2) · χ · ∂ sgn(Φ)`
      (see `PallLean/Paper93/Paper283/EulerLagrangePhi.lean`);

    * `StationaryA λ A` — stub of paper §28.3 line 6880
      `−λ Σ_{J∈J}(A[J,J])^{-1} ∈ ∂(compiler constraints)`
      (see `PallLean/Paper93/Paper283/EulerLagrangeA.lean`);

  and the downstream S1/S2 universal-gauge existence witness

    * `admissibleGauge_nonempty`
      (see `PallLean/Paper93/NFrame/LagrangianFunctional.lean`).

  Paper §28.3 p. 137–138 outlines how, given a stationary pair
  `(Φ⋆, A⋆)` of `S_NF`, the universal observer gauge Π⋆ is obtained
  by projecting onto the eigenspace of `A⋆` corresponding to its
  dominant eigenvalues (the amplituhedron-positive spectrum). The
  full spectral / eigenspace machinery is not developed here; we
  record only the *existence* implication

    stationary `(Φ, A)`  ⟹  an admissible Π⋆ exists,

  at the Prop level. The witness is the S1/S2 admissible-gauge
  existence theorem `NFrame.admissibleGauge_nonempty`, which supplies
  the trivial (rank-zero) gauge. A paper-faithful eigenspace
  construction of Π⋆ is deferred to downstream research (paper §28.3
  Euler–Lagrange → eigenspace projection).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  ## Paper citations

    * §28.3 p. 137–138 — Euler–Lagrange stationarity of `S_NF` and
      the dominant-eigenspace construction of Π⋆.
    * §28.3 line 6878 — stationary-Φ PDE.
    * §28.3 line 6880 — stationary-A principal-minor positivity.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import PallLean.Paper93.Concrete.RegularGraphFixed
import PallLean.Paper93.Paper283.TseitinCharge
import PallLean.Paper93.Paper283.EulerLagrangePhi
import PallLean.Paper93.Paper283.EulerLagrangeA
import PallLean.Paper93.NFrame.LagrangianFunctional

namespace PallLean.Paper93.Paper283

open Matrix

/-- **Paper §28.3 p. 137–138 — Π⋆ from stationarity.**

Given stationary witnesses `hΦ : StationaryPhi α β G χ Φ` for the
Φ-side Euler–Lagrange equation (paper §28.3 line 6878) and
`hA : StationaryA lam A` for the A-side principal-minor positivity
(paper §28.3 line 6880), there exists an admissible universal
observer gauge Π⋆ (in the sense of
`NFrame.AdmissibleGauge`).

**Simplified stub form.** The paper's eigenspace construction
produces Π⋆ by projecting onto the dominant-eigenvalue subspace of
the stationary matrix `A⋆`. That spectral machinery is not developed
here; instead we route the conclusion through the S1/S2 universal
existence witness
`PallLean.Paper93.NFrame.admissibleGauge_nonempty`, which supplies
the rank-zero trivial gauge as the degenerate starting vertex of the
Euler–Lagrange optimisation (paper §28.3 p. 137). A paper-faithful
eigenspace construction of Π⋆ from `A⋆` is deferred to downstream
research. -/
theorem piStar_exists_from_stationarity {N d : ℕ}
    (α β lam : ℝ) (_hα : 0 < α) (_hβ : 0 < β) (_hlam : 0 < lam)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (χ : TseitinCharge N)
    (Φ : Fin N → ℝ) (A : Matrix (Fin N) (Fin N) ℝ)
    (_hΦ : StationaryPhi (N := N) (d := d) α β G χ Φ)
    (_hA : StationaryA lam A) :
    ∃ PiStar : PallLean.Paper93.NFrame.CandidateGauge N,
      PallLean.Paper93.NFrame.AdmissibleGauge PiStar :=
  PallLean.Paper93.NFrame.admissibleGauge_nonempty

/-! ## Kernel-only axiom trace -/

#print axioms piStar_exists_from_stationarity

end PallLean.Paper93.Paper283
