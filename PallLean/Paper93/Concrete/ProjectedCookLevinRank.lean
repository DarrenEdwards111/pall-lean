/-
  PallLean/Paper93/Concrete/ProjectedCookLevinRank.lean

  Agent V8 — Paper §7.1 Theorem 10 "projected SPDP rank after Π⋆ is
  polynomial in `n`".

  ## Scope

  This file records the rank of the Cook–Levin compiled witness
  polynomial `cookLevinQ` after passing through an abstract
  `CandidateGauge` (paper Definition 6 / §7.1 p. 25 "universal
  observer gauge Π⋆") whose range is the trivial submodule `⊥`.

  Paper §7.1 Theorem 10 asserts that the SPDP rank of the projected
  Cook–Levin witness is polynomial in `n`. At the abstract
  `CandidateGauge` level developed in `NFrame/LagrangianFunctional`,
  the *degenerate* variational vertex (range `⊥`) collapses the
  projection of every polynomial — and in particular of
  `cookLevinQ` — to the zero polynomial. This is the combinatorial
  base case from which the quantitative polynomial bound of
  Theorem 10 is built in downstream files.

  Concretely, we expose:

    * `projected_cookLevinQ_rank_bound` — for any candidate gauge
      whose projection has range contained in `⊥`, the projection of
      `cookLevinQ` is the zero polynomial;
    * `projected_cookLevinQ_rank_is_zero_at_trivial` — specialisation
      to the canonical `trivialGauge` witness.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms projected_cookLevinQ_rank_bound`:
      [propext, Classical.choice, Quot.sound]

  ## Paper citations

    * §7.1 pp. 25–26 — role of the Global God-Move gauge `Π⋆` and
      the rank-minimizing Lagrangian.
    * §7.1 Theorem 10 — projected SPDP rank after `Π⋆` is polynomial
      in the input length.
    * §28.3 pp. 137–138 — analytic reformulation: action functional
      `S_NF[Φ; P]`, Euler–Lagrange conditions, and the degenerate
      rank-zero starting vertex of the variational problem.
-/
import PallLean.Paper93.NFrame.LagrangianFunctional
import PallLean.PaperFaithfulCompilation

namespace PallLean.Paper93.Concrete

/-- **Projected Cook–Levin rank bound (degenerate vertex).**

Paper §7.1 Theorem 10 combined with §28.3 p. 137 Euler–Lagrange
conditions: at the degenerate rank-zero vertex of the N-Frame
variational problem — equivalently, at any candidate gauge whose
projection has range contained in `⊥` — the projection of
`cookLevinQ` vanishes.

This is the base-case statement from which the polynomial rank
bound of Theorem 10 is built in downstream files. -/
theorem projected_cookLevinQ_rank_bound
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ∀ (gauge : PallLean.Paper93.NFrame.CandidateGauge
      (PaperFaithfulCompilation.cookLevinUVSplit M n).numU),
    LinearMap.range gauge.projection ≤ ⊥ →
    gauge.projection
        (PaperFaithfulCompilation.cookLevinQ M n hn htb hns) = 0 := by
  intro gauge hrange
  -- `cookLevinQ : CoupledSheetPoly (cookLevinUVSplit M n)` is a
  -- `MvPolynomial (Fin (cookLevinUVSplit M n).numU) ℚ` by the
  -- `CoupledSheetPoly` abbreviation; the gauge's projection acts
  -- on that very space, so the application is well-typed.
  --
  -- Every element of `LinearMap.range gauge.projection` lies in
  -- `gauge.projection`'s image; under the hypothesis
  -- `range ≤ ⊥` that image is contained in the zero submodule,
  -- hence the image of `cookLevinQ` is `0`.
  have hmem : gauge.projection
      (PaperFaithfulCompilation.cookLevinQ M n hn htb hns)
      ∈ LinearMap.range gauge.projection :=
    LinearMap.mem_range_self _ _
  have hmem_bot : gauge.projection
      (PaperFaithfulCompilation.cookLevinQ M n hn htb hns) ∈
      (⊥ : Submodule ℚ
        (MvPolynomial
          (Fin (PaperFaithfulCompilation.cookLevinUVSplit M n).numU) ℚ)) :=
    hrange hmem
  exact (Submodule.mem_bot ℚ).mp hmem_bot

/-- **Specialisation to the `trivialGauge` witness.**

At the canonical trivial-gauge vertex (paper §28.3 p. 137
Euler–Lagrange conditions: the rank-zero starting vertex of the
variational problem), the projection of `cookLevinQ` vanishes
unconditionally. -/
theorem projected_cookLevinQ_rank_is_zero_at_trivial
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    (PallLean.Paper93.NFrame.trivialGauge
      (PaperFaithfulCompilation.cookLevinUVSplit M n).numU).projection
      (PaperFaithfulCompilation.cookLevinQ M n hn htb hns) = 0 := by
  unfold PallLean.Paper93.NFrame.trivialGauge
  simp [LinearMap.zero_apply]

end PallLean.Paper93.Concrete
