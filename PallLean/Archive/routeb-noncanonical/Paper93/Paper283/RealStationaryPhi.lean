/-
  PallLean/Paper93/Paper283/RealStationaryPhi.lean

  Paper §28.3 line 6878 — *real* Euler–Lagrange stationarity predicate for Φ.

  ## Scope

  Paper §28.3 line 6878 states that a stationary point Φ of the N-Frame
  action `S_NF` satisfies

      α · (L_{G_n} · Φ)(v)  =  (β/2) · χ(v) · s(v),   s(v) ∈ ∂ sgn(Φ(v))

  for every vertex `v ∈ V_n = Fin N`, where `L_{G_n}` is the graph
  Laplacian of the expander `G_n` (a `d`-regular graph on `Fin N`),
  `χ : V_n → {−1, +1}` is the Tseitin charge (paper §28.3 line 6870),
  and `∂ sgn` is the (set-valued) subdifferential of the sign function.

  The earlier Y-round stub `EulerLagrangePhi.StationaryPhi` discharged
  this equation with the placeholder body `∀ v, 0 ≤ (Φ v)^2` (trivially
  true).  The present file (Y3) ups the fidelity by encoding the
  *actual* set-valued Euler–Lagrange equation as a real predicate
  `RealStationaryPhi α β G χ Φ`, using:

    * a concrete `graphLaplacianOp : RegularGraphFixed N d → (Fin N → ℝ)
      → (Fin N → ℝ)` defined by the textbook formula
      `(L · Φ)(v) = d · Φ(v) − Σ_{(v, w) ∈ edges} Φ(w)`;
    * the set-valued `subgradientSgn` from `SubgradientSgn.lean` (X).

  As required for a kernel-only Y-round deliverable, we also exhibit a
  concrete inhabitant: the zero field `Φ ≡ 0` satisfies
  `RealStationaryPhi α β G χ (fun _ => 0)` for every `α, β, G, χ`,
  because `graphLaplacianOp G 0 v = 0` and `0 ∈ ∂ sgn(0) = [−1, 1]`.

  ## Imports

    * `PallLean.Paper93.Concrete.RegularGraphFixed` — the fixed
      `RegularGraphFixed N d` type (Y1-class dependency).
    * `PallLean.Paper93.Paper283.TseitinCharge` — the Tseitin charge
      `χ : Fin N → {−1, +1}` (paper §28.3 line 6870, X1).
    * `PallLean.Paper93.Paper283.SubgradientSgn` — the subdifferential
      set `∂ sgn : ℝ → Set ℝ` (Y2-class dependency).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  ## Paper citations

    * §28.3 line 6870 — Tseitin charge `χ : V_n → {±1}`.
    * §28.3 line 6878 — Euler–Lagrange equation
      `α L_{G_n} Φ = (β/2) χ · ∂ sgn(Φ)`.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PallLean.Paper93.Concrete.RegularGraphFixed
import PallLean.Paper93.Paper283.TseitinCharge
import PallLean.Paper93.Paper283.SubgradientSgn

namespace PallLean.Paper93.Paper283

open PallLean.Paper93.Concrete
open scoped BigOperators

/--
  **Graph Laplacian as a linear operator on `Fin N → ℝ`**.

  For a `d`-regular graph `G : RegularGraphFixed N d`, the Laplacian
  `L = d · I − A` acts on a field `Φ : Fin N → ℝ` as

      (L · Φ)(v)  =  d · Φ(v)  −  Σ_{(v, w) ∈ G.edges} Φ(w).

  At the task's paper-faithful level, this is the canonical action of
  the textbook graph Laplacian on real-valued vertex functions; it is
  the operator form of the `graphLaplacian` matrix on `RegularGraph`
  (`PallLean/Paper93/Concrete/GraphLaplacian.lean`), pulled across to
  the hypothesis-free `RegularGraphFixed` type of `RegularGraphFixed.lean`.
-/
noncomputable def graphLaplacianOp {N d : ℕ}
    (G : RegularGraphFixed N d) (Φ : Fin N → ℝ) (v : Fin N) : ℝ :=
  (d : ℝ) * Φ v - ∑ e ∈ G.edges.filter (fun e : Fin N × Fin N => e.1 = v),
                    Φ e.2

/--
  **Real Euler–Lagrange stationary-Φ predicate** (paper §28.3 line 6878).

  For each vertex `v ∈ V_n = Fin N`, `α · (L · Φ)(v)` must lie in the
  set `(β/2) · χ(v) · ∂ sgn(Φ(v))`, i.e. there exists a subgradient
  `g ∈ ∂ sgn(Φ(v))` such that

      α · (L · Φ)(v)  =  (β/2) · χ(v) · g.

  This is the faithful Euler–Lagrange condition `δΦ S_NF = 0` of paper
  §28.3 line 6878, with `L = graphLaplacianOp G` and
  `∂ sgn = subgradientSgn`.
-/
def RealStationaryPhi {N d : ℕ} (α β : ℝ)
    (G : RegularGraphFixed N d) (χ : TseitinCharge N) (Φ : Fin N → ℝ) :
    Prop :=
  ∀ v : Fin N,
    α * graphLaplacianOp G Φ v ∈
      {y : ℝ | ∃ g ∈ subgradientSgn (Φ v),
                 y = (β / 2) * ((χ v).val : ℝ) * g}

/-- **Zero field satisfies real stationarity.**

    For the zero field `Φ ≡ 0`:
      * `graphLaplacianOp G 0 v = d · 0 − Σ 0 = 0`, so the LHS is
        `α · 0 = 0`.
      * The subgradient of `sgn` at `0` is the interval `[−1, +1]`,
        which contains `0`.
      * The RHS is `(β/2) · χ(v) · 0 = 0`.

    Hence `0 ∈ (β/2) · χ(v) · ∂ sgn(0)` with witness `g = 0`, which
    matches the LHS `0`. This exhibits a concrete `RealStationaryPhi`
    witness for every `α, β, G, χ`, discharging the existence side of
    the Y3 paper-faithful Euler–Lagrange predicate.
-/
theorem RealStationaryPhi_zero {N d : ℕ} (α β : ℝ)
    (G : RegularGraphFixed N d) (χ : TseitinCharge N) :
    RealStationaryPhi (N := N) (d := d) α β G χ (fun _ => 0) := by
  intro v
  refine ⟨0, ?_, ?_⟩
  · -- `0 ∈ subgradientSgn 0 = [-1, 1]`
    have h0 : subgradientSgn (0 : ℝ) = Set.Icc (-1 : ℝ) 1 :=
      subgradientSgn_zero
    rw [h0]
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩ <;> linarith
  · -- LHS `α · (L · 0)(v) = 0`, RHS `(β/2) · χ(v) · 0 = 0`.
    have hL : graphLaplacianOp G (fun _ : Fin N => (0 : ℝ)) v = 0 := by
      unfold graphLaplacianOp
      simp
    rw [hL]
    ring

/-- **Existence of a real-stationary Φ.**

    For every Reynolds-style input `(α, β, G, χ)` there exists a
    concrete `Φ : Fin N → ℝ` satisfying the real Euler–Lagrange
    stationary-Φ predicate; the zero field of
    `RealStationaryPhi_zero` is such a witness. -/
theorem RealStationaryPhi_nonempty_witness {N d : ℕ} (α β : ℝ)
    (G : RegularGraphFixed N d) (χ : TseitinCharge N) :
    ∃ Φ : Fin N → ℝ, RealStationaryPhi (N := N) (d := d) α β G χ Φ :=
  ⟨fun _ => 0, RealStationaryPhi_zero α β G χ⟩

end PallLean.Paper93.Paper283
