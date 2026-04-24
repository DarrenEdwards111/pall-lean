/-
  PallLean/Paper93/DeepMath/NFrame/ParityPenaltyAtNoZero.lean

  `parityPenalty` is locally constant on the smooth region `{Φ | ∀ i, Φ_i ≠ 0}`.

  Two statements:

  1. `parityPenalty_all_partials_zero_of_no_zero` — all partial
     derivatives of `parityPenalty` vanish at any `Φ` with no zero
     entries. This is a one-line wrapper around
     `parityPenalty_partial_zero_of_ne_zero`.

  2. `parityPenalty_locally_const_of_no_zero` — `parityPenalty chi · `
     is locally constant in the Pi-topology at any such `Φ`. The proof
     uses:
       * each `parityTerm (chi i) · ` is locally constant at `phi i ≠ 0`
         (from `sign_locally_eq_one` / `sign_locally_eq_neg_one`);
       * the coordinate projection `psi ↦ psi i` is continuous in the
         Pi-topology, so the per-coordinate eventual equality pulls
         back to `nhds phi`;
       * finite AND over `Fin n` via `eventually_all`;
       * `Finset.sum_congr` to rewrite each summand.

  Kernel-only; no `sorry`, no bespoke axioms, no `True`.
-/
import PallLean.Paper93.DeepMath.NFrame.ParityPenaltyDeriv
import PallLean.Paper93.DeepMath.NFrame.SignLocallyConst
import Mathlib.Topology.Constructions
import Mathlib.Order.Filter.Finite

namespace PallLean.Paper93.DeepMath.NFrame

open Filter Topology
open scoped BigOperators

/-- `parityPenalty` is locally constant at any Φ with no zero entries (smooth region):
    all partials vanish. One-line wrapper around
    `parityPenalty_partial_zero_of_ne_zero`. -/
theorem parityPenalty_all_partials_zero_of_no_zero {n : ℕ} (chi phi : Fin n → ℝ)
    (h : ∀ i, phi i ≠ 0) (k : Fin n) :
    HasDerivAt (fun t => parityPenalty chi (Function.update phi k t)) 0 (phi k) :=
  parityPenalty_partial_zero_of_ne_zero chi phi k (h k)

/-- `parityTerm chi_v ·` is eventually equal to its value at `phi_v` in a neighborhood of
    `phi_v ≠ 0`. This is the per-coordinate locally-constant fact, obtained by unfolding
    `parityTerm` and using `sign_locally_eq_one` / `sign_locally_eq_neg_one`. -/
theorem parityTerm_eventually_eq_of_ne_zero (chi_v phi_v : ℝ) (h : phi_v ≠ 0) :
    ∀ᶠ y in 𝓝 phi_v, parityTerm chi_v y = parityTerm chi_v phi_v := by
  rcases lt_or_gt_of_ne h with hneg | hpos
  · -- phi_v < 0: sign is eventually -1.
    filter_upwards [sign_locally_eq_neg_one phi_v hneg] with y hy
    unfold parityTerm
    rw [hy, Real.sign_of_neg hneg]
  · -- phi_v > 0: sign is eventually 1.
    filter_upwards [sign_locally_eq_one phi_v hpos] with y hy
    unfold parityTerm
    rw [hy, Real.sign_of_pos hpos]

/-- At any Φ with no zero entries, `parityPenalty chi` is locally constant near `phi` in the
    Pi-topology on `Fin n → ℝ`. -/
theorem parityPenalty_locally_const_of_no_zero {n : ℕ} (chi phi : Fin n → ℝ)
    (h : ∀ i, phi i ≠ 0) :
    ∀ᶠ psi in nhds phi, parityPenalty chi psi = parityPenalty chi phi := by
  -- Step 1: per-index eventual equality at `phi i`, pulled back along the
  -- continuous coordinate projection `psi ↦ psi i` to `nhds phi`.
  have hEach : ∀ i : Fin n, ∀ᶠ psi in nhds phi,
      parityTerm (chi i) (psi i) = parityTerm (chi i) (phi i) := by
    intro i
    have hTend : Tendsto (fun psi : Fin n → ℝ => psi i) (nhds phi) (nhds (phi i)) :=
      ((continuous_apply i).tendsto phi)
    exact hTend.eventually (parityTerm_eventually_eq_of_ne_zero (chi i) (phi i) (h i))
  -- Step 2: combine via `eventually_all` (finite AND over `Fin n`).
  have hAll : ∀ᶠ psi in nhds phi,
      ∀ i : Fin n, parityTerm (chi i) (psi i) = parityTerm (chi i) (phi i) :=
    eventually_all.2 hEach
  -- Step 3: rewrite each summand via `Finset.sum_congr`.
  filter_upwards [hAll] with psi hpsi
  unfold parityPenalty
  exact Finset.sum_congr rfl (fun i _hi => hpsi i)

end PallLean.Paper93.DeepMath.NFrame
