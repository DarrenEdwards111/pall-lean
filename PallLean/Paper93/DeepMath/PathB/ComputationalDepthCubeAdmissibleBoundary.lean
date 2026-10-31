import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCubeBoundaryRestrict

/-!
# Cube admissible boundary: general observer cuts, `boundaryCubeRank`, fragility vs robustness

The single-coordinate boundary rung (`…CubeBoundaryRestrict`) showed the mechanism on one restriction.  This file lifts
it to a **general admissible boundary** — an observer that sees a *subset* of coordinates and fixes the rest — and proves
the fragility/robustness split at that generality.  This is the boundary-first correction of the cube-native Godmove
route: measure not the raw derivative span, but derivative features *visible through a boundary*.

  `CubeBoundary n := Fin n → Option Bool` — a partial assignment: `none` = **visible** (free) coordinate, `some b` =
        **hidden** coordinate fixed to `b`.  `visible ρ` is the free set.
  `restrictB ρ f x = f (fun k => (ρ k).getD (x k))` — the projection: fix hidden coordinates, read visible ones from `x`.
  `boundaryCubeRank ρ κ f := cubeDerivRank κ (restrictB ρ f)` — derivative rank visible through `ρ`.  (Derivatives in
        *hidden* directions vanish automatically, so this counts only visible-direction features.)

**Cube-invariance** is inherited: `restrictB` reads only cube values, so `boundaryCubeRank` is a function of the
cube-function (the C9 fix persists through the boundary).

**Fragility of `∏Xᵢ` (proved)** — any boundary that hides one coordinate at `false` annihilates it:
  `restrictB_fullAnd_eq_zero`, `boundaryCubeRank_fullAnd_eq_zero` — `boundaryCubeRank ρ κ (boolFn ∏Xⱼ) = 0`.

**Robustness of parity (proved)** — the character survives *every* boundary and stays eigen-structured on visible cuts:
  `restrictPoint_flip_comm`, `cubeDeriv_restrictB_chiFull` — for a visible `j`, `Δⱼ(restrictB ρ χ) = −2·(restrictB ρ χ)`.
  `restrictB_chiFull_ne_zero` — `restrictB ρ χ ≠ 0` for every `ρ`.
  `one_le_boundaryCubeRank_chiFull` — with one visible coordinate and `2 ≠ 0`, `boundaryCubeRank ρ 1 χ ≥ 1`.

`boundary_separates_fullAnd_parity_general` bundles it: through any admissible boundary hiding some `i` at `false` and
leaving some `j` visible, the easy `∏Xᵢ` has boundary-rank `0` while parity has boundary-rank `≥ 1` — the correct
hardness order, at general-boundary generality.

## Honest scope

This is HAL's step 1–3 + the two sanity witnesses (steps "product/AND fragility" and "parity/MOD robustness") for the
general boundary.  It does **not** yet do steps 4–8: classifying *all* shallow `∑∏`/BT/SYM-count forms as
boundary-compressible, the composite-MOD incompatible-field observer argument, the global dual separator (the actual
"Cube Godmove"), or the Williams bridge.  Those are the load-bearing rungs and are not built here (and not fakeable).
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.NFrameACC0 (boolFn)

variable {n : ℕ} {F : Type*} [Field F]

/-- A **cube admissible boundary**: a partial assignment.  `none` = visible (free) coordinate, `some b` = hidden
coordinate fixed to `b`. -/
def CubeBoundary (n : ℕ) : Type := Fin n → Option Bool

/-- The visible (free) coordinates of a boundary. -/
def visible (ρ : Fin n → Option Bool) : Finset (Fin n) := Finset.univ.filter (fun i => ρ i = none)

/-- The boundary **projection**: fix hidden coordinates to their values, read visible ones from `x`. -/
def restrictB (ρ : Fin n → Option Bool) (f : (Fin n → Bool) → F) : (Fin n → Bool) → F :=
  fun x => f (fun k => (ρ k).getD (x k))

/-- **Boundary cube-derivative rank**: derivative features of `f` visible through the boundary `ρ`. -/
noncomputable def boundaryCubeRank (ρ : Fin n → Option Bool) (κ : ℕ) (f : (Fin n → Bool) → F) : ℕ :=
  cubeDerivRank κ (restrictB ρ f)

/-- **Cube-invariance through the boundary (proved)**: `boundaryCubeRank` depends only on the cube-function — cube-agreeing
polynomials have equal boundary rank (the C9 fix persists). -/
theorem boundaryCubeRank_cubeInvariant (ρ : Fin n → Option Bool) {κ : ℕ}
    {p q : MvPolynomial (Fin n) F}
    (h : PallLean.Paper93.DeepMath.PathB.SPDPApprox.AgreeOnCube p q) :
    boundaryCubeRank ρ κ (boolFn p) = boundaryCubeRank ρ κ (boolFn q) := by
  rw [boundaryCubeRank, boundaryCubeRank, agreeOnCube_boolFn_eq h]

/-- **Fragility of `∏Xᵢ` (proved)**: any boundary hiding one coordinate at `false` annihilates the full `AND`. -/
theorem restrictB_fullAnd_eq_zero (ρ : Fin n → Option Bool) (i : Fin n) (hi : ρ i = some false) :
    restrictB ρ (boolFn (∏ j, X j : MvPolynomial (Fin n) F)) = 0 := by
  funext x
  simp only [restrictB, boolFn, Pi.zero_apply, map_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [MvPolynomial.eval_X]
  simp [hi]

/-- **Fragility in boundary rank (proved)**: `boundaryCubeRank ρ κ (boolFn ∏Xⱼ) = 0` through such a boundary. -/
theorem boundaryCubeRank_fullAnd_eq_zero (ρ : Fin n → Option Bool) (i : Fin n) (hi : ρ i = some false)
    {κ : ℕ} : boundaryCubeRank ρ κ (boolFn (∏ j, X j : MvPolynomial (Fin n) F)) = 0 := by
  rw [boundaryCubeRank, restrictB_fullAnd_eq_zero ρ i hi, cubeDerivRank_zero]

/-- **Robustness of parity (proved)**: the character survives *every* boundary — `restrictB ρ χ ≠ 0`. -/
theorem restrictB_chiFull_ne_zero (ρ : Fin n → Option Bool) :
    restrictB ρ (chiFull : (Fin n → Bool) → F) ≠ 0 := by
  intro h
  have hx := congrFun h (fun _ => false)
  rw [restrictB, Pi.zero_apply] at hx
  exact chiFull_ne_zero _ hx

/-- The projected point commutes with a flip on any **visible** coordinate. -/
theorem restrictPoint_flip_comm (ρ : Fin n → Option Bool) {j : Fin n} (hj : ρ j = none)
    (x : Fin n → Bool) :
    (fun k => (ρ k).getD ((flipBit j x) k)) = flipBit j (fun k => (ρ k).getD (x k)) := by
  funext k
  simp only [flipBit]
  by_cases hkj : k = j
  · subst hkj; rw [if_pos rfl, if_pos rfl, hj, Option.getD_none, Option.getD_none]
  · rw [if_neg hkj, if_neg hkj]

/-- **Robustness of the eigenstructure through the boundary (proved)**: for a visible coordinate `j`, the projected
character is still an eigenfunction — `Δⱼ(restrictB ρ χ) = −2·(restrictB ρ χ)`. -/
theorem cubeDeriv_restrictB_chiFull (ρ : Fin n → Option Bool) {j : Fin n} (hj : ρ j = none) :
    cubeDeriv j (restrictB ρ (chiFull : (Fin n → Bool) → F))
      = (-2 : F) • restrictB ρ chiFull := by
  funext x
  simp only [cubeDeriv, restrictB, Pi.smul_apply, smul_eq_mul]
  rw [restrictPoint_flip_comm ρ hj, chiFull_flip]
  ring

/-- **Robustness in boundary rank (proved)**: with a visible coordinate and `2 ≠ 0`, parity keeps
`boundaryCubeRank ρ 1 χ ≥ 1`. -/
theorem one_le_boundaryCubeRank_chiFull (ρ : Fin n → Option Bool) {j : Fin n} (hj : ρ j = none)
    (h2 : (2 : F) ≠ 0) : 1 ≤ boundaryCubeRank ρ 1 (chiFull : (Fin n → Bool) → F) := by
  have hne : cubeDeriv j (restrictB ρ (chiFull : (Fin n → Bool) → F)) ≠ 0 := by
    rw [cubeDeriv_restrictB_chiFull ρ hj]
    exact smul_ne_zero (neg_ne_zero.mpr h2) (restrictB_chiFull_ne_zero ρ)
  have hmem : cubeDeriv j (restrictB ρ (chiFull : (Fin n → Bool) → F))
      ∈ cubeDerivSpan 1 (restrictB ρ chiFull) :=
    Submodule.subset_span ⟨[j], rfl, rfl⟩
  rw [boundaryCubeRank, cubeDerivRank, Nat.one_le_iff_ne_zero]
  intro hz
  rw [Submodule.finrank_eq_zero] at hz
  rw [hz, Submodule.mem_bot] at hmem
  exact hne hmem

/-- **The general-boundary separation (proved)**: through any admissible boundary hiding some `i` at `false` and leaving
some `j` visible, the easy `∏Xᵢ` has boundary-rank `0` (fragile) while parity has boundary-rank `≥ 1` (robust) — the
correct hardness order, at general-boundary generality (the cube-native Part C split). -/
theorem boundary_separates_fullAnd_parity_general
    (ρ : Fin n → Option Bool) (i : Fin n) (hi : ρ i = some false)
    {j : Fin n} (hj : ρ j = none) (h2 : (2 : F) ≠ 0) {κ : ℕ} :
    boundaryCubeRank ρ κ (boolFn (∏ k, X k : MvPolynomial (Fin n) F)) = 0
      ∧ 1 ≤ boundaryCubeRank ρ 1 (chiFull : (Fin n → Bool) → F) :=
  ⟨boundaryCubeRank_fullAnd_eq_zero ρ i hi, one_le_boundaryCubeRank_chiFull ρ hj h2⟩

end PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.boundaryCubeRank_cubeInvariant
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.boundaryCubeRank_fullAnd_eq_zero
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.boundary_separates_fullAnd_parity_general
