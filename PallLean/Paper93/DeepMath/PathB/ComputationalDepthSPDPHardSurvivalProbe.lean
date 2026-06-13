import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSPDPFeatureProjection

/-!
# A3 survival probe: does a concrete Tseitin-style residual survive the SPDP projection?

The decisive test for the projected-rank path is A3 on a *concrete* hard family.  This file runs the first probe
on the cleanest Tseitin-flavored object: the **inner-product / parity cut matrix**

`ipMatrix u v = ⟨u, v⟩ = ⊕_i u_i v_i`

— the `F₂` bilinear core of Tseitin parity constraints.  Its rows `r_u(v) = ⟨u, v⟩` are the linear functionals; the
matrix has *full* raw rank `2^a` (distinct `u` give distinct functionals).

## Result: POSITIVE survival (proved, clean axioms)

* `ip_unitVec` — `⟨u, e_j⟩ = u_j`: the value at the `j`-th unit vector reads off the `j`-th coefficient.
* `crank_ipMatrix` — `crank (ipMatrix a) = 2^a` (full raw rank).
* `spdp_ipMatrix_survives` — **`pcrank (spdpProj a k d) (ipMatrix a) = 2^a` for `d ≥ 1`**: the SPDP projection is
  injective on all `2^a` rows, so the full rank survives.  The mechanism is exactly the predicted one — the
  feature space resolves the parity coefficients (here through the order-`0` coordinate at the unit vectors `e_j`,
  which are low-weight, hence retained).  A3 PASSES for the linear Tseitin core.
* `lowDeg_ipMatrix_survives` — and so does low-degree (`d ≥ 1`): the same `2^a`.

## Honest scope — what this probe does and does NOT settle

This is a *genuine* positive A3 survival: a high-rank, parity-structured cut matrix whose full rank survives the
SPDP projection, proved.  It confirms the projection preserves linear/parity structure — the sanity property any
viable SPDP route needs.

But it is the **linear core**, and honesty requires stating its limits sharply:

1. `ipMatrix` rows are **degree 1**, so they survive even *low-degree* (`lowDeg_ipMatrix_survives`) — this probe
   does **not** exhibit SPDP doing anything low-degree cannot.  Inner-product is also in `P` (it is not an
   NP-hard family).  So survival here does not by itself separate anything.
2. The decisive case is the **high-degree** Tseitin residual: rows that are indicators of affine subspaces
   `[A v = s_u]` (products of `rank A` parity forms), which low-degree *collapses* (they often vanish on all
   low-weight inputs).  Whether SPDP's order-`≤k` derivatives on low-weight inputs separate distinct syndromes
   `s_u` is exactly the SPDP-rank lower bound for Tseitin — barriered, and **not** resolved here.

So the probe's verdict is: the SPDP path clears its first, necessary test (it preserves the parity core), but the
load-bearing question — survival of the *high-degree* expander-Tseitin residual — remains the open
`P ≠ NP`-strength obligation.  The next probe should target a genuinely degree-`> 1` affine-indicator block, where
this file's `ip_unitVec`-style coefficient read-off no longer applies and real derivative structure is required.
-/

namespace PallLean.Paper93.DeepMath.PathB.SPDPHardSurvivalProbe

open PallLean.Paper93.DeepMath.PathB.RankContextualWidth
open PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank
open PallLean.Paper93.DeepMath.PathB.LowDegreeProjection
open PallLean.Paper93.DeepMath.PathB.SPDPFeatureProjection

variable {a : ℕ}

/-- The `j`-th unit vector `e_j`. -/
def unitVec (j : Fin a) : Fin a → Bool := fun i => decide (i = j)

/-- The unit vector has Hamming weight `1`. -/
theorem hw_unitVec (j : Fin a) : hw (unitVec j) = 1 := by
  unfold hw unitVec
  rw [show (Finset.univ.filter (fun i => (decide (i = j)) = true)) = {j} by
    ext i; simp [decide_eq_true_eq]]
  exact Finset.card_singleton j

/-- The inner product `⟨u, v⟩ = ⊕_i u_i v_i` over `F₂` (parity of the coordinatewise-AND support). -/
def ip (u v : Fin a → Bool) : Bool :=
  decide ((Finset.univ.filter (fun i => u i = true ∧ v i = true)).card % 2 = 1)

/-- **Coefficient read-off (proved): `⟨u, e_j⟩ = u_j`.** -/
theorem ip_unitVec (u : Fin a → Bool) (j : Fin a) : ip u (unitVec j) = u j := by
  have hset : (Finset.univ.filter (fun i => u i = true ∧ (unitVec j) i = true))
            = (Finset.univ.filter (fun i => i = j)).filter (fun i => u i = true) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro i _
    simp only [unitVec, decide_eq_true_eq]
    tauto
  unfold ip
  rw [hset, Finset.filter_eq' Finset.univ j]
  simp only [Finset.mem_univ, if_true]
  rw [Finset.filter_singleton]
  cases hu : u j <;> simp

/-- The inner-product / parity cut matrix. -/
def ipMatrix (a : ℕ) : (Fin a → Bool) → (Fin a → Bool) → Bool := fun u v => ip u v

/-- The rows of `ipMatrix` are distinct: distinct `u` give distinct linear functionals. -/
theorem ip_row_injective : Function.Injective (fun u : Fin a → Bool => (fun v => ip u v)) := by
  intro u u' h
  funext j
  have hj := congrFun h (unitVec j)
  simp only [ip_unitVec] at hj
  exact hj

/-- **Full raw rank (proved): `crank (ipMatrix a) = 2^a`.** -/
theorem crank_ipMatrix : crank (ipMatrix a) = 2 ^ a := by
  have hrfl : crank (ipMatrix a)
      = (Finset.univ.image (fun u : Fin a → Bool => (fun v => ip u v))).card := rfl
  rw [hrfl, Finset.card_image_of_injective _ ip_row_injective, Finset.card_univ]
  simp [Fintype.card_bool, Fintype.card_fin]

/-- The SPDP feature map is injective on the rows of `ipMatrix` (for `d ≥ 1`): the `S = ∅` coordinate at the unit
vector `e_j` reads off `u_j`, so the whole vector `u` is recovered. -/
theorem spdp_ip_factor_injective (k d : ℕ) (hd : 1 ≤ d) :
    Function.Injective (fun u : Fin a → Bool => spdpProj a k d (fun v => ip u v)) := by
  intro u u' h
  funext j
  have hj : hw (unitVec j) ≤ d := by rw [hw_unitVec]; exact hd
  have hcard : (∅ : Finset (Fin a)).card ≤ k := by simp
  have hco := congrFun h (⟨⟨∅, hcard⟩, ⟨unitVec j, hj⟩⟩ : {S : Finset (Fin a) // S.card ≤ k} × LowWt a d)
  simp only [spdpProj] at hco
  rw [derivSet_empty, derivSet_empty] at hco
  simp only [ip_unitVec] at hco
  exact hco

/-- **POSITIVE A3 survival (proved): `pcrank (spdpProj a k d) (ipMatrix a) = 2^a` for `d ≥ 1`.**  The SPDP
projection preserves the full rank of the parity cut matrix. -/
theorem spdp_ipMatrix_survives (k d : ℕ) (hd : 1 ≤ d) :
    pcrank (spdpProj a k d) (ipMatrix a) = 2 ^ a := by
  rw [pcrank_eq_image]
  simp only [ipMatrix]
  rw [Finset.card_image_of_injective _ (spdp_ip_factor_injective k d hd), Finset.card_univ]
  simp [Fintype.card_bool, Fintype.card_fin]

/-- The low-degree projection is injective on the rows of `ipMatrix` (for `d ≥ 1`): the value at `e_j` reads off
`u_j`. -/
theorem lowDeg_ip_factor_injective (d : ℕ) (hd : 1 ≤ d) :
    Function.Injective (fun u : Fin a → Bool => lowDegProj a d (fun v => ip u v)) := by
  intro u u' h
  funext j
  have hj : hw (unitVec j) ≤ d := by rw [hw_unitVec]; exact hd
  have hco := congrFun h (⟨unitVec j, hj⟩ : LowWt a d)
  simp only [lowDegProj, ip_unitVec] at hco
  exact hco

/-- **The parity core survives low-degree too (proved).**  `ipMatrix` rows are degree `1`, so even the low-degree
projection keeps the full rank `2^a` — this probe does not separate SPDP from low-degree. -/
theorem lowDeg_ipMatrix_survives (d : ℕ) (hd : 1 ≤ d) :
    pcrank (lowDegProj a d) (ipMatrix a) = 2 ^ a := by
  rw [pcrank_eq_image]
  simp only [ipMatrix]
  rw [Finset.card_image_of_injective _ (lowDeg_ip_factor_injective d hd), Finset.card_univ]
  simp [Fintype.card_bool, Fintype.card_fin]

end PallLean.Paper93.DeepMath.PathB.SPDPHardSurvivalProbe

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPHardSurvivalProbe.ip_unitVec
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPHardSurvivalProbe.crank_ipMatrix
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPHardSurvivalProbe.spdp_ipMatrix_survives
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPHardSurvivalProbe.lowDeg_ipMatrix_survives
