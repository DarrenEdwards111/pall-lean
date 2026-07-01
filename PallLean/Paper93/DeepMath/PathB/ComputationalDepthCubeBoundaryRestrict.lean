import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCubeBoundarySPDPParity

/-!
# Cube-native admissible boundary: robust parity vs fragile `∏Xᵢ` under subcube restriction

The AND/MOD rung (`…CubeBoundarySPDPParity`) showed *raw* cube-derivative rank inverts hardness (easy `∏xᵢ` high, hard
parity low) and concluded the separation must come from the **boundary refinement** — the cube-native reincarnation of
the Part C admissible boundary that distinguished the robust permanent from the fragile `∏Xᵢ`.  This file builds that
boundary and proves it flips the picture the right way.

A **cube boundary** is a subcube restriction: fix coordinate `i` to a value `b`.

  `restrictCoord i b f x = f (update x i b)` — restrict `f` to the subcube `{xᵢ = b}`.

**Fragility of `∏Xᵢ` (proved)** — a single `false`-restriction annihilates it:
  `restrictCoord_fullAnd_eq_zero` — `restrictCoord i false (boolFn ∏Xⱼ) = 0`.
  `cubeDerivRank_restrictCoord_fullAnd_eq_zero` — hence its cube-rank *drops to `0`* under the boundary.

**Robustness of parity (proved)** — restriction preserves the character's eigenstructure and never annihilates it:
  `flipBit_update_comm` — flips and updates on distinct coordinates commute.
  `cubeDeriv_restrictCoord_chiFull` — for `j ≠ i`, `Δⱼ (restrictCoord i b χ) = −2·(restrictCoord i b χ)`: the eigenvalue
        `−2` survives on every *free* coordinate.
  `restrictCoord_chiFull_ne_zero` — `restrictCoord i b χ ≠ 0` for *every* restriction: parity never collapses.

`boundary_separates_fullAnd_parity` bundles the contrast: under the boundary the fragile `∏Xᵢ` has cube-rank `0` while
parity stays nonzero (and eigen-structured).  So the **boundary-refined** cube-rank ranks parity/`MOD` *above* `∏Xᵢ` —
the correct hardness direction, exactly the Part C robust-vs-fragile split, now cube-native.

## Honest scope

This is the *right refinement mechanism* proved on the two extreme witnesses (`∏Xᵢ` fragile, parity robust) — the
cube-native analog of `permPoly_blockBoundary_ne_zero` vs `permPoly_restrictRow_zero`.  It does **not** yet give a general
boundary-robust rank lower bound for a full `MOD_q`/permanent family under *all* admissible boundaries — that quantified
statement (the cube-native Part C theorem) is the next rung.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.NFrameACC0 (boolFn)

variable {n : ℕ} {F : Type*} [Field F]

/-- A **cube boundary**: restrict `f` to the subcube `{xᵢ = b}` by fixing coordinate `i` to `b`. -/
def restrictCoord (i : Fin n) (b : Bool) (f : (Fin n → Bool) → F) : (Fin n → Bool) → F :=
  fun x => f (Function.update x i b)

/-- The order-`κ` cube-derivative rank of the zero function is `0`. -/
theorem cubeDerivRank_zero {κ : ℕ} : cubeDerivRank κ (0 : (Fin n → Bool) → F) = 0 := by
  have hbot : cubeDerivSpan κ (0 : (Fin n → Bool) → F) = ⊥ := by
    rw [cubeDerivSpan, Submodule.span_eq_bot]
    rintro g ⟨L, hlen, rfl⟩
    exact cubeDerivList_zero L
  rw [cubeDerivRank, hbot, finrank_bot]

/-- **Fragility of `∏Xᵢ` (proved)**: a single `false`-restriction annihilates the full `AND`. -/
theorem restrictCoord_fullAnd_eq_zero (i : Fin n) :
    restrictCoord i false (boolFn (∏ j, X j : MvPolynomial (Fin n) F)) = 0 := by
  funext x
  show boolFn (∏ j, X j : MvPolynomial (Fin n) F) (Function.update x i false) = 0
  rw [boolFn, map_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [MvPolynomial.eval_X, Function.update_self]
  simp

/-- **Fragility in rank (proved)**: under the `false`-boundary the full `AND`'s cube-rank drops to `0`. -/
theorem cubeDerivRank_restrictCoord_fullAnd_eq_zero (i : Fin n) {κ : ℕ} :
    cubeDerivRank κ (restrictCoord i false (boolFn (∏ j, X j : MvPolynomial (Fin n) F))) = 0 := by
  rw [restrictCoord_fullAnd_eq_zero, cubeDerivRank_zero]

/-- The parity character is nowhere zero (a product of units `±1`). -/
theorem chiFull_ne_zero (x : Fin n → Bool) : (chiFull x : F) ≠ 0 := by
  rw [chiFull, Finset.prod_ne_zero_iff]
  intro k _
  cases x k <;> simp

/-- **Robustness of parity (proved)**: `restrictCoord i b χ ≠ 0` for *every* restriction — parity never collapses. -/
theorem restrictCoord_chiFull_ne_zero (i : Fin n) (b : Bool) :
    restrictCoord i b (chiFull : (Fin n → Bool) → F) ≠ 0 := by
  intro h
  have hx := congrFun h (fun _ => false)
  rw [restrictCoord, Pi.zero_apply] at hx
  exact chiFull_ne_zero _ hx

/-- Flips and updates on **distinct** coordinates commute. -/
theorem flipBit_update_comm {i j : Fin n} (hij : j ≠ i) (b : Bool) (x : Fin n → Bool) :
    Function.update (flipBit j x) i b = flipBit j (Function.update x i b) := by
  funext k
  simp only [flipBit, Function.update_apply]
  by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all

/-- **Robustness of the eigenstructure (proved)**: for a *free* coordinate `j ≠ i`, the restricted character is still an
eigenfunction with eigenvalue `−2` — `Δⱼ (restrictCoord i b χ) = −2·(restrictCoord i b χ)`.  The cube-derivative
structure survives the boundary on every free direction. -/
theorem cubeDeriv_restrictCoord_chiFull {i j : Fin n} (hij : j ≠ i) (b : Bool) :
    cubeDeriv j (restrictCoord i b (chiFull : (Fin n → Bool) → F))
      = (-2 : F) • restrictCoord i b chiFull := by
  funext x
  simp only [cubeDeriv, restrictCoord, Pi.smul_apply, smul_eq_mul]
  rw [flipBit_update_comm hij, chiFull_flip]
  ring

/-- **The boundary separates them (proved)**: under a `false`-boundary the fragile `∏Xᵢ` has cube-rank `0`, while parity
survives (nonzero) under *every* restriction — so boundary-refined cube-rank ranks parity/`MOD` above `∏Xᵢ`, the correct
hardness direction (cube-native Part C robust-vs-fragile split). -/
theorem boundary_separates_fullAnd_parity (i : Fin n) {κ : ℕ} :
    cubeDerivRank κ (restrictCoord i false (boolFn (∏ j, X j : MvPolynomial (Fin n) F))) = 0
      ∧ (∀ b : Bool, restrictCoord i b (chiFull : (Fin n → Bool) → F) ≠ 0) :=
  ⟨cubeDerivRank_restrictCoord_fullAnd_eq_zero i, fun b => restrictCoord_chiFull_ne_zero i b⟩

end PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.cubeDerivRank_restrictCoord_fullAnd_eq_zero
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.cubeDeriv_restrictCoord_chiFull
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.boundary_separates_fullAnd_parity
