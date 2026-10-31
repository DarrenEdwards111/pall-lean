import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameProductBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSPDPApprox

/-!
# Cube-native SPDP: shifted derivatives on the hypercube graph (pilot)

C9 proved raw `spdpRank` is **not** cube-invariant (`0` and `X₀²−X₀` agree on the cube but have different rank).  The fix
is to move the "shifted partial / derivative span" idea onto the **hypercube graph** where Boolean functions actually
live — using *discrete* edge derivatives `Δᵢf(x) = f(x⊕eᵢ) − f(x)` instead of polynomial `pderiv`.

  `flipBit i x` / `cubeDeriv i f` — the Hamming-edge derivative `f(x with bit i flipped) − f(x)`.
  `cubeDerivList L f`, `cubeDerivSpan κ f`, `cubeDerivRank κ f` — the iterated derivative, its span, and its finrank in
        the (finite-dim) function space `(Fin n → Bool) → F`.

**The C9 fix (proved)**: `cubeDerivRank` is a function of the *cube-function* only, so it is automatically cube-invariant.
  `cubeDerivRank_cubeInvariant` — `AgreeOnCube p q ⟹ cubeDerivRank κ (boolFn p) = cubeDerivRank κ (boolFn q)`.
  `sqSub_cubeDerivRank_eq_zero_rank` — the concrete C9 witness: `boolFn (X₀²−X₀)` and `boolFn 0` have *equal*
        cube-derivative rank (they were the pair with *different* `spdpRank`).

**Sanity (proved)**:
  `cubeDerivRank_const` — constants have cube-derivative rank `0` (order `≥ 1`).
  `one_le_cubeDerivRank_boolFn_X` — a variable/`AND` has *nonzero* cube-derivative structure (`≥ 1`), so the measure is
        non-degenerate (distinguishes non-constants from constants).

## Honest scope

A **pilot**: it establishes that cube-native SPDP is well-defined, cube-invariant (the C9 fix), and non-degenerate on
`AND`/variables.  It does **not** yet prove the target bounds (low `∑∏`/BT rank, high `MOD_q` rank, admissible-boundary
preservation) — those are the next steps if this lands cleanly.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.NFrameACC0 (boolFn)
open PallLean.Paper93.DeepMath.PathB.SPDPApprox (AgreeOnCube)

variable {n : ℕ} {F : Type*} [Field F]

/-- Flip the `i`-th bit of a cube point. -/
def flipBit (i : Fin n) (x : Fin n → Bool) : Fin n → Bool := fun k => if k = i then !(x k) else x k

/-- The **discrete edge derivative** on the cube: `Δᵢf(x) = f(x⊕eᵢ) − f(x)`. -/
def cubeDeriv (i : Fin n) (f : (Fin n → Bool) → F) : (Fin n → Bool) → F :=
  fun x => f (flipBit i x) - f x

/-- Iterated cube derivative along a list of coordinates. -/
def cubeDerivList (L : List (Fin n)) (f : (Fin n → Bool) → F) : (Fin n → Bool) → F :=
  L.foldl (fun g i => cubeDeriv i g) f

/-- The order-`κ` cube-derivative span: span of all `κ`-fold edge derivatives. -/
noncomputable def cubeDerivSpan (κ : ℕ) (f : (Fin n → Bool) → F) : Submodule F ((Fin n → Bool) → F) :=
  Submodule.span F {g | ∃ L : List (Fin n), L.length = κ ∧ g = cubeDerivList L f}

/-- Cube-native SPDP rank: the dimension of the order-`κ` cube-derivative span. -/
noncomputable def cubeDerivRank (κ : ℕ) (f : (Fin n → Bool) → F) : ℕ :=
  Module.finrank F (cubeDerivSpan κ f)

theorem cubeDeriv_zero (i : Fin n) : cubeDeriv i (0 : (Fin n → Bool) → F) = 0 := by
  funext x; simp [cubeDeriv]

theorem cubeDerivList_zero (L : List (Fin n)) : cubeDerivList L (0 : (Fin n → Bool) → F) = 0 := by
  induction L with
  | nil => rfl
  | cons i L' ih =>
    show cubeDerivList L' (cubeDeriv i (0 : (Fin n → Bool) → F)) = 0
    rw [cubeDeriv_zero, ih]

theorem cubeDeriv_const (c : F) (i : Fin n) : cubeDeriv i (fun _ : (Fin n → Bool) => c) = 0 := by
  funext x; simp [cubeDeriv]

/-- **Constants have cube-derivative rank `0`** (order `≥ 1`). -/
theorem cubeDerivRank_const (c : F) {κ : ℕ} (hκ : 1 ≤ κ) :
    cubeDerivRank κ (fun _ : (Fin n → Bool) => c) = 0 := by
  have hbot : cubeDerivSpan κ (fun _ : (Fin n → Bool) => c) = ⊥ := by
    rw [cubeDerivSpan, Submodule.span_eq_bot]
    rintro g ⟨L, hlen, rfl⟩
    cases L with
    | nil => simp at hlen; omega
    | cons i L' =>
      show cubeDerivList L' (cubeDeriv i (fun _ : (Fin n → Bool) => c)) = 0
      rw [cubeDeriv_const, cubeDerivList_zero]
  rw [cubeDerivRank, hbot, finrank_bot]

/-- Cube-derivative rank depends only on the function (trivially). -/
theorem cubeDerivRank_congr {κ : ℕ} {f g : (Fin n → Bool) → F} (h : f = g) :
    cubeDerivRank κ f = cubeDerivRank κ g := by rw [h]

/-- Cube-agreeing polynomials have the same cube-function. -/
theorem agreeOnCube_boolFn_eq {p q : MvPolynomial (Fin n) F} (h : AgreeOnCube p q) :
    boolFn p = boolFn q := by
  funext x
  exact h (fun i => if x i then 1 else 0) (fun i => by by_cases hx : x i <;> simp [hx])

/-- **The C9 fix (proved)**: cube-derivative rank is cube-invariant — cube-agreeing polynomials have equal rank,
where `spdpRank` differed. -/
theorem cubeDerivRank_cubeInvariant {κ : ℕ} {p q : MvPolynomial (Fin n) F} (h : AgreeOnCube p q) :
    cubeDerivRank κ (boolFn p) = cubeDerivRank κ (boolFn q) :=
  cubeDerivRank_congr (agreeOnCube_boolFn_eq h)

/-- **The concrete C9 witness (proved)**: `boolFn (X₀²−X₀)` and `boolFn 0` — the pair C9 gave with *different* `spdpRank`
— have *equal* cube-derivative rank. -/
theorem sqSub_cubeDerivRank_eq_zero_rank {κ : ℕ} :
    cubeDerivRank κ (boolFn (X (0 : Fin 1) ^ 2 - X 0 : MvPolynomial (Fin 1) F))
      = cubeDerivRank κ (boolFn (0 : MvPolynomial (Fin 1) F)) :=
  cubeDerivRank_cubeInvariant PallLean.Paper93.DeepMath.PathB.SPDPApprox.agreeOnCube_sq_sub

/-- A variable's cube-function has a nonzero edge derivative (value `1` at the all-`false` point). -/
theorem cubeDeriv_boolFn_X_ne_zero (i : Fin n) :
    cubeDeriv i (boolFn (X i : MvPolynomial (Fin n) F)) ≠ 0 := by
  intro h
  have hx := congrFun h (fun _ => false)
  simp only [cubeDeriv, boolFn, flipBit, MvPolynomial.eval_X, Pi.zero_apply] at hx
  simp at hx

/-- **Non-degeneracy (proved)**: a variable/`AND` gate has cube-derivative rank `≥ 1` — the measure separates
non-constants from constants. -/
theorem one_le_cubeDerivRank_boolFn_X (i : Fin n) :
    1 ≤ cubeDerivRank 1 (boolFn (X i : MvPolynomial (Fin n) F)) := by
  have hmem : cubeDeriv i (boolFn (X i : MvPolynomial (Fin n) F))
      ∈ cubeDerivSpan 1 (boolFn (X i : MvPolynomial (Fin n) F)) := by
    apply Submodule.subset_span
    exact ⟨[i], rfl, rfl⟩
  rw [cubeDerivRank, Nat.one_le_iff_ne_zero]
  intro hz
  rw [Submodule.finrank_eq_zero] at hz
  rw [hz, Submodule.mem_bot] at hmem
  exact cubeDeriv_boolFn_X_ne_zero i hmem

end PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.cubeDerivRank_cubeInvariant
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.one_le_cubeDerivRank_boolFn_X
