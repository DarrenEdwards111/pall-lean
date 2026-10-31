import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCubeBoundarySPDP

/-!
# Cube-native SPDP on AND / MOD: the parity character is an eigenfunction (rank ≤ 1)

The pilot (`…CubeBoundarySPDP`) established cube-derivative rank is well-defined, cube-invariant (the C9 fix), and
non-degenerate.  This file works out the AND/MOD rung — and it delivers an **honest, informative surprise**.

The `±1` parity **character** `χ(x) = ∏ₖ (−1)^{xₖ}` is an *eigenfunction* of every edge derivative:

  `chiFull_flip` — flipping one bit negates the character: `χ(x⊕eᵢ) = −χ(x)`.
  `cubeDeriv_chiFull` — hence `Δᵢχ = −2·χ` (eigenvalue `−2`).
  `cubeDerivList_chiFull` — every iterated derivative is `(−2)^{|L|}·χ`, all collinear.
  `cubeDerivRank_chiFull_le_one` — therefore **`cubeDerivRank κ χ ≤ 1`**: parity/`MOD`-type functions are *low* cube-rank.

## The honest finding — the naive measure is *inverted*

Contrast with the pilot's `one_le_cubeDerivRank_boolFn_X` (a variable/`AND` has rank `≥ 1`) and the Fourier picture: an
`AND` gate `∏_{i∈T} xᵢ` has Fourier support *all* of `2^{|T|}` subsets (spread across levels), so its cube-derivative
rank is **high** (`C(|T|,κ)` for the full product `T = [n]`), while parity `χ` is concentrated on a *single* character and
has rank `≤ 1` (**low**).

So the *raw* cube-derivative rank measures **Fourier spread**, not hardness: the easy full-`AND` `∏xᵢ` is high and the
harder parity is low — the **opposite** of what a hardness measure needs.  This is exactly the C0/C9 lesson recurring in
the cube-native world: like raw `spdpRank` (high for the easy `∏Xᵢ`), the raw cube-rank is *not* a hardness measure.

**Consequence (the honest redirect):** the separation cannot come from raw cube-rank; it must come from the
**boundary/admissible-observer refinement** (HAL's "under admissible observer boundaries") — the cube-native
reincarnation of the Part C boundary invariant, which distinguished the robust permanent from the fragile `∏Xᵢ`.  That is
the genuinely next step; this rung proves it is *needed* (rather than chasing a measure that inverts hardness).  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

variable {n : ℕ} {F : Type*} [Field F]

/-- The `±1` parity **character** on the cube: `χ(x) = ∏ₖ (−1)^{xₖ}`. -/
def chiFull (x : Fin n → Bool) : F := ∏ k, (if x k then (-1 : F) else 1)

/-- **Flipping one bit negates the parity character (proved)**: `χ(x⊕eᵢ) = −χ(x)`. -/
theorem chiFull_flip (i : Fin n) (x : Fin n → Bool) :
    chiFull (flipBit i x) = - (chiFull x : F) := by
  unfold chiFull
  rw [← Finset.mul_prod_erase Finset.univ (fun k => if (flipBit i x) k then (-1:F) else 1) (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ (fun k => if x k then (-1:F) else 1) (Finset.mem_univ i)]
  rw [Finset.prod_congr rfl (fun k hk => by
        show (if (flipBit i x) k then (-1:F) else 1) = (if x k then (-1:F) else 1)
        rw [flipBit, if_neg (Finset.ne_of_mem_erase hk)])]
  have hi : (if (flipBit i x) i then (-1:F) else 1) = -(if x i then (-1:F) else 1) := by
    rw [flipBit, if_pos rfl]; cases x i <;> simp
  rw [hi]; ring

/-- Cube derivative is linear in the function (scalar case). -/
theorem cubeDeriv_smul (c : F) (f : (Fin n → Bool) → F) (i : Fin n) :
    cubeDeriv i (c • f) = c • cubeDeriv i f := by
  funext x; simp only [cubeDeriv, Pi.smul_apply, smul_eq_mul, mul_sub]

/-- Iterated cube derivative is linear in the function (scalar case). -/
theorem cubeDerivList_smul (c : F) (L : List (Fin n)) (f : (Fin n → Bool) → F) :
    cubeDerivList L (c • f) = c • cubeDerivList L f := by
  induction L generalizing f with
  | nil => rfl
  | cons i L' ih =>
    show cubeDerivList L' (cubeDeriv i (c • f)) = c • cubeDerivList L' (cubeDeriv i f)
    rw [cubeDeriv_smul, ih]

/-- **The parity character is an eigenfunction (proved)**: `Δᵢχ = −2·χ`. -/
theorem cubeDeriv_chiFull (i : Fin n) :
    cubeDeriv i (chiFull : (Fin n → Bool) → F) = (-2 : F) • chiFull := by
  funext x
  simp only [cubeDeriv, chiFull_flip, Pi.smul_apply, smul_eq_mul]
  ring

/-- Every iterated derivative of the character is `(−2)^{|L|}·χ` — all collinear. -/
theorem cubeDerivList_chiFull (L : List (Fin n)) :
    cubeDerivList L (chiFull : (Fin n → Bool) → F) = ((-2 : F) ^ L.length) • chiFull := by
  induction L with
  | nil => simp [cubeDerivList]
  | cons i L' ih =>
    show cubeDerivList L' (cubeDeriv i chiFull) = _
    rw [cubeDeriv_chiFull, cubeDerivList_smul, ih, smul_smul]
    congr 1
    rw [List.length_cons, pow_succ]
    ring

/-- **The parity/`MOD` character has cube-derivative rank `≤ 1` (proved)** — it is *low*, being Fourier-concentrated on a
single character.  This is the honest finding: raw cube-rank measures Fourier spread, so it makes the *easy* `∏xᵢ` high
and the *harder* parity low — the boundary refinement is what's actually needed. -/
theorem cubeDerivRank_chiFull_le_one {κ : ℕ} :
    cubeDerivRank κ (chiFull : (Fin n → Bool) → F) ≤ 1 := by
  rw [cubeDerivRank]
  have hle : cubeDerivSpan κ (chiFull : (Fin n → Bool) → F) ≤ Submodule.span F {chiFull} := by
    rw [cubeDerivSpan, Submodule.span_le]
    rintro g ⟨L, hlen, rfl⟩
    rw [cubeDerivList_chiFull]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  refine le_trans (Submodule.finrank_mono hle) ?_
  simpa using finrank_span_le_card (R := F) ({chiFull} : Set ((Fin n → Bool) → F))

end PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.cubeDeriv_chiFull
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.cubeDerivRank_chiFull_le_one
