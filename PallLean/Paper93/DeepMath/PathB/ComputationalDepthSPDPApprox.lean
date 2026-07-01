import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCNormalForm

/-!
# Approximation-aware SPDP: agreement on the cube, and why `spdpRank` is not the right measure

Razborov–Smolensky delivers an `AC⁰[p]` circuit as a low-degree polynomial that **agrees with the circuit on a large
fraction of the Boolean cube** — not an exact polynomial identity.  This file formalises the honest consequences for the
SPDP machinery.

**Positive (error decomposition).**
  `spdpRank_normalForm_add_error_le` — for any `f`, splitting off an ACC normal form `h = ∑_{i<s}∏_{j<m} Q_{ij}`
        (`deg Q_{ij} ≤ t`) gives `spdpRank κ 0 f ≤ s·(#{J:|J|≤κ})·finrank(restrictTotalDegree κt) + spdpRank κ 0 (f−h)`.
        The residual difficulty is localised in the *error* `e = f − h`.

**The obstruction (why agreement is not enough).**
  `spdpRank_not_cubeInvariant` — two polynomials that agree on the *entire* cube can have **different** `spdpRank`:
        `0` and `X₀²−X₀` both vanish on `{0,1}`, yet `spdpRank 0 0 0 = 0 < 1 ≤ spdpRank 0 0 (X₀²−X₀)`.
        `X₀²−X₀` is a nonzero cube-vanishing polynomial with positive SPDP rank.

So an RS-style approximation — which only pins down `f` on the cube — does **not** bound `spdpRank(f)`: the error `e`
can vanish on the whole cube while carrying arbitrary SPDP rank (it lives in the ideal `(Xᵢ²−Xᵢ)`).  This is the precise
reason the polynomial method uses a **cube-invariant** measure — the multilinear representative / low-degree approximant
dimension (in this repo: `NFrameComplexity` / `sqfSpan`, the effective-dimension deficit) — rather than the exact
`spdpRank`.  The honest bridge from `∑∏` normal forms to `ACC⁰[p]` runs through that cube-invariant layer, not through
raw shifted-partial rank.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SPDPApprox

open MvPolynomial Finset

variable {F : Type*} [Field F]

/-- `spdpRank κ ℓ 0 = 0`. -/
theorem spdpRank_zero {n κ ℓ : ℕ} : SPDP.spdpRank κ ℓ (0 : MvPolynomial (Fin n) F) = 0 := by
  have hbot : SPDP.spdpSubspace κ ℓ (0 : MvPolynomial (Fin n) F) = ⊥ := by
    rw [SPDP.spdpSubspace, Submodule.span_eq_bot]
    rintro x ⟨S, mm, -, -, rfl⟩
    rw [SPDPLowerBound.iterDerivList_zero, mul_zero]
  rw [SPDP.spdpRank, hbot, finrank_bot]

/-- A nonzero polynomial has order-`0` SPDP rank at least `1`. -/
theorem one_le_spdpRank_of_ne_zero {n : ℕ} (p : MvPolynomial (Fin n) F) (hp : p ≠ 0) :
    1 ≤ SPDP.spdpRank 0 0 p := by
  have hmem : p ∈ SPDP.spdpSubspace 0 0 p := by
    apply Submodule.subset_span
    exact ⟨[], 1, rfl, by simp, by simp [SPDP.iterDerivList]⟩
  haveI : FiniteDimensional F (SPDP.spdpSubspace 0 0 p) :=
    Submodule.finiteDimensional_of_le (NFrameSPDPBridge.spdpSubspace_le_restrictTotalDegree 0 0 p)
  rw [SPDP.spdpRank, Nat.one_le_iff_ne_zero]
  intro hz
  rw [Submodule.finrank_eq_zero] at hz
  rw [hz, Submodule.mem_bot] at hmem
  exact hp hmem

/-- **Positive: the error decomposition (proved)**.  Splitting off an ACC normal form localises the residual SPDP rank
in the error `f − ∑∏Q`. -/
theorem spdpRank_normalForm_add_error_le {n s m t : ℕ} (f : MvPolynomial (Fin n) F)
    (Q : Fin s → Fin m → MvPolynomial (Fin n) F) (ht : ∀ i j, (Q i j).totalDegree ≤ t) (κ : ℕ) :
    SPDP.spdpRank κ 0 f
      ≤ s * ((Finset.univ.filter (fun J : Finset (Fin m) => J.card ≤ κ)).card
          * Module.finrank F ↥(MvPolynomial.restrictTotalDegree (Fin n) F (κ * t)))
        + SPDP.spdpRank κ 0 (f - ∑ i, ∏ j, Q i j) := by
  have hdecomp : f = (∑ i, ∏ j, Q i j) + (f - ∑ i, ∏ j, Q i j) := by ring
  calc SPDP.spdpRank κ 0 f
      = SPDP.spdpRank κ 0 ((∑ i, ∏ j, Q i j) + (f - ∑ i, ∏ j, Q i j)) := by rw [← hdecomp]
    _ ≤ SPDP.spdpRank κ 0 (∑ i, ∏ j, Q i j) + SPDP.spdpRank κ 0 (f - ∑ i, ∏ j, Q i j) :=
        SPDPLowerBound.spdpRank_add_le κ 0 _ _
    _ ≤ _ := Nat.add_le_add_right (SPDPUpperBound.spdpRank_sumProd_le Q ht κ) _

/-- Two polynomials agree on the Boolean cube if they evaluate equally at every `{0,1}`-point. -/
def AgreeOnCube {n : ℕ} (f g : MvPolynomial (Fin n) F) : Prop :=
  ∀ x : Fin n → F, (∀ i, x i = 0 ∨ x i = 1) → eval x f = eval x g

/-- `X₀²−X₀` vanishes on the cube (agrees with `0`). -/
theorem agreeOnCube_sq_sub : AgreeOnCube (X (0 : Fin 1) ^ 2 - X 0) (0 : MvPolynomial (Fin 1) F) := by
  intro x hx
  simp only [map_sub, map_pow, MvPolynomial.eval_X, map_zero]
  rcases hx 0 with h | h <;> rw [h] <;> ring

/-- `X₀²−X₀` is a nonzero polynomial. -/
theorem sq_sub_ne_zero : (X (0 : Fin 1) ^ 2 - X 0 : MvPolynomial (Fin 1) F) ≠ 0 := by
  intro hz
  have hc : MvPolynomial.coeff (Finsupp.single 0 2)
      (X (0 : Fin 1) ^ 2 - X 0 : MvPolynomial (Fin 1) F) = 0 := by rw [hz, MvPolynomial.coeff_zero]
  rw [MvPolynomial.coeff_sub, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial, if_pos rfl,
    MvPolynomial.coeff_X', if_neg (fun h => by simpa using DFunLike.congr_fun h 0)] at hc
  simp at hc

/-- **The obstruction (proved)**: `spdpRank` is *not* determined by agreement on the cube — two cube-agreeing
polynomials can have different SPDP rank.  Hence an RS-style approximation (which only pins `f` down on the cube) does
not bound `spdpRank(f)`. -/
theorem spdpRank_not_cubeInvariant :
    ∃ f g : MvPolynomial (Fin 1) F, AgreeOnCube f g ∧ SPDP.spdpRank 0 0 f ≠ SPDP.spdpRank 0 0 g := by
  refine ⟨X (0 : Fin 1) ^ 2 - X 0, 0, agreeOnCube_sq_sub, ?_⟩
  rw [spdpRank_zero]
  exact Nat.one_le_iff_ne_zero.mp (one_le_spdpRank_of_ne_zero _ sq_sub_ne_zero)

end PallLean.Paper93.DeepMath.PathB.SPDPApprox

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPApprox.spdpRank_normalForm_add_error_le
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPApprox.spdpRank_not_cubeInvariant
