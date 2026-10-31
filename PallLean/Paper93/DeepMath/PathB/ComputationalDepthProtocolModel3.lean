import PallLean.Paper93.DeepMath.PathB.ComputationalDepthProtocolModel2

/-!
# Communication protocol model 3: conditioning on the transcript kills correlation

The information-theoretic pay-off of the rectangle property.  For a **product**
input distribution `pX ⊗ pY`, conditioning on the transcript class leaves the two
inputs independent, so the conditional mutual information is zero:
`I(X ; Y | Π) = 0`.

We phrase the core for an abstract finite-valued **rectangle classifier**
`c : α × β → Z` (a function whose fibers are combinatorial rectangles, exactly the
shape `trans_cutPaste` gives the transcript).  Conditioned on a class value `z`
with positive mass, the joint input distribution factors as
`aliceCond ⊗ bobCond`, and `InfoTheory.mutualInfo_prodDist_eq_zero` finishes each
term; the zero-mass classes contribute `0` trivially.

* **`rectangleFn` / `rectangle_iff`** — the abstract rectangle property and its
  explicit product form (generalising ProtocolModel2's `trans_rectangle`);
* **`trans_rectangleFn` (proved)** — the transcript of any protocol is a rectangle
  classifier;
* **`classProb` / `condJoint`** — the class distribution `Π` and the conditional
  joint input given the class;
* **`condJoint_eq_prod` (proved)** — on a positive-mass class the conditional joint
  is the product `aliceCond ⊗ bobCond`;
* **`condMutualInfo_rectangle_eq_zero` (proved)** — `I(X ; Y | Π) = 0`.

The one honest gap to a fully protocol-instantiated statement: `List Bool` (the
transcript type) is not a `Fintype`, so invoking the core on a concrete protocol
means restricting to its finite realised-transcript set.  The classifier core and
`trans_rectangleFn` are the genuine content.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CommProtocol

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.InfoTheory

variable {α β Z τ : Type*}

/-! ## The abstract rectangle classifier (structural, no finiteness needed) -/

/-- Alice-consistency with class `z`: some `y` sends `(x,y)` to class `z`. -/
def aliceOKc (c : α × β → Z) (z : Z) (x : α) : Prop := ∃ y : β, c (x, y) = z

/-- Bob-consistency with class `z`: some `x` sends `(x,y)` to class `z`. -/
def bobOKc (c : α × β → Z) (z : Z) (y : β) : Prop := ∃ x : α, c (x, y) = z

/-- A **rectangle classifier**: the fibers of `c` are combinatorial rectangles
(cut-and-paste). -/
def rectangleFn (c : α × β → Z) : Prop :=
  ∀ (x : α) (y : β) (x' : α) (y' : β), c (x, y) = c (x', y') → c (x, y') = c (x', y')

/-- **The explicit rectangle factorisation (proved)** for an abstract classifier:
`c (x,y) = z ↔ aliceOKc z x ∧ bobOKc z y`. -/
theorem rectangle_iff (c : α × β → Z) (hc : rectangleFn c) (z : Z) (x : α) (y : β) :
    c (x, y) = z ↔ aliceOKc c z x ∧ bobOKc c z y := by
  constructor
  · intro h; exact ⟨⟨y, h⟩, ⟨x, h⟩⟩
  · rintro ⟨⟨y', hy'⟩, ⟨x', hx'⟩⟩
    have hcp := hc x y' x' y (hy'.trans hx'.symm)
    rw [hx'] at hcp
    exact hcp

/-- **The transcript is a rectangle classifier (proved)**: `trans_cutPaste`
repackaged as `rectangleFn`. -/
theorem trans_rectangleFn (P : Protocol α β τ) :
    rectangleFn (fun ab : α × β => trans P ab.1 ab.2) := by
  intro x y x' y' h
  exact trans_cutPaste P x y x' y' h

/-! ## The conditional distribution given the class, and `I(X;Y|Π)=0` -/

variable [Fintype α] [Fintype β] [Fintype Z]

/-- The class distribution `Π`: probability of transcript class `z` under `pX ⊗ pY`. -/
noncomputable def classProb (c : α × β → Z) (pX : α → ℝ) (pY : β → ℝ) (z : Z) : ℝ :=
  ∑ ab, if c ab = z then pX ab.1 * pY ab.2 else 0

/-- The conditional joint input distribution given the class `z`. -/
noncomputable def condJoint (c : α × β → Z) (pX : α → ℝ) (pY : β → ℝ) (z : Z) : α × β → ℝ :=
  fun ab => (if c ab = z then pX ab.1 * pY ab.2 else 0) / classProb c pX pY z

/-- Total `pX`-mass of the Alice-side of the class `z`. -/
noncomputable def aliceMass (c : α × β → Z) (pX : α → ℝ) (z : Z) : ℝ :=
  ∑ x, if aliceOKc c z x then pX x else 0

/-- Total `pY`-mass of the Bob-side of the class `z`. -/
noncomputable def bobMass (c : α × β → Z) (pY : β → ℝ) (z : Z) : ℝ :=
  ∑ y, if bobOKc c z y then pY y else 0

/-- The Alice-marginal of the conditional given class `z`. -/
noncomputable def aliceCond (c : α × β → Z) (pX : α → ℝ) (z : Z) : α → ℝ :=
  fun x => (if aliceOKc c z x then pX x else 0) / aliceMass c pX z

/-- The Bob-marginal of the conditional given class `z`. -/
noncomputable def bobCond (c : α × β → Z) (pY : β → ℝ) (z : Z) : β → ℝ :=
  fun y => (if bobOKc c z y then pY y else 0) / bobMass c pY z

/-- **The fiber weight factors (proved)**: the rectangle structure splits the joint
weight into an Alice-indicator and a Bob-indicator. -/
theorem indicator_scaled (c : α × β → Z) (pX : α → ℝ) (pY : β → ℝ) (z : Z)
    (hc : rectangleFn c) (ab : α × β) :
    (if c ab = z then pX ab.1 * pY ab.2 else 0)
      = (if aliceOKc c z ab.1 then pX ab.1 else 0) * (if bobOKc c z ab.2 then pY ab.2 else 0) := by
  by_cases hxy : c ab = z
  · obtain ⟨ha, hb⟩ := (rectangle_iff c hc z ab.1 ab.2).mp hxy
    rw [if_pos hxy, if_pos ha, if_pos hb]
  · rw [if_neg hxy]
    by_cases ha : aliceOKc c z ab.1
    · by_cases hb : bobOKc c z ab.2
      · exact absurd ((rectangle_iff c hc z ab.1 ab.2).mpr ⟨ha, hb⟩) hxy
      · rw [if_neg hb, mul_zero]
    · rw [if_neg ha, zero_mul]

/-- **The class distribution factors (proved)**: `Π(z) = aliceMass · bobMass`. -/
theorem classProb_factor (c : α × β → Z) (pX : α → ℝ) (pY : β → ℝ) (z : Z)
    (hc : rectangleFn c) :
    classProb c pX pY z = aliceMass c pX z * bobMass c pY z := by
  unfold classProb aliceMass bobMass
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl
    (fun a _ => Finset.sum_congr rfl (fun b _ => indicator_scaled c pX pY z hc (a, b)))

/-- **The conditional joint is a product (proved)**: `condJoint z = aliceCond ⊗ bobCond`. -/
theorem condJoint_eq_prod (c : α × β → Z) (pX : α → ℝ) (pY : β → ℝ) (z : Z)
    (hc : rectangleFn c) :
    condJoint c pX pY z = prodDist (aliceCond c pX z) (bobCond c pY z) := by
  funext ab
  simp only [condJoint, prodDist, aliceCond, bobCond]
  rw [classProb_factor c pX pY z hc, indicator_scaled c pX pY z hc ab, div_mul_div_comm]

/-- **The Alice-marginal sums to one (proved)** on a positive-mass class. -/
theorem aliceCond_sum (c : α × β → Z) (pX : α → ℝ) (z : Z) (hne : aliceMass c pX z ≠ 0) :
    ∑ x, aliceCond c pX z x = 1 := by
  simp only [aliceCond, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ hne

/-- **The Bob-marginal sums to one (proved)** on a positive-mass class. -/
theorem bobCond_sum (c : α × β → Z) (pY : β → ℝ) (z : Z) (hne : bobMass c pY z ≠ 0) :
    ∑ y, bobCond c pY z y = 1 := by
  simp only [bobCond, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ hne

/-- **Conditioning on the transcript class kills correlation (proved)**:
for a product input distribution and a rectangle classifier `c`,
`I(X ; Y | Π) = 0`. -/
theorem condMutualInfo_rectangle_eq_zero (c : α × β → Z) (pX : α → ℝ) (pY : β → ℝ)
    (hc : rectangleFn c) :
    avgMutualInfo (classProb c pX pY) (condJoint c pX pY) = 0 := by
  simp only [avgMutualInfo]
  refine Finset.sum_eq_zero (fun z _ => ?_)
  by_cases hz : classProb c pX pY z = 0
  · rw [hz, zero_mul]
  · rw [classProb_factor c pX pY z hc] at hz
    obtain ⟨haM, hbM⟩ := mul_ne_zero_iff.mp hz
    have hmi : mutualInfo (condJoint c pX pY z) = 0 := by
      rw [condJoint_eq_prod c pX pY z hc]
      exact mutualInfo_prodDist_eq_zero (aliceCond_sum c pX z haM) (bobCond_sum c pY z hbM)
    rw [hmi, mul_zero]

end PallLean.Paper93.DeepMath.PathB.CommProtocol

#print axioms PallLean.Paper93.DeepMath.PathB.CommProtocol.trans_rectangleFn
#print axioms PallLean.Paper93.DeepMath.PathB.CommProtocol.condJoint_eq_prod
#print axioms PallLean.Paper93.DeepMath.PathB.CommProtocol.condMutualInfo_rectangle_eq_zero
