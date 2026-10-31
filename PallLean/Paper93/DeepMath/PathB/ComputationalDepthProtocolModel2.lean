import PallLean.Paper93.DeepMath.PathB.ComputationalDepthProtocolModel1

/-!
# Communication protocol model 2: the explicit rectangle factorisation

From the cut-and-paste property (ProtocolModel1) the transcript fiber factors as a
product: `(x,y)` produces transcript `w` iff `x` is consistent with `w` (some `y'`
gives `w`) **and** `y` is consistent with `w` (some `x'` gives `w`).  So the fiber
is literally `{x | aliceOK} × {y | bobOK}` — the info-theoretic rectangle that
InfoTheory8 needs (conditioned on the transcript, the inputs are independent).

* **`aliceOK` / `bobOK`** — Alice / Bob consistency with a transcript;
* **`trans_rectangle` (proved)** — `trans P x y = w ↔ aliceOK P w x ∧ bobOK P w y`;
* **`indicator_factor` (proved)** — the fiber indicator factors as a product of
  an Alice-indicator and a Bob-indicator (the algebraic form used by
  InfoTheory8's `prodDist`).

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CommProtocol

open scoped Classical

variable {α β τ : Type*}

/-- Alice-consistency: some `y'` makes `(x,y')` produce transcript `w`. -/
def aliceOK (P : Protocol α β τ) (w : List Bool) (x : α) : Prop := ∃ y', trans P x y' = w

/-- Bob-consistency: some `x'` makes `(x',y)` produce transcript `w`. -/
def bobOK (P : Protocol α β τ) (w : List Bool) (y : β) : Prop := ∃ x', trans P x' y = w

/-- **The rectangle factorisation (proved)**: the transcript fiber is the product
`{x | aliceOK} × {y | bobOK}`. -/
theorem trans_rectangle (P : Protocol α β τ) (w : List Bool) (x : α) (y : β) :
    trans P x y = w ↔ aliceOK P w x ∧ bobOK P w y := by
  constructor
  · intro h; exact ⟨⟨y, h⟩, ⟨x, h⟩⟩
  · rintro ⟨⟨y', hy'⟩, ⟨x', hx'⟩⟩
    have hcp := trans_cutPaste P x y' x' y (hy'.trans hx'.symm)
    rw [hx'] at hcp
    exact hcp

/-- **The fiber indicator factors (proved)**: `[trans = w] = [aliceOK]·[bobOK]`, the
algebraic rectangle form feeding InfoTheory8's product distribution. -/
theorem indicator_factor (P : Protocol α β τ) (w : List Bool) (x : α) (y : β) :
    (if trans P x y = w then (1 : ℝ) else 0)
      = (if aliceOK P w x then (1 : ℝ) else 0) * (if bobOK P w y then (1 : ℝ) else 0) := by
  by_cases hxy : trans P x y = w
  · obtain ⟨ha, hb⟩ := (trans_rectangle P w x y).mp hxy
    rw [if_pos hxy, if_pos ha, if_pos hb, mul_one]
  · rw [if_neg hxy]
    by_cases ha : aliceOK P w x
    · by_cases hb : bobOK P w y
      · exact absurd ((trans_rectangle P w x y).mpr ⟨ha, hb⟩) hxy
      · rw [if_neg hb, mul_zero]
    · rw [if_neg ha, zero_mul]

end PallLean.Paper93.DeepMath.PathB.CommProtocol

#print axioms PallLean.Paper93.DeepMath.PathB.CommProtocol.trans_rectangle
#print axioms PallLean.Paper93.DeepMath.PathB.CommProtocol.indicator_factor
