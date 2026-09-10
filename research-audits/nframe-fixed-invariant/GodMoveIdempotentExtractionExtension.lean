import PallLean.PiStarConcrete

/-!
# An algebraic extraction extends to a same-ambient linear projection

Given an algebra homomorphism E from L source variables to m target
variables, put the two variable sets in disjoint parts of Fin (L+m).
The extension below sends a source polynomial p to the target embedding
of E(p), fixes every target-supported polynomial, and is idempotent.

The constant term shared by the two polynomial subalgebras is subtracted
once. This gives an actual linear projection without requiring E itself
to be an endomorphism or an idempotent substitution. No global SPDP-rank
monotonicity is asserted: such a comparison needs a separate proof on the
particular source used by a God-Move construction.
-/

namespace GodMoveIdempotentExtractionExtension

open MvPolynomial

abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℚ

variable {L m : ℕ}

/-- Put source variables in the first L ambient coordinates. -/
noncomputable def embedSource (L m : ℕ) : Poly L →ₐ[ℚ] Poly (L + m) :=
  rename (Fin.castAdd m)

/-- Put output variables in the last m ambient coordinates. -/
noncomputable def embedOutput (L m : ℕ) : Poly m →ₐ[ℚ] Poly (L + m) :=
  rename (Fin.natAdd L)

/-- Retain source coordinates and set output coordinates to zero. -/
noncomputable def restrictSource (L m : ℕ) : Poly (L + m) →ₐ[ℚ] Poly L :=
  aeval (Fin.addCases (fun i => X i) (fun _ => 0))

/-- Retain output coordinates and set source coordinates to zero. -/
noncomputable def restrictOutput (L m : ℕ) : Poly (L + m) →ₐ[ℚ] Poly m :=
  aeval (Fin.addCases (fun _ => 0) (fun i => X i))

/-- The common constant part, regarded as an output polynomial. -/
noncomputable def constantPart (L m : ℕ) : Poly (L + m) →ₐ[ℚ] Poly m :=
  aeval (fun _ => 0)

theorem constantPart_apply (p : Poly (L + m)) :
    constantPart L m p = C (coeff 0 p) := by
  unfold constantPart
  rw [aeval_zero']
  rfl

@[simp] theorem restrictSource_embedSource (p : Poly L) :
    restrictSource L m (embedSource L m p) = p := by
  unfold restrictSource embedSource
  rw [aeval_rename]
  simp only [Function.comp_def, Fin.addCases_left]
  rw [aeval_X_left]
  rfl

@[simp] theorem restrictOutput_embedOutput (q : Poly m) :
    restrictOutput L m (embedOutput L m q) = q := by
  unfold restrictOutput embedOutput
  rw [aeval_rename]
  simp only [Function.comp_def, Fin.addCases_right]
  rw [aeval_X_left]
  rfl

@[simp] theorem restrictSource_embedOutput (q : Poly m) :
    restrictSource L m (embedOutput L m q) = C (constantCoeff q) := by
  unfold restrictSource embedOutput
  rw [aeval_rename]
  simp only [Function.comp_def, Fin.addCases_right]
  rw [aeval_zero']
  rfl

@[simp] theorem restrictOutput_embedSource (p : Poly L) :
    restrictOutput L m (embedSource L m p) = C (constantCoeff p) := by
  unfold restrictOutput embedSource
  rw [aeval_rename]
  simp only [Function.comp_def, Fin.addCases_left]
  rw [aeval_zero']
  rfl

@[simp] theorem constantPart_embedSource (p : Poly L) :
    constantPart L m (embedSource L m p) = C (constantCoeff p) := by
  rw [constantPart_apply]
  change C (constantCoeff (rename (Fin.castAdd m) p)) = _
  rw [constantCoeff_rename]

@[simp] theorem constantPart_embedOutput (q : Poly m) :
    constantPart L m (embedOutput L m q) = C (constantCoeff q) := by
  rw [constantPart_apply]
  change C (constantCoeff (rename (Fin.natAdd L) q)) = _
  rw [constantCoeff_rename]

/-- Compute the extracted source part plus the existing output part,
subtracting the constant counted in both restrictions. -/
noncomputable def transfer (E : Poly L →ₐ[ℚ] Poly m) :
    Poly (L + m) →ₗ[ℚ] Poly m :=
  E.toLinearMap.comp (restrictSource L m).toLinearMap +
    (restrictOutput L m).toLinearMap - (constantPart L m).toLinearMap

/-- The same-ambient projection corresponding to E. -/
noncomputable def projection (E : Poly L →ₐ[ℚ] Poly m) :
    Poly (L + m) →ₗ[ℚ] Poly (L + m) :=
  (embedOutput L m).toLinearMap.comp (transfer E)

theorem projection_apply (E : Poly L →ₐ[ℚ] Poly m) (p : Poly (L + m)) :
    projection E p = embedOutput L m
      (E (restrictSource L m p) + restrictOutput L m p - C (coeff 0 p)) := by
  simp [projection, transfer, constantPart_apply]

/-- The extension performs the original algebraic extraction exactly on
the embedded source. No independent target equality is assumed. -/
theorem projection_embedSource (E : Poly L →ₐ[ℚ] Poly m) (p : Poly L) :
    projection E (embedSource L m p) = embedOutput L m (E p) := by
  simp [projection, transfer]

/-- Every output-supported polynomial is fixed by the extension. -/
theorem projection_embedOutput (E : Poly L →ₐ[ℚ] Poly m) (q : Poly m) :
    projection E (embedOutput L m q) = embedOutput L m q := by
  have hC : E (C (constantCoeff q)) = C (constantCoeff q) := E.commutes _
  simp [projection, transfer, hC]

theorem projection_apply_apply (E : Poly L →ₐ[ℚ] Poly m) (p : Poly (L + m)) :
    projection E (projection E p) = projection E p := by
  change projection E (embedOutput L m (transfer E p)) = embedOutput L m (transfer E p)
  exact projection_embedOutput E _

/-- Idempotence holds as equality of actual ambient linear maps. -/
theorem projection_idempotent (E : Poly L →ₐ[ℚ] Poly m) :
    projection E ∘ₗ projection E = projection E := by
  apply LinearMap.ext
  intro p
  exact projection_apply_apply E p

theorem projection_isProjectionGauge (E : Poly L →ₐ[ℚ] Poly m) :
    GaugeMonotonicity.IsProjectionGauge (projection E) :=
  ⟨projection_idempotent E⟩

/-- The range is precisely the complete target-coordinate polynomial space. -/
theorem projection_range (E : Poly L →ₐ[ℚ] Poly m) :
    LinearMap.range (projection E) = LinearMap.range (embedOutput L m).toLinearMap := by
  apply le_antisymm
  · rintro q ⟨p, rfl⟩
    exact ⟨transfer E p, rfl⟩
  · rintro q ⟨p, rfl⟩
    exact ⟨embedOutput L m p, projection_embedOutput E p⟩

end GodMoveIdempotentExtractionExtension

#print axioms GodMoveIdempotentExtractionExtension.projection_apply
#print axioms GodMoveIdempotentExtractionExtension.projection_embedSource
#print axioms GodMoveIdempotentExtractionExtension.projection_embedOutput
#print axioms GodMoveIdempotentExtractionExtension.projection_idempotent
#print axioms GodMoveIdempotentExtractionExtension.projection_isProjectionGauge
#print axioms GodMoveIdempotentExtractionExtension.projection_range
