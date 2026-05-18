import PallLean.Paper93.DeepMath.PathC.PiPlusBoolPoly
import PallLean.Paper93.DeepMath.PathC.PiPlusConstructive

/-!
# Boolean-ambient operations for Route C

Layer 2 of the paper-ambient refactor.  This file does not rewrite the old
Route-C pipeline; it gives typed Boolean-ambient versions of the basic maps that
new paper-faithful statements should use.

The important design decision is that `mlProjBool` means "enter the Boolean
paper ambient", i.e. quotient/normal-form reduction.  It is intentionally **not**
the old full-ring `mlProj`, which kills square monomials instead of reducing
`Xᵢ²` to `Xᵢ`.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

namespace BoolPoly

/-- Paper-faithful projection into the Boolean ambient.  This is the replacement
for using raw `mlProj` as if it were quotient reduction. -/
noncomputable abbrev mlProjBool {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) : BoolPoly n :=
  liftToBool p

@[simp] theorem coe_mlProjBool {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) :
    (mlProjBool p : MvPolynomial (Fin n) ℚ) =
      zeroProfileBooleanNormalize p := rfl

/-- Legacy bridge: the old `mlProj`, then enter the Boolean ambient.  This is
kept only for compatibility statements; it should not be used as the paper
quotient operation. -/
noncomputable abbrev legacyMlProjBool {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) : BoolPoly n :=
  liftToBool (mlProj p)

@[simp] theorem coe_legacyMlProjBool {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) :
    (legacyMlProjBool p : MvPolynomial (Fin n) ℚ) = mlProj p := by
  change zeroProfileBooleanNormalize (mlProj p) = mlProj p
  exact zeroProfileBooleanNormalize_mlProj p

/-- Lift any full-ring function to the Boolean ambient by normalizing after
application. -/
noncomputable def mapToBool {n : ℕ}
    (F : MvPolynomial (Fin n) ℚ → MvPolynomial (Fin n) ℚ)
    (p : BoolPoly n) : BoolPoly n :=
  liftToBool (F (p : MvPolynomial (Fin n) ℚ))

@[simp] theorem coe_mapToBool {n : ℕ}
    (F : MvPolynomial (Fin n) ℚ → MvPolynomial (Fin n) ℚ)
    (p : BoolPoly n) :
    (mapToBool F p : MvPolynomial (Fin n) ℚ) =
      zeroProfileBooleanNormalize (F (p : MvPolynomial (Fin n) ℚ)) := rfl

/-- A full-ring map respects the Boolean ambient if Boolean-equivalent inputs
are sent to Boolean-equivalent outputs. -/
def RespectsBooleanAmbient {n : ℕ}
    (F : MvPolynomial (Fin n) ℚ → MvPolynomial (Fin n) ℚ) : Prop :=
  ∀ ⦃p q : MvPolynomial (Fin n) ℚ⦄, p ≈ᵦ q → F p ≈ᵦ F q

/-- If a map respects Boolean equivalence, lifting after normalizing the input
is the same Boolean polynomial as lifting the raw input. -/
theorem mapToBool_liftToBool_eq_of_respects {n : ℕ}
    (F : MvPolynomial (Fin n) ℚ → MvPolynomial (Fin n) ℚ)
    (hF : RespectsBooleanAmbient F)
    (p : MvPolynomial (Fin n) ℚ) :
    mapToBool F (liftToBool p) = liftToBool (F p) := by
  apply BoolPoly.ext
  change zeroProfileBooleanNormalize (F (zeroProfileBooleanNormalize p)) =
    zeroProfileBooleanNormalize (F p)
  exact hF (p := zeroProfileBooleanNormalize p) (q := p) (by
    change zeroProfileBooleanNormalize (zeroProfileBooleanNormalize p) =
      zeroProfileBooleanNormalize p
    exact normalize_idempotent_apply p)

/-- The paper-ambient `Pi+` operation induced by an existing SAT-decider gauge.
It applies the old full-ring gauge to a normal representative and then returns
to Boolean normal form. -/
noncomputable def piPlusBool
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns) :
    BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars →
      BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars :=
  mapToBool piP.gauge

@[simp] theorem coe_piPlusBool
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (p : BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars) :
    (piPlusBool piP p :
      MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) =
      zeroProfileBooleanNormalize (piP.gauge
        (p : MvPolynomial
          (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)) := rfl

/-- Exact compatibility condition for an old full-ring `Pi+` gauge to descend to
the Boolean paper ambient.  This is the real replacement for assuming
`mlProj ∘ Pi+` commutes in the full ring. -/
def PiPlusRespectsBooleanAmbient
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  RespectsBooleanAmbient (n := (cook_levin_compilation M n hn2 htb hns).numVars)
    piP.gauge

/-- If the old full-ring gauge respects Boolean equivalence, the typed
Boolean-ambient `Pi+` is independent of the chosen representative. -/
theorem piPlusBool_liftToBool_eq_of_respects
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hpi : PiPlusRespectsBooleanAmbient piP)
    (p : MvPolynomial
      (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) :
    piPlusBool piP (liftToBool p) = liftToBool (piP.gauge p) :=
  mapToBool_liftToBool_eq_of_respects piP.gauge hpi p

/-- In the paper ambient, `mlProjBool` is just canonical quotient reduction, so
it is idempotent by construction. -/
theorem mlProjBool_idempotent {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) :
    mlProjBool ((mlProjBool p : BoolPoly n) : MvPolynomial (Fin n) ℚ) =
      mlProjBool p := by
  rw [liftToBool_eq_liftToBool_iff]
  change zeroProfileBooleanNormalize (zeroProfileBooleanNormalize p) =
    zeroProfileBooleanNormalize p
  exact normalize_idempotent_apply p

/-- The key paper-ambient square law is available immediately at the projection
boundary. -/
theorem mlProjBool_X_mul_X_eq_X {n : ℕ} (i : Fin n) :
    mlProjBool ((X i * X i : MvPolynomial (Fin n) ℚ)) =
      mlProjBool (X i : MvPolynomial (Fin n) ℚ) :=
  lift_X_mul_X_eq_lift_X i

/-! ## Axiom audit anchors -/

#print axioms coe_legacyMlProjBool
#print axioms mapToBool_liftToBool_eq_of_respects
#print axioms coe_piPlusBool
#print axioms piPlusBool_liftToBool_eq_of_respects
#print axioms mlProjBool_idempotent
#print axioms mlProjBool_X_mul_X_eq_X

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
