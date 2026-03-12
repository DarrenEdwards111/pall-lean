/-
  Restriction.lean — Polynomial restriction infrastructure

  Paper §6: A restriction ρ : {x₁,...,xₙ} → {0, 1, *} fixes some variables
  to Boolean values and leaves others "live" (free).

  Restricting a polynomial p by ρ means substituting fixed values and
  keeping live variables. The restricted polynomial lives in the same
  ambient ring (fixed variables become constants, effectively unused).
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

namespace Restriction

open MvPolynomial

/-- A restriction assigns each variable to either a fixed Boolean value
    or leaves it live (*). None = live, Some b = fixed to b. -/
def Restriction (n : ℕ) := Fin n → Option Bool

/-- The set of live (unfixed) variables under restriction ρ. -/
def liveVars {n : ℕ} (ρ : Restriction n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ρ i = none)

/-- Number of live variables. -/
def numLive {n : ℕ} (ρ : Restriction n) : ℕ := (liveVars ρ).card

/-- The identity restriction (all variables live). -/
def idRestriction (n : ℕ) : Restriction n := fun _ => none

@[simp] theorem liveVars_id (n : ℕ) : liveVars (idRestriction n) = Finset.univ := by
  simp [liveVars, idRestriction]

/-- Apply restriction ρ to polynomial p: substitute fixed variables,
    keep live variables. -/
noncomputable def restrictPoly {n : ℕ} {F : Type*} [CommRing F]
    (ρ : Restriction n) (p : MvPolynomial (Fin n) F) :
    MvPolynomial (Fin n) F :=
  MvPolynomial.aeval (fun i =>
    match ρ i with
    | none => MvPolynomial.X i       -- live: keep as variable
    | some false => 0                 -- fixed to 0
    | some true => 1                  -- fixed to 1
  ) p

/-- Restricting by identity is the identity. -/
theorem restrictPoly_id {n : ℕ} {F : Type*} [CommRing F]
    (p : MvPolynomial (Fin n) F) :
    restrictPoly (idRestriction n) p = p := by
  unfold restrictPoly idRestriction
  have : MvPolynomial.aeval (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) F)) p = p := by
    rw [show (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) F)) = MvPolynomial.X from rfl]
    exact AlgHom.congr_fun MvPolynomial.aeval_X_left p
  exact this

/-- Composition of restrictions: apply ρ₂ after ρ₁.
    If ρ₁ fixes variable i, the composition fixes it to the same value.
    If ρ₁ leaves i live, ρ₂ decides. -/
def composeRestriction {n : ℕ} (ρ₁ ρ₂ : Restriction n) : Restriction n :=
  fun i => match ρ₁ i with
    | some b => some b
    | none => ρ₂ i

/-- Live variables of composed restriction ⊆ live variables of ρ₁. -/
theorem liveVars_compose_subset {n : ℕ} (ρ₁ ρ₂ : Restriction n) :
    liveVars (composeRestriction ρ₁ ρ₂) ⊆ liveVars ρ₁ := by
  intro i
  simp only [liveVars, Finset.mem_filter, Finset.mem_univ, true_and,
    composeRestriction]
  intro hi
  match h : ρ₁ i with
  | none => rfl
  | some b => simp [h] at hi

/-- A random restriction with survival probability p fixes each variable
    independently: live with probability p, fixed to uniform {0,1} otherwise.
    We don't formalize the probability measure here — just the type. -/
structure RestrictionFamily (n : ℕ) where
  seed_length : ℕ
  generate : Fin (2 ^ seed_length) → Restriction n

end Restriction
