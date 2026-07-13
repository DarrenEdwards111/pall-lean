import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolographicObserverAudit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMathlibCandidates

/-!
# Regulated black-hole audit: when a singularity can, and cannot, supply exponential growth

This file tests the sharpened proposal suggested by the black-hole analogy.  A literal infinity is not a
complexity bound: complexity requires a finite value at each input length.  We therefore replace the
singularity by a finite precision regulator.  An encoding carrying `b` regulator bits is assigned the finite
singularity charge `2^b`.

The audit proves four facts.

1. **Forced precision really would work.**  If admissibility forces at least `n` regulator bits at length `n`,
   every admissible encoding has charge and total cost at least `2^n`.  The resulting scale beats every fixed
   polynomial.
2. **Finite precision is honest.**  A `b`-bit cap bounds the charge by `2^b`; no literal infinity is used.
3. **An arbitrary regulator manufactures arbitrary-looking growth.**  Any chosen precision schedule `p(n)`
   produces the charge `2^(p(n))`, even for the constant-false function.  Thus exponential boundary charge
   alone is not evidence of computational hardness.
4. **Unrestricted representation minimisation chooses zero precision.**  Adding the regulator to a faithful
   wrapper changes the bounded-cost question only by the unavoidable additive charge `1`.  In particular,
   any representable target at positive length has a zero-precision encoding, so a theorem saying that *all*
   faithful encodings require linear precision is false unless a new semantic/physical admissibility condition
   excludes that encoding.

Consequently the proposed route has one precise open socket: derive the linear-precision requirement from SAT
semantics and the allowed holographic geometry.  Assuming it gives an exponential lower bound; choosing it by
hand merely inserts the conclusion into the regulator.

Nothing here proves a SAT lower bound or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RegulatedBlackHoleAudit

open PallLean.Paper93.DeepMath.PathB.HolographicObserverAudit

/-! ## Finite regulated encodings -/

/-- A faithful bulk representation together with a finite near-singularity resolution. -/
structure RegulatedEncoding {Input Output : Type*}
    (R : RepresentationModel Input Output) where
  bulk : R.Rep
  precisionBits : Nat

namespace RegulatedEncoding

variable {Input Output : Type*} {R : RepresentationModel Input Output}

def eval (H : RegulatedEncoding R) : Input → Output := R.eval H.bulk

/-- The finite replacement for the singular divergence. -/
def singularityCharge (H : RegulatedEncoding R) : Nat := 2 ^ H.precisionBits

/-- Bulk representation cost plus the finite regulated charge. -/
def cost (H : RegulatedEncoding R) : Nat := R.cost H.bulk + singularityCharge H

/-- Every underlying representation admits the zero-precision faithful presentation. -/
def ofRep (r : R.Rep) : RegulatedEncoding R where
  bulk := r
  precisionBits := 0

@[simp] theorem eval_ofRep (r : R.Rep) : eval (ofRep r) = R.eval r := rfl
@[simp] theorem charge_ofRep (r : R.Rep) : singularityCharge (ofRep r) = 1 := by
  simp [singularityCharge, ofRep]
@[simp] theorem cost_ofRep (r : R.Rep) : cost (ofRep r) = R.cost r + 1 := by
  rfl

/-- A finite precision cap gives a finite exponential cap; no infinity is present. -/
theorem singularityCharge_le_of_precision_le (H : RegulatedEncoding R) {b : Nat}
    (hprecision : H.precisionBits ≤ b) :
    singularityCharge H ≤ 2 ^ b := by
  exact Nat.pow_le_pow_right (by omega) hprecision

end RegulatedEncoding

/-! ## The positive conditional: forced linear precision gives exponential cost -/

/-- The missing physical/semantic condition: admissibility forces at least `n` bits of resolution at length
`n`.  This predicate is named, not asserted for SAT. -/
def ForcesLinearPrecision {Input Output : Type*}
    (R : RepresentationModel Input Output)
    (Admissible : (n : Nat) → RegulatedEncoding R → Prop) : Prop :=
  ∀ n H, Admissible n H → n ≤ H.precisionBits

/-- If admissibility genuinely forces linear precision, every admissible charge is at least exponential. -/
theorem forced_linear_precision_gives_exponential_charge
    {Input Output : Type*} {R : RepresentationModel Input Output}
    {Admissible : (n : Nat) → RegulatedEncoding R → Prop}
    (hforced : ForcesLinearPrecision R Admissible)
    {n : Nat} {H : RegulatedEncoding R} (hH : Admissible n H) :
    2 ^ n ≤ RegulatedEncoding.singularityCharge H := by
  exact Nat.pow_le_pow_right (by omega) (hforced n H hH)

/-- The same forced charge lower-bounds the total regulated cost. -/
theorem forced_linear_precision_gives_exponential_cost
    {Input Output : Type*} {R : RepresentationModel Input Output}
    {Admissible : (n : Nat) → RegulatedEncoding R → Prop}
    (hforced : ForcesLinearPrecision R Admissible)
    {n : Nat} {H : RegulatedEncoding R} (hH : Admissible n H) :
    2 ^ n ≤ RegulatedEncoding.cost H := by
  exact le_trans (forced_linear_precision_gives_exponential_charge hforced hH)
    (Nat.le_add_left _ _)

/-- `2^n` beats every fixed polynomial.  This is the exact finite asymptotic replacement for the informal
word "infinity". -/
theorem two_pow_is_superpolynomial (A C B : Nat) :
    ∃ n : Nat, 1 ≤ n ∧ A * n ^ C + B < 2 ^ n :=
  Nat.exists_poly_lt_pow (p := 2) (by omega) A C B

/-- Hence forced linear precision supplies a superpolynomial lower bound for any selected admissible family. -/
theorem forced_family_cost_is_superpolynomial
    {Input Output : Type*} {R : RepresentationModel Input Output}
    {Admissible : (n : Nat) → RegulatedEncoding R → Prop}
    (H : (n : Nat) → RegulatedEncoding R)
    (hH : ∀ n, Admissible n (H n))
    (hforced : ForcesLinearPrecision R Admissible)
    (A C B : Nat) :
    ∃ n : Nat, 1 ≤ n ∧ A * n ^ C + B < RegulatedEncoding.cost (H n) := by
  obtain ⟨n, hn, hgap⟩ := two_pow_is_superpolynomial A C B
  exact ⟨n, hn, lt_of_lt_of_le hgap
    (forced_linear_precision_gives_exponential_cost hforced (hH n))⟩

/-! ## Negative controls: scheduled precision and an easy function -/

/-- Any externally chosen precision schedule can be installed on the same bulk representation. -/
def scheduledEncoding {Input Output : Type*} {R : RepresentationModel Input Output}
    (r : R.Rep) (p : Nat → Nat) (n : Nat) : RegulatedEncoding R where
  bulk := r
  precisionBits := p n

/-- The apparent growth then comes exactly from the chosen schedule. -/
theorem scheduled_charge_eq {Input Output : Type*} {R : RepresentationModel Input Output}
    (r : R.Rep) (p : Nat → Nat) (n : Nat) :
    RegulatedEncoding.singularityCharge (scheduledEncoding r p n) = 2 ^ p n := rfl

/-- A deliberately trivial representation model: every input maps to `false` at unit bulk cost. -/
def easyFalseModel : RepresentationModel Nat Bool where
  Rep := Unit
  eval := fun _ _ => false
  cost := fun _ => 1

/-- Give the easy constant-false function an `n`-bit regulator. -/
def easyExponentialBoundary (n : Nat) : RegulatedEncoding easyFalseModel :=
  scheduledEncoding () (fun m => m) n

@[simp] theorem easyExponentialBoundary_eval (n : Nat) :
    RegulatedEncoding.eval (easyExponentialBoundary n) = fun _ => false := rfl

@[simp] theorem easyExponentialBoundary_charge (n : Nat) :
    RegulatedEncoding.singularityCharge (easyExponentialBoundary n) = 2 ^ n := rfl

/-- **Easy-function false positive.**  The regulated boundary charge is superpolynomial even though the
underlying function is constant and has unit bulk cost. -/
theorem easy_function_has_superpolynomial_boundary_charge (A C B : Nat) :
    ∃ n : Nat, 1 ≤ n ∧
      A * n ^ C + B < RegulatedEncoding.singularityCharge (easyExponentialBoundary n) := by
  simpa using two_pow_is_superpolynomial A C B

/-! ## Representation minimisation and the zero-precision collapse -/

def HasRegulatedEncodingAtMost {Input Output : Type*}
    (R : RepresentationModel Input Output) (f : Input → Output) (B : Nat) : Prop :=
  ∃ H : RegulatedEncoding R,
    RegulatedEncoding.eval H = f ∧ RegulatedEncoding.cost H ≤ B

/-- Minimising over unrestricted regulated wrappers changes the original bounded-cost problem only by `+1`:
the minimiser selects zero precision. -/
theorem regulated_minimisation_iff_representation_minimisation
    {Input Output : Type*} (R : RepresentationModel Input Output)
    (f : Input → Output) (B : Nat) :
    HasRegulatedEncodingAtMost R f (B + 1) ↔ HasRepresentationAtMost R f B := by
  constructor
  · rintro ⟨H, heval, hcost⟩
    refine ⟨H.bulk, heval, ?_⟩
    have hcharge : 1 ≤ RegulatedEncoding.singularityCharge H := by
      unfold RegulatedEncoding.singularityCharge
      exact Nat.one_le_two_pow
    unfold RegulatedEncoding.cost at hcost
    omega
  · rintro ⟨r, heval, hcost⟩
    refine ⟨RegulatedEncoding.ofRep r, heval, ?_⟩
    simp only [RegulatedEncoding.cost_ofRep]
    omega

/-- A target family would force linear precision if every faithful encoding computing its length-`n` member
required at least `n` regulator bits. -/
def TargetForcesLinearPrecision {Input Output : Type*}
    (R : RepresentationModel Input Output) (target : Nat → Input → Output) : Prop :=
  ∀ n (H : RegulatedEncoding R),
    RegulatedEncoding.eval H = target n → n ≤ H.precisionBits

/-- **Zero-precision no-go.**  In the unrestricted faithful model, any representable target at a positive
length refutes universal precision forcing.  A surviving black-hole route therefore needs a nontrivial
admissibility law derived from the target semantics/geometry; the wrapper and singularity analogy alone cannot
supply it. -/
theorem faithful_zero_precision_refutes_target_forcing
    {Input Output : Type*} (R : RepresentationModel Input Output)
    (target : Nat → Input → Output) {n : Nat} (hn : 0 < n)
    (r : R.Rep) (hr : R.eval r = target n) :
    ¬ TargetForcesLinearPrecision R target := by
  intro hforced
  have h := hforced n (RegulatedEncoding.ofRep r) (by simpa using hr)
  simp [RegulatedEncoding.ofRep] at h
  omega

end PallLean.Paper93.DeepMath.PathB.RegulatedBlackHoleAudit

#print axioms PallLean.Paper93.DeepMath.PathB.RegulatedBlackHoleAudit.forced_linear_precision_gives_exponential_cost
#print axioms PallLean.Paper93.DeepMath.PathB.RegulatedBlackHoleAudit.forced_family_cost_is_superpolynomial
#print axioms PallLean.Paper93.DeepMath.PathB.RegulatedBlackHoleAudit.easy_function_has_superpolynomial_boundary_charge
#print axioms PallLean.Paper93.DeepMath.PathB.RegulatedBlackHoleAudit.regulated_minimisation_iff_representation_minimisation
#print axioms PallLean.Paper93.DeepMath.PathB.RegulatedBlackHoleAudit.faithful_zero_precision_refutes_target_forcing
