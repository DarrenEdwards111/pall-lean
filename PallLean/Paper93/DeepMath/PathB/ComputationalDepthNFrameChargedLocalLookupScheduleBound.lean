import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalEvaluatedStreamBound

/-!
# Polynomial budget for the charged local literal-lookup schedule

The paired SAT verifier must perform one indexed certificate lookup for every
literal in the decoded formula.  The individual lookup machine and its
quadratic clock were already verified.  This file closes the remaining
aggregate-cost bookkeeping: even malformed inputs decode to at most
quadratically many literals, every decoded address is bounded by the instance
length, and the sum of all canonical lookup clocks has a uniform quartic
bound in the paired input length.

This does not yet construct the parser/emitter transducer.  It proves that the
finite-control wiring of repeated parse/lookup/write phases is the only
remaining operational obligation; the repeated lookup work itself is
polynomially budgeted.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound

open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit
open PallLean.Paper93.DeepMath.PathB.CookLevinWholeRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalNPBridge
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalEvaluatedStreamBound

/-! ## Number and size of the decoded literal tasks -/

/-- All literal occurrences in a decoded formula, in clause order. -/
def decodedLiterals (x : List Bool) : List Lit :=
  (decodeFormula x).flatten

theorem decodedLiterals_length_le (x : List Bool) :
    (decodedLiterals x).length ≤ x.length * x.length := by
  have hb : ∀ y ∈ (decodeFormula x).map List.length, y ≤ x.length := by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    exact decodeFormula_clause_length_le x hc
  have hs := List.sum_le_card_nsmul
    ((decodeFormula x).map List.length) x.length hb
  simp only [List.length_map, nsmul_eq_mul] at hs
  rw [decodedLiterals, List.length_flatten]
  exact le_trans hs (Nat.mul_le_mul_right _ (decodeFormula_length_le x))

theorem decodedLiterals_var_le (x : List Bool) {l : Lit}
    (hl : l ∈ decodedLiterals x) :
    l.1 ≤ x.length := by
  change l ∈ (decodeFormula x).flatten at hl
  obtain ⟨c, hc, hl⟩ := List.mem_flatten.mp hl
  exact decodeFormula_var_le_length x hc hl

/-! ## Summing the already verified lookup clocks -/

/-- The exact clock used by the canonical `masterM` lookup for one literal. -/
def literalLookupCost (w : List Bool) (l : Lit) : Nat :=
  2 * (l.1 + 1) + 2 + 1 +
    (clockSum l.1 (signedLookupAssignment w l.1 l.2).length + 7)

/-- A quadratic per-literal envelope at instance length `n`. -/
def literalLookupEnvelope (n : Nat) : Nat :=
  32 * (n + 2) * (n + 2) + 2 * (n + 1) + 12

theorem literalLookupEnvelope_le (n : Nat) :
    literalLookupEnvelope n ≤ 200 * (n + 1) ^ 2 := by
  simp only [literalLookupEnvelope]
  nlinarith [Nat.zero_le n]

theorem literalLookupCost_le (x w : List Bool) {l : Lit}
    (hl : l ∈ decodedLiterals x) :
    literalLookupCost w l ≤ literalLookupEnvelope x.length := by
  have hv := decodedLiterals_var_le x hl
  unfold literalLookupCost
  calc
    2 * (l.1 + 1) + 2 + 1 +
          (clockSum l.1 (signedLookupAssignment w l.1 l.2).length + 7)
        ≤ 32 * (l.1 + 2) * (l.1 + 2) + 2 * (l.1 + 1) + 12 :=
      masterM_literal_clock_quadratic w l
    _ ≤ literalLookupEnvelope x.length := by
      unfold literalLookupEnvelope
      gcongr

/-- Sum of the exact clocks for all decoded literal occurrences. -/
def lookupScheduleCost (x w : List Bool) : Nat :=
  ((decodedLiterals x).map (literalLookupCost w)).sum

/-- A uniform quartic budget for the whole repeated lookup schedule. -/
def lookupScheduleBound (n : Nat) : Nat :=
  200 * (n + 1) ^ 4

theorem lookupScheduleBound_poly : PolyBounded lookupScheduleBound := by
  exact ⟨200, 4, fun _ => le_rfl⟩

theorem lookupScheduleCost_le (x w : List Bool) :
    lookupScheduleCost x w ≤ lookupScheduleBound x.length := by
  have hb : ∀ y ∈ (decodedLiterals x).map (literalLookupCost w),
      y ≤ literalLookupEnvelope x.length := by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨l, hl, rfl⟩ := hy
    exact literalLookupCost_le x w hl
  have hs := List.sum_le_card_nsmul
    ((decodedLiterals x).map (literalLookupCost w))
    (literalLookupEnvelope x.length) hb
  simp only [List.length_map, nsmul_eq_mul] at hs
  have hcount := decodedLiterals_length_le x
  have henv := literalLookupEnvelope_le x.length
  have hn2 : x.length * x.length ≤ (x.length + 1) ^ 2 := by
    nlinarith [Nat.zero_le x.length]
  calc
    lookupScheduleCost x w
        ≤ (decodedLiterals x).length * literalLookupEnvelope x.length := hs
    _ ≤ (x.length * x.length) * literalLookupEnvelope x.length :=
      Nat.mul_le_mul_right _ hcount
    _ ≤ (x.length * x.length) * (200 * (x.length + 1) ^ 2) :=
      Nat.mul_le_mul_left _ henv
    _ ≤ (x.length + 1) ^ 2 * (200 * (x.length + 1) ^ 2) :=
      Nat.mul_le_mul_right _ hn2
    _ = lookupScheduleBound x.length := by
      simp only [lookupScheduleBound]
      ring

/-! ## The whole paired verifier input -/

/-- Exact lookup work selected by the instance/certificate parser. -/
def pairedLookupScheduleCost (z : List Bool) : Nat :=
  lookupScheduleCost (unpackWitness z).1 (unpackWitness z).2

theorem pairedLookupScheduleCost_le (z : List Bool) :
    pairedLookupScheduleCost z ≤ lookupScheduleBound z.length := by
  have hx := unpackWitness_instance_length_le z
  apply le_trans (lookupScheduleCost_le (unpackWitness z).1 (unpackWitness z).2)
  unfold lookupScheduleBound
  exact Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left (by omega) 4)

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound.decodedLiterals_length_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound.decodedLiterals_var_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound.lookupScheduleBound_poly
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound.lookupScheduleCost_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound.pairedLookupScheduleCost_le
