import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTimeUnrolledTensorNetwork

/-!
# Exact balanced compression for polynomial-configuration machines

This file isolates the finite encoding used by the log-space instantiation.
For input size `n`, a fixed encoded machine has at most
`coefficient * (n + 1) ^ exponent` configurations.  Its deterministic step is
therefore an endomorphism of that finite carrier.  A run of `2^d` steps can be
contracted by the balanced transition tree at depth `d`, with bond dimension
equal to the explicit polynomial configuration capacity.

The polynomial configuration bound is part of the encoding interface.  Thus
the result applies directly to standard fixed-machine log-space encodings once
their configuration-count lemma is supplied; it does not assert that an
arbitrary polynomial-time machine has polynomially many configurations.
-/

namespace PallLean.Paper93.DeepMath.PathB.BalancedLogSpaceCompression

open PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork

/-- Explicit polynomial configuration capacity for a fixed-machine encoding. -/
def configurationCapacity (coefficient exponent n : Nat) : Nat :=
  coefficient * (n + 1) ^ exponent

/-- A deterministic computation whose complete configurations have already
been encoded in an explicitly polynomial finite carrier.  Fixed-machine
log-space computations have this form after the usual configuration encoding. -/
structure PolynomialConfigurationMachine
    (coefficient exponent n : Nat) where
  step : Fin (configurationCapacity coefficient exponent n) →
    Fin (configurationCapacity coefficient exponent n)
  initial : Fin (configurationCapacity coefficient exponent n)
  accept : Fin (configurationCapacity coefficient exponent n) → Bool

namespace PolynomialConfigurationMachine

def run {coefficient exponent n : Nat}
    (M : PolynomialConfigurationMachine coefficient exponent n)
    (time : Nat) : Fin (configurationCapacity coefficient exponent n) :=
  M.step^[time] M.initial

def decision {coefficient exponent n : Nat}
    (M : PolynomialConfigurationMachine coefficient exponent n)
    (time : Nat) : Bool :=
  M.accept (M.run time)

/-- Exact terminal-state preservation under balanced contraction. -/
theorem balanced_terminal {coefficient exponent n : Nat}
    (M : PolynomialConfigurationMachine coefficient exponent n) (d : Nat) :
    (CompositionTree.balancedPower M.step d).eval M.initial = M.run (2 ^ d) := by
  exact CompositionTree.balancedPower_terminal M.step M.initial d

/-- The parallel contraction depth is the logarithm `d` of the represented
`2^d` sequential steps. -/
theorem balanced_height {coefficient exponent n : Nat}
    (M : PolynomialConfigurationMachine coefficient exponent n) (d : Nat) :
    (CompositionTree.balancedPower M.step d).height = d :=
  CompositionTree.balancedPower_height M.step d

/-- The internal wire alphabet is exactly the explicit polynomial
configuration carrier. -/
theorem polynomial_bondDimension {coefficient exponent n : Nat}
    (_M : PolynomialConfigurationMachine coefficient exponent n) :
    bondDimension (Fin (configurationCapacity coefficient exponent n)) =
      coefficient * (n + 1) ^ exponent := by
  simp [bondDimension, configurationCapacity]

/-- Reading the accepting bit after balanced contraction exactly reproduces
the sequential machine decision. -/
theorem balanced_decision_exact {coefficient exponent n : Nat}
    (M : PolynomialConfigurationMachine coefficient exponent n) (d : Nat) :
    M.accept ((CompositionTree.balancedPower M.step d).eval M.initial) =
      M.decision (2 ^ d) := by
  rw [balanced_terminal]
  rfl

end PolynomialConfigurationMachine

end PallLean.Paper93.DeepMath.PathB.BalancedLogSpaceCompression

#print axioms PallLean.Paper93.DeepMath.PathB.BalancedLogSpaceCompression.PolynomialConfigurationMachine.balanced_terminal
#print axioms PallLean.Paper93.DeepMath.PathB.BalancedLogSpaceCompression.PolynomialConfigurationMachine.balanced_height
#print axioms PallLean.Paper93.DeepMath.PathB.BalancedLogSpaceCompression.PolynomialConfigurationMachine.polynomial_bondDimension
#print axioms PallLean.Paper93.DeepMath.PathB.BalancedLogSpaceCompression.PolynomialConfigurationMachine.balanced_decision_exact
