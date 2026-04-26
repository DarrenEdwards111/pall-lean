import PallLean.CompiledBoolFactorBridge
import PallLean.SymmetricPower
import Mathlib.Tactic

/-!
# Partial derivative of the booleanity factor in the Cook-Levin compilation

In the Cook-Levin compilation, each booleanity local constraint at variable
`v : Fin n` carries the polynomial `(boolLC n v).poly = X_v * (1 - X_v)`.
The corresponding factor in `compiledPoly` (and in `cookLevinLocalBlockQ`) is

  `1 - (boolLC n v).poly = 1 - X_v * (1 - X_v) = 1 - X_v + X_v^2`.

This file proves the simple but load-bearing identity

  `pderiv v (1 - (boolLC n v).poly) = 2 * X v - 1`

by composing two existing lemmas:

* `CompiledBoolFactorBridge.boolConstraint_factor_eq_boolFactor` :
    `1 - (boolLC n v).poly = boolFactor n v`,
* `SymmetricPower.pderiv_boolFactor_self` :
    `pderiv v (boolFactor N v) = -1 + 2 * X v`.

The result is the Route C / Route A booleanity-factor derivative used at
each compiled vertex `v` in Cook-Levin local block `Q_v` reasoning.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial PaperFaithfulSeparation SymmetricPower

attribute [local instance] Classical.dec

/-- Partial derivative of the booleanity factor `1 - (boolLC n v).poly`
with respect to its own variable `v` equals `2 * X v - 1`.

This is the booleanity-factor derivative used at vertex `v` in
`cookLevinLocalBlockQ` and in `compiledPoly`.

The proof composes the bridge identity
`1 - (boolLC n v).poly = boolFactor n v` with the concrete computation
`pderiv v (boolFactor N v) = -1 + 2 * X v` and rearranges. -/
theorem boolLC_factor_pderiv (n : ℕ) (v : Fin n) :
    MvPolynomial.pderiv v
        ((1 : MvPolynomial (Fin n) ℚ) - (boolLC n v).poly) =
      2 * MvPolynomial.X v - 1 := by
  rw [CompiledBoolFactorBridge.boolConstraint_factor_eq_boolFactor n v,
      SymmetricPower.pderiv_boolFactor_self n v]
  ring

end PallLean.Paper93.Paper283
