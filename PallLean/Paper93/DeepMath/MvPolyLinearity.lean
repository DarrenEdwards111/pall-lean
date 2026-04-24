import Mathlib.Algebra.MvPolynomial.Basic

namespace PallLean.Paper93.DeepMath

open MvPolynomial

theorem mvpoly_zero_mul {N : ℕ} (p : MvPolynomial (Fin N) ℚ) : 0 * p = 0 := zero_mul _
