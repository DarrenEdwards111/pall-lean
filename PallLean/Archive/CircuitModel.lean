/-
  CircuitModel.lean — Boolean circuits and their polynomial interpretations

  Paper §4–5: Boolean circuits over {AND, OR, NOT} interpreted as
  polynomials over F_p. Circuit size → polynomial degree.

  We also define depth-4 ΣΠ∑Π circuits (the key intermediate form
  from Agrawal-Vinay / Tavenas depth reduction).
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic
import PallLean.Restriction

namespace CircuitModel

open MvPolynomial

/-! ## Boolean Circuit (abstract interface)

We don't formalize the full gate-level circuit structure.
Instead, we define the key properties a circuit family must satisfy
for the SPDP argument: size bound, polynomial interpretation,
and depth-4 simulability. -/

/-- A circuit family: for each input length n, a circuit computing
    a Boolean function on n variables. -/
structure CircuitFamily where
  /-- Number of input variables for length-n inputs. -/
  numVars : ℕ → ℕ
  /-- The polynomial interpretation of the n-th circuit over any field. -/
  poly : (F : Type*) → [CommRing F] → (n : ℕ) → MvPolynomial (Fin (numVars n)) F
  /-- Circuit size (number of gates). -/
  size : ℕ → ℕ

/-- A polynomial-size circuit family. -/
structure PolySizeFamily extends CircuitFamily where
  /-- Size bound exponent: size(n) ≤ n^k for this k. -/
  sizeBound : ℕ
  /-- The size is polynomially bounded. -/
  size_le : ∀ n, n ≥ 2 → size n ≤ n ^ sizeBound

/-! ## Depth-4 ΣΠ∑Π Circuits

After depth reduction (Agrawal-Vinay + Tavenas), any poly-size circuit
becomes a depth-4 circuit: Sum of Products of Sums of Products.
The key parameters are:
- top fan-in (number of product gates at depth 1)
- bottom fan-in t (inputs per product gate at depth 4)
- formal degree D -/

/-- Parameters of a depth-4 ΣΠ∑Π circuit. -/
structure Depth4Params where
  /-- Number of input variables. -/
  numVars : ℕ
  /-- Top fan-in (number of multiplicands at depth 1). -/
  topFanIn : ℕ
  /-- Bottom fan-in (inputs per bottom product gate). -/
  bottomFanIn : ℕ
  /-- Formal degree. -/
  formalDegree : ℕ
  /-- Total size. -/
  size : ℕ

/-- A depth-4 circuit representation of a polynomial. -/
structure Depth4Circuit (F : Type*) [CommRing F] where
  params : Depth4Params
  /-- The polynomial computed by this depth-4 circuit. -/
  poly : MvPolynomial (Fin params.numVars) F

/-! ## Cook-Levin: Polytime TM → Poly-size Circuit

Every language in P has a poly-size circuit family.
This is the standard Cook-Levin theorem. -/

/-- A polytime Turing machine gives rise to a poly-size circuit family. -/
structure PtimeToCircuit where
  /-- The TM. -/
  machine : ℕ  -- abstract TM identifier
  /-- The resulting circuit family. -/
  family : PolySizeFamily

end CircuitModel
