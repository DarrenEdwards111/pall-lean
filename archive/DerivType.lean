/-
  DerivType.lean — Local derivative types for 3-SAT clause blocks

  Each clause in the Cook-Levin Tseitin polynomial has 4 variables:
  z_c (selector), v_{c,1}, v_{c,2}, v_{c,3} (literal variables).
  Differentiating by each gives a distinct "derivative type."

  Paper: Definition 18, Property P2 (finite local alphabet).
-/
import Mathlib.Tactic

namespace DerivType

/-- The 4 derivative types for a 3-SAT clause block -/
inductive DerivType
  | dz   -- ∂/∂z_c : derivative by selector variable
  | dv1  -- ∂/∂v_{c,1} : derivative by first literal variable
  | dv2  -- ∂/∂v_{c,2} : derivative by second literal variable
  | dv3  -- ∂/∂v_{c,3} : derivative by third literal variable
  deriving DecidableEq, Fintype, Repr

/-- Number of derivative types = 4 -/
theorem card_derivType : Fintype.card DerivType = 4 := by decide

/-- m = |DerivType| = 4 as used in profile compression bounds -/
theorem derivType_card_eq_four : Fintype.card DerivType = 4 := card_derivType

end DerivType
