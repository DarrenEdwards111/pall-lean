/-
  Paper93/InterfaceAlphabet.lean — Finite interface-local alphabet Σ from paper §9 / §9.3.

  This file defines the finite interface-local alphabet `InterfaceType` used in
  paper §9.3 (finite local alphabet). An interface symbol is the pair of:
    * a constraint type τ (4 values from `SymmetricPowerBound.ConstraintType`),
    * a local state index in `Fin 4` (a placeholder for local context, bounded
      constant, matching the convention that |M_τ| = O(1) in paper (P7)).

  We then define the bounded-length word type
      AlphabetWord q := Σ' (k : Fin (q+1)), List.Vector InterfaceType k.val
  which packages `Σ^{≤q}` (all words over `InterfaceType` of length ≤ q) and
  prove it is a `Fintype` with
      |AlphabetWord q| = ∑ k ∈ Finset.range (q+1), |InterfaceType|^k.

  All proofs are kernel-only; no `sorry`, no bad axioms introduced here beyond
  `propext, Classical.choice, Quot.sound`.
-/
import PallLean.SymmetricPowerBound
import PallLean.WithinProfileBound
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Vector
import Mathlib.Algebra.BigOperators.Fin

namespace PallLean
namespace Paper93

open SymmetricPowerBound

/-- Interface-local alphabet Σ. A symbol is the pair (constraintType, localState).
For Cook–Levin we use 4 `ConstraintType` values × a 4-valued local-state enum; the
total alphabet is finite of cardinality `4 * 4 = 16`. The `localState : Fin 4`
component is a placeholder for the bounded local context in the paper §9.3
canonical local-update normal form (P7), where |M_τ| = O(1). -/
structure InterfaceType where
  constraintType : ConstraintType
  localState     : Fin 4
  deriving DecidableEq

/-- `InterfaceType` is a `Fintype` since both components are. -/
instance : Fintype InterfaceType :=
  Fintype.ofEquiv (ConstraintType × Fin 4)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun s => (s.constraintType, s.localState)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Cardinality of `InterfaceType` is 16 = 4 · 4. -/
theorem card_InterfaceType :
    Fintype.card InterfaceType = 16 := by
  have h1 : Fintype.card InterfaceType
            = Fintype.card (ConstraintType × Fin 4) :=
    Fintype.card_congr
      { toFun := fun s => (s.constraintType, s.localState)
        invFun := fun p => ⟨p.1, p.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [h1]
  simp [Fintype.card_prod, Fintype.card_fin]
  decide

/-- `Σ^{≤q}`: bounded-length words of length ≤ q over `InterfaceType`.
Encoded as a dependent pair: the length `k : Fin (q+1)` together with a
`List.Vector InterfaceType k.val`. -/
def AlphabetWord (q : ℕ) : Type :=
  Σ' (k : Fin (q + 1)), List.Vector InterfaceType k.val

/-- `AlphabetWord q` is a `Fintype`. -/
instance (q : ℕ) : Fintype (AlphabetWord q) := by
  unfold AlphabetWord
  infer_instance

/-- Cardinality of `Σ^{≤q}`:
`|AlphabetWord q| = ∑_{k=0}^{q} |InterfaceType|^k`. -/
theorem card_AlphabetWord (q : ℕ) :
    Fintype.card (AlphabetWord q)
      = ∑ k ∈ Finset.range (q + 1), Fintype.card InterfaceType ^ k := by
  -- Rewrite via the Sigma equivalence for PSigma, then apply `card_sigma`
  -- and `card_vector`, finally re-index the sum over `Fin (q+1)` as
  -- a sum over `Finset.range (q+1)`.
  have hcong :
      Fintype.card (AlphabetWord q)
        = Fintype.card (Σ k : Fin (q + 1), List.Vector InterfaceType k.val) := by
    refine Fintype.card_congr ?_
    exact Equiv.psigmaEquivSigma (fun k : Fin (q + 1) =>
      List.Vector InterfaceType k.val)
  rw [hcong]
  rw [Fintype.card_sigma]
  -- Each fiber has cardinality |InterfaceType|^k
  have hfiber :
      ∀ k : Fin (q + 1),
        Fintype.card (List.Vector InterfaceType k.val)
          = Fintype.card InterfaceType ^ k.val := by
    intro k
    exact card_vector (α := InterfaceType) k.val
  simp_rw [hfiber]
  -- Convert sum over Fin (q+1) to sum over Finset.range (q+1)
  rw [← Fin.sum_univ_eq_sum_range
    (f := fun k => Fintype.card InterfaceType ^ k)]

end Paper93
end PallLean
