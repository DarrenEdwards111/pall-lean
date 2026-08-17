import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0OracleControl

/-!
# Separator branching with private pivots: the full linear-saving cash-out

This file lifts the one-common-variable example to an arbitrary `r`-bit separator.  Bottom gate
`j` may depend on the entire separator through an arbitrary Boolean function `effect σ j`, but it
also owns a private pivot `p j`; its value is their XOR.  Thus gates may overlap arbitrarily on the
separator, while their private pivots make the residual output vector independently controllable.

The restriction algorithm is charged honestly: enumerate all `2^r` separator assignments and all
`2^k` residual output vectors.  Its work is exactly `2^(r+k)`.  Therefore a certificate
`r+k ≤ n-s` yields total work at most `2^(n-s)`, including every branch.  When `s = Ω(n)`, this is
the required `2^(n-Ω(n))` form.

This is a real broader overlapping depth-two XOR/MOD2 fragment.  The remaining structural theorem
for general overlapping ACC supports is now precise: find a restriction separator and private-pivot
minor with `r+k ≤ n-Ω(n)`; ordinary branching with `r+k=n` has zero surplus.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SeparatorPivotBranching

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0OracleControl

variable {r k : ℕ}

/-- An overlapping separator-pivot layer.  `effect σ j` is the contribution of all shared
separator variables to gate `j`; `p j` is its private pivot. -/
structure SeparatorPivotLayer (r k : ℕ) where
  effect : (Fin r → Bool) → Fin k → Bool

/-- XOR of the shared effect with the private pivot. -/
def gateVector (L : SeparatorPivotLayer r k) (σ : Fin r → Bool) (p : Fin k → Bool) :
    Fin k → Bool := fun j => (L.effect σ j) != p j

/-- Choose private pivots that realize the requested residual output vector. -/
def pivotsFor (L : SeparatorPivotLayer r k) (σ : Fin r → Bool) (y : Fin k → Bool) :
    Fin k → Bool := fun j => (L.effect σ j) != y j

/-- For every separator branch, private pivots make the gate-output map surjective. -/
theorem gateVector_pivotsFor (L : SeparatorPivotLayer r k) (σ : Fin r → Bool)
    (y : Fin k → Bool) : gateVector L σ (pivotsFor L σ y) = y := by
  funext j
  simp [gateVector, pivotsFor]

/-- A depth-two circuit with arbitrary top control over the separator-pivot layer. -/
structure SeparatorPivotCircuit (r k : ℕ) where
  layer : SeparatorPivotLayer r k
  top : OracleControl k

def SeparatorPivotCircuit.eval (C : SeparatorPivotCircuit r k)
    (σ : Fin r → Bool) (p : Fin k → Bool) : Bool :=
  controlEval C.top (gateVector C.layer σ p)

/-- Exact semantic collapse: the whole overlapping circuit is satisfiable iff its top control is. -/
theorem sat_iff_top (C : SeparatorPivotCircuit r k) :
    (∃ σ p, C.eval σ p = true) ↔ ∃ y, controlEval C.top y = true := by
  constructor
  · rintro ⟨σ, p, hp⟩
    exact ⟨gateVector C.layer σ p, hp⟩
  · rintro ⟨y, hy⟩
    let σ : Fin r → Bool := fun _ => false
    refine ⟨σ, pivotsFor C.layer σ y, ?_⟩
    unfold SeparatorPivotCircuit.eval
    rw [gateVector_pivotsFor]
    exact hy

/-- The explicit restriction search (all separator branches and all residual output vectors) is
correct, even though a single branch would already suffice for this pivot-rich fragment. -/
theorem branched_search_iff (C : SeparatorPivotCircuit r k) :
    (∃ σ p, C.eval σ p = true) ↔
      ∃ σ ∈ (Finset.univ : Finset (Fin r → Bool)),
        ∃ y ∈ (Finset.univ : Finset (Fin k → Bool)), controlEval C.top y = true := by
  rw [sat_iff_top]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨fun _ => false, Finset.mem_univ _, y, Finset.mem_univ _, hy⟩
  · rintro ⟨_, _, y, _, hy⟩
    exact ⟨y, hy⟩

/-- Exact work of exploring every separator branch and every residual output vector. -/
def branchedWork (r k : ℕ) : ℕ := 2 ^ r * 2 ^ k

theorem branchedWork_eq : branchedWork r k = 2 ^ (r + k) := by
  simp [branchedWork, Nat.pow_add]

/-- **Full separator cash-out.**  After paying for every one of the `2^r` restriction leaves,
`r+k ≤ n-s` leaves an `s`-bit exponent saving. -/
theorem branchedWork_le_linear_gap (n saving : ℕ) (hs : saving ≤ n)
    (hgap : r + k ≤ n - saving) :
    branchedWork r k ≤ 2 ^ (n - saving) ∧ saving ≤ n := by
  refine ⟨?_, hs⟩
  rw [branchedWork_eq]
  exact Nat.pow_le_pow_right (by norm_num) hgap

/-- Zero-surplus boundary: if separator bits plus pivots exhaust all inputs, ordinary branching
pays exactly brute force. -/
theorem branchedWork_zero_surplus (hfull : r + k = n) :
    branchedWork r k = 2 ^ n := by
  rw [branchedWork_eq, hfull]

end PallLean.Paper93.DeepMath.PathB.ACC0SeparatorPivotBranching

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SeparatorPivotBranching.gateVector_pivotsFor
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SeparatorPivotBranching.sat_iff_top
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SeparatorPivotBranching.branched_search_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SeparatorPivotBranching.branchedWork_le_linear_gap
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SeparatorPivotBranching.branchedWork_zero_surplus
