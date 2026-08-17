import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SeparatorPivotBranching

/-!
# Separator-pivot universality and the padding no-go

Audit of the preceding separator-pivot cash-out reveals a crucial normalization issue.  The actual
active input type has `r+k` bits: `r` separator bits and `k` private pivots.  Its exhaustive branch
cost `2^(r+k)` is therefore exactly brute force on the active variables.  Comparing it with a larger
external `n` creates an apparent `n-(r+k)` saving only by counting unused/padded variables.

This file formalizes that correction and strengthens it semantically.  Every oracle control embeds
unchanged into a separator-pivot circuit, and on a canonical encoded slice the circuit evaluates
exactly as the original control.  Therefore the pivot layer cannot simplify an arbitrary top
control; it merely transports it.

The observer route must consequently obtain a saving relative to the number of **active** variables,
through control-layer collapse, cross-branch reuse, or another nontrivial semantic contraction.
Private-pivot surjectivity alone is a universality/no-go property, not a Williams-strength speedup.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SeparatorPivotUniversalityNoGo

open PallLean.Paper93.DeepMath.PathB.ACC0OracleControl
open PallLean.Paper93.DeepMath.PathB.ACC0SeparatorPivotBranching

variable {r k : ℕ}

/-- Embed any top control over an arbitrary separator effect. -/
def embedControl (effect : (Fin r → Bool) → Fin k → Bool) (C : OracleControl k) :
    SeparatorPivotCircuit r k := ⟨⟨effect⟩, C⟩

/-- Canonical encoding of a requested control input into private pivots at separator branch `σ`. -/
def encodePivots (effect : (Fin r → Bool) → Fin k → Bool) (σ : Fin r → Bool)
    (y : Fin k → Bool) : Fin k → Bool := fun j => effect σ j != y j

/-- **Universality (proved): every control is preserved exactly on the encoded slice.** -/
theorem embedControl_eval (effect : (Fin r → Bool) → Fin k → Bool) (C : OracleControl k)
    (σ : Fin r → Bool) (y : Fin k → Bool) :
    (embedControl effect C).eval σ (encodePivots effect σ y) = controlEval C y := by
  unfold SeparatorPivotCircuit.eval embedControl
  have henc : encodePivots effect σ y = pivotsFor (⟨effect⟩ : SeparatorPivotLayer r k) σ y := rfl
  rw [henc, gateVector_pivotsFor]

/-- Active-variable normalization: separator branching is exactly brute force on its `r+k` inputs. -/
theorem active_work_eq_bruteforce : branchedWork r k = 2 ^ (r + k) :=
  branchedWork_eq

/-- No positive exponent saving exists relative to the active-variable count. -/
theorem no_positive_active_saving (saving : ℕ) (hpos : 0 < saving)
    (hle : saving ≤ r + k) :
    ¬ branchedWork r k ≤ 2 ^ ((r + k) - saving) := by
  rw [branchedWork_eq]
  have hexp : (r + k) - saving < r + k := by omega
  have hp : 2 ^ ((r + k) - saving) < 2 ^ (r + k) :=
    Nat.pow_lt_pow_right (by norm_num) hexp
  omega

/-- If the active layer is compared with a larger ambient `n`, the entire apparent exponent saving
is exactly the unused-variable count `n-(r+k)`. -/
theorem padded_gap_is_unused (n : ℕ) (hactive : r + k ≤ n) :
    branchedWork r k = 2 ^ (n - (n - (r + k))) := by
  rw [branchedWork_eq]
  congr
  omega

/-- The canonical embedding preserves satisfiability in both directions, so an arbitrary control
SAT instance survives intact inside the separator-pivot fragment. -/
theorem embedControl_sat_iff (effect : (Fin r → Bool) → Fin k → Bool) (C : OracleControl k) :
    (∃ σ p, (embedControl effect C).eval σ p = true) ↔
      ∃ y, controlEval C y = true :=
  sat_iff_top (embedControl effect C)

end PallLean.Paper93.DeepMath.PathB.ACC0SeparatorPivotUniversalityNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SeparatorPivotUniversalityNoGo.embedControl_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SeparatorPivotUniversalityNoGo.no_positive_active_saving
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SeparatorPivotUniversalityNoGo.padded_gap_is_unused
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SeparatorPivotUniversalityNoGo.embedControl_sat_iff
