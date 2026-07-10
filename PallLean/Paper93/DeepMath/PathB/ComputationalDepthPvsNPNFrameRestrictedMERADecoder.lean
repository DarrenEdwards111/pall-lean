import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPNFrameHolographicDecodingComplexity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthProfileCount

/-!
# Restricted N-Frame MERA decoders: a proved polynomial accessible-rank ceiling

Book 1 proposes MERA as the local multiscale geometry of the observer boundary.  This file proves the
restricted theorem that proposal actually supports.

A decoder family has:

* a fixed finite bond alphabet of `bondStates` states;
* a fixed causal-cone width factor `coneFactor`;
* at most `log₂ n` MERA layers;
* accessible SPDP/task rank bounded by the number of causal-cone bond profiles.

The causal cone therefore contains at most `coneFactor * log₂ n` bonds, so its accessible rank is at
most

```text
bondStates ^ (coneFactor * log₂ n)
  ≤ n ^ (coneFactor * (log₂ bondStates + 1)).
```

This is a genuine polynomial ceiling.  Any target whose correctness requires rank above that ceiling
cannot be decoded by the restricted MERA family.

The theorem is deliberately restricted.  It does not say that every polynomial-time algorithm has
fixed bond dimension, logarithmic MERA depth, or a local causal cone, and it does not assert an SPDP
lower bound for SAT.  Those are separate bridge/hardness obligations.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPNFrameRestrictedMERADecoder

open PallLean.Paper93.DeepMath.PathB.ProfileCount

/-- A family of local bounded-bond, logarithmic-depth MERA decoders.

`rank_causal_cone` is the standard tensor-network counting statement: the task-relevant accessible
rank cannot exceed the number of assignments to the bonds crossing the causal cone. -/
structure BoundedBondLocalMERADecoderFamily where
  bondStates : Nat
  coneFactor : Nat
  bondStates_pos : 1 ≤ bondStates
  layers : Nat → Nat
  accessibleRank : Nat → Nat
  layers_le_log : ∀ n, layers n ≤ Nat.log 2 n
  rank_causal_cone :
    ∀ n, accessibleRank n ≤ bondStates ^ (coneFactor * layers n)

namespace BoundedBondLocalMERADecoderFamily

/-- The fixed polynomial exponent supplied by bond dimension and causal-cone width. -/
def polyExponent (M : BoundedBondLocalMERADecoderFamily) : Nat :=
  M.coneFactor * (Nat.log 2 M.bondStates + 1)

/-- **Restricted MERA accessible-rank ceiling.**  Fixed bond dimension, fixed causal-cone width and
logarithmic depth force polynomially bounded accessible rank. -/
theorem accessibleRank_le_poly (M : BoundedBondLocalMERADecoderFamily)
    (n : Nat) (hn : 1 ≤ n) :
    M.accessibleRank n ≤ n ^ M.polyExponent := by
  have hbase : 0 < M.bondStates := lt_of_lt_of_le Nat.zero_lt_one M.bondStates_pos
  have hexp : M.coneFactor * M.layers n ≤ M.coneFactor * Nat.log 2 n :=
    Nat.mul_le_mul_left M.coneFactor (M.layers_le_log n)
  calc
    M.accessibleRank n
        ≤ M.bondStates ^ (M.coneFactor * M.layers n) := M.rank_causal_cone n
    _ ≤ M.bondStates ^ (M.coneFactor * Nat.log 2 n) :=
      Nat.pow_le_pow_right hbase hexp
    _ ≤ n ^ (M.coneFactor * (Nat.log 2 M.bondStates + 1)) :=
      profile_count_le_poly M.bondStates M.coneFactor n hn
    _ = n ^ M.polyExponent := rfl

/-- Correct decoding of a target rank demand means the target's task-relevant SPDP rank survives in
the MERA decoder's accessible causal-cone rank. -/
def PreservesRequiredRank (M : BoundedBondLocalMERADecoderFamily)
    (requiredRank : Nat → Nat) : Prop :=
  ∀ n, requiredRank n ≤ M.accessibleRank n

/-- **Restricted MERA decoder lower bound.**  At any size where the required task rank exceeds the
polynomial causal-cone ceiling, no decoder in this fixed MERA family can preserve the required rank. -/
theorem not_preservesRequiredRank_of_exceeds_ceiling
    (M : BoundedBondLocalMERADecoderFamily) (requiredRank : Nat → Nat)
    (n : Nat) (hn : 1 ≤ n)
    (hhard : n ^ M.polyExponent < requiredRank n) :
    ¬ M.PreservesRequiredRank requiredRank := by
  intro hpres
  exact (not_lt_of_ge (le_trans (hpres n) (M.accessibleRank_le_poly n hn))) hhard

/-- Pointwise contradiction form, convenient when correctness is available only at one input size. -/
theorem no_correct_decoder_at_size
    (M : BoundedBondLocalMERADecoderFamily) (requiredRank : Nat → Nat)
    (n : Nat) (hn : 1 ≤ n)
    (hcorrect : requiredRank n ≤ M.accessibleRank n)
    (hhard : n ^ M.polyExponent < requiredRank n) : False := by
  exact (not_lt_of_ge (le_trans hcorrect (M.accessibleRank_le_poly n hn))) hhard

/-- A canonical family saturating the causal-cone profile count.  This shows the exponential-in-cone
count used above is not an artifact of a loose proof. -/
def profileSaturatedFamily (bondStates coneFactor : Nat) (hbond : 1 ≤ bondStates) :
    BoundedBondLocalMERADecoderFamily where
  bondStates := bondStates
  coneFactor := coneFactor
  bondStates_pos := hbond
  layers := fun n => Nat.log 2 n
  accessibleRank := fun n => bondStates ^ (coneFactor * Nat.log 2 n)
  layers_le_log := fun _ => le_rfl
  rank_causal_cone := fun _ => le_rfl

theorem profileSaturated_accessibleRank (bondStates coneFactor : Nat)
    (hbond : 1 ≤ bondStates) (n : Nat) :
    (profileSaturatedFamily bondStates coneFactor hbond).accessibleRank n =
      bondStates ^ (coneFactor * Nat.log 2 n) := rfl

/-- A diagonal rank demand just one above this family's polynomial ceiling is already excluded.  This
is a non-vacuity test for the restricted theorem, not an identification of the demand with SAT. -/
def diagonalRequiredRank (M : BoundedBondLocalMERADecoderFamily) (n : Nat) : Nat :=
  n ^ M.polyExponent + 1

theorem diagonalRequiredRank_not_preserved
    (M : BoundedBondLocalMERADecoderFamily) (n : Nat) (hn : 1 ≤ n) :
    ¬ M.PreservesRequiredRank M.diagonalRequiredRank := by
  apply M.not_preservesRequiredRank_of_exceeds_ceiling M.diagonalRequiredRank n hn
  simp [diagonalRequiredRank]

/-!
## Exact remaining bridge to SAT

To instantiate `not_preservesRequiredRank_of_exceeds_ceiling` for SAT, two new facts are required:

1. a concrete NP-complete residual family with task-relevant projected SPDP rank exceeding
   `n ^ M.polyExponent`;
2. a correctness/transport theorem showing that a decoder for that family must satisfy
   `PreservesRequiredRank`.

For the restricted bounded-bond MERA class these are meaningful class-specific lower-bound targets.
Extending the conclusion to all of P would additionally require every polynomial-time SAT solver to
compile into such a fixed-bond, logarithmic-depth local MERA family, which is not known and is not
asserted here.
-/

end BoundedBondLocalMERADecoderFamily
end PallLean.Paper93.DeepMath.PathB.PvsNPNFrameRestrictedMERADecoder

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameRestrictedMERADecoder.BoundedBondLocalMERADecoderFamily.accessibleRank_le_poly
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameRestrictedMERADecoder.BoundedBondLocalMERADecoderFamily.not_preservesRequiredRank_of_exceeds_ceiling
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameRestrictedMERADecoder.BoundedBondLocalMERADecoderFamily.no_correct_decoder_at_size
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameRestrictedMERADecoder.BoundedBondLocalMERADecoderFamily.profileSaturated_accessibleRank
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameRestrictedMERADecoder.BoundedBondLocalMERADecoderFamily.diagonalRequiredRank_not_preserved
