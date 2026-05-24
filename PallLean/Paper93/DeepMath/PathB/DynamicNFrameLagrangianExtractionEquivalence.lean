import PallLean.Paper93.DeepMath.PathB.DynamicNFrameLagrangianInvariant
import PallLean.Paper93.DeepMath.PathB.FaithfulLiveMinorObstruction

/-!
# Dynamic N-frame/Lagrangian extraction equivalence

This file proves the exact logical strength of the current dynamic
N-frame/Lagrangian live-minor theorem.

Because `DynamicNFrameLagrangianObserver` still carries an arbitrary
`stateActionRank : Nat -> Nat`, any SAT-deciding DTM can be paired with the
constant-zero rank accounting function.  That zero-rank presentation cannot
contain a positive binomial live minor.  Therefore the universal dynamic
N-frame/Lagrangian extraction theorem is not a smaller lemma: it is equivalent
to the no-SAT-decider theorem in this repository's polynomial-time DTM model.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- The dynamic N-frame/Lagrangian extraction theorem already implies that no
DTM in the repository's polynomial-time DTM model decides SAT under the chosen
encoding.

Proof route: dynamic extraction gives faithful trajectory extraction; the
existing zero-rank faithful presentation obstruction then rules out any
SAT-deciding DTM. -/
theorem no_DTMDecidesSATWithEncoding_of_universalDynamicNFrameLagrangianExtraction
    (enc : ThreeCNFEncoding)
    (hextract : UniversalDynamicNFrameLagrangianExtraction enc) :
    Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) :=
  no_DTMDecidesSATWithEncoding_of_universalFaithfulExtraction enc
    (faithfulExtraction_of_dynamicNFrameLagrangianExtraction enc hextract)

/-- Conversely, if no DTM decides SAT under the encoding, then the universal
dynamic extraction predicate is vacuously true: there are no
`DynamicNFrameLagrangianObserver` witnesses to inspect. -/
theorem universalDynamicNFrameLagrangianExtraction_of_no_DTMDecidesSATWithEncoding
    (enc : ThreeCNFEncoding)
    (hno : Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M)) :
    UniversalDynamicNFrameLagrangianExtraction enc := by
  intro c
  let k : Nat := Nat.max 20 (4 * (c + 1))
  let n : Nat := 2 ^ k
  refine ⟨n, ?_, ?_, ?_⟩
  · dsimp [n, k]
    exact Nat.pow_le_pow_right
      (by norm_num : 1 <= 2)
      (Nat.le_max_left 20 (4 * (c + 1)))
  · dsimp [n, k]
    have hpow :
        2 ^ (4 * (c + 1)) <= 2 ^ Nat.max 20 (4 * (c + 1)) :=
      Nat.pow_le_pow_right
        (by norm_num : 1 <= 2)
        (Nat.le_max_right 20 (4 * (c + 1)))
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow
  · intro L
    exact False.elim (hno ⟨L.M, L.decides⟩)

/-- Exact characterization of the current dynamic N-frame/Lagrangian live-minor
target.

This is the honest closure status: the target is paper-faithful as a dynamic
observer statement, but mathematically it is the SAT lower bound itself in the
current definitions. -/
theorem universalDynamicNFrameLagrangianExtraction_iff_no_DTMDecidesSATWithEncoding
    (enc : ThreeCNFEncoding) :
    UniversalDynamicNFrameLagrangianExtraction enc ↔
      Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) := by
  constructor
  · exact no_DTMDecidesSATWithEncoding_of_universalDynamicNFrameLagrangianExtraction
      enc
  · exact universalDynamicNFrameLagrangianExtraction_of_no_DTMDecidesSATWithEncoding
      enc

/-! ## Kernel-only axiom trace -/

#print axioms no_DTMDecidesSATWithEncoding_of_universalDynamicNFrameLagrangianExtraction
#print axioms universalDynamicNFrameLagrangianExtraction_of_no_DTMDecidesSATWithEncoding
#print axioms universalDynamicNFrameLagrangianExtraction_iff_no_DTMDecidesSATWithEncoding

end PallLean.Paper93.DeepMath.PathB
