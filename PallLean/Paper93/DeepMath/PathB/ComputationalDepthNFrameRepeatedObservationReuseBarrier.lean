import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDirectSumCrossingEnergy

/-!
# Repeated observation does not force repeated storage

Any family of observations of a fixed m-bit input factors through one retained
m-bit state. This includes observations indexed by a query/history parameter:
the factorization is simultaneous for all such parameters.

This is only an information-capacity counterexample. Decoders have no runtime
bound here. In particular, this does NOT give a fast SAT algorithm. It shows
why a refresh-cost lower bound must constrain or analyze computation, rather
than count repeated semantic distinctions as newly required storage.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameRepeatedObservationReuseBarrier

abbrev RetainedBits (m : Nat) := Fin m → Bool

/-- Repeated observations all factor through the same retained input. -/
theorem simultaneous_retained_input_factorization
    {m : Nat} {Query Cell : Type}
    (observe : Query → RetainedBits m → Cell) :
    ∃ encode : RetainedBits m → RetainedBits m,
      Function.Injective encode ∧
      ∃ decode : Query → RetainedBits m → Cell,
        ∀ q a, decode q (encode a) = observe q a := by
  exact ⟨id, Function.injective_id, observe, fun _ _ => rfl⟩

/-- Even two fully distinguishing observations of one bit can use the same
one-bit state. Their number times the input width exceeds the state width.
Thus simultaneous exact distinguishability alone cannot justify that product
as a lower bound on stored bits. -/
theorem two_observations_do_not_force_two_stored_bits :
    ∃ encode : RetainedBits 1 → RetainedBits 1,
      Function.Injective encode ∧
      (∃ decode : Fin 2 → RetainedBits 1 → RetainedBits 1,
        ∀ q a, decode q (encode a) = a) ∧
      ¬ (2 * 1 ≤ (1 : Nat)) := by
  refine ⟨id, Function.injective_id, ⟨fun _ a => a, fun _ _ => rfl⟩, ?_⟩
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameRepeatedObservationReuseBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRepeatedObservationReuseBarrier.simultaneous_retained_input_factorization
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRepeatedObservationReuseBarrier.two_observations_do_not_force_two_stored_bits
