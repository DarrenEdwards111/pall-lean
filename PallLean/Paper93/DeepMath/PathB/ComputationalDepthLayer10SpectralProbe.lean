import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer10Monotone
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer8LinearBound

/-!
# Layer 10D — spectral instantiation of the observer invariant, and a small-`n` test of (A)

A concrete instantiation of the observer/holographic invariant
(`ComputationalDepthLayer10ObserverHolography.ObserverFrontierHyp`) with a **Ramanujan-type spectral
quantity**, and a computational test of property (A) ("bounded under circuit size") at small `n`.

`specMax f` is the largest `|Walsh/Fourier coefficient|` of `f` — equivalently the maximum magnitude
eigenvalue of the associated `(ℤ/2)ⁿ` Cayley-graph structure (the spectrum where Ramanujan-type bounds
live).  This is the most natural "expander spectral quantity" attached to a Boolean function.

## The test result: **(A) fails for `specMax`** (decisively)

Property (A) requires `f ∈ SIZE n s → specMax f ≤ h s` for a polynomial `h`.  But:

* `dictator_in_SIZE_one` — the dictator `x ↦ x₀` is computed by a **size-1** circuit; and
* `specMax_dictator_two/three/four` (`native_decide`) — its spectral quantity is `2ⁿ` (`4, 8, 16`).

So a single-input, size-`1` function already has the *maximal* spectral quantity `2ⁿ`.  No `h` can satisfy
`2ⁿ ≤ h 1` for all `n` — **`specMax` violates (A) at the most basic level.**  (PARITY behaves the same:
`specMax (parityFn n) = 2ⁿ`, with a small circuit.)

## Honest reading

This is the *expected* outcome and a useful negative result: the naive Fourier/expander spectral quantity
is **not** an observer invariant — it is large on trivially-easy functions (dictators, parity), so it is
both unbounded under circuit size *and* the wrong shape (large on easy functions).  A viable spectral
invariant would have to be *small on every small-circuit function* — exactly the open difficulty, and
exactly what the natural-proofs barrier (Layer 10A) obstructs for any constructive+large quantity.  The
sandbox did its job: it falsified a concrete candidate at small `n`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer10

open Finset

/-- `±1` sign of a bit. -/
def sgn (b : Bool) : ℤ := if b then -1 else 1

/-- Character `χ_S(x) = (-1)^{|S ∩ x|}` — an eigenvalue of the `(ℤ/2)ⁿ` Cayley-graph structure. -/
def chi {n : ℕ} (S x : Fin n → Bool) : ℤ := ∏ i, (if S i && x i then -1 else 1)

/-- The (unnormalized) Walsh/Fourier coefficient: the correlation of `f` with the parity `χ_S`. -/
def walsh {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Fin n → Bool) : ℤ :=
  ∑ x : Fin n → Bool, sgn (f x) * chi S x

/-- **The spectral quantity:** the largest `|Walsh coefficient|` (max Cayley-graph eigenvalue magnitude). -/
def specMax {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ := Finset.univ.sup (fun S => (walsh f S).natAbs)

/-- The dictator `x ↦ x₀` is computed by a **size-1** circuit. -/
theorem dictator_in_SIZE_one {n : ℕ} (h : 0 < n) :
    (fun x : Fin n → Bool => x ⟨0, h⟩) ∈ Layer8.SIZE n 1 :=
  ⟨Layer8.Circuit.input ⟨0, h⟩, le_refl 1, fun _ => rfl⟩

/-! ### Small-`n` test of (A): the size-1 dictator has spectral quantity `2ⁿ` (`native_decide`) -/

theorem specMax_dictator_two : specMax (fun x : Fin 2 → Bool => x 0) = 4 := by native_decide
theorem specMax_dictator_three : specMax (fun x : Fin 3 → Bool => x 0) = 8 := by native_decide
theorem specMax_dictator_four : specMax (fun x : Fin 4 → Bool => x 0) = 16 := by native_decide

/-- PARITY, also a small-circuit function, has the maximal spectral quantity `2ⁿ`. -/
theorem specMax_parity_two : specMax (parityFn 2) = 4 := by native_decide
theorem specMax_parity_three : specMax (parityFn 3) = 8 := by native_decide

end PallLean.Paper93.DeepMath.PathB.Layer10

#print axioms PallLean.Paper93.DeepMath.PathB.Layer10.dictator_in_SIZE_one
#print axioms PallLean.Paper93.DeepMath.PathB.Layer10.specMax_dictator_four
