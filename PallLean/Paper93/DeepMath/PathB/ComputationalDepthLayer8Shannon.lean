import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer8GeneralCircuit
import Mathlib.Data.Fintype.BigOperators

/-!
# Layer 8 (general circuits, R1) — the Shannon counting bound, pigeonhole core

The logical heart of the **Shannon counting lower bound** (`SCOPE_LAYER8_GENERAL_CIRCUITS.md`, R1): there
are only `2^{2ⁿ}` Boolean functions on `n` bits, so if the size-`≤ s` circuits are covered by a finite set
of `< 2^{2ⁿ}` circuits, **some function is not computable by any size-`≤ s` circuit**.

`exists_hard_function` is this pigeonhole, fully proved (sorry-free).  It reduces the Shannon bound to a
purely combinatorial **counting hypothesis**: exhibit a covering `Finset` of circuits with cardinality
`< 2^{2ⁿ}`.  At the Shannon threshold `s ≈ 2ⁿ/n` such a covering exists because there are only
single-exponentially-many circuits of size `≤ s`.

**Honest status.**  This is a *nonconstructive existence* of a hard function — a genuine general-circuit
lower bound, but it names no explicit function.  The *explicit* super-polynomial frontier remains open and
fenced in the scope doc; nothing here approaches it.

**Remaining for an unconditional R1 (R1b).**  Construct the covering `Finset` with a single-exponential
card bound and discharge `hcard` at `s ≈ 2ⁿ/n`.  Note the *naive* over-approximation — `circuitsLE (s+1) =
leaves ∪ not(circuitsLE s) ∪ and/or(circuitsLE s × circuitsLE s)` — has card recurrence
`B(s+1) ≤ (n+2) + B(s) + 2·B(s)²`, which is **doubly** exponential in `s` and far too loose; R1b needs the
exact-size (Catalan) convolution or a straight-line-program encoding for the correct single-exponential
`((n+O(1))·s²)^s`-type bound.  That count is real combinatorics, identified here, not faked.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer8

open Finset

/-- **Shannon counting bound (pigeonhole core).**  If every circuit of size `≤ s` lies in a finite set `E`
with `E.card < 2^{2ⁿ}`, then some Boolean function on `n` bits is **not** in `SIZE n s` — there are more
functions (`2^{2ⁿ}`) than circuits available.  (Nonconstructive: exhibits no explicit hard function.) -/
theorem exists_hard_function {n s : ℕ} (E : Finset (Circuit n))
    (hcover : ∀ c : Circuit n, c.size ≤ s → c ∈ E)
    (hcard : E.card < 2 ^ (2 ^ n)) :
    ∃ f : (Fin n → Bool) → Bool, f ∉ SIZE n s := by
  classical
  have hcardfun : Fintype.card ((Fin n → Bool) → Bool) = 2 ^ (2 ^ n) := by
    simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  -- Every `SIZE n s` function is the evaluation of some circuit in `E`.
  have hsub : SIZE n s ⊆ ↑(E.image Circuit.eval) := by
    rintro f ⟨c, hcs, hcf⟩
    rw [Finset.coe_image]
    exact ⟨c, hcover c hcs, funext hcf⟩
  by_contra hcon
  push_neg at hcon
  have hall : ∀ f, f ∈ E.image Circuit.eval := fun f => Finset.mem_coe.mp (hsub (hcon f))
  have huniv : (Finset.univ : Finset ((Fin n → Bool) → Bool)) ⊆ E.image Circuit.eval :=
    fun f _ => hall f
  have h2 : (2 : ℕ) ^ (2 ^ n) ≤ E.card := by
    calc (2 : ℕ) ^ (2 ^ n) = Fintype.card ((Fin n → Bool) → Bool) := hcardfun.symm
      _ = (Finset.univ : Finset ((Fin n → Bool) → Bool)).card := (Finset.card_univ).symm
      _ ≤ (E.image Circuit.eval).card := Finset.card_le_card huniv
      _ ≤ E.card := Finset.card_image_le
  omega

end PallLean.Paper93.DeepMath.PathB.Layer8

#print axioms PallLean.Paper93.DeepMath.PathB.Layer8.exists_hard_function
