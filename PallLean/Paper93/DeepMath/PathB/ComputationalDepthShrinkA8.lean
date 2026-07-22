import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA7a
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKhrK3a

/-!
# Shrinkage brick A8: THE ANDREEV ASSEMBLY (conditional)

The assembly of the shrinkage arc.  Andreev's function is the hard block
function composed with block parities; its DeMorgan formula lower bound follows
from the counting bound (A6) amplified by shrinkage (A5), once the one
genuinely combinatorial fact — the good-restriction count that turns the
average shrinkage into a per-good-restriction gain — is supplied.  That fact is
isolated as a NAMED FENCE, exactly as `ShrinkageGamma2` isolates Håstad:

* `blockXor`/`andreevStar` — Andreev's function;
* **`AndreevShrinkage` (FENCE, unproved)** — the Subbotovskaya `Γ = 3/2`
  shrinkage inequality for `andreevStar` (squared, integer form).  This is the
  good-restriction counting content of Andreev 1987 — REAL mathematics, not
  discharged here;
* **`ShrinkageGamma2` (FENCE, unproved)** — the Håstad `Γ = 2` analogue;
* **`andreev_formula_lb` (proved from `AndreevShrinkage`)** — every DeMorgan
  formula computing `andreevStar` of a hard block function has size
  `≥ B·m^{3/2}/4`;
* **`andreev_five_halves` (proved from `AndreevShrinkage`)** — under the
  standard parameter optimisation, formula size `≥ N^{5/2}/4` (Andreev's
  `n^{5/2}`, conditional);
* **`andreev_cubed` (proved from `ShrinkageGamma2`)** — the same route gives
  `N^3` (conditional on the Håstad fence).

We have NOT proved `n^{5/2}` unconditionally: the good-restriction count is
fenced.  And none of this is `P ≠ NP` — it is a DeMorgan-formula bound, capped
below `NC¹`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-! ### Andreev's function -/

/-- Parity of block `i` (the `m` coordinates `emb hm i ·`). -/
def blockXor {k m : ℕ} (hm : 0 < m) (y : Fin (k * m) → Bool) (i : Fin k) : Bool :=
  decide (Odd (Finset.univ.filter (fun j : Fin m => y (emb hm i j) = true)).card)

/-- Andreev's function with the table fixed to a hard `k`-bit function `f`:
`A(y) = f(⊕block₁, …, ⊕block_k)`. -/
def andreevStar {k m : ℕ} (hm : 0 < m) (f : (Fin k → Bool) → Bool) :
    (Fin (k * m) → Bool) → Bool :=
  fun y => f (fun i => blockXor hm y i)

/-! ### The fences -/

/-- **FENCE (unproved): Subbotovskaya `Γ = 3/2` shrinkage for `andreevStar`.**
The genuine combinatorial content — the good-restriction count of Andreev 1987.
In squared integer form: `L(andreevStar) ≥ B·m^{3/2}/4`. -/
def AndreevShrinkage : Prop :=
  ∀ (k m : ℕ) (hm : 0 < m) (f : (Fin k → Bool) → Bool),
    dmsizeC f ^ 2 * m ^ 3 ≤ 16 * dmsizeC (andreevStar hm f) ^ 2

/-- **FENCE (unproved): Håstad `Γ = 2` shrinkage for `andreevStar`.**
In squared integer form: `L(andreevStar) ≥ B·m²/4`. -/
def ShrinkageGamma2 : Prop :=
  ∀ (k m : ℕ) (hm : 0 < m) (f : (Fin k → Bool) → Bool),
    dmsizeC f ^ 2 * m ^ 4 ≤ 16 * dmsizeC (andreevStar hm f) ^ 2

/-! ### The conditional assembly -/

/-- **THE AMPLIFIED FORMULA LOWER BOUND (proved from `AndreevShrinkage`)**:
a hard block function makes `andreevStar` need `B·m^{3/2}/4` leaves. -/
theorem andreev_formula_lb (hfence : AndreevShrinkage)
    (k m : ℕ) (hm : 0 < m) (B : ℕ)
    (hnum : (2 * B + 1) * (2 * k + 4) ^ (2 * B) < 2 ^ (2 ^ k)) :
    ∃ f : (Fin k → Bool) → Bool, ∀ t : DMTree (k * m),
      (∀ x, t.eval x = andreevStar hm f x) →
      B ^ 2 * m ^ 3 ≤ 16 * t.lsize ^ 2 := by
  obtain ⟨f, hf⟩ := exists_hard_card k B hnum
  refine ⟨f, fun t ht => ?_⟩
  have hshrink := hfence k m hm f
  have hbridge : dmsizeC (andreevStar hm f) ≤ t.lsize := dmsizeC_le _ t ht
  have hB2 : B ^ 2 * m ^ 3 ≤ dmsizeC f ^ 2 * m ^ 3 := by
    have : B ^ 2 ≤ dmsizeC f ^ 2 := Nat.pow_le_pow_left hf 2
    exact Nat.mul_le_mul_right _ this
  have hbr2 : 16 * dmsizeC (andreevStar hm f) ^ 2 ≤ 16 * t.lsize ^ 2 := by
    have : dmsizeC (andreevStar hm f) ^ 2 ≤ t.lsize ^ 2 :=
      Nat.pow_le_pow_left hbridge 2
    exact Nat.mul_le_mul_left _ this
  calc B ^ 2 * m ^ 3
      ≤ dmsizeC f ^ 2 * m ^ 3 := hB2
    _ ≤ 16 * dmsizeC (andreevStar hm f) ^ 2 := hshrink
    _ ≤ 16 * t.lsize ^ 2 := hbr2

/-- **ANDREEV `n^{5/2}` (proved from `AndreevShrinkage`)**: under the standard
parameter optimisation (`hnum` = counting, `hopt` = the `2^k ≈ N·k^{5/2}`
balance, both met by `k ≈ log N`), every DeMorgan formula for `andreevStar` has
`≥ N^{5/2}/4` leaves. -/
theorem andreev_five_halves (hfence : AndreevShrinkage)
    (k m N : ℕ) (hm : 0 < m) (hN : N = k * m) (B : ℕ)
    (hnum : (2 * B + 1) * (2 * k + 4) ^ (2 * B) < 2 ^ (2 ^ k))
    (hopt : N ^ 5 ≤ B ^ 2 * m ^ 3) :
    ∃ f : (Fin k → Bool) → Bool, ∀ t : DMTree (k * m),
      (∀ x, t.eval x = andreevStar hm f x) → N ^ 5 ≤ 16 * t.lsize ^ 2 := by
  obtain ⟨f, hf⟩ := andreev_formula_lb hfence k m hm B hnum
  exact ⟨f, fun t ht => le_trans hopt (hf t ht)⟩

/-- **ANDREEV `n³` (proved from `ShrinkageGamma2`)**: the Håstad exponent gives
`≥ N³/4` leaves under the corresponding parameter balance. -/
theorem andreev_cubed (hfence : ShrinkageGamma2)
    (k m N : ℕ) (hm : 0 < m) (hN : N = k * m) (B : ℕ)
    (hnum : (2 * B + 1) * (2 * k + 4) ^ (2 * B) < 2 ^ (2 ^ k))
    (hopt : N ^ 6 ≤ B ^ 2 * m ^ 4) :
    ∃ f : (Fin k → Bool) → Bool, ∀ t : DMTree (k * m),
      (∀ x, t.eval x = andreevStar hm f x) → N ^ 6 ≤ 16 * t.lsize ^ 2 := by
  obtain ⟨f, hf⟩ := exists_hard_card k B hnum
  refine ⟨f, fun t ht => ?_⟩
  have hshrink := hfence k m hm f
  have hbridge : dmsizeC (andreevStar hm f) ≤ t.lsize := dmsizeC_le _ t ht
  have hB2 : B ^ 2 * m ^ 4 ≤ dmsizeC f ^ 2 * m ^ 4 := by
    have : B ^ 2 ≤ dmsizeC f ^ 2 := Nat.pow_le_pow_left hf 2
    exact Nat.mul_le_mul_right _ this
  have hbr2 : 16 * dmsizeC (andreevStar hm f) ^ 2 ≤ 16 * t.lsize ^ 2 := by
    have : dmsizeC (andreevStar hm f) ^ 2 ≤ t.lsize ^ 2 :=
      Nat.pow_le_pow_left hbridge 2
    exact Nat.mul_le_mul_left _ this
  calc N ^ 6
      ≤ B ^ 2 * m ^ 4 := hopt
    _ ≤ dmsizeC f ^ 2 * m ^ 4 := hB2
    _ ≤ 16 * dmsizeC (andreevStar hm f) ^ 2 := hshrink
    _ ≤ 16 * t.lsize ^ 2 := hbr2

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.andreev_formula_lb
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.andreev_five_halves
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.andreev_cubed
