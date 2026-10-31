import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPITVariableWall

/-!
# The derandomization program is non-vacuous: a poly-size hitting set for bounded arity

`HittingSet.small_hitting_forces_lower_bound` left the object "a poly-size hitting-set family" as an
open socket.  This file shows the socket is **not vacuous**: for a genuine restricted class — degree-`d`
polynomials in a **fixed** number of variables `n`, over an infinite field — an explicit poly-size
hitting-set family provably *exists*.

* **`PolyHittingFamily n`** — the socketed object made concrete: for each degree bound `d`, a hitting
  set `H d` for total degree `d`, of size bounded by a fixed polynomial `c·(d+1)ᵉ` in the degree.
* **`boundedArityHittingFamily` (proved)** — over an infinite field, the Schwartz–Zippel grid gives
  such a family with `c = 1`, `e = n`: size exactly `(d+1)ⁿ`, polynomial in the degree `d`.
* **`poly_hitting_family_exists` (proved)** — hence for every fixed arity the poly-size hitting set
  is realized; the derandomization program has real, non-trivial instances.

**Honest scope.**  The exponent is `e = n`, so this is polynomial in the degree `d` for each **fixed**
number of variables `n` — and that is exactly the regime where derandomization is easy (`PITVariableWall`
already saw `n = 1` is linear).  It is **not** polynomial in the *combined* input when `n` grows with
the input size, because `(d+1)ⁿ` is then exponential — that unbounded-arity case is the genuine open
target and is **not** proved here.  So this brick proves the program is non-vacuous without pretending
to cross the open frontier.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundedArityHitting

open PallLean.Paper93.DeepMath.PathB.SchwartzZippel
open PallLean.Paper93.DeepMath.PathB.HittingSet
open PallLean.Paper93.DeepMath.PathB.PITVariableWall

variable {F : Type*} [Field F] [DecidableEq F]

/-- **A poly-size hitting-set family** in `n` variables — the object `HittingSet` socketed as open in
general.  For each degree bound `d` it provides a hitting set `H d` for total degree `d`, and its size
is bounded by a *fixed* polynomial `c·(d+1)ᵉ` in the degree (the exponent `e` and constant `c` do not
depend on `d`). -/
structure PolyHittingFamily (n : ℕ) where
  /-- The hitting set for degree bound `d`. -/
  H : ℕ → Finset (Fin n → F)
  /-- Each `H d` really is a hitting set for total degree `d`. -/
  hits : ∀ d, IsHittingSet (H d) d
  /-- Polynomial-size constant. -/
  c : ℕ
  /-- Polynomial-size exponent. -/
  e : ℕ
  /-- The size is bounded by the fixed polynomial `c·(d+1)ᵉ`. -/
  poly : ∀ d, (H d).card ≤ c * (d + 1) ^ e

/-- **A poly-size hitting-set family exists for bounded arity (proved).**  Over an infinite field, for
every fixed number of variables `n`, the Schwartz–Zippel grid (side `d+1`) yields a hitting-set family
of size exactly `(d+1)ⁿ` — polynomial in the degree `d`.  This is the previously-open poly-size
hitting-set object, realized in the bounded-arity regime. -/
noncomputable def boundedArityHittingFamily [Infinite F] (n : ℕ) : PolyHittingFamily (F := F) n where
  H d := Fintype.piFinset (fun _ : Fin n => (Infinite.exists_subset_card_eq F (d + 1)).choose)
  hits d := grid_is_hitting_set _ (by
    rw [(Infinite.exists_subset_card_eq F (d + 1)).choose_spec]; exact Nat.lt_succ_self d)
  c := 1
  e := n
  poly d := le_of_eq (by
    rw [grid_card_pow _ (Infinite.exists_subset_card_eq F (d + 1)).choose_spec, one_mul])

/-- **The program is non-vacuous (proved).**  For every fixed arity `n` over an infinite field, the
poly-size hitting-set socket of `HittingSet` is *realized* by an explicit family of size `(d+1)ⁿ`.
The unbounded-arity case (where `n` grows with the input) remains the open target. -/
theorem poly_hitting_family_exists [Infinite F] (n : ℕ) :
    ∃ fam : PolyHittingFamily (F := F) n, fam.c = 1 ∧ fam.e = n :=
  ⟨boundedArityHittingFamily n, rfl, rfl⟩

end PallLean.Paper93.DeepMath.PathB.BoundedArityHitting

#print axioms PallLean.Paper93.DeepMath.PathB.BoundedArityHitting.boundedArityHittingFamily
#print axioms PallLean.Paper93.DeepMath.PathB.BoundedArityHitting.poly_hitting_family_exists
