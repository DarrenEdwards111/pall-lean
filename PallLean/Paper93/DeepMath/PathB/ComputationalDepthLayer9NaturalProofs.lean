import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer9KarpLipton
import Mathlib.Data.Fintype.BigOperators

/-!
# Layer 9 — the natural-proofs barrier (Razborov–Rudich), as a conditional meta-theorem

Honest Layer-9 infrastructure (per `SCOPE_LAYER8_EXPLICIT_LOWER_BOUND_FRONTIER.md` §6's "could" list):
the Razborov–Rudich *natural proofs* framework as **definitions** plus the conditional barrier theorem
"a natural property useful against a class breaks any pseudorandom family in that class."

This is a statement **about why most lower-bound techniques fail**, **not** a circuit lower bound, and it
makes **no** progress toward `NP ⊄ P/poly` or `P ≠ NP`.

## The three Razborov–Rudich conditions

A *natural property* `P` (a predicate on truth tables) is:
* **constructive** — `P` is efficiently computable from the truth table.  *Not enforced here* (it needs a
  complexity model); it is exactly the property that makes `P` a *legal efficient test*, so it is reflected
  by requiring PRF security to apply to `P` (`SecurePRF … P`).
* **large** (`NaturalProperty.large`) — `P` accepts more than `negl` truth tables (a `1/poly` fraction,
  far above the negligible security bound).
* **useful** (`Useful`) — `P f = true` certifies `f ∉ C` (no small circuit).

## The barrier

`razborov_rudich_barrier` / `no_natural_property_if_secure_prf`: if `C` contains a pseudorandom family `G`
that `P` cannot distinguish from random (security: any test rejecting all of `G` accepts at most `negl`),
then a useful + large `P` is impossible — usefulness forces `P` to reject all of `G` (it is in `C`), so
security caps its acceptance at `negl`, contradicting largeness.  Equivalently: **secure PRFs in `C` ⇒ no
natural property useful against `C`** — so a lower bound against `C` must use an *unnatural* argument.

The PRF existence/security is a standard *cryptographic assumption*, fenced here as the hypothesis
`SecurePRF`; it is never asserted.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer9

open Finset

/-- A Boolean function on `n` bits (a truth table). -/
abbrev BoolFn (n : ℕ) := (Fin n → Bool) → Bool

/-- A property is **useful** against a function class `C` if accepting a truth table certifies that the
function lies outside `C` (has no `C`-circuit). -/
def Useful {n : ℕ} (P : BoolFn n → Bool) (C : Set (BoolFn n)) : Prop := ∀ f, P f = true → f ∉ C

/-- Usefulness forces `P` to **reject every function in the class**. -/
theorem useful_rejects_class {n : ℕ} {P : BoolFn n → Bool} {C : Set (BoolFn n)}
    (hUseful : Useful P C) {g : BoolFn n} (hgC : g ∈ C) : P g = false := by
  cases h : P g with
  | false => rfl
  | true => exact absurd hgC (hUseful g h)

/-- A **natural property** (Razborov–Rudich), minus the constructivity condition (which is fenced — see the
module docstring): a predicate on truth tables that is *large* and *useful* against `C`.  `negl` is the
security/negligibility threshold the largeness must exceed. -/
structure NaturalProperty (n : ℕ) (C : Set (BoolFn n)) (negl : ℕ) where
  /-- the truth-table predicate -/
  pred : BoolFn n → Bool
  /-- **largeness**: accepts more than `negl` truth tables -/
  large : negl < (Finset.univ.filter (fun f => pred f = true)).card
  /-- **usefulness**: accepting certifies "outside `C`" -/
  useful : Useful pred C

/-- A **pseudorandom family secure against the test `P`**: `G ⊆ C`, and `P` cannot distinguish `G` from
random — if `P` rejects all of `G`, then `P` accepts at most `negl` truth tables overall.  (This is the
cryptographic assumption; `P`'s constructivity is what makes it a legal test the security applies to.) -/
def SecurePRF {n : ℕ} (C : Set (BoolFn n)) (negl : ℕ) (G : Finset (BoolFn n))
    (P : BoolFn n → Bool) : Prop :=
  (∀ g ∈ G, g ∈ C) ∧
    ((∀ g ∈ G, P g = false) → (Finset.univ.filter (fun f => P f = true)).card ≤ negl)

open Classical in
/-- **Razborov–Rudich barrier (core).**  A *useful* and *large* property `P` cannot coexist with a
pseudorandom family `G ⊆ C` secure against `P`: usefulness ⇒ `P` rejects all of `G` ⇒ (security) `P`
accepts `≤ negl` ⇒ contradicts largeness.  A statement *about the barrier*, not a lower bound. -/
theorem razborov_rudich_barrier {n : ℕ} (P : BoolFn n → Bool) (C : Set (BoolFn n))
    (G : Finset (BoolFn n)) (negl : ℕ)
    (hUseful : Useful P C)
    (hGC : ∀ g ∈ G, g ∈ C)
    (hLarge : negl < (Finset.univ.filter (fun f => P f = true)).card)
    (hSecure : (∀ g ∈ G, P g = false) → (Finset.univ.filter (fun f => P f = true)).card ≤ negl) :
    False := by
  have hrej : ∀ g ∈ G, P g = false := fun g hg => useful_rejects_class hUseful (hGC g hg)
  exact absurd (hSecure hrej) (not_le.mpr hLarge)

/-- **Secure PRFs in `C` ⇒ no natural property useful against `C`** (packaged form).  Hence any lower bound
against `C` must be *unnatural*.  Conditional on the cryptographic `SecurePRF` assumption — never asserted.
-/
theorem no_natural_property_if_secure_prf {n : ℕ} (C : Set (BoolFn n)) (negl : ℕ)
    (G : Finset (BoolFn n)) (NP : NaturalProperty n C negl)
    (hsec : SecurePRF C negl G NP.pred) : False :=
  razborov_rudich_barrier NP.pred C G negl NP.useful hsec.1 NP.large hsec.2

end PallLean.Paper93.DeepMath.PathB.Layer9

#print axioms PallLean.Paper93.DeepMath.PathB.Layer9.razborov_rudich_barrier
#print axioms PallLean.Paper93.DeepMath.PathB.Layer9.no_natural_property_if_secure_prf
