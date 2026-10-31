import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer9NaturalProofs
import Mathlib.Data.Fintype.BigOperators

/-!
# Layer 10A — the barrier landscape: concrete constructivity for the natural-proofs barrier

Strengthens Layer 9's natural-proofs barrier (`SCOPE_LAYER10A_BARRIER_LANDSCAPE.md`).  Layer 9 *fenced* the
constructivity (efficiency) condition; here it is made **concrete**: a property is "constructive" when a
size-`≤ s` circuit over the `2ⁿ`-bit **truth table** decides it.  With this, the step "a natural property
is a legal efficient test, so PRF security applies to it" becomes a **theorem** (the property's own circuit
is the distinguisher), not a hypothesis.

* `truthTable` — an `n`-bit function as a `2ⁿ`-bit string (via `ttEquiv : (Fin n → Bool) ≃ Fin (2ⁿ)`).
* `Constructive` — `P` is decided by a size-`≤ s` truth-table circuit (the Razborov–Rudich condition).
* `FullyNaturalProperty` — constructive **+** large **+** useful (Layer 9's `Useful`).
* `SecureTT` — a PRF secure against size-`≤ s` truth-table circuits.
* `fullyNatural_breaks_secureTT` — a fully natural property + a secure PRF ⇒ `False`.  The property's
  circuit rejects all of `G` (usefulness) but accepts `> negl` (largeness); being a size-`≤ s` test, it is
  exactly what security forbids.

**Honest status.**  Still a theorem *about the barrier*, not a lower bound.  The PRF (`SecureTT`) is the
cryptographic assumption, fenced.  The improvement over Layer 9 is that constructivity — the part Layer 9
left abstract — is now a concrete circuit witness, so the barrier is sharper and self-contained.  See the
scope doc for relativization/algebrization, which need oracle-separation machinery beyond this file.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer10

open PallLean.Paper93.DeepMath.PathB Finset

/-- Index the `2ⁿ` inputs of an `n`-bit function by `Fin (2ⁿ)`. -/
noncomputable def ttEquiv (n : ℕ) : (Fin n → Bool) ≃ Fin (2 ^ n) :=
  Fintype.equivFinOfCardEq (by simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin])

/-- The **truth table** of `f` as a `2ⁿ`-bit string. -/
noncomputable def truthTable {n : ℕ} (f : Layer9.BoolFn n) : Fin (2 ^ n) → Bool :=
  fun i => f ((ttEquiv n).symm i)

/-- `P` is **constructive at size `s`** (the Razborov–Rudich condition): a circuit on the `2ⁿ` truth-table
bits, of size `≤ s`, decides `P`. -/
def Constructive {n : ℕ} (P : Layer9.BoolFn n → Bool) (s : ℕ) : Prop :=
  ∃ D : Layer8.Circuit (2 ^ n), D.size ≤ s ∧ ∀ f, P f = D.eval (truthTable f)

/-- A **fully natural property** (Razborov–Rudich, complete): constructive (a size-`≤ s` truth-table
circuit) **+** large **+** useful against `C`. -/
structure FullyNaturalProperty (n : ℕ) (C : Set (Layer9.BoolFn n)) (negl s : ℕ) where
  /-- the truth-table predicate -/
  pred : Layer9.BoolFn n → Bool
  /-- constructivity witness: a size-`≤ s` circuit over the truth table -/
  circuit : Layer8.Circuit (2 ^ n)
  circuit_size : circuit.size ≤ s
  computes : ∀ f, pred f = circuit.eval (truthTable f)
  /-- largeness -/
  large : negl < (Finset.univ.filter (fun f => pred f = true)).card
  /-- usefulness -/
  useful : Layer9.Useful pred C

/-- A PRF **secure against size-`≤ s` truth-table circuits**: `G ⊆ C`, and no size-`≤ s` circuit that
rejects all of `G` accepts more than `negl` truth tables. -/
def SecureTT {n : ℕ} (C : Set (Layer9.BoolFn n)) (negl s : ℕ) (G : Finset (Layer9.BoolFn n)) : Prop :=
  (∀ g ∈ G, g ∈ C) ∧
  ∀ D : Layer8.Circuit (2 ^ n), D.size ≤ s →
    (∀ g ∈ G, D.eval (truthTable g) = false) →
    (Finset.univ.filter (fun f => D.eval (truthTable f) = true)).card ≤ negl

open Classical in
/-- **Razborov–Rudich barrier, with concrete constructivity.**  A fully natural property cannot coexist
with a PRF secure against size-`≤ s` truth-table circuits: the property's own circuit rejects all of `G`
(usefulness) yet accepts `> negl` truth tables (largeness) — and it *is* a legal size-`≤ s` test, so
security caps it at `negl`.  Unlike Layer 9, the "efficient test" is the property's concrete circuit, not a
hypothesis. -/
theorem fullyNatural_breaks_secureTT {n : ℕ} {C : Set (Layer9.BoolFn n)} {negl s : ℕ}
    {G : Finset (Layer9.BoolFn n)} (NP : FullyNaturalProperty n C negl s) (hsec : SecureTT C negl s G) :
    False := by
  have hrej : ∀ g ∈ G, NP.circuit.eval (truthTable g) = false := by
    intro g hg
    rw [← NP.computes g]
    exact Layer9.useful_rejects_class NP.useful (hsec.1 g hg)
  have hcap := hsec.2 NP.circuit NP.circuit_size hrej
  have hset : (Finset.univ.filter (fun f => NP.circuit.eval (truthTable f) = true))
            = (Finset.univ.filter (fun f => NP.pred f = true)) := by
    apply Finset.filter_congr
    intro f _; rw [NP.computes f]
  rw [hset] at hcap
  exact absurd hcap (not_le.mpr NP.large)

end PallLean.Paper93.DeepMath.PathB.Layer10

#print axioms PallLean.Paper93.DeepMath.PathB.Layer10.fullyNatural_breaks_secureTT
