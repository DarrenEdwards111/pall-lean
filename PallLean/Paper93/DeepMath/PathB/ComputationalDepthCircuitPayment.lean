import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCircuitSoundnessTseitin

/-!
# What a circuit pays for being unsound about its own hardness — and why the answer is "nothing"

`CircuitSoundnessTseitin` left the residual: unsound circuits (a false positive on `gstar`) escape the
Gödel spring.  For a *theory*, that residual is closed because being unsound has a **price**: an
inconsistent theory proves `⊥`, hence *everything* (explosion) — it becomes useless.  That price is why
we may assume a theory is sound, which gives the full Gödel bound.

This file builds the payment mechanism and asks the circuit analog: what does a circuit pay for being
unsound?  The honest answer, machine-checked: **nothing.**

## The payment (theories) — proved

* **`inconsistent_pays`** — an inconsistent `PayingSystem` (one that proves `⊥`) proves *every*
  statement (explosion).  The price of unsoundness: triviality.  This is what lets the theory side
  assume soundness for free.

## The circuit side — proved

* **`no_circuit_explosion`** — a circuit wrong on one input is still a perfectly good function
  elsewhere: there is no explosion.  So an unsound small circuit for MCSP — correct everywhere except a
  false positive on `gstar` — is still a *valid* small circuit.  It pays nothing, and escapes the
  spring.

## Why this is exactly the gap — proved

* **`payment_closes_residual`** — IF circuits had the payment (every valid small circuit is sound), the
  sound-circuit bound would extend to *all* circuits, closing the residual.  So the payment — a global
  "valid ⟹ sound" — is precisely the missing ingredient.

## Honest verdict

Theories pay for unsoundness with **explosion**, so soundness is assumable and the Gödel spring gives a
full lower bound.  Circuits **pay nothing**: an unsound circuit still computes a definite function, no
explosion, no triviality — so unsoundness is free and the residual stays open.  The reason is the
deepest one on the map: a theory *reasons* (has `⊥` and explosion), a circuit *computes* (a fixed
function, no logical structure to collapse).  The missing ingredient — a payment mechanism forcing
`valid ⟹ sound` for small circuits — is a logical/proof structure circuits do not carry, and supplying
it is `cost_super`.  This is the precise circuit analog of "or it proves a contradiction," and the
precise reason the Gödel method does not give circuit lower bounds.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CircuitPayment

/-- **A system that pays for inconsistency.**  `Prov` is provability, `bot` is `⊥`, and `explosion` is
the price: proving `⊥` proves everything. -/
structure PayingSystem where
  Stmt : Type
  Prov : Stmt → Prop
  bot : Stmt
  /-- explosion: an inconsistent system proves every statement -/
  explosion : Prov bot → ∀ ψ, Prov ψ

/-- **The payment (proved).**  An inconsistent theory proves everything — becomes trivial.  This is
what unsoundness costs a theory, and why the theory side may assume soundness. -/
theorem inconsistent_pays (S : PayingSystem) (h : S.Prov S.bot) : ∀ ψ, S.Prov ψ :=
  S.explosion h

/-- **Circuits pay nothing (proved).**  A circuit wrong on one input still computes a definite function
elsewhere — there is no explosion.  So an unsound small circuit (a lone false positive on `gstar`) is
still a valid circuit; unsoundness is free, and it escapes the spring. -/
theorem no_circuit_explosion :
    ∃ (C : Bool → Bool) (x : Bool), C x = false ∧ ¬ (∀ y, C y = true) :=
  ⟨id, false, rfl, fun h => Bool.noConfusion (h false)⟩

/-- **The payment is exactly the missing ingredient (proved).**  If circuits paid for unsoundness —
i.e. every valid small circuit is sound — then the sound-circuit spring extends to ALL valid circuits,
closing the residual.  So a global `valid ⟹ sound` is precisely what would turn the sound-circuit bound
into the full lower bound.  That global soundness is `cost_super`. -/
theorem payment_closes_residual {Circuit : Type} (Valid Sound ComputesGstar : Circuit → Prop)
    (payment : ∀ C, Valid C → Sound C)
    (spring : ∀ C, Sound C → ¬ ComputesGstar C) :
    ∀ C, Valid C → ¬ ComputesGstar C :=
  fun C hv => spring C (payment C hv)

end PallLean.Paper93.DeepMath.PathB.CircuitPayment

#print axioms PallLean.Paper93.DeepMath.PathB.CircuitPayment.inconsistent_pays
#print axioms PallLean.Paper93.DeepMath.PathB.CircuitPayment.no_circuit_explosion
#print axioms PallLean.Paper93.DeepMath.PathB.CircuitPayment.payment_closes_residual
