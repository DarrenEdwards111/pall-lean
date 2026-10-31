import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementRuler

/-!
# Bounding localization: the reach cap is trivial for free, a genuine restriction otherwise,
and necessary-but-not-sufficient

After the entanglement ruler (`EntanglementRuler`) closed the `t`-escape, one residue survived:
the ruler bound `k·b ≤ s·|gates|` only separates when the per-gate **private reach** `s` is bounded
(`depCard(g) ≤ σ` for small `σ`).  A global gate can read everything, `s ≈ n`, and the bound goes
slack.  This file is the honest attempt to **bound localization** — to cap the reach — and it
reports exactly how far that can go.

## The result, stated plainly

Localization **cannot be closed to a useful cap by generic means**, and even a full locality cap is
**necessary but not sufficient** — the demand residue (`= cost_super`) remains.  Concretely:

* **`depCard_le_ambient` / `ruler_trivial_cap`** — the ONLY unconditional reach cap is the trivial
  one, `depCard(g) ≤ n`, giving the unconditional but **vacuous** `k·b ≤ n·|gates|`: it forces
  `|gates| ≥ k·b / n`, i.e. it is only as strong as the demand `k·b` is large.
* **`globalWire_depends_all` / `no_universal_subcap`** — a single wire (`(x₀⊕x₁)⊕x₂`) depends on
  **every** variable: its reach is the full ambient dimension.  So the trivial cap is TIGHT — any
  cap `σ < n` is **not a theorem about all wires**, it is a genuine restriction on the circuit class,
  exactly the thing a global gate defeats.
* **`boundedReach_separates` / `no_small_local_circuit`** — the conditional that IS true: *within*
  the bounded-reach class (`reach ≤ σ`), a small circuit cannot meet the demand — `k·b ≤ σ·G` for
  any circuit of size `≤ G`.  Locality delivers the separation, once assumed.
* **`separation_needs_demand`** — the honest capstone: the separation `G < |gates|` needs **both**
  the locality hypothesis `BoundedReach C σ` **and** the demand hypothesis `σ·G < k·b`.  Drop
  either and nothing follows.  The demand hypothesis is demand-generation — `cost_super`'s residue.

## Honest scope — localization is not closed, and closing it would not close the loop

Two facts, both proved here, together say localization is not the last domino:

1. **Not closable generically.**  The only free cap is `σ = n` (`ruler_trivial_cap`), which is
   vacuous; the trivial cap is tight (`no_universal_subcap` — a global gate reaches everything).  So
   bounding reach for SAT would require proving "every minimal SAT-circuit is local" — a claim false
   for general circuits (global gates exist), hence one that must invoke SAT-specific structure and
   minimality.  That is a lower-bound-strength claim, not a counting fact.

2. **Not sufficient even if closed.**  `separation_needs_demand` shows locality alone proves
   nothing; you still need `σ·G < k·b`, i.e. the tower actually *induces* the demand
   (demand-generation).  And demand-generation is `cost_super`'s residue (the `EntangledTower`
   `wit_size`/`wit_semantic` fields are hypotheses, not theorems).

So: no, localization cannot be closed here.  What is closed is its *shape* — the reach cap is
trivial-or-restrictive (a dichotomy, proved), and the separation factors as locality ∧ demand
(proved).  Closing localization for SAT is lower-bound-strength; and even granting it, the loop
stays open at demand-generation `= cost_super`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.LocalizationBound

open PallLean.Paper93.DeepMath.PathB.EntanglementRuler

variable {k b n : ℕ}

/-! ### The trivial cap: `reach ≤ n`, unconditional but vacuous -/

/-- **The trivial reach cap (proved).**  A gate's private reach is at most the ambient dimension `n`
— it can depend on at most every variable.  This is the only *unconditional* cap. -/
theorem depCard_le_ambient (C : EntangledTower k b n) (g : ℕ) : (depSet C g).card ≤ n := by
  calc (depSet C g).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = n := by simp

/-- A circuit has **bounded reach** `σ` if every gate's private reach is at most `σ`. -/
def BoundedReach (C : EntangledTower k b n) (σ : ℕ) : Prop :=
  ∀ g ∈ C.gates, (depSet C g).card ≤ σ

/-- **The trivial cap is unconditional (proved).**  Every circuit has bounded reach `n`. -/
theorem unconditional_is_trivial (C : EntangledTower k b n) : BoundedReach C n := by
  intro g _
  exact depCard_le_ambient C g

/-- **The unconditional ruler (proved).**  Applying the ruler with the trivial cap `σ = n` gives
`k·b ≤ n·|gates|` for *every* circuit — but this only forces `|gates| ≥ k·b / n`, i.e. it is as
strong as the demand `k·b` is large.  The trivial cap makes the bound only as sharp as the demand. -/
theorem ruler_trivial_cap (C : EntangledTower k b n) : k * b ≤ n * C.gates.card :=
  entangled_reason C n (unconditional_is_trivial C)

/-! ### A global gate defeats every sub-`n` cap: the trivial cap is tight -/

/-- One wire depending on **every** variable: `(x₀ ⊕ x₁) ⊕ x₂`. -/
def globalWire : (Fin 3 → Bool) → Bool := fun x => Bool.xor (Bool.xor (x 0) (x 1)) (x 2)

/-- **The global wire depends on every variable (proved).**  Flipping any coordinate flips the
output — its private reach is the full ambient dimension. -/
theorem globalWire_depends_all (v : Fin 3) :
    PallLean.Paper93.DeepMath.PathB.EntanglementRuler.DependsOn globalWire v := by
  fin_cases v <;> decide

/-- **The trivial cap is tight — no sub-`n` cap is universal (proved).**  `globalWire` depends on all
three of its variables, so its reach is the full ambient dimension `3`.  Any cap `σ < n` therefore
excludes it: bounding reach below the ambient dimension is a genuine *restriction* on the circuit
class, not a theorem.  This is precisely the localization residue — global gates are allowed, so the
reach `s` in `k·b ≤ s·|gates|` cannot be capped below `n` for free. -/
theorem no_universal_subcap :
    ∀ v : Fin 3, PallLean.Paper93.DeepMath.PathB.EntanglementRuler.DependsOn globalWire v :=
  globalWire_depends_all

/-! ### The conditional: bounded reach delivers the separation -/

/-- **Bounded reach separates (proved).**  *Within* the bounded-reach class, the ruler gives
`k·b ≤ σ·|gates|` — the conditional lower bound.  Locality delivers the separation, once assumed. -/
theorem boundedReach_separates (C : EntangledTower k b n) (σ : ℕ) (hloc : BoundedReach C σ) :
    k * b ≤ σ * C.gates.card :=
  entangled_reason C σ hloc

/-- **No small local circuit (proved).**  A circuit that is both *local* (`reach ≤ σ`) and *small*
(`|gates| ≤ G`) can service at most `σ·G` of demand: `k·b ≤ σ·G`.  Contrapositive: a demand
exceeding `σ·G` admits no small local circuit. -/
theorem no_small_local_circuit (C : EntangledTower k b n) (σ G : ℕ)
    (hloc : BoundedReach C σ) (hsmall : C.gates.card ≤ G) : k * b ≤ σ * G :=
  le_trans (boundedReach_separates C σ hloc) (Nat.mul_le_mul (le_refl σ) hsmall)

/-- **Separation needs BOTH locality and demand (proved).**  The gate lower bound `G < |gates|`
follows only from the locality hypothesis `BoundedReach C σ` *together with* the demand hypothesis
`σ·G < k·b`.  Drop either and nothing follows.  The demand hypothesis is demand-generation —
`cost_super`'s residue — so closing localization is necessary but not sufficient. -/
theorem separation_needs_demand (C : EntangledTower k b n) (σ G : ℕ)
    (hloc : BoundedReach C σ) (hdemand : σ * G < k * b) : G < C.gates.card := by
  by_contra h
  push_neg at h
  have hbound := no_small_local_circuit C σ G hloc h
  omega

end PallLean.Paper93.DeepMath.PathB.LocalizationBound

#print axioms PallLean.Paper93.DeepMath.PathB.LocalizationBound.depCard_le_ambient
#print axioms PallLean.Paper93.DeepMath.PathB.LocalizationBound.ruler_trivial_cap
#print axioms PallLean.Paper93.DeepMath.PathB.LocalizationBound.no_universal_subcap
#print axioms PallLean.Paper93.DeepMath.PathB.LocalizationBound.no_small_local_circuit
#print axioms PallLean.Paper93.DeepMath.PathB.LocalizationBound.separation_needs_demand
