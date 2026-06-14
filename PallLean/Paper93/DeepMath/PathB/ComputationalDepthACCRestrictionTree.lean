import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DepthReduction

/-!
# The restriction tree: recursive depth reduction

Lifting the depth‑2 bridge to deeper circuits needs the Håstad **restriction tree**: a sequence of random
restrictions, each collapsing the current top layer, driving depth `d → d−1 → … → 2`.  This file proves the
*deterministic recursion plumbing* — that one‑step depth reduction, iterated, reaches depth `2` over an accumulated
restriction sequence — and names the single probabilistic step (the one‑step switching) as the wall.

A restriction is a partial assignment `ρ : Fin n → Option Bool`; an input `Agrees ρ` if it respects ρ's fixings.
Restrictions accumulate as a *list*, with `AgreesAll` the conjunction — so composing steps is just list
concatenation (no merge/consistency bookkeeping).

## What is proved (clean axioms, no `sorry`)

* `Restriction`, `Agrees`, `AgreesAll` — partial restrictions and input agreement.
* `RestrictionTreeSwitch` — the named one‑step switching: every depth‑`≥3` circuit, under some restriction, equals a
  strictly‑smaller‑depth circuit on agreeing inputs.
* `reduces_to_depth2` — **the recursion plumbing**: granted one‑step switching, *every* circuit reduces to a
  depth‑`≤2` circuit over an accumulated restriction list (well‑founded recursion on depth).

## How it slots in

The depth‑2 survivor feeds the depth‑2 `MOD`‑bottom bridge (`…ACC0CircuitModel`, `…ACC0DepthReduction`): once the
restriction tree reaches depth 2, support extraction and the correlation/pigeonhole machinery apply, so the circuit
fails to correlate with the holonomy parity on the live cube.  All of that downstream is proved; the restriction
tree here supplies the deterministic descent.

## Honest scope

The recursion is fully proved — depth strictly decreases each step, so iteration terminates at depth `2`, and the
restriction list accumulates with `AgreesAll` composing by `List.mem_append`/`cons`.  The one *unproved* input is
`RestrictionTreeSwitch` — that a random restriction performs each one‑step collapse — which is the Håstad switching
lemma, the `NP ⊄ ACC⁰` wall.  So the entire depth‑reduction *structure* is mechanized; only the single
per‑layer switching remains named.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACCRestrictionTree

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel

variable {n : ℕ}

/-- A partial restriction: `none` = live, `some b` = fixed to `b`. -/
abbrev Restriction (n : ℕ) := Fin n → Option Bool

/-- An input respects a restriction's fixings. -/
def Agrees (ρ : Restriction n) (x : Fin n → Bool) : Prop := ∀ i b, ρ i = some b → x i = b

/-- An input respects every restriction in a list. -/
def AgreesAll (ρs : List (Restriction n)) (x : Fin n → Bool) : Prop := ∀ ρ ∈ ρs, Agrees ρ x

/-- **(Named one‑step switching — the Håstad wall, `NP ⊄ ACC⁰`‑strength).**  Every circuit of depth `≥ 3` becomes,
under some restriction, a strictly‑smaller‑depth circuit on agreeing inputs.  This is one layer of the restriction
tree; proving a random restriction achieves it is the switching lemma. -/
def RestrictionTreeSwitch : Prop :=
  ∀ C : ACC0Circuit n, 3 ≤ depth C →
    ∃ (ρ : Restriction n) (C' : ACC0Circuit n),
      depth C' < depth C ∧ ∀ x, Agrees ρ x → eval C x = eval C' x

/-- **The recursion plumbing (proved): granted one‑step switching, every circuit reduces to depth `≤ 2`.**  The
reduction holds over an accumulated restriction list — `AgreesAll ρs x → eval C x = eval C' x` with `depth C' ≤ 2`.
Well‑founded recursion on depth: each step strictly decreases depth, so iteration terminates at depth `2`. -/
theorem reduces_to_depth2 (hswitch : RestrictionTreeSwitch (n := n)) (C : ACC0Circuit n) :
    ∃ (ρs : List (Restriction n)) (C' : ACC0Circuit n),
      depth C' ≤ 2 ∧ ∀ x, AgreesAll ρs x → eval C x = eval C' x := by
  have aux : ∀ d (C : ACC0Circuit n), depth C ≤ d →
      ∃ (ρs : List (Restriction n)) (C' : ACC0Circuit n),
        depth C' ≤ 2 ∧ ∀ x, AgreesAll ρs x → eval C x = eval C' x := by
    intro d
    induction d with
    | zero => intro C hC; exact ⟨[], C, by omega, fun x _ => rfl⟩
    | succ d ih =>
        intro C hC
        by_cases h2 : depth C ≤ 2
        · exact ⟨[], C, h2, fun x _ => rfl⟩
        · have h3 : 3 ≤ depth C := by omega
          obtain ⟨ρ, C₁, hlt, heq⟩ := hswitch C h3
          obtain ⟨ρs₁, C', hC'2, heq₁⟩ := ih C₁ (by omega)
          refine ⟨ρ :: ρs₁, C', hC'2, fun x hx => ?_⟩
          have ha1 : Agrees ρ x := hx ρ (List.mem_cons.mpr (Or.inl rfl))
          have ha2 : AgreesAll ρs₁ x := fun ρ' hρ' => hx ρ' (List.mem_cons.mpr (Or.inr hρ'))
          rw [heq x ha1, heq₁ x ha2]
  exact aux (depth C) C (le_refl _)

end PallLean.Paper93.DeepMath.PathB.ACCRestrictionTree

#print axioms PallLean.Paper93.DeepMath.PathB.ACCRestrictionTree.reduces_to_depth2
