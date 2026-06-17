import Mathlib

/-!
# Pointwise RS composition — single-gate per-point guarantee ⇒ whole-circuit per-input `3/4` supply (proved)

Entry 214 encoded the single-`OR`-gate Fermat-indicator approximant and proved its per-point detection (`≥3/4` per
gate, over the random seed).  This file proves the **RS composition tracked pointwise**: composing the per-gate
approximants across a constant-depth `ACC⁰[p]` circuit, with the errors **union-bounded over the gates** at each fixed
input, yields a per-input `≥3/4` correct approximant for the *whole circuit* — exactly the `Uniform34` supply (entry
212), the last BT-side structural bridge.

The argument.  Over the seed space `Seed` (the random choices), at a fixed input `x`: the circuit-approximant is wrong
only if *some* gate-approximant is wrong (the composition: all gates right ⇒ circuit right).  So the circuit-wrong seeds
inject into the union of the gate-wrong seed-sets; by the union bound their count is `≤ ∑_g #{gate g wrong} ≤ G·M` (each
of `G` gates wrong on `≤ M` seeds).  With `4·G·M ≤ |Seed|` (each gate using enough independent trials so its per-point
error is `≤ 1/(4G)`), the circuit is correct on `≥ 3/4` of the seeds at every input.

## What is proved (clean axioms, no `sorry`)

* **`Composes`** — the composition socket: if every gate-approximant is correct (at `x` under `σ`), the
  circuit-approximant is correct — equivalently, circuit-wrong ⇒ some gate wrong.
* **`circuit_perpoint_3_4`** — the pointwise composition (PROVED): given `Composes`, a per-gate per-point bound
  (`∀ g x, #{σ | gate g wrong} ≤ M`), and `4·(G·M) ≤ |Seed|`, the whole circuit is correct on `≥ 3/4` of seeds at every
  input: `3·|Seed| ≤ 4·#{σ | circuit correct at x}` — the per-input `3/4` supply.

## Honest scope

This proves the **pointwise RS composition** — the union bound over gates that lifts the single-gate per-point `≥3/4`
guarantee (entry 214) to a whole-circuit per-input `≥3/4` supply — completely, in pure `Finset`/`Fintype` counting (the
union bound `Finset.card_biUnion_le` and the gate-count sum), no measure theory.  This is the structural bridge to the
`Uniform34` per-input supply (entry 212): the seed space with the circuit-correct predicate *is* a per-input `≥3/4`
supply.  What remains a named socket is **`Composes`**: that an `ACC⁰[p]` circuit's gate-wise approximant is correct
whenever all its gate-approximants are (the substitution/correctness of replacing each gate by its `F_p`-polynomial
approximant) — the structural circuit-semantics step (cf. the entry-195 reconstruction correctness).  This proves the
composition's counting heart, not the gate-substitution semantics.  (Also: `Uniform34` of entry 212 used *exact* `3w`;
this gives the genuine `≥3/4`, the honest RS output.)  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RSPointwiseComposition

open Finset
open scoped Classical

variable {I Seed γ : Type*} [Fintype Seed] [Fintype γ]

/-- **The composition socket.**  If every gate-approximant is correct at input `x` under seed `σ`, the
circuit-approximant is correct — equivalently, `circuitWrong x σ → ∃ g, gateWrong g x σ` (circuit wrong ⇒ some gate
wrong).  This is the structural correctness of the gate-wise approximation (replacing each gate by its `F_p`-polynomial
approximant); stated, not proved. -/
def Composes (gateWrong : γ → I → Seed → Prop) (circuitWrong : I → Seed → Prop) : Prop :=
  ∀ x σ, circuitWrong x σ → ∃ g, gateWrong g x σ

/-- **Pointwise RS composition (PROVED).**  Given the composition (`Composes`), a per-gate per-point error bound
(`∀ g x, #{σ | gate g wrong at x} ≤ M`), and `4·(G·M) ≤ |Seed|` (where `G = #gates`; each gate's per-point error
`≤ 1/(4G)`), the whole circuit is correct on `≥ 3/4` of the seeds at *every* input `x`:
`3·|Seed| ≤ 4·#{σ | ¬ circuitWrong x σ}`.  Proof: the circuit-wrong seeds inject into `⋃_g {gate g wrong}`
(`Composes`), so their count is `≤ ∑_g #{gate g wrong} ≤ G·M` (union bound + the gate-count sum); then
`#{correct} = |Seed| − #{wrong} ≥ |Seed| − G·M ≥ (3/4)|Seed|` (`omega` with `4·G·M ≤ |Seed|`). -/
theorem circuit_perpoint_3_4 (gateWrong : γ → I → Seed → Prop) (circuitWrong : I → Seed → Prop)
    (M : ℕ) (hcomp : Composes gateWrong circuitWrong)
    (hgate : ∀ g x, (Finset.univ.filter (fun σ => gateWrong g x σ)).card ≤ M)
    (hbound : 4 * (Fintype.card γ * M) ≤ Fintype.card Seed) (x : I) :
    3 * Fintype.card Seed ≤ 4 * (Finset.univ.filter (fun σ => ¬ circuitWrong x σ)).card := by
  have hwrong : (Finset.univ.filter (fun σ => circuitWrong x σ)).card ≤ Fintype.card γ * M := by
    calc (Finset.univ.filter (fun σ => circuitWrong x σ)).card
        ≤ (Finset.univ.biUnion (fun g => Finset.univ.filter (fun σ => gateWrong g x σ))).card := by
          refine Finset.card_le_card ?_
          intro σ hσ
          rw [Finset.mem_filter] at hσ
          obtain ⟨g, hg⟩ := hcomp x σ hσ.2
          exact Finset.mem_biUnion.mpr
            ⟨g, Finset.mem_univ g, Finset.mem_filter.mpr ⟨Finset.mem_univ σ, hg⟩⟩
      _ ≤ ∑ g : γ, (Finset.univ.filter (fun σ => gateWrong g x σ)).card := Finset.card_biUnion_le
      _ ≤ ∑ _g : γ, M := Finset.sum_le_sum (fun g _ => hgate g x)
      _ = Fintype.card γ * M := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hpart : (Finset.univ.filter (fun σ => ¬ circuitWrong x σ)).card
      + (Finset.univ.filter (fun σ => circuitWrong x σ)).card = Fintype.card Seed := by
    rw [add_comm]
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Seed))
      (p := fun σ => circuitWrong x σ)
    rw [Finset.card_univ] at h; exact h
  omega

end PallLean.Paper93.DeepMath.PathB.ACC0RSPointwiseComposition

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RSPointwiseComposition.circuit_perpoint_3_4
