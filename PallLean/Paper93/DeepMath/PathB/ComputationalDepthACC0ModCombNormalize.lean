import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModResidueSpeedup

/-!
# Normalizing the AC⁰-structure-over-`MOD`-bottom fragment

`and_of_mods` handled the binary `MOD ∧ MOD` case.  This file generalizes it to an **arbitrary** boolean
combination (`AND`/`OR`/`NOT`/`const`) over a fixed family of `MOD` gates — the full "AC⁰ structure over a `MOD`
bottom" syntactic fragment — and shows it normalizes to a `Depth2ModCircuit`, hence is residue-searchable in
`< 2^n` cells when `∏ q_i < 2^n`, **regardless of the gate supports**.

The mechanism: a combination `C` over `MOD`-leaves evaluates as `combEval gates C`, which **factors through the
`MOD`-gate outputs** — `combEval gates C x = combTop C (fun i => (gates i).eval x)` (by induction on `C`).  So the
whole circuit is the depth-2 circuit `⟨gates, combTop C⟩` (top `=` the boolean combination folded onto the leaf
values), and the residue speedup applies.

## What is proved (clean axioms, no `sorry`)

* `ModComb`, `combEval`, `combTop` — boolean combinations over `MOD`-gate leaves and their two evaluations.
* `combEval_eq_combTop` — **the factorization**: the combination value is a function of the `MOD`-gate outputs.
* `modComb_normalizes` — **`combEval gates C = (⟨gates, combTop C⟩ : Depth2ModCircuit).eval`** (the normal form).
* `modComb_searchable` — the combination's SAT is decided by a residue search over `< 2^n` cells when `∏ q_i < 2^n`.

## Honest scope

A genuine normalization of the full AC⁰-over-`MOD`-bottom fragment to the residue observer, with the residue gain
(any supports).  The `MOD`-bottom structure (the gate family `gates` and the combination `C`) is **given**; deriving
it from an *arbitrary* `ACC⁰` circuit is the full Yao–Beigel–Tarui normal form (still open).  Still the cell-count
model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModCombNormalize

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ModResidueSpeedup

variable {n k : ℕ}

/-- A boolean combination (`AND`/`OR`/`NOT`/`const`) over `k` `MOD`-gate leaves. -/
inductive ModComb (n k : ℕ) where
  | leaf : Fin k → ModComb n k
  | const : Bool → ModComb n k
  | cnot : ModComb n k → ModComb n k
  | cand : ModComb n k → ModComb n k → ModComb n k
  | cor : ModComb n k → ModComb n k → ModComb n k

/-- Evaluate a combination on an input, with leaves the `MOD`-gate outputs. -/
def combEval (gates : Fin k → ModGate n) : ModComb n k → (Fin n → Bool) → Bool
  | .leaf i, x => (gates i).eval x
  | .const b, _ => b
  | .cnot c, x => !(combEval gates c x)
  | .cand a b, x => combEval gates a x && combEval gates b x
  | .cor a b, x => combEval gates a x || combEval gates b x

/-- Evaluate a combination on a vector of leaf values (the "top" function). -/
def combTop : ModComb n k → (Fin k → Bool) → Bool
  | .leaf i, v => v i
  | .const b, _ => b
  | .cnot c, v => !(combTop c v)
  | .cand a b, v => combTop a v && combTop b v
  | .cor a b, v => combTop a v || combTop b v

/-- **The factorization (proved): the combination value is a function of the `MOD`-gate outputs.** -/
theorem combEval_eq_combTop (gates : Fin k → ModGate n) :
    ∀ (C : ModComb n k) (x : Fin n → Bool),
      combEval gates C x = combTop C (fun i => (gates i).eval x) := by
  intro C
  induction C with
  | leaf i => intro x; rfl
  | const b => intro x; rfl
  | cnot c ih => intro x; simp only [combEval, combTop, ih]
  | cand a b iha ihb => intro x; simp only [combEval, combTop, iha, ihb]
  | cor a b iha ihb => intro x; simp only [combEval, combTop, iha, ihb]

/-- **The normal form (proved): a `MOD`-combination is a `Depth2ModCircuit`** with top `=` the folded combination. -/
theorem modComb_normalizes (gates : Fin k → ModGate n) (C : ModComb n k) :
    combEval gates C = Depth2ModCircuit.eval ⟨gates, combTop C⟩ :=
  funext (fun x => combEval_eq_combTop gates C x)

/-- **The combination is residue-searchable below brute force (proved).**  An arbitrary boolean combination of a
`MOD`-gate family has its SAT decided by a residue search over `< 2^n` cells when `∏ q_i < 2^n` — independent of the
gate supports (the AC⁰ structure folds into the top). -/
theorem modComb_searchable (gates : Fin k → ModGate n) (hpos : ∀ i, 0 < (gates i).modulus)
    (C : ModComb n k) (hregime : (∏ i, (gates i).modulus) < 2 ^ n) :
    ∃ G : ((j : Fin k) → ZMod (gates j).modulus) → Bool,
      (Satisfiable (combEval gates C)
        ↔ ∃ v ∈ Finset.univ.image (modResVec ⟨gates, combTop C⟩), G v = true)
      ∧ (Finset.univ.image (modResVec ⟨gates, combTop C⟩)).card < 2 ^ n := by
  rw [modComb_normalizes gates C]
  exact mod_circuit_sat_speedup ⟨gates, combTop C⟩ hpos hregime

end PallLean.Paper93.DeepMath.PathB.ACC0ModCombNormalize

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModCombNormalize.combEval_eq_combTop
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModCombNormalize.modComb_normalizes
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModCombNormalize.modComb_searchable
