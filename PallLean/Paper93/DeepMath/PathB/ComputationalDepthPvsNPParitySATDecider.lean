import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPParityToSATReduction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPParitySATBridge

/-!
# Concrete parity-CNF SAT-decider lower bound — brick 4 of the cross-model bridge

Bricks 1–3 gave: the reduction `MOD₂ ≤ SAT`, `AC⁰[p]` closure under substitution, and the transfer lemma
against an abstract `hDec_correct` hypothesis.  This file makes the transfer **concrete and about SAT** by
instantiating the encoding with the identity family (the parity-CNF instance `parityCNF (ofFn x)` is fully
determined by `x`) and connecting the SAT semantics through brick 1:

> Any `AC⁰[p]` circuit `Dec` whose output on `x` **decides satisfiability of `parityCNF (ofFn x)`** yields,
> after one `NOT` gate, an `AC⁰[p]` circuit computing `PARITY` — so a parity `AC⁰[p]` size lower bound forces
> `Dec` to be large.

The bridge to satisfiability is exactly brick 1: `Satisfiable (parityCNF (ofFn x)) ↔ ⊕ (ofFn x) = 0`, and the
new lemma `bxor_ofFn` identifies `⊕ (ofFn x)` with `parityFunction n x`.  So the decider's Boolean output is
`¬PARITY`, and `not Dec` computes `PARITY`.

## Honest scope

Brick 4: the concrete SAT-decider instantiation using the identity encoding (so the transfer statement is
literally about `Satisfiable (parityCNF …)`, via brick 1).  The `hDec_sat` hypothesis is the honest
antecedent "there is an `AC⁰[p]` circuit deciding satisfiability of the parity-CNF family"; it is satisfiable
(such circuits exist), so the lower bound is non-vacuous.  What remains outside this file: a *generic* CNF
bit-encoding (so the decider need not be specialised to the family), discharging
`RealAC0pParitySizeLowerBoundAt` from the subcircuit-form capstone, and the uniform↔non-uniform identification
with an abstract `MachineModel` decider.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPParitySATDecider

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.PvsNPParityToSAT
open SATDepthMachine
open BoolCircuitSyntax

/-- The list-parity of `ofFn x` is the `parityFunction`. -/
theorem bxor_ofFn : ∀ (n : Nat) (x : Fin n → Bool), bxor (List.ofFn x) = parityFunction n x
  | 0, x => by simp [parityFunction, boolParity]
  | n + 1, x => by
    rw [List.ofFn_succ, bxor_cons, bxor_ofFn n (fun i => x i.succ)]
    simp only [parityFunction, boolParity]

/-- **Brick 4 — concrete parity-CNF SAT-decider lower bound.**

If `Dec` is an `AC⁰[p]` circuit whose output on input `x` is `true` exactly when `parityCNF (ofFn x)` is
satisfiable, then under any parity `AC⁰[p]` size lower bound at depth `Dec.depth + 1`, `Dec` has size
`≥ lower - 1`.  (The `+1`/`-1` is the single `NOT` gate turning the `¬PARITY` decider into a `PARITY`
circuit.) -/
theorem no_small_ac0p_parityCNF_decider
    (n p lower : Nat) (Dec : BoolCircuitSyntax n)
    (hDec_ac0p : Dec.IsAC0pSyntax p)
    (hDec_sat : ∀ x : Fin n → Bool,
      Dec.eval x = true ↔ Satisfiable (parityCNF (List.ofFn x)))
    (H : RealAC0pParitySizeLowerBoundAt p n (Dec.depth + 1) lower) :
    lower ≤ Dec.size + 1 := by
  -- `not Dec` computes parity, is AC⁰[p], has depth `Dec.depth + 1`.
  have hnot_ac0p : (BoolCircuitSyntax.not Dec).IsAC0pSyntax p := by
    simp only [BoolCircuitSyntax.IsAC0pSyntax]; exact hDec_ac0p
  have hnot_computes : (BoolCircuitSyntax.not Dec).Computes (parityFunction n) := by
    intro x
    simp only [BoolCircuitSyntax.eval]
    have h1 : Dec.eval x = true ↔ parityFunction n x = false := by
      rw [hDec_sat x, parityCNF_sat_iff_even, bxor_ofFn]
    cases hd : Dec.eval x <;> cases hpp : parityFunction n x <;> simp_all
  have hnot_depth : (BoolCircuitSyntax.not Dec).depth ≤ Dec.depth + 1 := by
    simp [BoolCircuitSyntax.depth]
  have hle := H (BoolCircuitSyntax.not Dec) hnot_ac0p hnot_computes hnot_depth
  simpa [BoolCircuitSyntax.size] using hle

end PallLean.Paper93.DeepMath.PathB.PvsNPParitySATDecider

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPParitySATDecider.bxor_ofFn
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPParitySATDecider.no_small_ac0p_parityCNF_decider
