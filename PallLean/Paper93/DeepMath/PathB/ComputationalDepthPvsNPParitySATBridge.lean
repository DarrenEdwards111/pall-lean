import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPCircuitComposition

/-!
# Parity–SAT bridge assembly — brick 3 of the cross-model bridge

Bricks 1 and 2 give, respectively, the correct reduction `MOD₂ ≤ SAT` and closure of `AC⁰[p]` under circuit
substitution.  This file assembles them against the prime capstone interface:

> If an `AC⁰[p]` circuit `Dec` decides the parity-CNF family through an `AC⁰`, depth-`≤ 1` encoding of the
> instances, then substituting the encoding into `Dec` yields an `AC⁰[p]` circuit computing `PARITY` — of
> depth `≤ Dec.depth + 1`.  Combined with any parity `AC⁰[p]` size lower bound (the capstone), this forces
> `Dec` to be large.

The point is **non-circularity**: the encoding `enc` is a *fixed*, input-local (`depth ≤ 1`) map — it does not
"decide" anything; all the deciding work is in `Dec`.  The composition `subst Dec enc` then computes `PARITY`
purely as a consequence of `Dec` deciding the family, so a small `AC⁰[p]` decider would give a small `AC⁰[p]`
parity circuit, which the Razborov–Smolensky capstone forbids.

## Honest scope

Brick 3: the reduction-transfer lemma, assembling bricks 1+2 with the `RealAC0pParitySizeLowerBoundAt`
capstone interface.  The hypotheses `enc`/`Dec`/`hDec_correct` are the honest antecedent "SAT restricted to
the parity-CNF family is decided by an `AC⁰[p]` circuit over an `AC⁰` encoding"; they are **not** sockets —
this is a genuine reduction lemma whose antecedent is exactly what "the family is in `AC⁰[p]`" means.  What is
**not** in this file: the concrete CNF bit-encoding realising `enc` (brick 4), and the fact that the capstone
supplies `RealAC0pParitySizeLowerBoundAt` in this exact interface form.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPParitySATBridge

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.PvsNPCircuitComposition
open BoolCircuitSyntax

/-- `AC⁰ ⊆ AC⁰[p]`: a Boolean-gate circuit is in particular an `AC⁰[p]` circuit. -/
theorem isAC0Syntax_imp_isAC0pSyntax {n : Nat} (p : Nat) (C : BoolCircuitSyntax n) :
    C.IsAC0Syntax → C.IsAC0pSyntax p := by
  induction C using rec_size with
  | const b => intro _; simp only [BoolCircuitSyntax.IsAC0pSyntax]
  | input i => intro _; simp only [BoolCircuitSyntax.IsAC0pSyntax]
  | not C ih =>
    intro hC
    simp only [BoolCircuitSyntax.IsAC0Syntax] at hC
    simp only [BoolCircuitSyntax.IsAC0pSyntax]
    exact ih hC
  | andGate Cs ih =>
    intro hC
    simp only [BoolCircuitSyntax.IsAC0Syntax] at hC
    simp only [BoolCircuitSyntax.IsAC0pSyntax]
    intro c hc
    exact ih c hc (hC c hc)
  | orGate Cs ih =>
    intro hC
    simp only [BoolCircuitSyntax.IsAC0Syntax] at hC
    simp only [BoolCircuitSyntax.IsAC0pSyntax]
    intro c hc
    exact ih c hc (hC c hc)
  | modGate q r Cs _ =>
    intro hC
    simp only [BoolCircuitSyntax.IsAC0Syntax] at hC

section Bridge

variable {n p N : Nat}
variable (enc : Fin N → BoolCircuitSyntax n)
variable (Dec : BoolCircuitSyntax N)

/-- The composite circuit: substitute the encoding into the decider. -/
def composedParityCircuit : BoolCircuitSyntax n := subst Dec enc

/-- **The composite computes `PARITY`** whenever the decider computes it through the encoding. -/
theorem composedParityCircuit_computes
    (hDec_correct : ∀ x : Fin n → Bool,
      Dec.eval (fun j => (enc j).eval x) = parityFunction n x) :
    (composedParityCircuit enc Dec).Computes (parityFunction n) := by
  intro x
  unfold composedParityCircuit
  rw [eval_subst]
  exact hDec_correct x

/-- **The composite is `AC⁰[p]`** whenever the decider is `AC⁰[p]` and the encoding is `AC⁰`. -/
theorem composedParityCircuit_isAC0p
    (hDec_ac0p : Dec.IsAC0pSyntax p)
    (henc_ac0 : ∀ j, (enc j).IsAC0Syntax) :
    (composedParityCircuit enc Dec).IsAC0pSyntax p := by
  unfold composedParityCircuit
  exact isAC0pSyntax_subst p Dec enc
    (fun j => isAC0Syntax_imp_isAC0pSyntax p (enc j) (henc_ac0 j)) hDec_ac0p

/-- **The composite has depth `≤ Dec.depth + 1`** when the encoding is depth `≤ 1` (input-local). -/
theorem composedParityCircuit_depth_le
    (henc_depth : ∀ j, (enc j).depth ≤ 1) :
    (composedParityCircuit enc Dec).depth ≤ Dec.depth + 1 := by
  unfold composedParityCircuit
  exact depth_subst_le 1 Dec enc henc_depth

/-- **Brick 3 — the transfer lemma.**  Any parity `AC⁰[p]` size lower bound at depth `Dec.depth + 1`
forces the encoded parity-CNF decider `Dec` to satisfy `lower ≤ (subst Dec enc).size`.

Read contrapositively: a *small* `AC⁰[p]` decider for the parity-CNF family (through an `AC⁰`, depth-`≤ 1`
encoding) cannot exist once `lower` is super-polynomial — which is exactly the Razborov–Smolensky capstone. -/
theorem decider_size_ge_of_parity_LB
    (lower : Nat)
    (henc_ac0 : ∀ j, (enc j).IsAC0Syntax)
    (henc_depth : ∀ j, (enc j).depth ≤ 1)
    (hDec_ac0p : Dec.IsAC0pSyntax p)
    (hDec_correct : ∀ x : Fin n → Bool,
      Dec.eval (fun j => (enc j).eval x) = parityFunction n x)
    (H : RealAC0pParitySizeLowerBoundAt p n (Dec.depth + 1) lower) :
    lower ≤ (composedParityCircuit enc Dec).size := by
  refine H (composedParityCircuit enc Dec) ?_ ?_ ?_
  · exact composedParityCircuit_isAC0p enc Dec hDec_ac0p henc_ac0
  · exact composedParityCircuit_computes enc Dec hDec_correct
  · exact composedParityCircuit_depth_le enc Dec henc_depth

/-- **Contrapositive cash-out.**  Under a parity `AC⁰[p]` size lower bound, no `AC⁰[p]` circuit smaller than
`lower` can decide the parity-CNF family through an `AC⁰`, depth-`≤ 1` encoding. -/
theorem no_small_encoded_parityCNF_decider
    (lower : Nat)
    (henc_ac0 : ∀ j, (enc j).IsAC0Syntax)
    (henc_depth : ∀ j, (enc j).depth ≤ 1)
    (hDec_ac0p : Dec.IsAC0pSyntax p)
    (hDec_correct : ∀ x : Fin n → Bool,
      Dec.eval (fun j => (enc j).eval x) = parityFunction n x)
    (H : RealAC0pParitySizeLowerBoundAt p n (Dec.depth + 1) lower) :
    lower ≤ (composedParityCircuit enc Dec).size :=
  decider_size_ge_of_parity_LB enc Dec lower henc_ac0 henc_depth hDec_ac0p hDec_correct H

end Bridge

end PallLean.Paper93.DeepMath.PathB.PvsNPParitySATBridge

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPParitySATBridge.isAC0Syntax_imp_isAC0pSyntax
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPParitySATBridge.composedParityCircuit_computes
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPParitySATBridge.composedParityCircuit_isAC0p
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPParitySATBridge.composedParityCircuit_depth_le
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPParitySATBridge.decider_size_ge_of_parity_LB
