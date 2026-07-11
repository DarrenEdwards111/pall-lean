import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameACCBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMODRankRecurrence
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameFpDegree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameFpANDOR
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameFpAmplify
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCompositeMODWall

/-!
# The N-Frame → ACC⁰ degree dynamic-SPDP ladder

This file wires the whole ACC⁰ polynomial-method arc into a single map.  Each **rung** re-exposes a headline
theorem from the arc, anchored (`:=`) to the real proof, so the entire structure is visible and machine-checked
in one place.  The arc pins down *exactly* how far the degree dynamic-SPDP reaches (`AC⁰[p]`, a single prime) and
*exactly* where it walls (composite / mixed `MOD`).

## The ladder

```text
 R0  cash-out            ACC_upper + hard_lower ⟹ f ∉ ACC⁰                    (mechanical)   [ACCBridge]
 R1  gate composition    additive gate recurrences ⟹ measure ≤ gateCount      (AC⁰ side)     [ACCBridge]
 ─── the wrong measure ─────────────────────────────────────────────────────────────────────
 R2a ℚ-rank: cheap gate  a single MOD_m gate has commMatrix rank ≤ m                          [MODRank]
 R2b ℚ-rank: blows up    MOD_2 over sub-circuits (= IP) has rank 2^n; no bounded recurrence   [MODRank]
      ⇒ ℚ-communication-rank is REJECTED as the ACC dynamic-SPDP (fails already at AC⁰[2]).
 ─── pivot to F_p-degree ───────────────────────────────────────────────────────────────────
 R3  MOD_p               MOD_p has an exact F_p polynomial of degree ≤ p-1     (Fermat)       [FpDegree]
 R4a OR gate             OR of degree-d children ⟹ degree (p-1)·d, correct off the form's zero [FpANDOR]
 R4b AND gate            dual: degree (p-1)·d                                                  [FpANDOR]
 R5a amplify (count)     ∃ W: error set ≤ 2^k/p^t                              (RS averaging)  [FpAmplify]
 R5b amplify (degree)    the amplifying polynomial has degree ≤ (p-1)·t                        [FpAmplify]
      ⇒ AC⁰[p] ACC-upper is complete: depth d ⟹ degree ((p-1)t)^d, error ≤ size·p^{-t}.
 ─── the wall ──────────────────────────────────────────────────────────────────────────────
 R6a composite = ∧       MOD_{pq} = MOD_p ∧ MOD_q for distinct primes         (CRT)           [CompositeWall]
 R6b characteristic lock the F_p symmetric form computes MOD_p but PROVABLY NOT MOD_q          [CompositeWall]
 R6  the wall            no single prime field's symmetric construction spans two primes       [CompositeWall]
```

## What the ladder establishes

* The **cash-out is mechanical** (R0): a semantically-invariant, `P`-bounded, hard-below resource separates.
* The naive **ℚ-communication-rank fails** (R2): bounded on an isolated MOD gate, exponential on a depth-2
  `AC⁰[2]` circuit, and blind to the prime/composite split.
* The **`F_p`-degree measure works for a single prime** (R3–R5): every `AC⁰[p]` gate multiplies degree by
  `≤ p-1`, amplifiable to error `p^{-t}` — the genuine Razborov–Smolensky ACC-upper side.
* The **composite / mixed `MOD` wall** (R6) is the terminal obstruction: the method is characteristic-locked, so
  it cannot span two primes — exactly why `AC⁰[p]` fell to the polynomial method and `NEXP ⊄ ACC⁰` needed
  Williams' algorithmic method instead.

## Honest scope

A map + anchors.  It proves **no** ACC⁰ lower bound and crosses **no** wall: R0–R5 are the (crossable) `AC⁰[p]`
upper machinery, R6 is the (uncrossable-by-this-method) obstruction, formalised.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACCDegreeLadder

/-! ## R0–R1 — the engine and the AC⁰ gate composition -/

/-- **Rung 0 — the cash-out (mechanical).**  `ACC_upper + hard_lower + monotone gap ⟹ f ∉ ACC⁰`. -/
abbrev ladder_R0_cashout := @NFrameACCBridge.acc_bridge_cashout

/-- **Rung 1 — AC⁰-gate composition.**  Any dynamic-SPDP obeying the additive gate recurrences is `≤ gateCount`;
so AND/OR/NOT layers compose without blow-up. -/
abbrev ladder_R1_gate_composition := @NFrameACCBridge.additive_le_gateCount

/-! ## R2 — why ℚ-communication-rank is the wrong measure -/

/-- **Rung 2a — a single MOD gate is ℚ-rank cheap.**  `rank_ℚ(M_{MOD_m}) ≤ m` for every `m`. -/
abbrev ladder_R2a_qrank_single_gate := @NFrameMODRankRecurrence.modm_commMatrix_rank_le

/-- **Rung 2b — MOD over sub-circuits blows up.**  `MOD_2(AND…) = IP` has ℚ-rank `2^n`; no `bound(m, ·)`
recurrence holds — so ℚ-communication-rank is rejected as the ACC dynamic-SPDP. -/
abbrev ladder_R2b_qrank_blows_up := @NFrameMODRankRecurrence.no_bounded_MOD_recurrence

/-! ## R3–R5 — the F_p-degree measure: the AC⁰[p] upper side -/

/-- **Rung 3 — MOD_p is degree-cheap over `F_p`.**  An exact `F_p` polynomial of total degree `≤ p-1`. -/
abbrev ladder_R3_modp_degree := @NFrameFpDegree.modp_low_degree_representation

/-- **Rung 4a — the OR gate degree recurrence.**  Degree-`d` children ⟹ degree `≤ (p-1)·d`. -/
abbrev ladder_R4a_or_degree := @NFrameFpANDOR.orComp_totalDegree_le

/-- **Rung 4a′ — the OR gate correctness** (off the linear form's zero set). -/
abbrev ladder_R4a_or_correct := @NFrameFpANDOR.orComp_eval_eq

/-- **Rung 4b — the AND gate degree recurrence** (dual). -/
abbrev ladder_R4b_and_degree := @NFrameFpANDOR.andComp_totalDegree_le

/-- **Rung 5 — Razborov–Smolensky amplification (abstract averaging).**  Per-input error `≤ 1/p` ⟹ some
`t`-tuple is bad on `≤ p^{-t}` of inputs. -/
abbrev ladder_R5_amplify := @NFrameFpAmplify.amplify

/-- **Rung 5a — the amplified OR error bound.**  `∃ W`, error set `≤ 2^k / p^t`. -/
abbrev ladder_R5a_amplified_error := @NFrameFpAmplify.or_amplified_error_bound

/-- **Rung 5b — the amplifying polynomial's degree.**  `≤ (p-1)·t`, independent of fan-in. -/
abbrev ladder_R5b_amplify_degree := @NFrameFpAmplify.orAmp_totalDegree_le

/-! ## R6 — the composite / mixed MOD wall -/

/-- **Rung 6a — composite = conjunction at different primes.**  `MOD_{ab} = MOD_a ∧ MOD_b` for coprime `a, b`. -/
abbrev ladder_R6a_crt := @NFrameCompositeMODWall.modGate_mul_coprime

/-- **Rung 6b — the characteristic lock.**  No function of the `F_p` symmetric form computes `MOD_q` for `q ∤ p`. -/
abbrev ladder_R6b_char_lock := @NFrameCompositeMODWall.symForm_char_locked

/-- **Rung 6 — the wall.**  For distinct primes `p, q`: `MOD_{pq} = MOD_p ∧ MOD_q`, and over `F_p` the symmetric
construction computes `MOD_p` but provably not `MOD_q` — so no single prime field spans both.  The terminal
obstruction of the polynomial/degree method. -/
abbrev ladder_R6_wall := @NFrameCompositeMODWall.composite_mod_wall

/-! ## Top of the ladder

The rungs above are all machine-checked (`#print axioms` below).  Read together they say: the degree dynamic-SPDP
is a *complete and honest* account of `AC⁰[p]` (R0–R5) whose *proven* terminal obstruction is composite / mixed
`MOD` (R6).  The ladder climbs to `AC⁰[p]` and stops exactly at the wall that separates the polynomial method
from full `ACC⁰` — the wall Williams' algorithmic method had to go around.  No rung is an ACC⁰ lower bound. -/

end PallLean.Paper93.DeepMath.PathB.NFrameACCDegreeLadder

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACCDegreeLadder.ladder_R0_cashout
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACCDegreeLadder.ladder_R2b_qrank_blows_up
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACCDegreeLadder.ladder_R3_modp_degree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACCDegreeLadder.ladder_R4a_or_degree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACCDegreeLadder.ladder_R5a_amplified_error
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACCDegreeLadder.ladder_R6_wall
