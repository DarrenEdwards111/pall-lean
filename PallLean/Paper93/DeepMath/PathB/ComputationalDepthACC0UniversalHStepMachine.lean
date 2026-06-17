import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NTM

/-!
# The physical `hstep` realization with explicit overhead `B`

Entry 181 proved the `hstep` *correctness contract* (decode → step → re-encode is faithful at the encoded-tape level).
This file turns it into an actual **universal-machine simulation lemma with explicit overhead**: the universal machine
`U` reaches the re-encoded configuration from the encoded one within a bounded number `B` of *its own* steps, where `B`
is the explicit sum of the four phase costs.

The universal step is realised in four phases over `U`'s own transitions: **decode** the simulated `(M, c)` from the
tape, **look up** the firing rule, **rewrite** the tape, and **re-encode** to `(M, applyTrans c t)`.  If each phase is
realised as a `U`-transition run within its own bound (`bDecode`, `bLookup`, `bRewrite`, `bReencode` — the per-phase
realisation hypotheses), then `U` reaches the final configuration within `B = bDecode + bLookup + bRewrite + bReencode`
of its own steps.  The overhead composition is proved from `reachIn_add` (reachability is additive); the explicit `B` is
the sum.

## What is proved (clean axioms, no `sorry`)

* **`hstep_realized_with_overhead`** — given the four per-phase reachabilities, `U` reaches `c4` from `c0` within
  `bDecode + bLookup + bRewrite + bReencode` steps (the phases compose, via `reachIn_add`).
* **`hstep_exists_overhead`** — hence `∃ B, reachIn U B c0 c4` (the explicit `B` is the phase sum): the `hstep`
  realisation as a simulation lemma with bounded overhead.

## Honest scope

This proves the **overhead composition**: *if* each of the four phases (decode / rule-lookup / tape-rewrite / re-encode)
is realised as a run of `U`'s own transitions within its bound, *then* the whole universal step runs within the explicit
`B = ∑` of those bounds — turning the entry-181 semantic contract into a step-bounded simulation lemma.  The four
per-phase reachabilities are taken as hypotheses: they are the genuine remaining construction — building `U`'s actual
transition table so that each phase is a real `U`-transition sequence over the `encodeTape` layout (the proved
sub-machine *contracts* of `…ACC0TapeEncoding` / `…ACC0RuleLookup` / `…ACC0TapeRewrite` / `…ACC0UniversalDecode` specify
*what* each phase computes; realising them as transitions with the per-phase step counts is the remaining classical TM
engineering).  What is established here is that *once each phase is realised*, the overhead is exactly the additive sum.
Classical Turing-machine construction, not an open problem; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalHStepMachine

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (NTM reachIn reachIn_add)

/-- **The `hstep` realisation with explicit overhead (proved).**  The universal step runs in four phases — decode
(`c0 → c1`), rule-lookup (`c1 → c2`), tape-rewrite (`c2 → c3`), re-encode (`c3 → c4`).  If each phase is a run of `U`'s
own transitions within its bound, then `U` reaches `c4` from `c0` within `bDecode + bLookup + bRewrite + bReencode`
steps.  Proved by composing the phases with `reachIn_add` (reachability is additive). -/
theorem hstep_realized_with_overhead (U : NTM) (c0 c1 c2 c3 c4 : U.Config)
    (bDecode bLookup bRewrite bReencode : ℕ)
    (hDecode : reachIn U bDecode c0 c1)
    (hLookup : reachIn U bLookup c1 c2)
    (hRewrite : reachIn U bRewrite c2 c3)
    (hReencode : reachIn U bReencode c3 c4) :
    reachIn U (bDecode + bLookup + bRewrite + bReencode) c0 c4 := by
  rw [show bDecode + bLookup + bRewrite + bReencode
        = bDecode + (bLookup + (bRewrite + bReencode)) by ring,
      reachIn_add]
  refine ⟨c1, hDecode, ?_⟩
  rw [reachIn_add]
  refine ⟨c2, hLookup, ?_⟩
  rw [reachIn_add]
  exact ⟨c3, hRewrite, hReencode⟩

/-- **The `hstep` realisation as a bounded-overhead simulation lemma (proved): `∃ B, reachIn U B c0 c4`.**  The explicit
overhead is `B = bDecode + bLookup + bRewrite + bReencode` — the universal machine performs one simulated `M`-step in `B`
of its own steps, the `B`-bounded form of `hstep` (modulo the per-phase realisations). -/
theorem hstep_exists_overhead (U : NTM) (c0 c1 c2 c3 c4 : U.Config)
    (bDecode bLookup bRewrite bReencode : ℕ)
    (hDecode : reachIn U bDecode c0 c1) (hLookup : reachIn U bLookup c1 c2)
    (hRewrite : reachIn U bRewrite c2 c3) (hReencode : reachIn U bReencode c3 c4) :
    ∃ B, reachIn U B c0 c4 :=
  ⟨_, hstep_realized_with_overhead U c0 c1 c2 c3 c4 bDecode bLookup bRewrite bReencode
    hDecode hLookup hRewrite hReencode⟩

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalHStepMachine

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalHStepMachine.hstep_realized_with_overhead
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalHStepMachine.hstep_exists_overhead
