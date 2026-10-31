import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalRun
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalLookupPhase

/-!
# The physical universal interpreter loop — phases assembled, multi-step cost `k·B` (proved)

Closing the transition-table compile socket's last mechanics.  Entry 304 proved the encoded universal machine `uEncNTM`
tracks the full run (logical); entry 305 proved the per-step overhead `B = stepOverhead`.  This file assembles the
**interpreter loop** from the proved phase contracts and proves the **multi-step cost lift** `k · B`.

**The phases (all proved elsewhere, bundled here).**  One universal step on a genuine `M`-step `concreteStep M c d`:

1. **decode** — `decodeSim (encodeSim M c) = some (M, c)` (`…ACC0UniversalDecode.decodeSim_encodeSim`);
2. **lookup** — a matching rule `t ∈ matchingRules M c.1 (readSym c)` fires, reaches `d = applyTrans c t`, with scan
   cost `≤ M.length` (`…ACC0UniversalLookupPhase.lookup_phase`);
3. **apply** — write/move/state via `applyTrans` (in 2);
4. **re-encode** — `decodeSim (encodeSim M d) = some (M, d)` (round-trip).

`physical_uStep_phases` bundles these four into the single-step realization, with the scan-cost bound.

**The multi-step lift.**  Given a physical realization `Realizes` (reaches within a step budget) that realizes *one*
`uEncStep` in `B` steps (`perStep`) and composes additively (`compose`), an entire encoded run `reachIn uEncNTM k s t`
is realized in `k · B` steps (`physical_tracks_lift`) — by induction on `k`, accumulating the per-step `B`.  This is
exactly `physicalU_tracks_uEncNTM` with `C = 0`.

## What is proved (clean axioms, no `sorry`)

* **`physical_uStep_phases`** — one universal step realized via the four proved phases (decode, lookup with scan
  `≤ M.length`, apply, re-encode).
* **`physical_tracks_lift`** — the multi-step cost: `reachIn uEncNTM k s t` ⟹ `Realizes (enc s) (enc t) (k · B)`,
  given per-step realization in `B` and additive composition.

## Honest scope

This assembles the interpreter loop from the proved phase contracts and proves the multi-step cost lift `k · B`.  The
two remaining inputs, isolated as hypotheses of `physical_tracks_lift`, are the genuine last physical primitives: (i)
`perStep` — one `uEncStep` is realized by the concrete physical machine `U` in `B` primitive steps (the decode →
lookup → apply → re-encode loop executing one tape-operation per step, with `B = stepOverhead`, entry 305); and (ii)
`compose`/`refl0` — `U`'s reachability composes additively (standard).  Both are classical Turing-machine engineering
over the proved sub-machine contracts, not open problems.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PhysicalUniversalLoop

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine CConfig concreteStep applyTrans readSym toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalDecode (encodeSim decodeSim decodeSim_encodeSim)
open PallLean.Paper93.DeepMath.PathB.ACC0RuleLookup (matchingRules)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalRun (uEncStep uEncNTM)

/-- **One universal step, via the four proved phases (PROVED).**  For a genuine `M`-step `concreteStep M c d`: the tape
decodes to `(M, c)` (decode), a matching rule fires to `d = applyTrans c t` with scan cost `≤ M.length` (lookup +
apply), and the result re-encodes/round-trips to `(M, d)` (re-encode).  The interpreter loop's single step, assembled. -/
theorem physical_uStep_phases (M : TMachine) (c d : CConfig) (h : concreteStep M c d) :
    decodeSim (encodeSim M c) = some (M, c)
      ∧ (∃ t ∈ matchingRules M c.1 (readSym c),
          d = applyTrans c t ∧ (matchingRules M c.1 (readSym c)).length ≤ M.length)
      ∧ decodeSim (encodeSim M d) = some (M, d) := by
  refine ⟨decodeSim_encodeSim M c, ?_, decodeSim_encodeSim M d⟩
  obtain ⟨t, ht, _hreach, hd, hscan⟩ := ACC0UniversalLookupPhase.lookup_phase M c d h
  exact ⟨t, ht, hd, hscan⟩

/-- **The multi-step cost lift (PROVED): `reachIn uEncNTM k s t ⟹ Realizes (enc s) (enc t) (k · B)`.**  Given a physical
realization `Realizes` that handles one `uEncStep` in `B` steps (`perStep`) and composes additively (`compose`, `refl0`),
an entire encoded run of `k` steps is realized in `k · B` physical steps — by induction on `k`, accumulating `B` per
step.  (`= physicalU_tracks_uEncNTM` with `C = 0`.) -/
theorem physical_tracks_lift {Realizes : List Bool → List Bool → ℕ → Prop}
    (enc : List Bool → List Bool) (B : ℕ)
    (refl0 : ∀ a, Realizes a a 0)
    (perStep : ∀ s u, uEncStep s u → Realizes (enc s) (enc u) B)
    (compose : ∀ a b c m n, Realizes a b m → Realizes b c n → Realizes a c (m + n)) :
    ∀ (k : ℕ) (s t : List Bool), reachIn uEncNTM k s t → Realizes (enc s) (enc t) (k * B) := by
  intro k
  induction k with
  | zero =>
    intro s t h
    simp only [reachIn] at h
    subst h
    simpa using refl0 (enc s)
  | succ k ih =>
    intro s t h
    obtain ⟨u, hstep, hr⟩ := h
    have h1 : Realizes (enc s) (enc u) B := perStep s u hstep
    have h2 : Realizes (enc u) (enc t) (k * B) := ih u t hr
    have hc := compose (enc s) (enc u) (enc t) B (k * B) h1 h2
    have hkB : (k + 1) * B = B + k * B := by ring
    rw [hkB]
    exact hc

/-!
**The interpreter loop.**  The four phases (decode/lookup/apply/re-encode) are proved and bundled
(`physical_uStep_phases`), and the multi-step cost lift `k · B` is proved (`physical_tracks_lift`).  The remaining last
physical primitives — isolated as the `perStep` and `compose`/`refl0` hypotheses — are: one `uEncStep` realized by `U`
in `B = stepOverhead` primitive steps (the decode→lookup→apply→re-encode loop, one tape-op per step, entry 305), and
`U`'s reachability composing additively (standard).  Both are classical TM engineering over the proved sub-machine
contracts.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0PhysicalUniversalLoop

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PhysicalUniversalLoop.physical_uStep_phases
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PhysicalUniversalLoop.physical_tracks_lift
