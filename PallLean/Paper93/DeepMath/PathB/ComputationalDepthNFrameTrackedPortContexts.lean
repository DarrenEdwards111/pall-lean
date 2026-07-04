import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSliceCoverObstruction

/-!
# N-Frame: tracked ports across contexts — the full identity family, lifted

The context lift of the tracking theorem, on the coordinate family where the full identity structure is
already formal: the slot-0 sign bits carry the workhorse probe family — `2^(m−2)` pin-contexts, every one of
them an identity context (`f = bvec j₀ ⊕ sign`), with **unconditional** sensitivity.

  `sat3_sign_port_tracks_contexts` — **PROVED, the lift**: a mediated slot-0 sign bit's mediator wire flips
        with the sign bit at **every one** of the `2^(m−2)` pin contexts — one flip obligation per context,
        the whole family at once.  The mediator wire must behave like the sign bit across the entire
        independent context cube: SAT's context structure is pushed down into the port.

## Honest scope

Two cautions, recorded so the aggregate is attacked honestly.  First, the slot-2 selector version of this
lift needs one new evaluation lemma (empty designated block, single slot-2 literal on a pinned or free
variable — flip value `bvec j`, so sensitivity is conditional for pinned variables and unconditional for
unpinned ones); that is a mechanical workhorse-style build, named as the next rung.  Second, the obligations
are *flips, not context separations*: a pass-through wire (the raw coordinate) satisfies all `2^(m−2)`
obligations at cost one gate — so no per-port count can bite, and the aggregate must charge what it costs to
satisfy *many selectors' obligation families through shared budget-priced wires simultaneously*.  That
aggregate is the standing face.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE CONTEXT LIFT (proved)**: a mediated slot-0 sign bit's mediator wire flips with the sign at every
one of the `2^(m−2)` pin contexts — the whole identity family imposes obligations at once. -/
theorem sat3_sign_port_tracks_contexts (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (p r : ℕ) (hmed : MediatedAt c (sat3SignBit N cIdx) p r) :
    ∀ bvec : Fin (sat3M N - 2) → Bool,
      (runFrom (Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
          (sat3Probe N ⟨0, hv⟩ false)) (sat3SignBit N cIdx) true) [] c).getD r false
      ≠ (runFrom (Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
          (sat3Probe N ⟨0, hv⟩ false)) (sat3SignBit N cIdx) false) [] c).getD r false := by
  intro bvec
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  have hbeh : ∀ a : Bool,
      sat3Family N (Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
        (sat3Probe N ⟨0, hv⟩ false)) (sat3SignBit N cIdx) a)
      = xor (bvec ⟨0, by omega⟩) a := by
    intro a
    rw [patch_probe_update]
    exact sat3Context_probe_eval N hv hk hkv cIdx bvec ⟨0, by omega⟩ ⟨0, hv⟩ rfl a
  have hsens : sat3Family N (Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
        (sat3Probe N ⟨0, hv⟩ false)) (sat3SignBit N cIdx) true)
      ≠ sat3Family N (Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
        (sat3Probe N ⟨0, hv⟩ false)) (sat3SignBit N cIdx) false) := by
    rw [hbeh true, hbeh false]
    cases hb : bvec ⟨0, by omega⟩ <;> decide
  have h := slice_ports_must_flip (sat3Family N) c hcomp
    [(⟨sat3SignBit N cIdx, p, r⟩ : Fin N × ℕ × ℕ)]
    (by
      intro t' ht'
      rw [List.mem_singleton] at ht'
      subst ht'
      exact hmed)
    (⟨sat3SignBit N cIdx, p, r⟩ : Fin N × ℕ × ℕ) List.mem_cons_self
    (sat3Patch N cIdx (sat3Context N cIdx hk bvec) (sat3Probe N ⟨0, hv⟩ false)) hsens
  obtain ⟨t', ht', hflip⟩ := h
  rw [List.mem_singleton] at ht'
  subst ht'
  exact hflip

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_sign_port_tracks_contexts
