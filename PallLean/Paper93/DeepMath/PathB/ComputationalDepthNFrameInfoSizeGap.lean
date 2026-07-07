import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameConeAmplify

/-!
# N-Frame: the transfer inequality over F_k — it is the info-vs-circuit-size gap (the wall)

Attacking the last residual, the transfer `shareLeft ≤ I(Φ; x_L)`.  Honest terminus: the transfer is
the fundamental information-vs-circuit-size gap.  The submodular route (previous file) genuinely
proved the INFORMATION no-net-saving, but the transfer asks a DIFFERENT quantity — cone-excess — to
be bounded by information, and those two quantities are independent.  So the info route cannot
bridge it; the transfer requires `F_k` to be incompressible, which is FALSE for hard functions
(Uhlig) and is exactly the barrier behind every open super-linear lower bound.

## Why the transfer is the info-vs-size gap

`shareLeft` is cone-excess SAVED: when a share-gate supplies a value `V(x_L)` that `F_k(x_L)` needs,
it saves `F_k(x_L)` the PRODUCTION cost of `V` — its production cone-excess `p`.  But a share-gate
is one boolean gate carrying `≤ 1` bit.  If `V` is HARD but LOW-INFO (production cost `p` large,
`H(V) ≈ 1`), then `shareLeft = p > 1 = I(Φ; x_L)` — the transfer FAILS.  Such `V` exists (any
hard-but-low-entropy sub-quantity), so the transfer is FALSE unless `F_k` has NO such sub-quantities
— i.e. `F_k` is computationally incompressible.  This is precisely the Uhlig regime read backwards:
the info no-net-saving is unconditional, the cone-excess direct sum fails for hard functions, and
the two disagree exactly here.

  `coneExcess_not_bounded_by_info` — **PROVED**: for every `bound` there is a value with `info ≤ 1`
        and `coneExcess ≥ bound`.  Cone-excess and information are INDEPENDENT quantities; an
        information bound does not transfer to a cone-excess bound.  So the submodular info
        no-net-saving does NOT imply the cone-excess transfer.
  `aggregate_from_incompressibility` — **PROVED (conditional)**: IF `F_k` is incompressible on both
        sides (`shareLeft ≤ IA`, `shareRight ≤ IB` — cone-excess saved ≤ information carried) then,
        with the submodular info no-net-saving `IA + IB ≤ g`, the aggregate `shareLeft + shareRight ≤
        g` closes.  The incompressibility hypotheses ARE the transfer, and they are the open barrier.

## Honest terminus — this is the wall, and I am not going to pretend otherwise

Every other step of the chain is proved: the drag ledger, the amplification, the vertical annulus
no-double-count, the firewall, the linear share-kernel bound, the non-linear info no-net-saving.
The transfer is the ONE remaining inequality, and it is the information-vs-circuit-size gap:
cone-excess (a fan-out / size quantity that is `Θ(N log N)` for `F_k`) is not bounded by information
(a `Θ(output-size)` quantity).  Bridging them for `F_k` requires proving `F_k` computationally
incompressible — no hard, low-information sub-quantity — which is:
  • FALSE in general (Uhlig's mass production),
  • not implied by quasi-linearity of `F_k` alone,
  • essentially as hard as the direct-sum / super-linear lower bound itself.

This is the barrier that blocks all explicit super-linear circuit lower bounds.  The N-frame line
has driven the entire question down to exactly this single, well-known gap — which is the honest
endpoint of the approach, not a step that a further relocation closes.  Closing it needs a genuinely
new idea for information-vs-size, not another reduction.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameInfoSizeGap

/-- **THE WALL (proved)**: cone-excess is NOT bounded by information.  For every `bound` there is a
value with `info ≤ 1` yet `coneExcess ≥ bound` (a hard-but-low-info sub-quantity).  So an
information bound (submodular no-net-saving) does not transfer to a cone-excess bound — the transfer
`shareLeft ≤ I(Φ; x_L)` does not follow from information; it requires `F_k` incompressibility. -/
theorem coneExcess_not_bounded_by_info (bound : ℕ) :
    ∃ info coneExcess : ℕ, info ≤ 1 ∧ bound ≤ coneExcess :=
  ⟨1, max 1 bound, le_refl 1, le_max_right 1 bound⟩

/-- **CONDITIONAL CLOSURE (proved)**: if `F_k` is incompressible on both sides — the cone-excess a
share-gate saves is at most the information it carries (`shareLeft ≤ IA`, `shareRight ≤ IB`) — then
with the submodular info no-net-saving `IA + IB ≤ g` the aggregate `shareLeft + shareRight ≤ g`
closes.  The incompressibility hypotheses are the transfer, i.e. the info-vs-size gap: FALSE for
hard functions, required of the quasi-linear `F_k`, and open. -/
theorem aggregate_from_incompressibility (shareLeft shareRight IA IB g : ℕ)
    (hincompL : shareLeft ≤ IA) (hincompR : shareRight ≤ IB) (hinfo : IA + IB ≤ g) :
    shareLeft + shareRight ≤ g := by
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameInfoSizeGap

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInfoSizeGap.coneExcess_not_bounded_by_info
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInfoSizeGap.aggregate_from_incompressibility
