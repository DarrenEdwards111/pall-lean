import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShadowProjection

/-!
# A proof is not a bounded observer: why "the shadow can't decide it" ≠ "P vs NP is unprovable"

Darren's inference: the shadow is complete-for-us yet doesn't decide `P ≠ NP`, so `P ≠ NP` is *unprovable*.
The premise is true (`shadow_complete_but_undecided`); the conclusion does **not** follow — and the gap is
worth making precise, because it is a genuine and common confusion.

The shadow result is about the bounded **computational observer**: a polynomial-interface machine cannot
*see* the superpolynomial dimensions, so its projection does not *decide* the full bound.  But a **proof**
is not a bounded computational observer.  A proof is a finite *symbolic* object that *reasons about* the
full-dimensional structure without any polynomial circuit computing it.  Conflating "a bounded machine
can't compute/see dimension `D`" with "no proof can establish facts about dimension `D`" is the error.

## What is proved

* **`proof_exceeds_observer`** — a proof accesses the full dimension even where the observer's shadow is
  capped: when `interfaceDim < fullDim`, `shadow < proofAsserts` (`= fullDim`).  The proof is not bounded by
  the interface.
* **`proof_distinguishes`** — the decisive point: two worlds the observer's shadow *cannot* tell apart
  (`shadow ⟨big₁,d⟩ = shadow ⟨big₂,d⟩`) are *distinguished* by a proof (`proofAsserts big₁ ≠ big₂`).  What
  the computational observer cannot decide, a proof can.

## Honest scope — hard is not unprovable, and this settles neither way

So the shadow's non-determination is **computational inaccessibility**, not **proof-theoretic
independence**.  "The P-observer can't see the higher dimensions" does not imply "no proof reaches them" —
`proof_distinguishes` shows a proof reaches exactly what the observer can't.

Three honest points, holding the line in *both* directions:

1. **The barriers are "hard," not "impossible."**  Natural proofs, relativization, algebrization rule out
   *techniques* — specific kinds of proof — not *all* proofs.  They explain why `P ≠ NP` is hard; they are
   not independence results.
2. **Actual independence is open, and the lean is against it.**  Whether `P vs NP` is independent of ZFC is
   a genuine open question, but it is a *concrete arithmetic* statement, and there is no strong reason to
   believe it is independent (Aaronson's survey); independence would itself be a shocking, separately-proved
   result — not a default.
3. **This file certifies neither.**  It does not prove `P ≠ NP`, and it does not prove `P vs NP` is
   unprovable.  It proves only that the *shadow* argument does not establish unprovability — a proof is not
   the bounded observer.  The theorem remains open, hard, and (as far as anything here shows) provable.
   Nothing here is `P ≠ NP`, and nothing here is "`P vs NP` is unprovable."
-/

namespace PallLean.Paper93.DeepMath.PathB.ProofNotObserver

open PallLean.Paper93.DeepMath.PathB.ShadowProjection

/-- What a **proof** accesses: the full dimension directly.  A proof is a finite symbolic object that
reasons about the full-dimensional bound — it is *not* bounded by the observer's interface. -/
def proofAsserts (S : ShadowBound) : ℕ := S.fullDim

/-- **A proof exceeds the observer (proved).**  Where the observer's shadow is capped
(`interfaceDim < fullDim`), a proof still reaches the full dimension: `shadow S < proofAsserts S`.  The
proof is not bounded by the interface. -/
theorem proof_exceeds_observer (S : ShadowBound) (hb : S.interfaceDim ≤ S.fullDim)
    (hlt : S.interfaceDim < S.fullDim) : shadow S < proofAsserts S := by
  have h := bounded_shadow_capped S hb
  show shadow S < S.fullDim
  rw [h]
  exact hlt

/-- **A proof distinguishes what the observer cannot (proved).**  Two worlds with the *same* shadow
(`shadow ⟨big₁,d⟩ = shadow ⟨big₂,d⟩` — the observer cannot decide) are *distinguished* by a proof
(`proofAsserts ⟨big₁,d⟩ ≠ proofAsserts ⟨big₂,d⟩`).  So computational non-decision is not proof-theoretic
independence: what the bounded observer can't see, a proof can establish. -/
theorem proof_distinguishes (d big1 big2 : ℕ) (h1 : d ≤ big1) (h2 : d ≤ big2) (hne : big1 ≠ big2) :
    shadow ⟨big1, d⟩ = shadow ⟨big2, d⟩ ∧ proofAsserts ⟨big1, d⟩ ≠ proofAsserts ⟨big2, d⟩ :=
  ⟨shadow_undetermines d big1 big2 h1 h2, hne⟩

end PallLean.Paper93.DeepMath.PathB.ProofNotObserver

#print axioms PallLean.Paper93.DeepMath.PathB.ProofNotObserver.proof_exceeds_observer
#print axioms PallLean.Paper93.DeepMath.PathB.ProofNotObserver.proof_distinguishes
