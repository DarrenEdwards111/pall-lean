import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingFinalWiring

/-!
# `hinj` reduction — isolating the exact remaining target of the switching lemma

`switching_measure_bound_modulo_inj` (and the three deterministic decoder routes) all reduce the tight
general Håstad switching lemma to a single primitive, `hinj`:

  `∀ x y ∈ Bad, (replayPath cs x s, lab x) = (replayPath cs y s, lab y) → x = y`

i.e. the encoding `ρ ↦ (end-state, label)` is injective on the bad set. For a finite map injectivity is
equivalent to having a left inverse — a **forward decoder** recovering `ρ` from `(end-state, label)`.

**Where the gap is (pinned).** The concrete decoder `recoverStream` is *already general*: its correctness
`Depth3.recoverStream_eq` holds for **any** running state `τ ⊑ σ` that **falsification-agrees** with the
descent state `σ` on `cs` (`∀ U ∈ cs, termFalsified τ U = termFalsified σ U`). The `hnf` restriction enters
at exactly one point — `recoverStream_correct` starts `τ = all-free`, which falsifies nothing, so the base
agreement forces `termFalsified ρ U = false` for all `U` (= `hnf`). So the *entire* remaining content of
`hinj` is: supply the decoder a starting state that falsification-agrees with `ρ` — equivalently, recover the
set of `ρ`-falsified terms from `(end-state, label)`. That is Razborov's satisfy-encoding forward decoder,
and it is a from-scratch construction (not done here, not faked).

This file isolates that target as a clean brick: `hinj` follows from **any** forward decoder `dec` with the
left-inverse property `hdec`. The remaining mathematical work is exactly to build `dec` (for the general
regime) and prove `hdec`; `Depth3.recoverStream_correct` already supplies the `hnf`-regime start.

## What is proved (clean axioms, no `sorry`)

* `hinj_of_forward_decoder` — `hinj` from a left-inverse forward decoder. Reduces the switching lemma's sole
  remaining hypothesis to constructing that decoder.

## Honest scope

A reduction/scaffolding brick, not a proof of `hinj`: it converts the injectivity obligation into the
decoder-construction obligation and pins where the `hnf` restriction is the only gap. The hard part —
the general forward decoder — remains open. `AC⁰`/depth-3; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **`hinj` from a forward decoder (proved).**  If there is a decoder `dec` that recovers `ρ` from its
encoding `(replayPath cs ρ s, lab ρ)` on the bad set (`hdec`, the left-inverse property), then the encoding
is injective on `Bad` — the exact `hinj` hypothesis of `switching_measure_bound_modulo_inj`.  This isolates
the switching lemma's remaining content to constructing `dec`. -/
theorem hinj_of_forward_decoder {w s : ℕ} (cs : List (Clause n))
    (Bad : Finset (Restriction n)) (lab : Restriction n → PathLabel w s)
    (dec : Restriction n → PathLabel w s → Restriction n)
    (hdec : ∀ ρ ∈ Bad, dec (replayPath cs ρ s) (lab ρ) = ρ) :
    ∀ x ∈ Bad, ∀ y ∈ Bad,
      (replayPath cs x s, lab x) = (replayPath cs y s, lab y) → x = y := by
  intro x hx y hy heq
  rw [Prod.mk.injEq] at heq
  calc x = dec (replayPath cs x s) (lab x) := (hdec x hx).symm
    _ = dec (replayPath cs y s) (lab y) := by rw [heq.1, heq.2]
    _ = y := hdec y hy

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.hinj_of_forward_decoder
