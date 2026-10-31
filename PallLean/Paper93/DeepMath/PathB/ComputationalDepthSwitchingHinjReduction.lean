import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingFinalWiring
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSetDecoderDecomp

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

**A chain of three reductions, each strictly shrinking the target** (all proved, using existing infra):

1. `hinj_of_forward_decoder` — `hinj ⟸` recover the whole `ρ` from `(end-state, label)`.
2. `hinj_of_sel_decoder` — `hinj ⟸` recover only the **selected set** `replaySel cs ρ s`, since
   `replayPath_inj` already proves `σ` is determined by `(replayPath, replaySel)` (`σ = freeOn end-state
   replaySel`).
3. `hinj_of_free_indicator` — `hinj ⟸` the label recovers the **`ρ`-free subset of `decodedSel`**, since
   `replaySel_eq_decodedSel_filter` proves `replaySel cs ρ s = decodedSel cs (replayPath cs ρ s) ∩ {ρ-free}`
   and `decodedSel` is computed from the **end-state alone**. This is the tight `(2w)^s` core: one bit per
   selected coordinate — pivot (`ρ`-free) vs `ρ`-set — the exact classical Håstad star-pattern.

## What is proved (clean axioms, no `sorry`)

* `hinj_of_forward_decoder`, `hinj_of_sel_decoder`, `hinj_of_free_indicator` — the reduction chain above.
* `hinj_hnf` — **`hinj` proved outright on the `hnf` regime** (unconditional, no `recT`, no label): where
  every `ρ ∈ Bad` falsifies no term, `decodedSel_eq_replaySel` recovers `replaySel` from the end-state alone,
  so `hinj` holds. The whole reduction chain closes end-to-end exactly where the decoder already exists.

## Honest scope

The reduction chain pins the remaining target as tightly as the proved infrastructure allows — down to "the
label recovers the star-pattern" — and `hinj_hnf` **closes `hinj` on the `hnf` regime** through that chain (a
genuine proof, not scaffolding; combined with `switching_measure_bound_modulo_inj` it re-derives the
unconditional `hnf` switching bound via injectivity). The general regime remains open at exactly one
primitive: the term-recovery oracle `recT` (recover the active term per step from the end-state for general
`ρ`) — the Razborov satisfy-encoding decoder, never constructed in the arc. `AC⁰`/depth-3; nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
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

/-- **Sharper: `hinj` from a *selected-set* decoder (proved).**  `replayPath_inj` already proves that `σ`
is determined by `(replayPath cs σ s, replaySel cs σ s)` (via `freeOn` — the end-state with the selected
coordinates cleared).  So the decoder need only recover the **selected set** `replaySel cs ρ s` from
`(end-state, label)`, not the whole restriction.  This strictly shrinks the target of
`hinj_of_forward_decoder`. -/
theorem hinj_of_sel_decoder {w s : ℕ} (cs : List (Clause n))
    (Bad : Finset (Restriction n)) (lab : Restriction n → PathLabel w s)
    (selDec : Restriction n → PathLabel w s → Finset (Fin n))
    (hsel : ∀ ρ ∈ Bad, selDec (replayPath cs ρ s) (lab ρ) = replaySel cs ρ s) :
    ∀ x ∈ Bad, ∀ y ∈ Bad,
      (replayPath cs x s, lab x) = (replayPath cs y s, lab y) → x = y := by
  intro x hx y hy heq
  rw [Prod.mk.injEq] at heq
  have hsel_eq : replaySel cs x s = replaySel cs y s := by
    rw [← hsel x hx, ← hsel y hy, heq.1, heq.2]
  exact replayPath_inj cs s heq.1 hsel_eq

/-- **Sharpest: `hinj` from a *ρ-free indicator* (proved).**  By `replaySel_eq_decodedSel_filter`,
`replaySel cs ρ s = decodedSel cs (replayPath cs ρ s) ∩ {v : ρ v = none}`, and `decodedSel` is computed
from the **end-state alone** (no label).  So the *only* thing the label must supply is a `freeSet` picking
out the `ρ`-free (pivot) coordinates among the end-state-computable `decodedSel` — the star-pattern.  Thus
`hinj` reduces to: the label recovers the `ρ`-free subset of `decodedSel`.  This is the tight `(2w)^s`
core (one bit per selected coordinate: pivot vs `ρ`-set) — the exact classical Håstad encoding content. -/
theorem hinj_of_free_indicator {w s : ℕ} (cs : List (Clause n))
    (Bad : Finset (Restriction n)) (lab : Restriction n → PathLabel w s)
    (freeSet : Restriction n → PathLabel w s → Finset (Fin n))
    (hfree : ∀ ρ ∈ Bad,
      decodedSel cs (replayPath cs ρ s) ∩ freeSet (replayPath cs ρ s) (lab ρ)
        = replaySel cs ρ s) :
    ∀ x ∈ Bad, ∀ y ∈ Bad,
      (replayPath cs x s, lab x) = (replayPath cs y s, lab y) → x = y :=
  hinj_of_sel_decoder cs Bad lab
    (fun endstate l => decodedSel cs endstate ∩ freeSet endstate l)
    (fun ρ hρ => hfree ρ hρ)

/-- **`hinj` closed on the `hnf` regime (PROVED, unconditional).**  When every `ρ ∈ Bad` falsifies no term
of `cs`, `decodedSel_eq_replaySel` gives `decodedSel cs (replayPath cs ρ s) = replaySel cs ρ s` — the
selected set is recovered from the **end-state alone** (no `recT`, no label), because with nothing falsified
by `ρ` there are no `ρ`-set coordinates to disambiguate.  Feeding `selDec = decodedSel ∘ end-state` into
`hinj_of_sel_decoder` closes `hinj` on this regime.  This is the first end-to-end *proof* of `hinj` (not a
reduction): the whole chain closes exactly where the decoder exists.  Combined with
`switching_measure_bound_modulo_inj` it re-derives the unconditional `hnf` switching bound through the
injectivity route.  The general regime still needs the term-recovery oracle `recT`. -/
theorem hinj_hnf {w s : ℕ} (cs : List (Clause n))
    (Bad : Finset (Restriction n)) (lab : Restriction n → PathLabel w s)
    (hhnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, termFalsified ρ T = false) :
    ∀ x ∈ Bad, ∀ y ∈ Bad,
      (replayPath cs x s, lab x) = (replayPath cs y s, lab y) → x = y := by
  refine hinj_of_sel_decoder cs Bad lab (fun endstate _ => decodedSel cs endstate) ?_
  intro ρ hρ
  exact decodedSel_eq_replaySel (fun T hT => hhnf ρ hρ T hT) s

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.hinj_of_forward_decoder
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.hinj_of_sel_decoder
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.hinj_of_free_indicator
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.hinj_hnf
