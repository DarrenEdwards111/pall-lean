import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingGeneralReindex
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCountModuloRecovery
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSetDecoderDecomp
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingLiveDNFDecoder
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSatDecoderScope

/-!
# Switching-lemma arc — machine-checked manifest

A single verified entry point for the Håstad switching-lemma arc built this session: a `#check` index
of every load-bearing theorem, confirming the whole arc composes and is clean (`[propext,
Classical.choice, Quot.sound]`, no `sorry`, no custom axioms).  Mirrors the codebase's other manifests
(`Depth3FullPipelineManifest`, `ExpanderTseitinBSWManifest`).

## Structure of the arc

**Decoder / counting (deterministic):**
* `decodeLoop_recover` — decoder loop correct given the active-literal list.
* `replay_switching_count` — the `(2w)^s` cardinality count, modulo the per-step decoder `hdec`.
* `litAtPos_active`, `decodeActiveTermLit_canonTermPos` — position↔literal codec + per-step inverse.
* `decode_from_endstate`, `replaySel_recovered` — end-state literal recovery modulo term-recovery.
* `replay_count_modulo_termRecovery` — `(2w)^s` count modulo the active-term oracle.
* `replaySel_subset_decodedSel`, `replaySel_eq_decodedSel_filter` — set-decoder completeness + the
  exact decomposition `replaySel = decodedSel ∩ {ρ-free}`.
* `replay_count_modulo_freeIndicator` — count modulo the ρ-free indicator (lightest oracle).

**Live-DNF normalization (general ⇒ `hnf`):**
* `activeTerm_liveCs`, `replayPath_liveCs`, `replaySel_liveCs` — path/selected-set invariant under
  dropping `ρ`-falsified terms.
* `replaySel_eq_decodedSel_liveCs` — the general identity `replaySel = decodedSel over liveCs`.
* `liveCs_base_agree` — the decoder's `hnf`-base holds on the live sub-DNF.

**Probabilistic measure:**
* `pweight_ratio` — the `s`-fold weight ratio.
* `stars_replayPath` — the path fixes exactly the selected coordinates.
* `sum_weight_inj_le`, `restrWeight_replayPath` — the measure assembly.
* `sum_restrWeight_eq_one` — total probability.
* `switching_measure_bound_modulo_inj` — the measure bound modulo injectivity (= the confound).

**Headline bounds:**
* `switching_bound_hnf` — **unconditional** tight bound `(2w·2p/(1-p))^s` on the `hnf` regime.
* `switching_bound_general` — the weak general bound `(#live-sub-DNFs)·(2w·2p/(1-p))^s`.

## The wall

Every route reduces the *tight general* switching bound to one primitive: `hinj` — recover `ρ` from
`(end-state, label)` (= the decoder, the confound).  It is **absent** on the `hnf`/live-sub-DNF regime
(`switching_bound_hnf`, proved) and is the *whole cost* of the general regime (the `2^{|cs|}` factor in
`switching_bound_general`).  Discharging it unconditionally is Razborov's satisfy-encoding forward
decoder — a from-scratch construction, **not** done and **not** faked.  Honest ceiling: AC⁰/depth-3.
`Depth3CollapseModel.collapse` and P vs NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB.SwitchingArcManifest

open PallLean.Paper93.DeepMath.PathB.SwitchingCounting

-- Decoder / counting
#check @replay_switching_count
#check @litAtPos_active
#check @decodeActiveTermLit_canonTermPos
#check @decode_from_endstate
#check @replaySel_recovered
#check @replay_count_modulo_termRecovery
#check @replaySel_subset_decodedSel
#check @replaySel_eq_decodedSel_filter

-- Live-DNF normalization
#check @activeTerm_liveCs
#check @replayPath_liveCs
#check @replaySel_liveCs
#check @replaySel_eq_decodedSel_liveCs
#check @liveCs_base_agree

-- Probabilistic measure
#check @pweight_ratio
#check @stars_replayPath
#check @sum_weight_inj_le
#check @restrWeight_replayPath
#check @sum_restrWeight_eq_one
#check @switching_measure_bound_modulo_inj

-- Headline bounds
#check @switching_bound_hnf
#check @switching_bound_general

-- Clean-axiom confirmation of the two headline bounds
#print axioms switching_bound_hnf
#print axioms switching_bound_general

end PallLean.Paper93.DeepMath.PathB.SwitchingArcManifest
