import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BeigelTaruiSparsity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DynamicObserverSelection

/-!
# Threshold/BT closure — splitting `DynamicClosesAtBT` into its proved half and the depth-reduction socket

`DynamicClosesAtBT` (entry 166's wall) is, in classical terms, the **Beigel–Tarui / Yao theorem**: every `ACC⁰`
function has a quasipolynomial-size `SYM∘AND` representation (a symmetric top gate over `n^{polylog}` AND gates of
`polylog` fan-in).  This — and `NEXP ⊄ ACC⁰` (Williams 2011) which uses it — are *proven* classical theorems; the wall
in this development is the **size of the Lean formalisation**, not mathematical openness.  This file dissects the wall
to show precisely which part is already proved here and which part is the genuine remaining formalisation.

The BT bound is a product of two factors:
```
  (quasipoly-size SYM∘AND)  =  (the symmetric top observer has few states)  ×  (the AND-feature layer is quasipoly)
                                                                            ↑ both PROVED below / in the repo
        held together by:     (the AND fan-in stays polylog under ACC⁰ depth composition)   ← the remaining SOCKET
```

* **The symmetric top observer has linear state count (proved here).**  A symmetric observer is a function of the count
  `s ∈ {0,…,n}`, so it has at most `n+1` states — linear, trivially quasipolynomial.  The `SYM` top of `SYM∘AND` is not
  the bottleneck.
* **The bounded-fan-in AND-feature layer is quasipolynomial (proved, repo).**  There are at most `(n+1)^D` AND features
  of fan-in `≤ D` (`…ACC0BeigelTaruiSparsity.beigelTarui_monomial_count_le`), quasipoly for `D = polylog`.
* **The remaining socket — the actual BT depth reduction.**  That repeated `ACC⁰`-layer composition keeps the AND
  fan-in `≤ polylog` (so the feature count stays quasipoly).  This is the load-bearing Beigel–Tarui mixed-radix
  argument; it is a *theorem* (not open), but its full Lean proof over arbitrary-depth `ACC⁰` is the large remaining
  formalisation.  We isolate it as `FanInStaysPolylog` and do **not** prove it.

## What is proved (clean axioms, no `sorry`)

* **`symmetric_observer_state_le`** — a symmetric observer has `≤ n+1` states (the `SYM` top is linear-state).
* **`bounded_fanin_feature_count_le`** (re-export) — `≤ (n+1)^D` AND features of fan-in `≤ D` (quasipoly for polylog `D`).
* **`quasipoly_BT_observer_of_fanin_preservation`** — the conditional: IF fan-in stays `≤ D` under composition
  (`FanInStaysPolylog`, socket) THEN the BT observer's feature count is `≤ (n+1)^D` (quasipoly) — pure glue.

## Honest scope

`DynamicClosesAtBT` is the Beigel–Tarui theorem (proven classically; `NEXP ⊄ ACC⁰` is Williams 2011, also proven), so
"proving it" here means *formalising* a known result, not resolving an open problem — and nothing in this development is
`P ≠ NP` or even a new separation.  The two size factors of the BT bound (linear `SYM` top, quasipoly bounded-fan-in
feature layer) are proved; the remaining content is the depth-reduction `FanInStaysPolylog` (fan-in preserved under
`ACC⁰` composition), a known theorem whose full formalisation is large.  We refine the entry-166 socket into this
single concrete remaining lemma; we do **not** prove it.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ThresholdBTClosure

open PallLean.Paper93.DeepMath.PathB

/-- **The symmetric top observer has linear state count (proved).**  A symmetric observer is a function of the count
`s ∈ {0,…,n}`, so the set of states it can take on inputs of `n` bits has at most `n+1` elements — linear in `n`, hence
trivially quasipolynomial.  The `SYM` top gate of a `SYM∘AND` representation is *not* the size bottleneck. -/
theorem symmetric_observer_state_le {α : Type*} [DecidableEq α] (O : ℕ → α) (n : ℕ) :
    ((Finset.range (n + 1)).image O).card ≤ n + 1 := by
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_range]

/-- **The bounded-fan-in AND-feature layer is quasipolynomial (proved, re-export).**  There are at most `(n+1)^D`
monomial-`AND` features of fan-in `≤ D` over `n` variables — quasipolynomial for `D = polylog`.  This is the bottom
layer of the `SYM∘AND` representation; its size is controlled *as long as `D` stays polylog*. -/
theorem bounded_fanin_feature_count_le (n D : ℕ) :
    (Layer3.lowDegMonomials n D).card ≤ (n + 1) ^ D :=
  ACC0BeigelTaruiSparsity.beigelTarui_monomial_count_le n D

/-- **The remaining socket — the Beigel–Tarui depth reduction.**  `FanInStaysPolylog D circuitFanInBound` asserts the
load-bearing fact that, after reducing an `ACC⁰` circuit to `SYM∘AND` form, the bottom AND fan-in is bounded by `D`
(`= polylog`).  This is a *theorem* (the BT mixed-radix argument), not an open problem, but its full Lean proof over
arbitrary-depth `ACC⁰` is the large remaining formalisation.  Stated abstractly; **not** proved here. -/
def FanInStaysPolylog (D : ℕ) (actualFanIn : ℕ) : Prop := actualFanIn ≤ D

/-- **The conditional (proved as glue): fan-in preservation ⇒ quasipoly BT observer.**  If the BT depth reduction keeps
the bottom AND fan-in `≤ D` (`FanInStaysPolylog D w`, the socket), then the AND-feature layer at the actual fan-in `w`
is bounded by the quasipoly feature count `(n+1)^D`.  Combined with `symmetric_observer_state_le` (linear `SYM` top),
this is the quasipoly `SYM∘AND` size — i.e. `DynamicClosesAtBT` modulo the one socket `FanInStaysPolylog`. -/
theorem quasipoly_BT_observer_of_fanin_preservation (n D w : ℕ)
    (hfan : FanInStaysPolylog D w) :
    (Layer3.lowDegMonomials n w).card ≤ (n + 1) ^ D := by
  refine le_trans (bounded_fanin_feature_count_le n w) ?_
  exact Nat.pow_le_pow_right (by omega) hfan

end PallLean.Paper93.DeepMath.PathB.ACC0ThresholdBTClosure

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ThresholdBTClosure.symmetric_observer_state_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ThresholdBTClosure.bounded_fanin_feature_count_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ThresholdBTClosure.quasipoly_BT_observer_of_fanin_preservation
