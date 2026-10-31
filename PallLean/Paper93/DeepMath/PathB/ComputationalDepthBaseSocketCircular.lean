import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW10

/-!
# The base-hardness socket is equivalent to the separation (no non-circular salvage)

The stress-test showed KRW composition cannot amplify the ratio `ρ = dmdepth / log₂ arity`
(`comp_ratio_preserved`), so the depth tower beats NC¹ *only* if the base already has unbounded `ρ`.
The natural next question — can the base-hardness be obtained non-circularly? — is answered here in
the sharpest form: **the base socket is literally equivalent to `P ⊄ NC¹`.**  It is not a weaker
assumption one could hope to discharge by other means; it *is* the conclusion.

* **`UnboundedRatioFamily L`** — `L`'s power-of-two slices have unbounded `ρ`: for every `r` some
  length `2^k` has `dmdepth(langSlice L (2^k)) > r·(k+1)` (i.e. `> r·log₂ arity`).  This is exactly
  an "explicit super-NC¹ base" (an `hsq`-style gadget realised in `P`).
* **`unboundedRatio_iff_not_powNC1` (proved)** — `UnboundedRatioFamily L ↔ ¬ PowNC1 L` (just the de
  Morgan dual of the NC¹-ratio bound).
* **`base_ratio_socket_iff_krw_separation` (proved)** — chaining with the tight KRW socket
  (`krw_socket_iff_separation`): an explicit in-`P` unbounded-`ρ` base exists **iff** the KRW
  separation socket is filled, i.e. **iff `P ⊄ NC¹`**.

**Verdict.**  There is no non-circular salvage *within the general-depth composition framework*: the
base socket is provably equivalent to the separation, and (`comp_ratio_preserved`) composition adds
no amplification, so the hardness must be put in at the base — and an explicit super-`ρ` base *is*
the open problem.  (Where a non-circular route genuinely exists — MONOTONE depth, via query-to-
communication lifting — the amplification survives and explicit `ω(log)` monotone-depth functions
are known unconditionally; but the general KW game's universal-relation obstruction, which KRW is
designed to overcome, blocks that transfer.  That gap is not formalised here.)  Nothing is `P ≠ NP`,
and nothing closes or refutes KRW.
-/

namespace PallLean.Paper93.DeepMath.PathB.BaseSocketCircular

open PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-- `L`'s power-of-two slices have **unbounded ratio** `ρ = dmdepth / log₂ arity`: no constant `r`
bounds `dmdepth(langSlice L (2^k))` by `r·(k+1)`.  Equivalently, `L` is an explicit super-NC¹ base. -/
def UnboundedRatioFamily (L : List Bool → Bool) : Prop :=
  ∀ r, ∃ k, r * (k + 1) < dmdepth (langSlice L (2 ^ k))

/-- **Unbounded ratio is exactly non-membership in (power-of-two) NC¹-depth (proved).** -/
theorem unboundedRatio_iff_not_powNC1 (L : List Bool → Bool) :
    UnboundedRatioFamily L ↔ ¬ PowNC1 L := by
  simp only [UnboundedRatioFamily, PowNC1, not_exists, not_forall, not_le]

/-- **An explicit in-`P` unbounded-ratio base exists iff `¬ PowNC1` holds in `P` (proved).** -/
theorem base_ratio_socket_iff_powNC1 :
    (∃ L, ComposableMachine.InP L ∧ UnboundedRatioFamily L)
      ↔ (∃ L, ComposableMachine.InP L ∧ ¬ PowNC1 L) := by
  simp only [unboundedRatio_iff_not_powNC1]

/-- **THE CIRCULARITY, as a theorem (proved).**  An explicit in-`P` base with unbounded ratio
(`hsq`-style super-NC¹ gadget realised in `P`) exists **iff** the KRW separation socket is filled —
i.e. iff `P ⊄ NC¹`.  So the base-hardness socket is not a weaker hypothesis than the goal; it is
equivalent to it.  No non-circular salvage exists in this framework. -/
theorem base_ratio_socket_iff_krw_separation :
    (∃ L, ComposableMachine.InP L ∧ UnboundedRatioFamily L)
      ↔ (∃ (F : (k : ℕ) → (Fin (2 ^ k) → Bool) → Bool) (L : List Bool → Bool),
            ComposableMachine.InP L ∧ Realizes L F ∧ ¬ DepthLogBounded F) :=
  base_ratio_socket_iff_powNC1.trans krw_socket_iff_separation.symm

end PallLean.Paper93.DeepMath.PathB.BaseSocketCircular

#print axioms PallLean.Paper93.DeepMath.PathB.BaseSocketCircular.unboundedRatio_iff_not_powNC1
#print axioms PallLean.Paper93.DeepMath.PathB.BaseSocketCircular.base_ratio_socket_iff_krw_separation
