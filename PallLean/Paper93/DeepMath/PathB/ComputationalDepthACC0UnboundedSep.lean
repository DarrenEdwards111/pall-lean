import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UnboundedAC0
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0StrictSep
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModqUniform

/-!
# Bridge (AC⁰ ⊊ AC⁰[2], real model) — strict separation in unbounded fan-in (proved)

The strict class separation `AC⁰ ⊊ AC⁰[2]` in the genuine (unbounded-fan-in) `BoolCircuitSyntax` model.  `PARITY` is computed
by a single `MOD_2` gate over all inputs — concretely `toBoolSyntax (mod 2 univ 1)` — which is a depth-`1` `AC⁰[2]`
(`IsAC0pSyntax 2`) circuit (`parity_mem_acc02_unbounded`).  Yet every `AC⁰` (`MOD`-free) circuit computing `PARITY` needs
super-polynomial size (`parity_superpoly_ac0`).  Hence `AC⁰ ⊊ AC⁰[2]` in the real model.

## What is proved (clean axioms, no `sorry`)

* **`parity_mem_acc02_unbounded`** (PROVED) — `PARITY ∈ AC⁰[2]` at depth `1` (a single unbounded-fan-in `MOD_2` gate).
* **`ac0_strict_subset_acc02_unbounded`** (PROVED) — `PARITY` is a depth-`1` `AC⁰[2]` circuit, but any depth-`d` `AC⁰`
  circuit computing it has `3^t < 4·#{subcircuits}` (super-polynomial) — witnessing `AC⁰ ⊊ AC⁰[2]`.

## Honest scope

The strict separation `AC⁰ ⊊ AC⁰[2]` in the real unbounded-fan-in model (reusing the `toBoolSyntax` translation lemmas for
the `AC⁰[2]` witness and `parity_superpoly_ac0` for the `AC⁰` size bound).  The **Williams cash-out** (`NEXP ⊄ ACC⁰`) is a
different, P≠NP-strength theorem and remains **open** / not faked.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UnboundedSep

open PallLean.Paper93.DeepMath.PathB.ACC0ParityBarrier (parityFn)
open PallLean.Paper93.DeepMath.PathB.ACC0ToBoolSyntax (toBoolSyntax toBoolSyntax_eval toBoolSyntax_isAC0p)
open PallLean.Paper93.DeepMath.PathB.ACC0StrictSep (eval_mod2_univ)
open PallLean.Paper93.DeepMath.PathB.ACC0ModqUniform (tbs_depth_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UnboundedAC0 (parity_superpoly_ac0)
open PallLean.Paper93.DeepMath.PathB.Layer3 (subcircuits)

/-- **`PARITY ∈ AC⁰[2]` at depth `1` in the real model (PROVED).**  A single unbounded-fan-in `MOD_2` gate over all inputs
(the translation of `mod 2 univ 1`) computes `PARITY`. -/
theorem parity_mem_acc02_unbounded {n : ℕ} :
    ∃ Cir : BoolCircuitSyntax n, BoolCircuitSyntax.IsAC0pSyntax 2 Cir ∧ Cir.depth ≤ 1
      ∧ Cir.eval = parityFn := by
  refine ⟨toBoolSyntax (.mod 2 Finset.univ 1), toBoolSyntax_isAC0p 2 _ rfl, ?_, ?_⟩
  · simp [tbs_depth_eq, ACC0CircuitModel.depth]
  · funext x
    rw [toBoolSyntax_eval 2 (.mod 2 Finset.univ 1) x rfl]
    exact congrFun eval_mod2_univ x

private theorem two_ne_zero_mod3 : (2 : ZMod 3) ≠ 0 := by decide

open Classical in
/-- **`AC⁰ ⊊ AC⁰[2]` in the real (unbounded-fan-in) model (PROVED).**  `PARITY` is a depth-`1` `AC⁰[2]` circuit, but every
depth-`d` `AC⁰` circuit computing it has `3^t < 4·(subcircuits).toFinset.card` (super-polynomial size). -/
theorem ac0_strict_subset_acc02_unbounded {m d t : ℕ} (ht1 : 1 ≤ t)
    (hm : 8 * ((2 * t) ^ d) ^ 2 ≤ m) :
    (∃ Cir : BoolCircuitSyntax (2 * m + 1), BoolCircuitSyntax.IsAC0pSyntax 2 Cir ∧ Cir.depth ≤ 1
        ∧ Cir.eval = parityFn) ∧
      (∀ Cir : BoolCircuitSyntax (2 * m + 1), BoolCircuitSyntax.IsAC0Syntax Cir → Cir.depth ≤ d →
        Cir.eval = parityFn → 3 ^ t < 4 * (subcircuits Cir).toFinset.card) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine ⟨parity_mem_acc02_unbounded, ?_⟩
  intro Cir hac hd heval
  exact parity_superpoly_ac0 3 two_ne_zero_mod3 Cir hac hd t ht1
    (fun x => by rw [heval]; rfl) (by simpa using hm)

/-!
**`AC⁰ ⊊ AC⁰[2]` in the real model, proved.**  A single unbounded-fan-in `MOD_2` gate computes `PARITY`, but no
polynomial-size `AC⁰` circuit does.  Remaining (open, not faked): the Williams cash-out to `NEXP ⊄ ACC⁰`.  Not
`NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UnboundedSep

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UnboundedSep.ac0_strict_subset_acc02_unbounded
