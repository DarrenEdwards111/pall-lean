import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCDepth3Switch
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingDepthReduction

/-!
# The cross-model bridge: why switching does not cross the `MOD` layer

The switching depth reduction (`…Depth3SwitchingDepthReduction`) collapses a width-`w` **DNF** to depth `≤ 2` on a
`1 - (4pw/(1-p))^s` fraction of restrictions — by fixing only `~s` of the `n` coordinates and leaving the rest
*free*.  `ACCDepth3Switch.switch_step` is the deterministic atom of the sibling **`MOD` model**: a `MOD` gate's
clause drops from a CNF-of-`MOD` *only when the gate is forced*, which (by locality, `modGate_eval_eq_of_agreeOn`)
requires its **entire support fixed** (`hfix : ∀ i ∈ G.support, ∃ b, ρ i = some b`).

This file builds the bridge between the two — and the bridge is a **no-go**, exactly the Razborov–Smolensky vs.
switching boundary: the switching mechanism (few coordinates fixed, support coordinates left free) **cannot** supply
`switch_step`'s precondition for `MOD` gates, because the `MOD` statistic is *fully live* on any free support
coordinate.

The algebraic core: flipping one support coordinate changes the `MOD` statistic `modQStatOn S q` by `±1`, which is
nonzero in `ZMod q` for `q ≥ 2`.  Hence:

* the statistic is non-constant on **any** restriction cube leaving a support coordinate free
  (`mod_statistic_live_on_free_cube`); and
* for parity (`q = 2`) the **gate value itself** flips, so the gate is non-constant on that cube
  (`mod_gate_parity_nonconstant`) — so it is neither forced true nor false, and `switch_step` cannot fire.

Contrast: a width-`w` DNF depth-collapses with only `~s` coordinates fixed (`depth_collapse_mass_ge`); a `MOD` gate
of support `s` stays live until *all* `s` coordinates are fixed.  That gap is precisely why the switching argument
reduces `AC⁰` depth but provably does **not** reduce `MOD`/`ACC⁰` depth.

## What is proved (clean axioms, no `sorry`)

* `weightOn_update_add`, `modQStatOn_update` — flipping a support coordinate shifts the statistic by `±1`.
* `modQStatOn_flip_ne` — **full sensitivity of the `MOD` statistic** (`q ≥ 2`): a support‑coordinate flip always
  changes `modQStatOn S q`.
* `mod_statistic_live_on_free_cube` — the statistic is non‑constant on any cube leaving a support coordinate free.
* `mod_gate_parity_nonconstant` — **the no‑go**: a parity gate (`modulus = 2`) is non‑constant on any cube leaving a
  support coordinate free, so `switch_step`'s "forced gate" precondition fails there.

## Honest scope

This is the *negative* half of the cross‑model question, and it is the correct mathematical answer: the bridge does
**not** compose into a switching‑driven `ACC⁰` depth reduction — that would contradict the known hardness of `ACC⁰`
lower bounds.  What it formalises is *why*: the `MOD` statistic's full sensitivity blocks the switching mechanism.
Genuine `ACC⁰` lower bounds need a *different* tool on the `MOD` layer (polynomial approximation / Razborov–Smolensky,
the Williams algorithmic method), not switching.  Proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACCSwitchingModBridge

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACCRestrictionTree

variable {n : ℕ}

/-! ## Flipping a support coordinate shifts the statistic by `±1` -/

/-- **The support count under a single‑coordinate update (proved).**  For `i ∈ S`, updating coordinate `i` to `b`
moves the count by the difference of the two indicators (stated additively to avoid `ℕ` subtraction). -/
theorem weightOn_update_add (S : Finset (Fin n)) (x : Fin n → Bool) {i : Fin n} (hi : i ∈ S) (b : Bool) :
    weightOn S (Function.update x i b) + (if x i then 1 else 0)
      = weightOn S x + (if b then 1 else 0) := by
  unfold weightOn
  have herase : ∑ j ∈ S.erase i, (if Function.update x i b j then (1 : ℕ) else 0)
              = ∑ j ∈ S.erase i, (if x j then (1 : ℕ) else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [← Finset.sum_erase_add S _ hi,
      ← Finset.sum_erase_add S (fun j => if x j then (1 : ℕ) else 0) hi,
      Function.update_self, herase]
  ring

/-- **The statistic under a single‑coordinate update (proved), in `ZMod q`.** -/
theorem modQStatOn_update (S : Finset (Fin n)) (q : ℕ) (x : Fin n → Bool) {i : Fin n} (hi : i ∈ S)
    (b : Bool) :
    modQStatOn S q (Function.update x i b) + (if x i then (1 : ZMod q) else 0)
      = modQStatOn S q x + (if b then (1 : ZMod q) else 0) := by
  unfold modQStatOn
  have h := congrArg (fun m : ℕ => (m : ZMod q)) (weightOn_update_add S x hi b)
  push_cast at h
  exact h

/-- **Full sensitivity of the `MOD` statistic (proved, `q ≥ 2`): a support‑coordinate flip always changes it.** -/
theorem modQStatOn_flip_ne {q : ℕ} (hq : 2 ≤ q) (S : Finset (Fin n)) (x : Fin n → Bool) {i : Fin n}
    (hi : i ∈ S) :
    modQStatOn S q (Function.update x i (!(x i))) ≠ modQStatOn S q x := by
  haveI : Fact (1 < q) := ⟨hq⟩
  intro hcontra
  have key := modQStatOn_update S q x hi (!(x i))
  rw [hcontra] at key
  have hif : (if x i then (1 : ZMod q) else 0) = (if !(x i) then (1 : ZMod q) else 0) :=
    add_left_cancel key
  cases hxi : x i with
  | true => simp [hxi] at hif
  | false => simp [hxi] at hif

/-! ## The no-go: a `MOD` gate stays live on any free support coordinate -/

/-- **The statistic is non‑constant on a cube leaving a support coordinate free (proved, `q ≥ 2`).**  Whenever
`ρ i = none` for `i ∈ S`, two `ρ`‑agreeing inputs differ in `modQStatOn S q`. -/
theorem mod_statistic_live_on_free_cube {q : ℕ} (hq : 2 ≤ q) (S : Finset (Fin n)) (ρ : Restriction n)
    {i : Fin n} (hisupp : i ∈ S) (hfree : ρ i = none) :
    ∃ x y, Agrees ρ x ∧ Agrees ρ y ∧ modQStatOn S q x ≠ modQStatOn S q y := by
  set x : Fin n → Bool := fun j => (ρ j).getD false with hx
  refine ⟨x, Function.update x i (!(x i)), ?_, ?_, ?_⟩
  · intro j b hjb
    simp [hx, hjb]
  · intro j b hjb
    have hji : j ≠ i := by
      rintro rfl
      rw [hfree] at hjb
      simp at hjb
    rw [Function.update_of_ne hji]
    simp [hx, hjb]
  · exact (modQStatOn_flip_ne hq S x hisupp).symm

/-- **The cross‑model no‑go (proved): a parity gate is non‑constant on any cube leaving a support coordinate free.**
For `G.modulus = 2`, if `ρ i = none` for `i ∈ G.support`, there are two `ρ`‑agreeing inputs with different gate
values.  So `G` is neither forced true nor false on the `ρ`‑cube — `switch_step`'s precondition (a forced gate)
genuinely requires the **full support** fixed, which the switching depth reduction (leaving coordinates free) cannot
supply.  This is why switching does not reduce `MOD`/`ACC⁰` depth. -/
theorem mod_gate_parity_nonconstant (G : ModGate n) (hq : G.modulus = 2) (ρ : Restriction n)
    {i : Fin n} (hisupp : i ∈ G.support) (hfree : ρ i = none) :
    ∃ x y, Agrees ρ x ∧ Agrees ρ y ∧ G.eval x ≠ G.eval y := by
  obtain ⟨m, S, t⟩ := G
  dsimp only at hq hisupp
  subst hq
  set x : Fin n → Bool := fun j => (ρ j).getD false with hx
  refine ⟨x, Function.update x i (!(x i)), ?_, ?_, ?_⟩
  · intro j b hjb
    simp [hx, hjb]
  · intro j b hjb
    have hji : j ≠ i := by
      rintro rfl
      rw [hfree] at hjb
      simp at hjb
    rw [Function.update_of_ne hji]
    simp [hx, hjb]
  · unfold ModGate.eval
    have hne : modQStatOn S 2 (Function.update x i (!(x i))) ≠ modQStatOn S 2 x :=
      modQStatOn_flip_ne (le_refl 2) S x hisupp
    have hdec : ∀ a b c : ZMod 2, a ≠ b → (decide (a = c) ≠ decide (b = c)) := by decide
    exact hdec _ _ t hne.symm

end PallLean.Paper93.DeepMath.PathB.ACCSwitchingModBridge

#print axioms PallLean.Paper93.DeepMath.PathB.ACCSwitchingModBridge.modQStatOn_flip_ne
#print axioms PallLean.Paper93.DeepMath.PathB.ACCSwitchingModBridge.mod_statistic_live_on_free_cube
#print axioms PallLean.Paper93.DeepMath.PathB.ACCSwitchingModBridge.mod_gate_parity_nonconstant
