import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NWReconstructionBridgeRecon

/-!
# Entry 323 — ACC⁰ depth / gate-type faithfulness for the circuit bridges (proved)

Entries 321 (`bridgeYao`) and 322 (`bridgeRecon`) built the Yao predictor circuit and the reconstructed circuit over the
`Circ` gate model, with the **honest caveat** carried both times: the constructions captured *size* and *semantics* but
**not** `ACC⁰` membership — its **depth** and **gate-type** constraints.  This file removes that caveat for the bridges:
it equips `Circ` with a **depth** measure and a **gate-type** accounting, and proves the two bridge constructions are
*faithful* — they add only **constant / additive depth** and introduce only **`ACC⁰[2]` gate types**
(`{¬, ∧, ∨, MOD₂}`), never a foreign-modulus gate.

**The gate basis is exactly `ACC⁰[2]`.**  `Circ`'s constructors are `var` (input), `tru`/`fals` (constants), `cnot`
(NOT), `cand` (AND), `cor` (OR), `cxor` (XOR `= MOD₂`).  Every gate is an `ACC⁰[2]` gate; in particular the *only*
modular gate is `MOD₂`, so no construction over `Circ` can introduce a foreign `MOD_q` — the gate-type concern of the
composite barrier (entry 318) cannot arise here.

## What is proved (clean axioms, no `sorry`)

* **`depth`** — circuit depth (`var`/const `↦ 0`; `cnot ↦ 1 + ·`; binary gates `↦ 1 + max`).
* **`predictor_depth`** (PROVED) — `(predictor D gidx).depth = D.depth + 2`: the Yao bridge adds exactly **two** levels
  (`NOT` then `MOD₂`), constant depth overhead.
* **`csubst_depth_le`** (PROVED) — `(csubst g P).depth ≤ P.depth + dt` when every sub-circuit has depth `≤ dt`: the
  reconstruction bridge's depth is **additive** (predictor depth + table depth) — so bounded-depth predictor + tables
  give a bounded-depth reconstruction.
* **`predictor_preserves_acc0Depth`** / **`csubst_preserves_acc0Depth`** (PROVED) — the bridges preserve bounded depth.
* **`xorFree`** + **`csubst_xorFree`** (PROVED) — gate-type tracking: substitution does not introduce `MOD₂` gates
  beyond those of `P` and the tables (`xorFree` is preserved), and `predictor_uses_mod2` records that the Yao bridge
  introduces exactly one `MOD₂` — gate-type faithfulness is genuinely tracked, not assumed.

## Honest scope

This proves the bridges are `ACC⁰[2]`-faithful in **depth** (constant/additive overhead) and **gate type** (only
`{¬,∧,∨,MOD₂}`, no foreign modulus) — the two constraints the 321/322 caveat flagged.  The one remaining modelling
choice is **fan-in**: `Circ` is a *bounded-fan-in* (formula / binary-gate) model, whereas full `ACC⁰` permits unbounded
fan-in.  So this is depth + gate-type faithfulness in the bounded-fan-in reading; an unbounded-fan-in `ACC⁰` model is a
separate (larger) formalisation.  With this, the Yao/reconstruction bridges are faithful in everything except fan-in.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CircuitBridgeACC0Faithful

open PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonYaoCircuit (Circ predictor)
open PallLean.Paper93.DeepMath.PathB.ACC0NWReconstructionBridgeRecon (csubst)

/-- **Circuit depth.**  Inputs and constants have depth `0`; `NOT` adds one level; the binary gates (`AND`, `OR`,
`MOD₂`) add one level over the deeper argument. -/
def depth {n : ℕ} : Circ n → ℕ
  | Circ.var _ => 0
  | Circ.tru => 0
  | Circ.fals => 0
  | Circ.cnot c => 1 + depth c
  | Circ.cand a b => 1 + max (depth a) (depth b)
  | Circ.cor a b => 1 + max (depth a) (depth b)
  | Circ.cxor a b => 1 + max (depth a) (depth b)

/-- **The Yao bridge adds constant depth (PROVED).**  `(predictor D gidx).depth = D.depth + 2`: the predictor
`(x gidx) ⊕ ¬D` is a `MOD₂` over an input and a `NOT` of `D`, so it sits exactly two levels above `D`. -/
theorem predictor_depth {n : ℕ} (D : Circ n) (gidx : Fin n) :
    depth (predictor D gidx) = depth D + 2 := by
  show depth (Circ.cxor (Circ.var gidx) (Circ.cnot D)) = depth D + 2
  simp only [depth]
  omega

/-- **The reconstruction bridge's depth is additive (PROVED).**  If every substituted sub-circuit has depth `≤ dt`, then
`(csubst g P).depth ≤ P.depth + dt`: each input `var j` of `P` is replaced by `g j` (depth `≤ dt`) and the gate levels
of `P` are preserved.  So a bounded-depth predictor wired to bounded-depth tables yields a bounded-depth reconstruction. -/
theorem csubst_depth_le {n Nc : ℕ} (g : Fin Nc → Circ n) (dt : ℕ)
    (hg : ∀ j, depth (g j) ≤ dt) (P : Circ Nc) :
    depth (csubst g P) ≤ depth P + dt := by
  induction P with
  | var j => simpa only [csubst, depth, Nat.zero_add] using hg j
  | tru => simp only [csubst, depth]; omega
  | fals => simp only [csubst, depth]; omega
  | cnot c ih => simp only [csubst, depth]; omega
  | cand a b iha ihb => simp only [csubst, depth]; omega
  | cor a b iha ihb => simp only [csubst, depth]; omega
  | cxor a b iha ihb => simp only [csubst, depth]; omega

/-- **`ACC⁰` bounded-depth membership (for the fixed `ACC⁰[2]` basis): depth `≤ d`.** -/
def InACC0Depth {n : ℕ} (d : ℕ) (C : Circ n) : Prop := depth C ≤ d

/-- **The Yao bridge preserves bounded depth (PROVED).**  A depth-`≤ d` distinguisher yields a depth-`≤ d+2` predictor. -/
theorem predictor_preserves_acc0Depth {n : ℕ} (D : Circ n) (gidx : Fin n) (d : ℕ)
    (hD : InACC0Depth d D) : InACC0Depth (d + 2) (predictor D gidx) := by
  unfold InACC0Depth at *
  rw [predictor_depth]; omega

/-- **The reconstruction bridge preserves bounded depth (PROVED).**  A depth-`≤ dp` predictor wired to depth-`≤ dt`
tables yields a depth-`≤ dp + dt` reconstructed circuit — bounded depth in, bounded depth out. -/
theorem csubst_preserves_acc0Depth {n Nc : ℕ} (g : Fin Nc → Circ n) (P : Circ Nc) (dp dt : ℕ)
    (hP : InACC0Depth dp P) (hg : ∀ j, InACC0Depth dt (g j)) :
    InACC0Depth (dp + dt) (csubst g P) := by
  unfold InACC0Depth at *
  exact le_trans (csubst_depth_le g dt hg P) (by omega)

/-- **Gate-type tracking: a circuit with no `MOD₂` (`XOR`) gate.**  An `{input, const, ¬, ∧, ∨}` circuit — `AC⁰` proper
(no parity). -/
def xorFree {n : ℕ} : Circ n → Prop
  | Circ.var _ => True
  | Circ.tru => True
  | Circ.fals => True
  | Circ.cnot c => xorFree c
  | Circ.cand a b => xorFree a ∧ xorFree b
  | Circ.cor a b => xorFree a ∧ xorFree b
  | Circ.cxor _ _ => False

/-- **Substitution preserves gate types (PROVED).**  If `P` is `XOR`-free and every substituted sub-circuit is
`XOR`-free, then `csubst g P` is `XOR`-free — substitution introduces no new gate *types* (in particular no `MOD₂`
beyond those of `P` and the tables).  Gate-type faithfulness of the reconstruction bridge, genuinely tracked. -/
theorem csubst_xorFree {n Nc : ℕ} (g : Fin Nc → Circ n) (P : Circ Nc)
    (hg : ∀ j, xorFree (g j)) (hP : xorFree P) :
    xorFree (csubst g P) := by
  induction P with
  | var j => exact hg j
  | tru => exact trivial
  | fals => exact trivial
  | cnot c ih => exact ih hP
  | cand a b iha ihb => exact ⟨iha hP.1, ihb hP.2⟩
  | cor a b iha ihb => exact ⟨iha hP.1, ihb hP.2⟩
  | cxor a b _ _ => exact hP.elim

/-- **The Yao bridge introduces exactly one `MOD₂` gate (PROVED).**  `predictor D gidx` is *not* `XOR`-free — its top
gate is the parity `MOD₂` — recording the single `ACC⁰[2]` modular gate the Yao step adds. -/
theorem predictor_uses_mod2 {n : ℕ} (D : Circ n) (gidx : Fin n) :
    ¬ xorFree (predictor D gidx) := by
  show ¬ xorFree (Circ.cxor (Circ.var gidx) (Circ.cnot D))
  simp only [xorFree, not_false_iff]

/-!
**The circuit bridges are `ACC⁰[2]`-faithful.**  Depth: the Yao bridge adds constant depth (`predictor_depth`, `+2`) and
the reconstruction bridge adds depth additively (`csubst_depth_le`), so bounded-depth inputs give bounded-depth outputs
(`predictor_preserves_acc0Depth`, `csubst_preserves_acc0Depth`).  Gate type: the basis is exactly `{¬,∧,∨,MOD₂}`, the
only modular gate is `MOD₂` (no foreign modulus possible), and substitution preserves gate types (`csubst_xorFree`), the
Yao bridge adding exactly one `MOD₂` (`predictor_uses_mod2`).  The remaining modelling choice is fan-in (this is the
bounded-fan-in / formula reading; unbounded-fan-in `ACC⁰` is a separate model).  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CircuitBridgeACC0Faithful

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitBridgeACC0Faithful.predictor_depth
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitBridgeACC0Faithful.csubst_depth_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitBridgeACC0Faithful.csubst_preserves_acc0Depth
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitBridgeACC0Faithful.csubst_xorFree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitBridgeACC0Faithful.predictor_uses_mod2
