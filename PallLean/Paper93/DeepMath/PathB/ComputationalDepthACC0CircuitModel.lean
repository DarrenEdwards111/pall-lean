import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCSwitchingPipeline

/-!
# An ACC⁰ circuit model, and the support‑extraction bridge

The correlation/switching machinery was built over abstract *support families* `supports : Fin k → Finset (Fin n)`.
This file attaches it to an actual named circuit class: an `ACC0Circuit` (AND / OR / NOT / `MOD q` gates, with
`depth` and `size`), and proves the **support‑extraction bridge** for the depth‑2 `MOD`‑bottom fragment — the part
the proved machinery handles.

The bridge: a depth‑2 circuit whose bottom layer is `MOD q_j` gates over supports `S_j` has its output a function
of the bottom statistics, i.e. `eval x = g (weightVec supports x)` for an explicit `g` (`eval_factors`).  So the
proved `predictor_fails_of_survivors` applies verbatim: after a low‑survivor restriction, the circuit cannot
correlate with the holonomy parity.

## What is proved (clean axioms, no `sorry`)

* `ACC0Circuit`, `eval`, `depth`, `size` — the target class (`MOD`‑augmented constant‑depth circuits).
* `ModGate`, `Depth2ModCircuit` — the depth‑2 `MOD`‑bottom fragment and its `supports` family.
* `eval_factors` — **support extraction**: the circuit's output factors through its bottom `MOD` statistics
  (`= g (weightVec supports x)`).
* `depth2_circuit_fails_of_survivors` — **the bridge**: a depth‑2 `MOD`‑bottom circuit fails to correlate with the
  holonomy parity after any restriction whose surviving‑support count is below `log₂` of its live count.

## Honest scope

This names the ACC⁰ target class and attaches the machinery to its depth‑2 `MOD`‑bottom fragment with *bounded
overlap* (the regime the switching pipeline controls).  The general inductive `ACC0Circuit` (arbitrary depth,
AND/OR/NOT over `MOD` gates) is *defined* but only the depth‑2 `MOD`‑bottom fragment is *bridged*; lifting to
deeper circuits needs the depth‑reduction switching (random restrictions collapsing AND/OR layers), and lifting
past bounded overlap is the higher‑moment Håstad wall — the remaining `NP ⊄ ACC⁰` frontier.  So the machine now
speaks about real circuits, with the wall at exactly: **unbounded support reuse / high‑overlap depth‑reduction**.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel

open PallLean.Paper93.DeepMath.PathB.HolonomyBalanceFragments
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline

variable {n k : ℕ}

/-! ## The ACC⁰ target class -/

/-- An ACC⁰ circuit: AND / OR / NOT over inputs and `MOD q` gates (a `MOD q` gate over support `S` with target `t`
accepts when `∑_{i∈S} x_i ≡ t (mod q)`). -/
inductive ACC0Circuit (n : ℕ) where
  | const : Bool → ACC0Circuit n
  | var : Fin n → ACC0Circuit n
  | not : ACC0Circuit n → ACC0Circuit n
  | and : ACC0Circuit n → ACC0Circuit n → ACC0Circuit n
  | or : ACC0Circuit n → ACC0Circuit n → ACC0Circuit n
  | mod : (q : ℕ) → Finset (Fin n) → ZMod q → ACC0Circuit n

/-- The Boolean value of a circuit on an input. -/
def eval : ACC0Circuit n → (Fin n → Bool) → Bool
  | .const b, _ => b
  | .var i, x => x i
  | .not c, x => !(eval c x)
  | .and a b, x => eval a x && eval b x
  | .or a b, x => eval a x || eval b x
  | .mod q S t, x => decide (modQStatOn S q x = t)

/-- Circuit depth. -/
def depth : ACC0Circuit n → ℕ
  | .const _ => 0
  | .var _ => 0
  | .not c => 1 + depth c
  | .and a b => 1 + max (depth a) (depth b)
  | .or a b => 1 + max (depth a) (depth b)
  | .mod _ _ _ => 1

/-- Circuit size (gate count). -/
def size : ACC0Circuit n → ℕ
  | .const _ => 1
  | .var _ => 1
  | .not c => 1 + size c
  | .and a b => 1 + size a + size b
  | .or a b => 1 + size a + size b
  | .mod _ _ _ => 1

/-! ## The depth‑2 `MOD`‑bottom fragment, and support extraction -/

/-- A bottom‑layer `MOD q` gate over a support, with an acceptance target. -/
structure ModGate (n : ℕ) where
  modulus : ℕ
  support : Finset (Fin n)
  target : ZMod modulus

/-- A `MOD` gate accepts when its support‑count hits the target residue. -/
def ModGate.eval (G : ModGate n) (x : Fin n → Bool) : Bool :=
  decide (modQStatOn G.support G.modulus x = G.target)

/-- A depth‑2 circuit: an arbitrary top function of `k` bottom `MOD` gates. -/
structure Depth2ModCircuit (n k : ℕ) where
  gates : Fin k → ModGate n
  top : (Fin k → Bool) → Bool

/-- The circuit's value: the top function applied to the bottom `MOD` gate outputs. -/
def Depth2ModCircuit.eval (C : Depth2ModCircuit n k) (x : Fin n → Bool) : Bool :=
  C.top (fun j => (C.gates j).eval x)

/-- The **support family** extracted from the bottom `MOD` gates. -/
def Depth2ModCircuit.supports (C : Depth2ModCircuit n k) : Fin k → Finset (Fin n) :=
  fun j => (C.gates j).support

/-- **Support extraction (proved): a depth‑2 `MOD`‑bottom circuit factors through its bottom statistics.**  Its
value is `g (weightVec supports x)` for the explicit top‑of‑mod‑thresholds function `g`. -/
theorem eval_factors (C : Depth2ModCircuit n k) :
    ∃ g : (Fin k → ℕ) → Bool, ∀ x, C.eval x = g (weightVec C.supports x) :=
  ⟨fun w => C.top (fun j => decide (((w j : ℕ) : ZMod (C.gates j).modulus) = (C.gates j).target)),
    fun _ => rfl⟩

/-! ## The bridge to the proved machinery -/

/-- **The bridge (proved): a depth‑2 `MOD`‑bottom circuit fails to correlate with the holonomy parity after a
low‑survivor restriction.**  Support extraction reduces the circuit to a `weightVec` predictor, and
`predictor_fails_of_survivors` (the pigeonhole cell bridge) applies: whenever the restriction's surviving‑support
count is below `log₂` of its live count, there is a holonomy support `D` the circuit cannot correlate with. -/
theorem depth2_circuit_fails_of_survivors (C : Depth2ModCircuit n k) (L : Finset (Fin n))
    (h : 2 ^ survivingCount C.supports L < L.card) :
    ∃ D : Finset (Fin n), ∃ v w, v ≠ w ∧
      2 * (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
            (fun x => C.eval x = fParity D x)).card
        ≤ ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).card := by
  obtain ⟨g, hg⟩ := eval_factors C
  obtain ⟨D, v, w, hvw, hb⟩ := predictor_fails_of_survivors C.supports L g h
  refine ⟨D, v, w, hvw, ?_⟩
  simp only [hg]
  exact hb

end PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel.eval_factors
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel.depth2_circuit_fails_of_survivors
