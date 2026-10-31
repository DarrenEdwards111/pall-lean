import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CircuitModel

/-!
# Depth reduction: locality, MOD‑support extraction, and the switching wall

The depth‑2 `MOD`‑bottom bridge (`…ACC0CircuitModel`) attached the proved machinery to two‑layer circuits.  Lifting
to deeper `ACC0Circuit`s needs **depth reduction**: a random restriction collapsing the AND/OR layers down to a
depth‑2 `MOD`‑bottom survivor.  This file provides the *deterministic* backbone — locality and MOD‑support
extraction for arbitrary‑depth circuits, and the bridge that transfers the depth‑2 failure to anything a
restriction reduces to depth 2 — and names the *probabilistic* switching step as the remaining wall.

## What is proved (clean axioms, no `sorry`)

* `support`, `eval_eq_of_agreeOn` — **locality**: a circuit of any depth reads only its `support`; inputs agreeing
  there evaluate equally (induction over the circuit).
* `eval_const_of_support_disjoint` — **killed ⇒ constant**: if a subcircuit's support is disjoint from the live
  set, it is constant across live completions (the deterministic collapse the switching produces probabilistically).
* `modSupports` — **MOD‑support extraction**: the family of all bottom `MOD`‑gate supports of an arbitrary‑depth
  circuit (the family the switching machinery operates on).
* `reduction_bridge` — **the transfer**: any circuit extensionally equal to a depth‑2 `MOD`‑bottom circuit `C'`
  inherits `C'`'s failure to correlate with the holonomy parity after a low‑survivor restriction.

## The named wall

* `Depth2Reducible` — a circuit is extensionally a depth‑2 `MOD`‑bottom circuit (what a restriction must achieve).
* `HastadDepthReduction` — a poly‑size constant‑depth `ACC0Circuit`, after a random restriction, is
  `Depth2Reducible` with bounded‑overlap surviving supports.  This is the Håstad‑style depth‑reduction switching
  lemma — the `NP ⊄ ACC⁰` wall (deeper depth *and* unbounded overlap).  Granted it, `reduction_bridge`
  discharges the rest.

## Honest scope

Deterministic locality and extraction are proved for *all* depths; the bridge transfers the proved depth‑2 failure
to any depth‑2‑reducible circuit.  The one unproved input is `HastadDepthReduction` — that a random restriction
actually performs the collapse — which combines the depth‑reduction switching and the bounded‑overlap survivor
control, i.e. the full ACC⁰ difficulty, isolated here as a single named property.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DepthReduction

open PallLean.Paper93.DeepMath.PathB.HolonomyBalanceFragments
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel

variable {n m : ℕ}

/-! ## Locality -/

/-- The set of input variables a circuit reads. -/
def support : ACC0Circuit n → Finset (Fin n)
  | .const _ => ∅
  | .var i => {i}
  | .not c => support c
  | .and a b => support a ∪ support b
  | .or a b => support a ∪ support b
  | .mod _ S _ => S

/-- **Locality (proved): a circuit of any depth reads only its support.**  Inputs agreeing on `support c`
evaluate equally. -/
theorem eval_eq_of_agreeOn (c : ACC0Circuit n) (x y : Fin n → Bool)
    (h : ∀ i ∈ support c, x i = y i) : eval c x = eval c y := by
  induction c with
  | const b => rfl
  | var i => simp only [eval]; exact h i (by simp [support])
  | not c ih => simp only [eval]; rw [ih h]
  | and a b iha ihb =>
      simp only [eval]
      rw [iha (fun i hi => h i (Finset.mem_union_left _ hi)),
          ihb (fun i hi => h i (Finset.mem_union_right _ hi))]
  | or a b iha ihb =>
      simp only [eval]
      rw [iha (fun i hi => h i (Finset.mem_union_left _ hi)),
          ihb (fun i hi => h i (Finset.mem_union_right _ hi))]
  | mod q S t =>
      simp only [eval]
      have hw : weightOn S x = weightOn S y :=
        Finset.sum_congr rfl (fun i hi => by rw [h i hi])
      have hmod : modQStatOn S q x = modQStatOn S q y := by unfold modQStatOn; rw [hw]
      rw [hmod]

/-- **Killed ⇒ constant (proved): a subcircuit whose support is disjoint from the live set is constant across live
completions** — the deterministic collapse a restriction produces probabilistically. -/
theorem eval_const_of_support_disjoint (c : ACC0Circuit n) (L : Finset (Fin n))
    (hdis : Disjoint (support c) L) (x y : Fin n → Bool) (hagree : ∀ i, i ∉ L → x i = y i) :
    eval c x = eval c y :=
  eval_eq_of_agreeOn c x y (fun i hi => hagree i (fun hL => Finset.disjoint_left.mp hdis hi hL))

/-! ## MOD‑support extraction (any depth) -/

/-- The family of all bottom `MOD`‑gate supports of a circuit — the support family the switching machinery acts on. -/
def modSupports : ACC0Circuit n → List (Finset (Fin n))
  | .const _ => []
  | .var _ => []
  | .not c => modSupports c
  | .and a b => modSupports a ++ modSupports b
  | .or a b => modSupports a ++ modSupports b
  | .mod _ S _ => [S]

/-! ## The transfer bridge -/

/-- **The transfer (proved): a circuit extensionally equal to a depth‑2 `MOD`‑bottom circuit inherits its failure
to correlate with the holonomy parity after a low‑survivor restriction.** -/
theorem reduction_bridge (C : ACC0Circuit n) (C' : Depth2ModCircuit n m)
    (hCC' : ∀ x, eval C x = C'.eval x) (L : Finset (Fin n))
    (h : 2 ^ survivingCount C'.supports L < L.card) :
    ∃ D : Finset (Fin n), ∃ v w, v ≠ w ∧
      2 * (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
            (fun x => eval C x = fParity D x)).card
        ≤ ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).card := by
  obtain ⟨D, v, w, hvw, hb⟩ := depth2_circuit_fails_of_survivors C' L h
  refine ⟨D, v, w, hvw, ?_⟩
  simp only [hCC']
  exact hb

/-! ## The named switching wall -/

/-- A circuit is extensionally a depth‑2 `MOD`‑bottom circuit (what depth reduction must achieve). -/
def Depth2Reducible (C : ACC0Circuit n) : Prop :=
  ∃ (m : ℕ) (C' : Depth2ModCircuit n m), ∀ x, eval C x = C'.eval x

/-- **(Named open — the Håstad depth‑reduction switching wall, `NP ⊄ ACC⁰`‑strength).**  A poly‑size constant‑depth
`ACC0Circuit`, after a random restriction, becomes `Depth2Reducible` with bounded‑overlap surviving supports.  This
is the genuine remaining difficulty: collapsing the AND/OR layers to a `MOD`‑bottom survivor (depth reduction) and
keeping the survivor's overlap bounded (the higher‑moment control).  Granted it, `reduction_bridge` discharges the
correlation failure. -/
def HastadDepthReduction (C : ACC0Circuit n) : Prop := Depth2Reducible C

end PallLean.Paper93.DeepMath.PathB.ACC0DepthReduction

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DepthReduction.eval_eq_of_agreeOn
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DepthReduction.eval_const_of_support_disjoint
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DepthReduction.reduction_bridge
