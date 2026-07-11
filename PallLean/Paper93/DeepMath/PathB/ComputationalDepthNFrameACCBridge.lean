import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# N-Frame → ACC⁰ bridge: an audit, not a lower bound

The proposed route to an ACC⁰ lower bound through the N-Frame boundary / dynamic-SPDP path is:

```text
small ACC⁰ circuit
  → faithful positive N-Frame compilation
  → polynomially bounded causal dynamic-SPDP complexity     (the ACC upper bound)
  → hard function has super-polynomial dynamic-SPDP         (the intrinsic lower bound)
  → contradiction.
```

This file builds the **honest scaffolding** for that programme and localises the one missing bridge.  It
defines real `ACCCircuit`s (unbounded fan-in AND/OR/NOT and MOD_m), a faithful-compilation interface, the
gate-by-gate complexity recurrences, and proves the **cash-out is mechanical**.  It proves **no** lower bound.

## What is proved

* `eval` / `gateCount` / `depth` — a concrete ACC⁰ circuit model with semantics.
* `PositiveDynamicSPDPCompilation` — the faithful-compilation interface, with `faithful` (semantic
  preservation) as a **field**; `trivialCompilation` inhabits it — and, being cost `= gateCount`, shows the
  interface alone is the representation countermodel again (it must be strengthened to a *causal* cost with a
  hard lower bound; the interface does not force that).
* `acc_bridge_cashout` — **the cash-out theorem**: `ACC_upper + hard_lower + monotone gap ⟹ f ∉ ACC⁰`, proved
  mechanically.
* `additive_le_gateCount` — **the AC⁰-gate composition theorem**: any dynamic-SPDP obeying *additive* gate
  recurrences (AND/OR/NOT/MOD each cost `≤ Σ children + 1`) is bounded by `gateCount`.  So the AND/OR/NOT layer
  composes with no blow-up.

## What is NOT proved — the isolated crux

The additive recurrence covers the MOD gate *by fiat*.  The actual rank-based dynamic-SPDP of a MOD_m gate is
**not** additive: for a single prime `p` the Razborov–Smolensky low-degree method controls it (`AC⁰[p]`), but
for **composite / mixed moduli** no bounded recurrence is known.  `MODRecurrence` names this obligation; whether
it holds for composite `m` with a *causal* compilation is exactly the open theorem `small ACC ⇒ low causal
positive dynamic-SPDP`.  Until it is proved, "boundary"/"amplituhedron" are geometric motivation, not a
separation.

## Honest scope

An interface + a mechanical cash-out + the AC⁰-gate composition.  Every hard hypothesis (`ACC_upper` for the
real rank measure, the intrinsic `hard_lower` for an explicit `f`, and the composite-MOD recurrence) is an
explicit, undischarged obligation.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACCBridge

/-! ## A concrete ACC⁰ circuit model -/

/-- An ACC⁰ circuit over `n` inputs: constant-depth, unbounded fan-in AND/OR, NOT, and MOD_m gates.  A MOD_m
gate fires iff the number of `true` inputs is divisible by `m`. -/
inductive ACCCircuit (n : Nat) where
  | input : Fin n → ACCCircuit n
  | const : Bool → ACCCircuit n
  | not : ACCCircuit n → ACCCircuit n
  | and : List (ACCCircuit n) → ACCCircuit n
  | or : List (ACCCircuit n) → ACCCircuit n
  | mod : Nat → List (ACCCircuit n) → ACCCircuit n

namespace ACCCircuit

/-- Semantics of an ACC⁰ circuit.  The valuation `x` is taken first so that the fan-in gates recurse through
the recognised `List.map (eval x)` pattern (structural recursion over the nested inductive). -/
def eval {n : Nat} (x : Fin n → Bool) : ACCCircuit n → Bool
  | .input i => x i
  | .const b => b
  | .not c => !(eval x c)
  | .and l => (l.map (eval x)).all id
  | .or l => (l.map (eval x)).any id
  | .mod m l => decide (((l.map (eval x)).filter id).length % m = 0)

/-- Total number of gates (the circuit size `s`). -/
def gateCount {n : Nat} : ACCCircuit n → Nat
  | .input _ => 1
  | .const _ => 1
  | .not c => gateCount c + 1
  | .and l => (l.map gateCount).sum + 1
  | .or l => (l.map gateCount).sum + 1
  | .mod _ l => (l.map gateCount).sum + 1

/-- Circuit depth `d`. -/
def depth {n : Nat} : ACCCircuit n → Nat
  | .input _ => 0
  | .const _ => 0
  | .not c => depth c + 1
  | .and l => (l.map depth).foldr max 0 + 1
  | .or l => (l.map depth).foldr max 0 + 1
  | .mod _ l => (l.map depth).foldr max 0 + 1

end ACCCircuit

open ACCCircuit

/-- `C` computes `f`. -/
def ComputedBy {n : Nat} (C : ACCCircuit n) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, eval x C = f x

/-- `f` is in (size, depth)-bounded ACC⁰. -/
def InACC {n : Nat} (sizeBound depthBound : Nat) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ C : ACCCircuit n, ComputedBy C f ∧ gateCount C ≤ sizeBound ∧ depth C ≤ depthBound

/-! ## The faithful-compilation interface -/

/-- A **faithful positive dynamic-SPDP compilation** of an ACC⁰ circuit: a positive geometric/SPDP object whose
evaluation reproduces the circuit (`faithful` = semantic preservation, a field), together with its causal
dynamic-SPDP `cost`.  The intended constraint — that `cost` is *causally derived from the circuit's gates and
wires*, with no appended sheet — is **not** expressible at this level, which is exactly why the interface alone
is insufficient (see `trivialCompilation`). -/
structure PositiveDynamicSPDPCompilation (n : Nat) where
  source : ACCCircuit n
  Obj : Type
  objEval : Obj → (Fin n → Bool) → Bool
  compiled : Obj
  faithful : ∀ x, objEval compiled x = eval x source
  cost : Nat

/-- The trivial faithful compilation: the object *is* the circuit.  It is genuinely semantic-preserving, but its
cost is just `gateCount` — a circular, non-lower-bounding measure.  So the interface admits the representation
countermodel; the content is entirely in supplying a *causal* cost that is *also* hard for the target. -/
def trivialCompilation {n : Nat} (C : ACCCircuit n) : PositiveDynamicSPDPCompilation n where
  source := C
  Obj := ACCCircuit n
  objEval := fun c x => eval x c
  compiled := C
  faithful := fun _ => rfl
  cost := gateCount C

theorem trivialCompilation_faithful {n : Nat} (C : ACCCircuit n) (x : Fin n → Bool) :
    (trivialCompilation C).objEval (trivialCompilation C).compiled x = eval x C := rfl

/-! ## The cash-out theorem (mechanical) -/

/-- **The cash-out.**  A causal dynamic-SPDP `R` that is (upper) bounded by a monotone `B` of the circuit size
on *every* circuit, and (lower) bounded below `L` on *every* circuit computing `f`, separates `f` from
`(sizeBound, depthBound)`-ACC⁰ as soon as `B sizeBound ≤ L`.  This is the `ACC_upper + hard_lower ⇒ f ∉ ACC`
step, proved mechanically. -/
theorem acc_bridge_cashout {n : Nat} (R : ACCCircuit n → Nat) (f : (Fin n → Bool) → Bool)
    (B : Nat → Nat) (L sizeBound depthBound : Nat) (hmono : Monotone B)
    (hUp : ∀ C : ACCCircuit n, R C ≤ B (gateCount C))
    (hLow : ∀ C : ACCCircuit n, ComputedBy C f → L < R C)
    (hgap : B sizeBound ≤ L) :
    ¬ InACC sizeBound depthBound f := by
  rintro ⟨C, hCf, hsz, _⟩
  have h1 := hUp C
  have h2 := hLow C hCf
  have h3 : B (gateCount C) ≤ B sizeBound := hmono hsz
  omega

/-! ## Gate-by-gate complexity recurrences -/

/-- The **additive gate recurrences**: every gate costs at most the sum of its children's costs plus one.  This
is what AND/OR/NOT genuinely satisfy for reasonable causal measures; it covers the MOD gate *by fiat* (the last
conjunct) — the load-bearing assumption whose truth for composite moduli is open. -/
def GateAdditive {n : Nat} (R : ACCCircuit n → Nat) : Prop :=
  (∀ i, R (.input i) ≤ 1) ∧
  (∀ b, R (.const b) ≤ 1) ∧
  (∀ c, R (.not c) ≤ R c + 1) ∧
  (∀ l, R (.and l) ≤ (l.map R).sum + 1) ∧
  (∀ l, R (.or l) ≤ (l.map R).sum + 1) ∧
  (∀ m l, R (.mod m l) ≤ (l.map R).sum + 1)

/-- Helper: a pointwise cost bound lifts to a sum bound over a list of subcircuits. -/
theorem map_sum_le {n : Nat} {R : ACCCircuit n → Nat} (l : List (ACCCircuit n))
    (h : ∀ c ∈ l, R c ≤ gateCount c) : (l.map R).sum ≤ (l.map gateCount).sum := by
  induction l with
  | nil => simp
  | cons a t iht =>
    simp only [List.map_cons, List.sum_cons]
    have ha : R a ≤ gateCount a := h a (by simp)
    have ht : (t.map R).sum ≤ (t.map gateCount).sum := iht (fun c hc => h c (by simp [hc]))
    omega

/-- **AC⁰-gate composition.**  Any dynamic-SPDP obeying the additive gate recurrences is bounded by the gate
count — the AND/OR/NOT layer composes with no rank blow-up.  (The MOD gate is included only because the additive
recurrence assumes it; see `MODRecurrence`.) -/
theorem additive_le_gateCount {n : Nat} (R : ACCCircuit n → Nat) (h : GateAdditive R) :
    ∀ C : ACCCircuit n, R C ≤ gateCount C
  | .input i => by simpa [gateCount] using h.1 i
  | .const b => by simpa [gateCount] using h.2.1 b
  | .not c => by
      have ih := additive_le_gateCount R h c
      have := h.2.2.1 c
      simp only [gateCount]; omega
  | .and l => by
      have ih : ∀ c ∈ l, R c ≤ gateCount c := fun c _ => additive_le_gateCount R h c
      have hsum := map_sum_le l ih
      have := h.2.2.2.1 l
      simp only [gateCount]; omega
  | .or l => by
      have ih : ∀ c ∈ l, R c ≤ gateCount c := fun c _ => additive_le_gateCount R h c
      have hsum := map_sum_le l ih
      have := h.2.2.2.2.1 l
      simp only [gateCount]; omega
  | .mod m l => by
      have ih : ∀ c ∈ l, R c ≤ gateCount c := fun c _ => additive_le_gateCount R h c
      have hsum := map_sum_le l ih
      have := h.2.2.2.2.2 m l
      simp only [gateCount]; omega
  termination_by C => sizeOf C
  decreasing_by
    all_goals simp_wf
    all_goals (first | omega | (rename_i hc; have := List.sizeOf_lt_of_mem hc; omega))

/-- **The additive route to a separation.**  If a *causal* dynamic-SPDP `R` obeys the additive gate recurrences
(so `R ≤ gateCount`) and is intrinsically hard for `f` (`R C > L` for every circuit computing `f`, with
`sizeBound ≤ L`), then `f ∉ ACC⁰`.  Both remaining hypotheses are undischarged: the additive MOD recurrence for
composite moduli, and the intrinsic hardness for an explicit `f`. -/
theorem acc_bridge_from_additive {n : Nat} (R : ACCCircuit n → Nat) (f : (Fin n → Bool) → Bool)
    (L sizeBound depthBound : Nat) (hadd : GateAdditive R)
    (hLow : ∀ C : ACCCircuit n, ComputedBy C f → L < R C) (hgap : sizeBound ≤ L) :
    ¬ InACC sizeBound depthBound f :=
  acc_bridge_cashout R f id L sizeBound depthBound monotone_id
    (fun C => additive_le_gateCount R hadd C) hLow hgap

/-! ## The MOD-gate crux -/

/-- The **MOD-gate recurrence obligation**: the actual (rank-based, causal) dynamic-SPDP of a MOD_m gate,
bounded by a function of the modulus and the children's total cost.  The additive form is `bound m s = s + 1`
(independent of `m`); a genuine rank measure has a bound depending on the *arithmetic structure* of `m`. -/
def MODRecurrence {n : Nat} (R : ACCCircuit n → Nat) (bound : Nat → Nat → Nat) : Prop :=
  ∀ (m : Nat) (l : List (ACCCircuit n)), R (.mod m l) ≤ bound m ((l.map R).sum)

/-- Under the additive recurrences, the MOD gate obeys the *modulus-independent linear* bound `s + 1`.  This is
precisely the assumption the audit flags as unproven for the real rank measure at composite `m`: for a single
prime it is (Razborov–Smolensky) controllable; for composite / mixed moduli no such bound is known, and this is
where the N-Frame route stops at `AC⁰[p]` unless a bounded composite-MOD recurrence with a causal compilation is
proved. -/
theorem additive_gives_linear_MOD {n : Nat} (R : ACCCircuit n → Nat) (h : GateAdditive R) :
    MODRecurrence R (fun _ s => s + 1) :=
  fun m l => h.2.2.2.2.2 m l

end PallLean.Paper93.DeepMath.PathB.NFrameACCBridge

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACCBridge.acc_bridge_cashout
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACCBridge.additive_le_gateCount
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACCBridge.acc_bridge_from_additive
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACCBridge.additive_gives_linear_MOD
