import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTreeExtraction

/-!
# The SAT slack transfer: `6 ≤ cbudget (SATFamily 22)` through the gadget

Step 2 of the slack program: the above-floor bound on `AllEqual₃` lands on the
exact codec family.  Two mirrored gate-maps do the work:

* **mask** (`maskGate`/`computes_mask`/`cbudget_mask_le`) — pin any set of
  coordinates to constants in one map: `cbudget (f ∘ override) ≤ cbudget f`;
* **retraction** (`retractGate`/`computes_retract`/`cbudget_retract_le`) — re-index
  a circuit whose function factors through a coordinate injection:
  `cbudget (h ∘ lift) ≤ cbudget h` across input arities.

Pinning the 19 non-sign bits of the three-clause word and retracting the three
sign positions `9, 15, 21` onto `Fin 3` turns any circuit for `SATFamily 22` into
one for `AllEqual₃` (`SAT_embeds_allEq3` + a definitional word computation), so:

* **`slack_SATFamily_22` (proved)**: `6 ≤ cbudget (SATFamily 22)`.

## Honest scope

This is a constant above the three-sign cone floor, transferred by a mechanism —
not a route-to-superpolynomial by itself.  The decisive open questions (recorded):
does the slack **compose** across many disjoint gadgets (`+1` per gadget → `2n +
Ω(n)`?), and can any composition recur past every polynomial?  If composition
stalls at `O(n)`, that is a barrier to record, not a rung to iterate.  Nothing
here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit

/-! ### The mask: pin many coordinates in one gate-map -/

/-- Override the masked coordinates with their pinned constants. -/
def overrideFn {n : ℕ} (m : Fin n → Option Bool) (x : Fin n → Bool) : Fin n → Bool :=
  fun k => (m k).getD (x k)

/-- Pin the masked variables at the gate level. -/
def maskGate {n : ℕ} (m : Fin n → Option Bool) : CGate n → CGate n
  | .var j => match m j with | some b => .cst b | none => .var j
  | .cst b => .cst b
  | .un op j => .un op j
  | .bin op j k => .bin op j k

theorem evalGate_mask {n : ℕ} (m : Fin n → Option Bool) (x : Fin n → Bool)
    (vals : List Bool) (g : CGate n) :
    evalGate x vals (maskGate m g) = evalGate (overrideFn m x) vals g := by
  cases g with
  | var j =>
    show evalGate x vals (match m j with | some b => CGate.cst b | none => CGate.var j)
      = (m j).getD (x j)
    cases hm : m j with
    | some b => rfl
    | none => rfl
  | cst b => rfl
  | un op j => rfl
  | bin op j k => rfl

theorem runFrom_mask {n : ℕ} (m : Fin n → Option Bool) (x : Fin n → Bool) :
    ∀ (gs : List (CGate n)) (vals : List Bool),
      runFrom x vals (gs.map (maskGate m)) = runFrom (overrideFn m x) vals gs := by
  intro gs
  induction gs with
  | nil => intro vals; rfl
  | cons g rest ih =>
    intro vals
    show runFrom x (vals ++ [evalGate x vals (maskGate m g)]) (rest.map (maskGate m))
      = runFrom (overrideFn m x) (vals ++ [evalGate (overrideFn m x) vals g]) rest
    rw [evalGate_mask m x vals g]
    exact ih _

theorem computes_mask {n : ℕ} (c : List (CGate n)) (f : (Fin n → Bool) → Bool)
    (m : Fin n → Option Bool) (hcomp : computes c f) :
    computes (c.map (maskGate m)) (fun x => f (overrideFn m x)) := by
  intro x
  show (runFrom x [] (c.map (maskGate m))).getD ((c.map (maskGate m)).length - 1) false
    = f (overrideFn m x)
  rw [runFrom_mask m x c [], List.length_map]
  exact hcomp (overrideFn m x)

theorem cbudget_mask_le {n : ℕ} (m : Fin n → Option Bool) (f : (Fin n → Bool) → Bool) :
    cbudget (fun x => f (overrideFn m x)) ≤ cbudget f := by
  obtain ⟨c, hcomp, hlen⟩ := Nat.sInf_mem (cbudget_set_nonempty f)
  have hlen' : c.length = cbudget f := hlen
  have hb : cbudget (fun x => f (overrideFn m x)) ≤ (c.map (maskGate m)).length :=
    Nat.sInf_le ⟨c.map (maskGate m), computes_mask c f m hcomp, rfl⟩
  rw [List.length_map] at hb
  omega

/-! ### The retraction: re-index a pullback circuit across arities -/

/-- Lift a small input along a coordinate correspondence. -/
def liftFn {m : ℕ} (n : ℕ) (ρ : ℕ → Option (Fin m)) (x : Fin m → Bool) : Fin n → Bool :=
  fun j => match ρ j.val with | some i => x i | none => false

/-- Re-index a gate along the correspondence. -/
def retractGate {m : ℕ} (ρ : ℕ → Option (Fin m)) : CGate n → CGate m
  | .var j => match ρ j.val with | some i => .var i | none => .cst false
  | .cst b => .cst b
  | .un op j => .un op j
  | .bin op j k => .bin op j k

theorem evalGate_retract {n m : ℕ} (ρ : ℕ → Option (Fin m)) (x : Fin m → Bool)
    (vals : List Bool) (g : CGate n) :
    evalGate x vals (retractGate ρ g) = evalGate (liftFn n ρ x) vals g := by
  cases g with
  | var j =>
    show evalGate x vals (match ρ j.val with | some i => CGate.var i | none => CGate.cst false)
      = (match ρ j.val with | some i => x i | none => false)
    cases hm : ρ j.val with
    | some i => rfl
    | none => rfl
  | cst b => rfl
  | un op j => rfl
  | bin op j k => rfl

theorem runFrom_retract {n m : ℕ} (ρ : ℕ → Option (Fin m)) (x : Fin m → Bool) :
    ∀ (gs : List (CGate n)) (vals : List Bool),
      runFrom x vals (gs.map (retractGate ρ)) = runFrom (liftFn n ρ x) vals gs := by
  intro gs
  induction gs with
  | nil => intro vals; rfl
  | cons g rest ih =>
    intro vals
    show runFrom x (vals ++ [evalGate x vals (retractGate ρ g)]) (rest.map (retractGate ρ))
      = runFrom (liftFn n ρ x) (vals ++ [evalGate (liftFn n ρ x) vals g]) rest
    rw [evalGate_retract ρ x vals g]
    exact ih _

theorem computes_retract {n m : ℕ} (c : List (CGate n)) (h : (Fin n → Bool) → Bool)
    (ρ : ℕ → Option (Fin m)) (hcomp : computes c h) :
    computes (c.map (retractGate ρ)) (fun x => h (liftFn n ρ x)) := by
  intro x
  show (runFrom x [] (c.map (retractGate ρ))).getD
      ((c.map (retractGate ρ)).length - 1) false = h (liftFn n ρ x)
  rw [runFrom_retract ρ x c [], List.length_map]
  exact hcomp (liftFn n ρ x)

theorem cbudget_retract_le {n m : ℕ} (ρ : ℕ → Option (Fin m))
    (h : (Fin n → Bool) → Bool) :
    cbudget (fun x : Fin m → Bool => h (liftFn n ρ x)) ≤ cbudget h := by
  obtain ⟨c, hcomp, hlen⟩ := Nat.sInf_mem (cbudget_set_nonempty h)
  have hlen' : c.length = cbudget h := hlen
  have hb : cbudget (fun x : Fin m → Bool => h (liftFn n ρ x))
      ≤ (c.map (retractGate ρ)).length :=
    Nat.sInf_le ⟨c.map (retractGate ρ), computes_retract c h ρ hcomp, rfl⟩
  rw [List.length_map] at hb
  omega

/-! ### The concrete gadget wiring -/

/-- The three-clause base word as a literal list. -/
def sBase : List Bool :=
  [true, true, true, false,
   true, false, false, false, false, true,
   true, false, false, false, false, true,
   true, false, false, false, false, true]

/-- Pin every coordinate of the three-clause word except the three sign bits. -/
def sMask : Fin 22 → Option Bool := fun k =>
  if k.val = 9 ∨ k.val = 15 ∨ k.val = 21 then none
  else some (sBase.getD k.val false)

/-- The sign positions onto `Fin 3`. -/
def sRho : ℕ → Option (Fin 3) := fun j =>
  if j = 9 then some 0 else if j = 15 then some 1 else if j = 21 then some 2 else none

theorem encodeVar'_zero : encodeVar' 0 = [false, false, false] := by
  have h := encodeVar'_cellVar 0 0
  rw [show PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex.cellVar 0 0 = 0 from rfl] at h
  rw [h]
  rfl

theorem se_concrete (a b c : Bool) : encodeFormula' (se a b c)
    = [true, true, true, false,
       true, false, false, false, false, a,
       true, false, false, false, false, b,
       true, false, false, false, false, c] := by
  show encodeNat 3 ++ (List.map encodeClause' (se a b c)).flatten = _
  simp only [se, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    encodeClause', encodeLit', List.append_nil, encodeVar'_zero]
  rfl

/-- The pulled-back pinned family is exactly `AllEqual₃`. -/
theorem pull_eq : (fun x : Fin 3 → Bool =>
    (fun y : Fin 22 → Bool => SATFamily 22 (overrideFn sMask y)) (liftFn 22 sRho x))
    = allEq3Fin := by
  funext x
  show SATFamily 22 (overrideFn sMask (liftFn 22 sRho x)) = allEq3Fin x
  rw [SATFamily_apply]
  have hword : wordOfFin (overrideFn sMask (liftFn 22 sRho x))
      = encodeFormula' (se (x 0) (x 1) (x 2)) := by
    rw [se_concrete]
    apply List.ext_getElem
    · rw [wordOfFin_length]
      rfl
    · intro k h1 h2
      have hk22 : k < 22 := by
        rw [wordOfFin_length] at h1
        omega
      rw [wordOfFin_getElem _ k h1 hk22]
      interval_cases k <;> rfl
  rw [hword]
  exact SAT_embeds_allEq3 (x 0) (x 1) (x 2)

/-- **THE SLACK TRANSFER (proved)**: the above-floor bound lands on the exact codec
family. -/
theorem slack_SATFamily_22 : 6 ≤ cbudget (SATFamily 22) := by
  have h1 := cbudget_retract_le (n := 22) (m := 3) sRho
    (fun y : Fin 22 → Bool => SATFamily 22 (overrideFn sMask y))
  rw [pull_eq] at h1
  have h2 := cbudget_mask_le sMask (SATFamily 22)
  have h0 := cbudget_allEq3Fin
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_mask_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_retract_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.slack_SATFamily_22
