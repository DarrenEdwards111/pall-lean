import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementRuler

/-!
# Attacking NoSharing for SAT directly: every LOCAL sharer falls, the global gate survives

`NoSharing` — the two depth-`d` slots of the tower cannot be mass-produced with shared gates — is the
single obligation the injection reduced to.  Here we attack it for SAT *directly*: push against it as
hard as the mathematics allows, and report which sharers fall and which one survives.

The attack **succeeds against the entire class of local sharers**, and isolates one irreducible
adversary.

## The attack

The two slots own **disjoint private territories** (`priv_disjoint`), and each demands
private-nonlinearity on its own territory.  The core theorem is that **sharing forces a global gate**:

* **`shared_gate_depends_both`** — a gate that witnesses *both* slots must depend on a private
  variable of *each* — hence on two distinct variables in the two disjoint territories.  A shared gate
  is a **global** gate, reading both territories.  (Two applications of `witness_forces_reach` plus
  disjointness.)
* **`local_gate_not_shared`** — contrapositive: a **single-territory** gate (one that only reaches
  one slot's private variables) *cannot* be shared across the two slots.
* **`local_circuit_no_cross_sharing`** — so a circuit built from local gates has **NoSharing**: no
  gate serves two distinct slots.  The attack fully succeeds against local circuits.

## What survives

* **`global_gate_is_shared`** — the one surviving adversary: a *global* gate genuinely can be shared.
  In `straddleExample`, the single gate `0` witnesses *both* blocks.  Mass production lives exactly
  here — a gate that reads both disjoint territories.

So the direct attack on NoSharing kills every local sharer and leaves precisely the **global
two-territory gate** — which is the Uhlig straddler, and excluding it is **localization**.

## Honest scope — the attack chips out the whole local class; the core survivor is cost_super

Attacking NoSharing for SAT directly is real progress, not a stall: it **proves** NoSharing against
every single-territory (local) gate — the whole class is excluded, machine-checked.  The residue is a
single, sharp adversary: the global gate reading both slots' private territories.  Ruling *that* out
for SAT's minimal circuit is exactly `bounded reach` — **localization** — which the map already places
at lower-bound strength, `= cost_super`.  So the direct attack does not break NoSharing, but it does
not fail either: it reduces NoSharing to global-gate sharing precisely, killing everything local.  The
surviving core is the localization wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.AttackNoSharing

open PallLean.Paper93.DeepMath.PathB.EntanglementRuler

variable {k b n : ℕ}

/-- **Sharing forces a global gate (proved).**  A gate `g` that witnesses two distinct slots `i ≠ j`
must depend on a private variable of *each* — two distinct variables in the two disjoint territories.
Any shared gate is global: it reads both territories.  This is the direct attack's core. -/
theorem shared_gate_depends_both (C : EntangledTower k b n) (i j : Fin k) (hij : i ≠ j) (g : ℕ)
    (hi : g ∈ C.witness i) (hj : g ∈ C.witness j) :
    ∃ v w, C.privMask i v = true ∧ C.privMask j w = true ∧ v ≠ w ∧
      PallLean.Paper93.DeepMath.PathB.EntanglementRuler.DependsOn (C.wireFn g) v ∧
      PallLean.Paper93.DeepMath.PathB.EntanglementRuler.DependsOn (C.wireFn g) w := by
  obtain ⟨v, hv, hdv⟩ := witness_forces_reach C i g hi
  obtain ⟨w, hw, hdw⟩ := witness_forces_reach C j g hj
  refine ⟨v, w, hv, hw, ?_, hdv, hdw⟩
  intro hvw
  have hjfalse : C.privMask j v = false := C.priv_disjoint i j hij v hv
  rw [hvw, hw] at hjfalse
  exact Bool.noConfusion hjfalse

/-- A gate is **single-territory** if its private-variable dependencies all lie in one slot's
territory: whenever it depends on a private variable of block `i` and of block `j`, then `i = j`. -/
def SingleTerritory (C : EntangledTower k b n) (g : ℕ) : Prop :=
  ∀ i j v w, C.privMask i v = true → C.privMask j w = true →
    PallLean.Paper93.DeepMath.PathB.EntanglementRuler.DependsOn (C.wireFn g) v →
    PallLean.Paper93.DeepMath.PathB.EntanglementRuler.DependsOn (C.wireFn g) w → i = j

/-- **A local gate cannot be shared (proved).**  A single-territory gate cannot witness two distinct
slots: sharing would force it to depend on both territories, contradicting single-territory.  Every
local sharer falls. -/
theorem local_gate_not_shared (C : EntangledTower k b n) (g : ℕ) (hloc : SingleTerritory C g)
    (i j : Fin k) (hij : i ≠ j) : ¬ (g ∈ C.witness i ∧ g ∈ C.witness j) := by
  rintro ⟨hi, hj⟩
  obtain ⟨v, w, hv, hw, _, hdv, hdw⟩ := shared_gate_depends_both C i j hij g hi hj
  exact hij (hloc i j v w hv hw hdv hdw)

/-- Every gate is **local** (single-territory). -/
def AllLocal (C : EntangledTower k b n) : Prop := ∀ g, SingleTerritory C g

/-- **A local circuit has NoSharing (proved).**  If every gate is single-territory, no gate serves
two distinct slots — the two slots share nothing.  The attack fully succeeds against local circuits. -/
theorem local_circuit_no_cross_sharing (C : EntangledTower k b n) (hall : AllLocal C)
    (i j : Fin k) (hij : i ≠ j) (g : ℕ) : ¬ (g ∈ C.witness i ∧ g ∈ C.witness j) :=
  local_gate_not_shared C g (hall g) i j hij

/-- **The surviving adversary: a global gate CAN be shared (proved).**  In `straddleExample`, the
single gate `0` witnesses *both* blocks — a global gate reading both disjoint territories.  Mass
production lives exactly here; excluding it for SAT is localization. -/
theorem global_gate_is_shared :
    (0 : ℕ) ∈ straddleExample.witness 0 ∧ (0 : ℕ) ∈ straddleExample.witness 1 := by
  constructor <;> decide

end PallLean.Paper93.DeepMath.PathB.AttackNoSharing

#print axioms PallLean.Paper93.DeepMath.PathB.AttackNoSharing.shared_gate_depends_both
#print axioms PallLean.Paper93.DeepMath.PathB.AttackNoSharing.local_gate_not_shared
#print axioms PallLean.Paper93.DeepMath.PathB.AttackNoSharing.local_circuit_no_cross_sharing
#print axioms PallLean.Paper93.DeepMath.PathB.AttackNoSharing.global_gate_is_shared
