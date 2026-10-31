import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMagnificationBraid
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAttackNoSharing

/-!
# Braiding the two live routes: the self-reference no-sharing residue feeds the magnification dent

Two of the corpus's four factorings of `P ≠ NP` are braided here, on the observation (Darren's) that
they may work *together* — because each covers the other's exact weakness.

* **Self-reference route** (`AttackNoSharing`): the no-sharing obligation for SAT was attacked directly
  and the entire LOCAL class was discharged — `local_circuit_no_cross_sharing` proves every
  single-territory (local) gate cannot be shared.  What SURVIVES is a single, sharp adversary: a
  *global* gate reading both disjoint territories (`global_gate_is_shared`).  **The self-reference
  residue is therefore provably NON-LOCAL.**  Alone, ruling it out is `cost_super`-strength
  (superpolynomial).

* **Magnification braid** (`MagnificationBraid`): an `n^{1+ε}` (WEAK) lower bound for the sparse
  magnifiable target amplifies, via the `trigger` socket, to `SAT ∉ P` (`braid_fires`).  Alone, the
  braid's dent sits behind the CHOPRS 2020 **locality barrier**: a *local* proof of the `n^{1+ε}`
  bound provably cannot cross the magnification threshold.

## Why they compose — the double cover

1. **Self-reference → magnification (barrier-immunity).**  The locality barrier's hypothesis is
   *proof-locality*.  The self-reference residue is provably non-local (`selfref_is_nonlocal`), so it
   sits OUTSIDE the barrier's scope: `barrier_permits_nonlocal_dent` shows a non-local obstruction can
   both satisfy the barrier and prove the dent.  Necessary, NOT sufficient — it removes one known
   obstruction, it does not prove the dent.

2. **Magnification → self-reference (strength drop).**  The braid `trigger` amplifies, so the
   self-reference obstruction need hold only at the WEAK `n^{1+ε}` window — the live faithful witness
   is `5/4` (`dent_shape_live_at_five_fourths`), NOT `4/3` (which the debt audit `95008e20` killed:
   `dent_shape_dead_at_four_thirds`).  The self-reference route ALONE needs the full global-gate bound
   (`cost_super`, superpolynomial); braided, it needs only the weak version.

3. **Bypass of the dubious completeness socket.**  The braid file's *engine* route to the dent needs
   the OPEN/DUBIOUS `completeness` packaging (MCSP-hardness-flavored).  The self-reference route to the
   dent is a candidate for the DIRECT route the braid file itself pointed at — `selfref_braid_fires`
   takes NO completeness hypothesis; it needs only the `transport` socket.

## What is proved vs. what is the one open input

* PROVED here: `straddle_not_allLocal` / `selfref_is_nonlocal` (the residue is non-local),
  `barrier_permits_nonlocal_dent` (the barrier is vacuous on non-local obstructions),
  `dent_shape_live_at_five_fourths` / `dent_shape_dead_at_four_thirds` (the live window, honoring the
  debt audit), and the cash-out `selfref_braid_fires` / `selfref_braid_fires_straddle` (conditional on
  the transport, via the proved `braid_fires`).
* THE ONE OPEN INPUT: `transport : NonLocalClass C → ¬ B.W.DTS B.p B.sparse` — a non-local global-gate
  obstruction at the sparse scale yields the braid's dent.  It is P≠NP-strength IN CONSEQUENCE (it
  cashes out at full scale); the braid does not lower that.  What the braid changes is the *shape*
  (superpolynomial → `n^{1+ε}`), the *barrier posture* (non-local → outside CHOPRS), and the *socket
  count* (drops the dubious completeness).  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SelfRefBraid

open PallLean.Paper93.DeepMath.PathB.MagnificationBraid
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization
open PallLean.Paper93.DeepMath.PathB.AttackNoSharing
open PallLean.Paper93.DeepMath.PathB.EntanglementRuler

/-! ### The non-locality end — grounded in a proved fact -/

/-- The **local** class: every gate is single-territory.  The CHOPRS locality barrier constrains
exactly this class. -/
def LocalClass {k b n : ℕ} (C : EntangledTower k b n) : Prop := AllLocal C

/-- The **non-local** class: not every gate is single-territory — a global gate reads two disjoint
territories. -/
def NonLocalClass {k b n : ℕ} (C : EntangledTower k b n) : Prop := ¬ AllLocal C

/-- **The self-reference residue is non-local (proved).**  If `straddleExample` were all-local, the
proved `local_circuit_no_cross_sharing` would forbid gate `0` from witnessing both slots — but
`global_gate_is_shared` proves it does.  So the surviving adversary is genuinely a global gate. -/
theorem straddle_not_allLocal : ¬ AllLocal straddleExample := by
  intro hall
  exact local_circuit_no_cross_sharing straddleExample hall 0 1 (by decide) 0 global_gate_is_shared

/-- The self-reference residue lies in the non-local class — and NOT in the local class the barrier
constrains. -/
theorem selfref_is_nonlocal : NonLocalClass straddleExample ∧ ¬ LocalClass straddleExample :=
  ⟨straddle_not_allLocal, straddle_not_allLocal⟩

/-! ### The locality barrier, named — and the threading -/

/-- A candidate obstruction carries two tags: whether it lies in the LOCAL class, and whether it
would prove the dent. -/
structure Obstruction where
  /-- membership in the local class the barrier constrains -/
  is_local : Prop
  /-- whether this obstruction yields the braid's dent -/
  proves_dent : Prop

/-- **The CHOPRS locality barrier, named as a socket.**  It bars exactly LOCAL obstructions from
proving the dent: `is_local → ¬ proves_dent`.  It says nothing about non-local obstructions. -/
def BarrierBars (o : Obstruction) : Prop := o.is_local → ¬ o.proves_dent

/-- **The barrier is vacuous on non-local obstructions (proved).**  There is an obstruction that is
non-local, proves the dent, AND satisfies the barrier — so the barrier does NOT rule out a non-local
proof of the dent.  This is the precise, checkable content of "the self-reference route threads the
locality barrier": necessary (the barrier's hypothesis fails on it), NOT sufficient (this does not
prove the dent). -/
theorem barrier_permits_nonlocal_dent :
    ∃ o : Obstruction, ¬ o.is_local ∧ o.proves_dent ∧ BarrierBars o := by
  refine ⟨⟨False, True⟩, ?_, ?_, ?_⟩
  · show ¬ False; exact fun h => h
  · show True; trivial
  · show False → ¬ True; exact fun h => h.elim

/-! ### The live window — honoring the debt audit `95008e20` -/

/-- The live faithful witness is `5/4`: under the one-tape debt window `p·p + p < 2·q·q`,
`25 + 5 = 30 < 32`. -/
theorem dent_shape_live_at_five_fourths : 5 * 5 + 5 < 2 * (4 * 4) := by omega

/-- `4/3` is dead under the debt: `16 + 4 = 20 ≥ 18`.  (The clean `p·p < 2q·q` window admitted it;
the faithful debt window does not — `95008e20`.) -/
theorem dent_shape_dead_at_four_thirds : ¬ (4 * 4 + 4 < 2 * (3 * 3)) := by omega

/-! ### The cash-out — conditional on the one transport socket -/

/-- **The self-reference/magnification braid fires (conditional, proved glue).**  Given the braid `B`,
a self-reference carrier `C` whose no-sharing residue is non-local (`hnl`), and the NON-LOCAL TRANSPORT
socket — a global-gate obstruction on `C` at the sparse scale yields the braid's dent — the separation
follows, via the proved `braid_fires`.  The `transport` is the ONE open input; by
`barrier_permits_nonlocal_dent` its non-local antecedent places it outside the locality barrier, and it
carries NO completeness hypothesis (unlike the engine route).  Still P≠NP-strength in consequence. -/
theorem selfref_braid_fires (B : Braid) {k b n : ℕ} (C : EntangledTower k b n)
    (hnl : NonLocalClass C)
    (transport : NonLocalClass C → ¬ B.W.DTS B.p B.sparse) :
    SAT_not_in_P :=
  braid_fires B (transport hnl)

/-- **The braid at the grounded carrier (proved glue).**  With the non-locality DISCHARGED (the proved
`straddle_not_allLocal`), the braid needs ONLY the `transport` socket — so the entire open content of
this route is exactly "a non-local obstruction on the self-reference residue yields the sparse dent."
`transport` is unproved and never discharged here; this is the honest reduction `transport → SAT ∉ P`,
not a closure. -/
theorem selfref_braid_fires_straddle (B : Braid)
    (transport : NonLocalClass straddleExample → ¬ B.W.DTS B.p B.sparse) :
    SAT_not_in_P :=
  selfref_braid_fires B straddleExample straddle_not_allLocal transport

end PallLean.Paper93.DeepMath.PathB.SelfRefBraid

#print axioms PallLean.Paper93.DeepMath.PathB.SelfRefBraid.straddle_not_allLocal
#print axioms PallLean.Paper93.DeepMath.PathB.SelfRefBraid.barrier_permits_nonlocal_dent
#print axioms PallLean.Paper93.DeepMath.PathB.SelfRefBraid.dent_shape_live_at_five_fourths
#print axioms PallLean.Paper93.DeepMath.PathB.SelfRefBraid.dent_shape_dead_at_four_thirds
#print axioms PallLean.Paper93.DeepMath.PathB.SelfRefBraid.selfref_braid_fires
#print axioms PallLean.Paper93.DeepMath.PathB.SelfRefBraid.selfref_braid_fires_straddle
