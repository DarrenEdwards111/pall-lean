import PallLean.Paper93.DeepMath.PathB.ComputationalDepthChargedHolographicMachine

/-!
# Observer-Class Semantics for P vs NP — on the NON-VACUOUS charged machine

**Correction.**  An earlier version of this file based `P` on a free `Machine` whose `init` was an arbitrary
function — that is VACUOUS (`init x := decide (L x)` decides any `L` in 0 steps, so every language is in P), exactly
the uncharged-init cheat.  This version bases `P` on the corpus's `ChargedMachine.InP`: `init` is **forced**
(`⟨start, 0, x⟩`, copies the input; no computation), and steps are a fixed finite `delta` table — so `InP` is a
genuine, uniform, non-vacuous P.

The observer-class framing, faithfully, on that model:

* `PLang := InP` — the P-observer: one fixed charged machine, poly clock.
* `NPObs` / `AcceptNP` — the one-sector NP-observer: a fixed `InP` verifier and poly witness bound; `x` is
  accepted iff **one** witness `w` (appended, `verify (x ++ w)`) verifies.  The full witness table is never read.
* `p_subset_np`, `accept_iff_nonempty`, `satIsNP` — P ⊆ NP; accepting = boundary nonempty; every verifier's
  boundary language is NP.
* `PolyCollapse` — the boundary admits polynomial deterministic collapse (deciding nonemptiness is in P), a
  predicate.
* `bridge` — `P = NP ⇔ every NP boundary admits polynomial deterministic collapse`.
* calibration — `fullBoundary_collapses`, `emptyBoundary_collapses`, `sameLang_sameCollapse`: boundary size and
  verifier representation are NOT the collapse cost.
* `sat_specialization` / `sat_separation` — **fenced, conditional on `SATComplete`** (Cook–Levin NP-hardness, a
  hypothesis, not built): `P = NP ⇔ PolyCollapse SATV` and `¬ PolyCollapse SATV ⇔ P ≠ NP`.  The *`SAT ∈ NP`* half
  is proved (`satIsNP`); the NP-hardness half is `SATComplete`, fenced.

`¬ PolyCollapse SATV` is the open separation statement.  SPDP/holography/rigidity are absent (proposed estimators
only).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics

open Classical
open PallLean.Paper93.DeepMath.PathB.ChargedHolographicMachine (ChargedMachine InP)
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-- The P-observer languages: the corpus's genuine (forced-init, local-step) uniform P. -/
def PLang (L : List Bool → Bool) : Prop := InP L

/-- `InP` respects pointwise equality of languages. -/
theorem PLang_congr {L L' : List Bool → Bool} (h : ∀ x, L x = L' x) (hL : PLang L) : PLang L' := by
  obtain ⟨M, hp, hd⟩ := hL
  exact ⟨M, hp, fun x => (hd x).trans (h x)⟩

/-- Every constant language is in P (a one-state charged machine, zero clock). -/
theorem PLang_const (b : Bool) : PLang (fun _ => b) := by
  refine ⟨{ Q := 1, start := ⟨0, by omega⟩, delta := fun _ _ => (⟨0, by omega⟩, false, 2),
            accept := fun _ => b, clock := fun _ => 0 }, ⟨0, 0, fun n => Nat.zero_le _⟩, fun x => ?_⟩
  rfl

/-! ## The one-sector NP-observer -/

/-- A fixed `InP` verifier with a poly witness bound. -/
structure NPObs where
  /-- Verify the appended string `input ++ witness`. -/
  verify : List Bool → Bool
  /-- Witness-length bound. -/
  wb : ℕ → ℕ
  /-- Poly witness bound. -/
  poly_wb : PolyBounded wb
  /-- The verifier is in P. -/
  ptime : PLang verify

/-- **One accepting observation**: one existentially-selected witness `w` verifies. -/
def AcceptNP (ob : NPObs) (x : List Bool) : Prop :=
  ∃ w, w.length ≤ ob.wb x.length ∧ ob.verify (x ++ w) = true

/-- The boundary of `x`: the accepting witnesses. -/
def Boundary (ob : NPObs) (x : List Bool) : Set (List Bool) :=
  {w | w.length ≤ ob.wb x.length ∧ ob.verify (x ++ w) = true}

/-- Accepting = the boundary is nonempty (exhibit one member). -/
theorem accept_iff_nonempty (ob : NPObs) (x : List Bool) :
    AcceptNP ob x ↔ (Boundary ob x).Nonempty := Iff.rfl

/-- The boundary-nonemptiness language of a verifier, as a `Bool` decision. -/
noncomputable def acceptBool (ob : NPObs) : List Bool → Bool := fun x => decide (AcceptNP ob x)

theorem acceptBool_iff (ob : NPObs) (x : List Bool) : acceptBool ob x = true ↔ AcceptNP ob x :=
  decide_eq_true_iff

/-- **The NP-observer languages** = NP. -/
def NPLang (L : List Bool → Bool) : Prop := ∃ ob : NPObs, ∀ x, L x = true ↔ AcceptNP ob x

/-- **Every verifier's boundary language is NP** (in particular, a SAT verifier's is). -/
theorem satIsNP (ob : NPObs) : NPLang (acceptBool ob) :=
  ⟨ob, fun x => acceptBool_iff ob x⟩

/-- **P ⊆ NP**: a deterministic observer is a one-sector NP-observer with the empty witness. -/
theorem p_subset_np (L : List Bool → Bool) (h : PLang L) : NPLang L := by
  refine ⟨{ verify := L, wb := fun _ => 0, poly_wb := ⟨0, 0, fun n => Nat.zero_le _⟩, ptime := h },
    fun x => ?_⟩
  constructor
  · intro hx; exact ⟨[], Nat.le_refl 0, by simpa using hx⟩
  · rintro ⟨w, hw, hv⟩
    have : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hw)
    subst this; simpa using hv

/-! ## Polynomial deterministic collapse and the bridge -/

/-- **Polynomial deterministic collapse**: deciding the boundary's nonemptiness is in P (a predicate). -/
def PolyCollapse (ob : NPObs) : Prop := PLang (acceptBool ob)

/-- `P = NP` in the model. -/
def PeqNP : Prop := ∀ L, NPLang L → PLang L

/-- **The bridge**: `P = NP ⇔ every NP boundary admits polynomial deterministic collapse`. -/
theorem bridge : PeqNP ↔ ∀ ob : NPObs, PolyCollapse ob := by
  constructor
  · intro h ob
    exact h (acceptBool ob) (satIsNP ob)
  · intro h L hL
    obtain ⟨ob, hob⟩ := hL
    refine PLang_congr (fun x => ?_) (h ob)
    -- acceptBool ob x = L x
    rw [Bool.eq_iff_iff, acceptBool_iff]
    exact (hob x).symm

/-! ## Calibration — boundary size and representation are NOT the collapse cost -/

/-- A verifier that accepts everything (huge boundary). -/
def fullObs : NPObs :=
  { verify := fun _ => true, wb := fun _ => 0, poly_wb := ⟨0, 0, fun n => Nat.zero_le _⟩,
    ptime := PLang_const true }

/-- **A huge boundary can collapse trivially.**  `fullObs` accepts every input, yet its language is `⊤ ∈ P`.
Boundary *size* is not the collapse cost. -/
theorem fullBoundary_collapses : PolyCollapse fullObs := by
  refine PLang_congr (L := fun _ => true) (fun x => ?_) (PLang_const true)
  show true = acceptBool fullObs x
  exact (decide_eq_true_iff.mpr ⟨[], Nat.le_refl 0, rfl⟩).symm

/-- A verifier that accepts nothing (empty boundary). -/
def emptyObs : NPObs :=
  { verify := fun _ => false, wb := fun _ => 0, poly_wb := ⟨0, 0, fun n => Nat.zero_le _⟩,
    ptime := PLang_const false }

/-- **An empty boundary collapses** (the language is `∅ ∈ P`). -/
theorem emptyBoundary_collapses : PolyCollapse emptyObs := by
  refine PLang_congr (L := fun _ => false) (fun x => ?_) (PLang_const false)
  show false = acceptBool emptyObs x
  have hnot : ¬ AcceptNP emptyObs x := by rintro ⟨w, _, hv⟩; simp [emptyObs] at hv
  simp [acceptBool, hnot]

/-- **Representation is not the collapse cost**: two verifiers with the same acceptance have the same collapse. -/
theorem sameLang_sameCollapse (ob ob' : NPObs) (h : ∀ x, AcceptNP ob x ↔ AcceptNP ob' x) :
    PolyCollapse ob ↔ PolyCollapse ob' := by
  have hb : ∀ x, acceptBool ob x = acceptBool ob' x := fun x => by
    rw [Bool.eq_iff_iff, acceptBool_iff, acceptBool_iff]; exact h x
  exact ⟨PLang_congr hb, PLang_congr (fun x => (hb x).symm)⟩

/-! ## The fenced SAT specialization (conditional on NP-completeness / Cook–Levin) -/

/-- `SATV`'s boundary is NP-complete: its collapse forces every NP language into P.  This is the Cook–Levin
NP-hardness half — a hypothesis, not built here. -/
def SATComplete (SATV : NPObs) : Prop := ∀ L, NPLang L → (PolyCollapse SATV → PLang L)

/-- **The SAT specialization** (conditional).  Given NP-completeness of `SATV`'s boundary, `P = NP` is equivalent
to that single boundary collapsing. -/
theorem sat_specialization (SATV : NPObs) (hc : SATComplete SATV) :
    PeqNP ↔ PolyCollapse SATV := by
  constructor
  · intro h; exact (bridge.mp h) SATV
  · intro hcol L hL; exact hc L hL hcol

/-- **The fenced separation.**  `SATV`'s boundary failing to collapse is equivalent to `P ≠ NP`.  `¬ PolyCollapse
SATV` is the open separation statement; the NP-hardness (`SATComplete`) is fenced. -/
theorem sat_separation (SATV : NPObs) (hc : SATComplete SATV) :
    ¬ PolyCollapse SATV ↔ ¬ PeqNP := by
  rw [sat_specialization SATV hc]

end PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics.p_subset_np
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics.bridge
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics.fullBoundary_collapses
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics.sat_specialization
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics.sat_separation
