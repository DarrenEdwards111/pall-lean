import Mathlib

/-!
# Observer-Class Semantics for P vs NP — the faithful, uniform foundation

The observer-class reformulation, built to HAL's brutally-semantic, **uniform** scope.  It is a *foundation*, not
a separation: faithful definitions, the structural theorems, and the one open quantity fenced exactly.

* `Ptime` / `PLang` — the **P-observer**: ONE fixed step-counted machine (uniform — a single `Machine`, not a
  program per length) deciding every input within `c·|x|^k` steps.
* `NPObs` / `AcceptNP` — the **one-sector NP-observer**: a fixed poly verifier `V` and poly witness bound; `x` is
  accepted iff **one** existentially-selected sector `w` verifies.  The full witness table is never materialised.
* `accept_iff_nonempty` — `AcceptNP ob x ↔ (Boundary ob x).Nonempty`.
* `p_subset_np` — every P-observer language is an NP-observer language.
* `PolyCollapse` — the boundary admits **polynomial deterministic collapse**: deciding its nonemptiness is in P
  (a *predicate*, per HAL — not a per-`n` numerical minimum, which would smuggle nonuniformity back in).
* `bridge` — **`P = NP ⇔ every NP boundary admits polynomial deterministic collapse`.**
* `fullBoundary_collapses`, `emptyBoundary_collapses`, `sameLang_sameCollapse` — **calibration**: a *huge* boundary
  can collapse trivially, an empty one collapses, and two different verifiers for the same language have the same
  collapse.  So boundary *size* and verifier *representation* are NOT the collapse cost.
* `sat_bridge` — **conditional**: for an NP-complete SAT verifier, `¬ PolyCollapse SATV ⇔ P ≠ NP` (fenced; the
  NP-completeness reduction is a hypothesis, not built here).

SPDP, holography, rigidity, and N-frame mixing are deliberately absent from this core — they are at most *proposed
estimators* of `PolyCollapse`, elsewhere.  This file says exactly what P- and NP-observers can access.  Nothing
here proves `P ≠ NP`; `¬ PolyCollapse SATV` is the open separation statement.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics

open Classical

/-- Polynomial growth. -/
def IsPoly (T : ℕ → ℕ) : Prop := ∃ c k : ℕ, ∀ n, T n ≤ c * n ^ k + c

theorem isPoly_zero : IsPoly (fun _ => 0) := ⟨0, 0, fun n => by simp⟩

/-- A deterministic machine (uniform: a single finitely-described object), with a genuine step count. -/
structure Machine (α : Type) where
  /-- Internal configuration space. -/
  Config : Type
  /-- One local step. -/
  step : Config → Config
  /-- Fixed local initialization from the input. -/
  init : α → Config
  /-- Output once halted (`some b`), else `none`. -/
  output : Config → Option Bool

/-- The configuration after `t` steps. -/
def Machine.run {α : Type} (M : Machine α) (a : α) (t : ℕ) : M.Config := M.step^[t] (M.init a)

/-- `M` decides `P` within time `T` (of the input size). -/
def Decides {α : Type} (M : Machine α) (P : α → Prop) (size : α → ℕ) (T : ℕ → ℕ) : Prop :=
  ∀ a, ∃ t, t ≤ T (size a) ∧ M.output (M.run a t) = some (decide (P a))

/-- `P` is poly-time decidable: **one** machine, poly time. -/
def Ptime {α : Type} (P : α → Prop) (size : α → ℕ) : Prop :=
  ∃ (M : Machine α) (T : ℕ → ℕ), IsPoly T ∧ Decides M P size T

/-- Poly-time is invariant under pointwise logical equivalence (the deciding machine outputs the same bit). -/
theorem Ptime_congr {α : Type} {P P' : α → Prop} {size : α → ℕ}
    (h : ∀ a, P a ↔ P' a) (hP : Ptime P size) : Ptime P' size := by
  obtain ⟨M, T, hT, hdec⟩ := hP
  refine ⟨M, T, hT, fun a => ?_⟩
  obtain ⟨t, ht, ho⟩ := hdec a
  exact ⟨t, ht, ho.trans (congrArg (fun p : Prop => some (decide p)) (propext (h a)))⟩

/-- The always-`true` language is poly-time (a trivial one-step machine). -/
theorem Ptime_true {α : Type} (size : α → ℕ) : Ptime (fun _ : α => True) size :=
  ⟨{ Config := Unit, step := id, init := fun _ => (), output := fun _ => some true },
    fun _ => 0, isPoly_zero, fun a => ⟨0, Nat.zero_le _, by simp [Machine.run]⟩⟩

/-- The always-`false` language is poly-time. -/
theorem Ptime_false {α : Type} (size : α → ℕ) : Ptime (fun _ : α => False) size :=
  ⟨{ Config := Unit, step := id, init := fun _ => (), output := fun _ => some false },
    fun _ => 0, isPoly_zero, fun a => ⟨0, Nat.zero_le _, by simp [Machine.run]⟩⟩

/-- Any everywhere-true predicate is poly-time. -/
theorem Ptime_of_forall {α : Type} {P : α → Prop} {size : α → ℕ} (h : ∀ a, P a) : Ptime P size :=
  Ptime_congr (fun a => (iff_true_intro (h a)).symm) (Ptime_true size)

/-- Any everywhere-false predicate is poly-time. -/
theorem Ptime_of_forall_not {α : Type} {P : α → Prop} {size : α → ℕ} (h : ∀ a, ¬ P a) : Ptime P size :=
  Ptime_congr (fun a => (iff_false_intro (h a)).symm) (Ptime_false size)

/-- A language over bit strings. -/
def Language := List Bool → Prop

/-- **The P-observer languages** = P. -/
def PLang (L : Language) : Prop := Ptime L List.length

/-! ## The one-sector NP-observer -/

/-- A fixed poly verifier with a poly witness bound. -/
structure NPObs where
  /-- Verify `(input, witness)`. -/
  V : List Bool → List Bool → Bool
  /-- Witness-length bound. -/
  wbound : ℕ → ℕ
  /-- Poly witness bound. -/
  poly_wbound : IsPoly wbound
  /-- The verifier is poly-time. -/
  ptime : Ptime (fun p : List Bool × List Bool => V p.1 p.2 = true) (fun p => p.1.length + p.2.length)

/-- **One accepting observation**: one existentially-selected sector verifies. -/
def AcceptNP (ob : NPObs) (x : List Bool) : Prop :=
  ∃ w, w.length ≤ ob.wbound x.length ∧ ob.V x w = true

/-- The boundary of `x`: the set of accepting witnesses. -/
def Boundary (ob : NPObs) (x : List Bool) : Set (List Bool) :=
  {w | w.length ≤ ob.wbound x.length ∧ ob.V x w = true}

/-- Accepting = the boundary is nonempty (exhibit one member, do not read the whole set). -/
theorem accept_iff_nonempty (ob : NPObs) (x : List Bool) :
    AcceptNP ob x ↔ (Boundary ob x).Nonempty := Iff.rfl

/-- **The NP-observer languages** = NP. -/
def NPLang (L : Language) : Prop := ∃ ob : NPObs, ∀ x, L x ↔ AcceptNP ob x

/-- **P ⊆ NP**: a deterministic observer is a one-sector NP-observer with the empty witness. -/
theorem p_subset_np (L : Language) (h : PLang L) : NPLang L := by
  have hLp : Ptime (fun p : List Bool × List Bool => L p.1) (fun p => p.1.length + p.2.length) := by
    obtain ⟨M, T, ⟨c, k, hck⟩, hdec⟩ := h
    refine ⟨{ Config := M.Config, step := M.step, init := fun p => M.init p.1, output := M.output },
      fun n => c * n ^ k + c, ⟨c, k, fun n => le_refl _⟩, fun p => ?_⟩
    obtain ⟨t, ht, ho⟩ := hdec p.1
    refine ⟨t, ?_, ho⟩
    calc t ≤ T p.1.length := ht
      _ ≤ c * p.1.length ^ k + c := hck _
      _ ≤ c * (p.1.length + p.2.length) ^ k + c := by
          have : p.1.length ≤ p.1.length + p.2.length := Nat.le_add_right _ _
          gcongr
  refine ⟨{ V := fun x _ => decide (L x), wbound := fun _ => 0, poly_wbound := isPoly_zero,
            ptime := Ptime_congr (fun p => decide_eq_true_iff.symm) hLp },
          fun x => ⟨fun hx => ⟨[], by simp, decide_eq_true_iff.mpr hx⟩,
                    fun ⟨w, _, hv⟩ => of_decide_eq_true hv⟩⟩

/-! ## Polynomial deterministic collapse and the bridge -/

/-- **Polynomial deterministic collapse**: deciding the boundary's nonemptiness is in P (a predicate). -/
def PolyCollapse (ob : NPObs) : Prop := PLang (fun x => AcceptNP ob x)

/-- `P = NP` in the model. -/
def PeqNP : Prop := ∀ L, NPLang L → PLang L

/-- **The bridge**: `P = NP ⇔ every NP boundary admits polynomial deterministic collapse`. -/
theorem bridge : PeqNP ↔ ∀ ob : NPObs, PolyCollapse ob := by
  constructor
  · intro h ob
    exact h (fun x => AcceptNP ob x) ⟨ob, fun _ => Iff.rfl⟩
  · intro h L hL
    obtain ⟨ob, hob⟩ := hL
    exact Ptime_congr (fun x => (hob x).symm) (h ob)

/-! ## Calibration — boundary size and representation are NOT the collapse cost -/

/-- A verifier that accepts everything (huge boundary). -/
def fullObs : NPObs :=
  { V := fun _ _ => true, wbound := fun _ => 0, poly_wbound := isPoly_zero,
    ptime := Ptime_of_forall (fun _ => rfl) }

/-- **A huge boundary can collapse trivially.**  `fullObs` accepts every input (its boundary is all short
witnesses), yet its language is `⊤ ∈ P` — so it collapses.  Boundary *size* is not the collapse cost. -/
theorem fullBoundary_collapses : PolyCollapse fullObs :=
  Ptime_of_forall (fun x => ⟨[], by simp [fullObs], rfl⟩)

/-- A verifier that accepts nothing (empty boundary). -/
def emptyObs : NPObs :=
  { V := fun _ _ => false, wbound := fun _ => 0, poly_wbound := isPoly_zero,
    ptime := Ptime_of_forall_not (fun _ => by simp) }

/-- **An empty boundary collapses** (the language is `∅ ∈ P`). -/
theorem emptyBoundary_collapses : PolyCollapse emptyObs :=
  Ptime_of_forall_not (fun x => by simp [AcceptNP, emptyObs])

/-- **Representation is not the collapse cost**: two verifiers accepting the same language have the same
collapse, regardless of their boundary sizes. -/
theorem sameLang_sameCollapse (ob ob' : NPObs) (h : ∀ x, AcceptNP ob x ↔ AcceptNP ob' x) :
    PolyCollapse ob ↔ PolyCollapse ob' :=
  ⟨fun hc => Ptime_congr h hc, fun hc => Ptime_congr (fun x => (h x).symm) hc⟩

/-! ## The fenced SAT specialization (conditional on NP-completeness) -/

/-- **Fenced separation.**  If `SATV`'s boundary is NP-complete (its collapse forces every NP language into P),
then its boundary failing to collapse is *equivalent* to `P ≠ NP`.  The NP-completeness hypothesis is not built
here; `¬ PolyCollapse SATV` is the open separation statement. -/
theorem sat_bridge (SATV : NPObs)
    (hcomplete : ∀ L, NPLang L → (PolyCollapse SATV → PLang L)) :
    ¬ PolyCollapse SATV ↔ ¬ PeqNP := by
  constructor
  · intro h hpeq; exact h ((bridge.mp hpeq) SATV)
  · intro h hc; exact h (fun L hL => hcomplete L hL hc)

end PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics.p_subset_np
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics.bridge
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics.fullBoundary_collapses
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics.sat_bridge
