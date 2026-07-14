import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinMaster

/-!
# Cook–Levin M1 — master group simulation lemmas

Each master group applies its sub-machine's δ *verbatim* (the helpers in `CookLevinMaster` are byte-for-byte copies
of the sub-machine δ's), so while the master is inside a group at a non-halt sub-phase, one master step mirrors one
sub-machine step.  These are the `comp_phase1`-pattern lift lemmas: `run masterM t (embed G c) = embed G (run
subMachine t c)` until the sub-machine halts, letting the master reuse the sub-machines' proven run-lemmas.

All seven phase-groups are covered:
* **SHA/SHB** (`rendShift`, groups `3`/`6`) — state already `Fin 9 × Bool × Bool`, so the embedding is the identity
  on the sub-state (`embedRend`);
* **INIT** (`scanRightSep`, group `0`), **LOOPCHK** (`loopCtrl`, group `1`), **RANCH1/RANCH2** (`scanLeftSep`,
  groups `4`/`7`), **RRES** (`readRes`, group `8`) — narrower phase spaces, so the embedding widens the sub-phase
  with `Fin.castLE` (`embedScanR`/`embedLoop`/`embedScanL`/`embedRes`), with `castLE3_ne`/`castLE4_ne` transferring
  the "off the halt phase" hypothesis across the widening.

Each group gets a per-group `master_delta_*` helper (unfold the big master δ once to expose the group's verbatim
sub-machine helper), an `sim_step_*` (one-step lift under the embedding), and an `sim_run_*` (the run-level lift).

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinMasterSim

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinRendShift (rendShift)
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinScanLeftSep (scanLeftSep)
open PallLean.Paper93.DeepMath.PathB.CookLevinScanRightSep (scanRightSep)
open PallLean.Paper93.DeepMath.PathB.CookLevinLoopEnds (loopCtrl readRes)

/-- Embed a `rendShift` configuration into the master under group tag `g`. -/
def embedRend (g : Fin 10) (c : Cfg rendShift) : Cfg masterM :=
  ⟨(g, c.st.1, c.st.2.1, c.st.2.2), c.hd, c.tp⟩

/-- The master's δ in group `3` (SHA), at a non-halt sub-phase, is exactly `rendShift`'s δ (re-tagged). -/
theorem master_delta_SHA {sp : Fin 9} {c0 c1 b : Bool} (h : sp ≠ 8) :
    masterM.δ (3, sp, c0, c1) b = inGroup 3 (rendShift.δ (sp, c0, c1) b) := by
  simp only [masterM]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide), if_neg h]
  rfl

/-- **Simulation step (SHA).**  While `rendShift` has not halted, one master step in group `3` mirrors one
`rendShift` step. -/
theorem sim_step_SHA (c : Cfg rendShift) (h : c.st.1 ≠ 8) :
    step masterM (embedRend 3 c) = embedRend 3 (step rendShift c) := by
  obtain ⟨⟨sp, c0, c1⟩, hd, tp⟩ := c
  have hr : rendShift.halt (sp, c0, c1) = false := by
    simp only [rendShift]; exact decide_eq_false h
  simp only [embedRend, step, hr, Bool.false_eq_true, ↓reduceIte,
    show masterM.halt ((3 : Fin 10), sp, c0, c1) = false from rfl]
  rw [master_delta_SHA h]
  simp only [inGroup]

/-- **Simulation run (SHA).**  While `rendShift` stays unhalted through step `t`, the master run in group `3`
mirrors the `rendShift` run — lifting any `rendShift` run-lemma to the master. -/
theorem sim_run_SHA (t : ℕ) (c : Cfg rendShift) (hmin : ∀ i < t, (run rendShift i c).st.1 ≠ 8) :
    run masterM t (embedRend 3 c) = embedRend 3 (run rendShift t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, ih (fun i hi => hmin i (Nat.lt_succ_of_lt hi)),
      sim_step_SHA _ (hmin t (Nat.lt_succ_self t)), ← run_succ]

/-! ## SHB — same `rendShift`, group `6` (identity embed) -/

theorem master_delta_SHB {sp : Fin 9} {c0 c1 b : Bool} (h : sp ≠ 8) :
    masterM.δ (6, sp, c0, c1) b = inGroup 6 (rendShift.δ (sp, c0, c1) b) := by
  simp only [masterM]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_pos (by decide), if_neg h]
  rfl

theorem sim_step_SHB (c : Cfg rendShift) (h : c.st.1 ≠ 8) :
    step masterM (embedRend 6 c) = embedRend 6 (step rendShift c) := by
  obtain ⟨⟨sp, c0, c1⟩, hd, tp⟩ := c
  have hr : rendShift.halt (sp, c0, c1) = false := by simp only [rendShift]; exact decide_eq_false h
  simp only [embedRend, step, hr, Bool.false_eq_true, ↓reduceIte,
    show masterM.halt ((6 : Fin 10), sp, c0, c1) = false from rfl]
  rw [master_delta_SHB h]
  simp only [inGroup]

theorem sim_run_SHB (t : ℕ) (c : Cfg rendShift) (hmin : ∀ i < t, (run rendShift i c).st.1 ≠ 8) :
    run masterM t (embedRend 6 c) = embedRend 6 (run rendShift t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, ih (fun i hi => hmin i (Nat.lt_succ_of_lt hi)),
      sim_step_SHB _ (hmin t (Nat.lt_succ_self t)), ← run_succ]

/-! ## Cast-embed groups (`Fin 3`/`Fin 4` sub-phase ↪ `Fin 9`)

The four remaining sub-machines have narrower phase spaces than `rendShift`, so their master embedding widens
the sub-phase with `Fin.castLE`.  Two cast lemmas transfer the "off the halt phase" hypothesis across the widening
(by `fin_cases`, so `castLE` reduces on concrete phases and `decide` closes). -/

/-- `ph ≠ 2` in `Fin 3` transfers to its `Fin 9` widening. -/
theorem castLE3_ne {ph : Fin 3} (h : ph ≠ 2) : (Fin.castLE (by omega) ph : Fin 9) ≠ 2 := by
  fin_cases ph
  · decide
  · decide
  · exact absurd rfl h

/-- `ph ≠ 3` in `Fin 4` transfers to its `Fin 9` widening. -/
theorem castLE4_ne {ph : Fin 4} (h : ph ≠ 3) : (Fin.castLE (by omega) ph : Fin 9) ≠ 3 := by
  fin_cases ph
  · decide
  · decide
  · decide
  · exact absurd rfl h

/-! ### Per-group δ helpers (unfold the big master δ once, outside the phase case-split) -/

theorem master_delta_INIT {sp : Fin 9} {c0 c1 b : Bool} (h : sp ≠ 2) :
    masterM.δ (0, sp, c0, c1) b = inGroup 0 (scanRightStep sp c0 b) := by
  simp only [masterM]; rw [if_pos (by decide), if_neg h]

theorem master_delta_LOOPCHK {sp : Fin 9} {c0 c1 b : Bool} (h : sp ≠ 2) :
    masterM.δ (1, sp, c0, c1) b = inGroup 1 (loopStep sp c0 b) := by
  simp only [masterM]; rw [if_neg (by decide), if_pos (by decide), if_neg h]

theorem master_delta_RANCH1 {sp : Fin 9} {c0 c1 b : Bool} (h : sp ≠ 2) :
    masterM.δ (4, sp, c0, c1) b = inGroup 4 (scanLeftStep sp c0 b) := by
  simp only [masterM]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_pos (by decide), if_neg h]

theorem master_delta_RANCH2 {sp : Fin 9} {c0 c1 b : Bool} (h : sp ≠ 2) :
    masterM.δ (7, sp, c0, c1) b = inGroup 7 (scanLeftStep sp c0 b) := by
  simp only [masterM]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide), if_neg h]

theorem master_delta_RRES {sp : Fin 9} {c0 c1 b : Bool} (h : sp ≠ 3) :
    masterM.δ (8, sp, c0, c1) b = inGroup 8 (readResStep sp c0 b) := by
  simp only [masterM]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_pos (by decide), if_neg h]

/-! ### INIT — `scanRightSep`, group `0` -/

/-- Embed a `scanRightSep` config into the master under group tag `g`. -/
def embedScanR (g : Fin 10) (c : Cfg scanRightSep) : Cfg masterM :=
  ⟨(g, Fin.castLE (by omega) c.st.1, c.st.2, false), c.hd, c.tp⟩

theorem sim_step_INIT (c : Cfg scanRightSep) (h : c.st.1 ≠ 2) :
    step masterM (embedScanR 0 c) = embedScanR 0 (step scanRightSep c) := by
  obtain ⟨⟨ph, s⟩, hd, tp⟩ := c
  have hr : scanRightSep.halt (ph, s) = false := by simp only [scanRightSep]; exact decide_eq_false h
  simp only [embedScanR, step, hr, Bool.false_eq_true, ↓reduceIte,
    show masterM.halt ((0 : Fin 10), Fin.castLE (by omega) ph, s, false) = false from rfl]
  rw [master_delta_INIT (castLE3_ne h)]
  fin_cases ph
  · simp [inGroup, embedScanR, moveHead, scanRightStep, scanRightSep, Fin.castLE]
  · simp [inGroup, embedScanR, moveHead, scanRightStep, scanRightSep, Fin.castLE]
    split <;> exact ⟨rfl, rfl, rfl⟩
  · exact absurd rfl h

theorem sim_run_INIT (t : ℕ) (c : Cfg scanRightSep) (hmin : ∀ i < t, (run scanRightSep i c).st.1 ≠ 2) :
    run masterM t (embedScanR 0 c) = embedScanR 0 (run scanRightSep t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, ih (fun i hi => hmin i (Nat.lt_succ_of_lt hi)),
      sim_step_INIT _ (hmin t (Nat.lt_succ_self t)), ← run_succ]

/-! ### LOOPCHK — `loopCtrl`, group `1` (no compare-`if`) -/

/-- Embed a `loopCtrl` config into the master under group tag `g`. -/
def embedLoop (g : Fin 10) (c : Cfg loopCtrl) : Cfg masterM :=
  ⟨(g, Fin.castLE (by omega) c.st.1, c.st.2, false), c.hd, c.tp⟩

theorem sim_step_LOOPCHK (c : Cfg loopCtrl) (h : c.st.1 ≠ 2) :
    step masterM (embedLoop 1 c) = embedLoop 1 (step loopCtrl c) := by
  obtain ⟨⟨ph, s⟩, hd, tp⟩ := c
  have hr : loopCtrl.halt (ph, s) = false := by simp only [loopCtrl]; exact decide_eq_false h
  simp only [embedLoop, step, hr, Bool.false_eq_true, ↓reduceIte,
    show masterM.halt ((1 : Fin 10), Fin.castLE (by omega) ph, s, false) = false from rfl]
  rw [master_delta_LOOPCHK (castLE3_ne h)]
  fin_cases ph
  · simp [inGroup, embedLoop, moveHead, loopStep, loopCtrl, Fin.castLE]
  · simp [inGroup, embedLoop, moveHead, loopStep, loopCtrl, Fin.castLE]
  · exact absurd rfl h

theorem sim_run_LOOPCHK (t : ℕ) (c : Cfg loopCtrl) (hmin : ∀ i < t, (run loopCtrl i c).st.1 ≠ 2) :
    run masterM t (embedLoop 1 c) = embedLoop 1 (run loopCtrl t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, ih (fun i hi => hmin i (Nat.lt_succ_of_lt hi)),
      sim_step_LOOPCHK _ (hmin t (Nat.lt_succ_self t)), ← run_succ]

/-! ### RANCH1 / RANCH2 — `scanLeftSep`, groups `4` and `7` -/

/-- Embed a `scanLeftSep` config into the master under group tag `g`. -/
def embedScanL (g : Fin 10) (c : Cfg scanLeftSep) : Cfg masterM :=
  ⟨(g, Fin.castLE (by omega) c.st.1, c.st.2, false), c.hd, c.tp⟩

theorem sim_step_RANCH1 (c : Cfg scanLeftSep) (h : c.st.1 ≠ 2) :
    step masterM (embedScanL 4 c) = embedScanL 4 (step scanLeftSep c) := by
  obtain ⟨⟨ph, s⟩, hd, tp⟩ := c
  have hr : scanLeftSep.halt (ph, s) = false := by simp only [scanLeftSep]; exact decide_eq_false h
  simp only [embedScanL, step, hr, Bool.false_eq_true, ↓reduceIte,
    show masterM.halt ((4 : Fin 10), Fin.castLE (by omega) ph, s, false) = false from rfl]
  rw [master_delta_RANCH1 (castLE3_ne h)]
  fin_cases ph
  · simp [inGroup, embedScanL, moveHead, scanLeftStep, scanLeftSep, Fin.castLE]
  · simp [inGroup, embedScanL, moveHead, scanLeftStep, scanLeftSep, Fin.castLE]
    split <;> exact ⟨rfl, rfl, rfl⟩
  · exact absurd rfl h

theorem sim_step_RANCH2 (c : Cfg scanLeftSep) (h : c.st.1 ≠ 2) :
    step masterM (embedScanL 7 c) = embedScanL 7 (step scanLeftSep c) := by
  obtain ⟨⟨ph, s⟩, hd, tp⟩ := c
  have hr : scanLeftSep.halt (ph, s) = false := by simp only [scanLeftSep]; exact decide_eq_false h
  simp only [embedScanL, step, hr, Bool.false_eq_true, ↓reduceIte,
    show masterM.halt ((7 : Fin 10), Fin.castLE (by omega) ph, s, false) = false from rfl]
  rw [master_delta_RANCH2 (castLE3_ne h)]
  fin_cases ph
  · simp [inGroup, embedScanL, moveHead, scanLeftStep, scanLeftSep, Fin.castLE]
  · simp [inGroup, embedScanL, moveHead, scanLeftStep, scanLeftSep, Fin.castLE]
    split <;> exact ⟨rfl, rfl, rfl⟩
  · exact absurd rfl h

theorem sim_run_RANCH1 (t : ℕ) (c : Cfg scanLeftSep) (hmin : ∀ i < t, (run scanLeftSep i c).st.1 ≠ 2) :
    run masterM t (embedScanL 4 c) = embedScanL 4 (run scanLeftSep t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, ih (fun i hi => hmin i (Nat.lt_succ_of_lt hi)),
      sim_step_RANCH1 _ (hmin t (Nat.lt_succ_self t)), ← run_succ]

theorem sim_run_RANCH2 (t : ℕ) (c : Cfg scanLeftSep) (hmin : ∀ i < t, (run scanLeftSep i c).st.1 ≠ 2) :
    run masterM t (embedScanL 7 c) = embedScanL 7 (run scanLeftSep t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, ih (fun i hi => hmin i (Nat.lt_succ_of_lt hi)),
      sim_step_RANCH2 _ (hmin t (Nat.lt_succ_self t)), ← run_succ]

/-! ### RRES — `readRes`, group `8` (`Fin 4` sub-phase, no compare-`if`) -/

/-- Embed a `readRes` config into the master under group tag `g`. -/
def embedRes (g : Fin 10) (c : Cfg readRes) : Cfg masterM :=
  ⟨(g, Fin.castLE (by omega) c.st.1, c.st.2, false), c.hd, c.tp⟩

theorem sim_step_RRES (c : Cfg readRes) (h : c.st.1 ≠ 3) :
    step masterM (embedRes 8 c) = embedRes 8 (step readRes c) := by
  obtain ⟨⟨ph, s⟩, hd, tp⟩ := c
  have hr : readRes.halt (ph, s) = false := by simp only [readRes]; exact decide_eq_false h
  simp only [embedRes, step, hr, Bool.false_eq_true, ↓reduceIte,
    show masterM.halt ((8 : Fin 10), Fin.castLE (by omega) ph, s, false) = false from rfl]
  rw [master_delta_RRES (castLE4_ne h)]
  fin_cases ph
  · simp [inGroup, embedRes, moveHead, readResStep, readRes, Fin.castLE]
  · simp [inGroup, embedRes, moveHead, readResStep, readRes, Fin.castLE]
  · simp [inGroup, embedRes, moveHead, readResStep, readRes, Fin.castLE]
  · exact absurd rfl h

theorem sim_run_RRES (t : ℕ) (c : Cfg readRes) (hmin : ∀ i < t, (run readRes i c).st.1 ≠ 3) :
    run masterM t (embedRes 8 c) = embedRes 8 (run readRes t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, ih (fun i hi => hmin i (Nat.lt_succ_of_lt hi)),
      sim_step_RRES _ (hmin t (Nat.lt_succ_self t)), ← run_succ]

end PallLean.Paper93.DeepMath.PathB.CookLevinMasterSim
