import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinMaster

/-!
# Cook–Levin M1 — master group simulation lemmas

Each master group applies its sub-machine's δ *verbatim* (the helpers in `CookLevinMaster` are byte-for-byte copies
of the sub-machine δ's), so while the master is inside a group at a non-halt sub-phase, one master step mirrors one
sub-machine step.  These are the `comp_phase1`-pattern lift lemmas: `run masterM t (embed G c) = embed G (run
subMachine t c)` until the sub-machine halts, letting the master reuse the sub-machines' proven run-lemmas.

This file establishes the pattern on the widest group, **SHA** (`rendShift`, group `3`) — whose state is already
`Fin 9 × Bool × Bool`, so the embedding is the identity on the sub-state.  The other groups (the `Fin 3`/`Fin 4`
scans and `loopCtrl`/`readRes`) follow the same two lemmas with a `Fin.castLE` on the sub-phase.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinMasterSim

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinRendShift (rendShift)
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster

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

-- The cast-embed groups (RANCH1/RANCH2 `scanLeftSep`, INIT `scanRightSep`, LOOPCHK `loopCtrl`, RRES `readRes`)
-- follow the same two lemmas with a `Fin 3/4 ↪ Fin 9` embedding.  They need a per-group `master_delta_*` helper
-- (unfold the big δ once, outside the phase case-split, to avoid the `simp` step blow-up).  Next chunk.

end PallLean.Paper93.DeepMath.PathB.CookLevinMasterSim
