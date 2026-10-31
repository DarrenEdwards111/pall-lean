import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinWrite
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinInitAccept

/-!
# Cook–Levin M2 — the `⇒` converse: a satisfying assignment decodes to the run

The soundness half (`fullFormula_satisfiable`) shows an accepting run yields a satisfying assignment.  This file
proves the **hard direction**: any assignment `a` satisfying the tableau is forced — clause by clause, row by row —
to agree with the *real run*, so the accept clause makes the run accept.

The engine is the decode invariant `Decoded a t` = "on row `t`, `a`'s state bit, head bit, and cell bits match the
real config at step `t`".  It is
* **seeded** by the init clauses (`decoded_zero`), and
* **propagated** by one row's worth of clauses (`decoded_succ`): the one-hot pins the unique on-bits, the δ-dynamics
  clause carries the state/head forward, the cell-copy clause carries the non-head cells, and the *write* clause
  (`CookLevinWrite`) carries the head cell.

`decoded_all` runs the induction to row `B`; the accept clause then forces `(run B).st` to be accepting-and-halting.
Together with the soundness half this is the tableau reduction's correctness: `Satisfiable (fullTableau) ⟺ the run
halts-and-accepts` (given the head bound).  The poly transducer emitting `φ` remains the deferred remainder.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinConverse

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinTransition
open PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics
open PallLean.Paper93.DeepMath.PathB.CookLevinWrite
open PallLean.Paper93.DeepMath.PathB.CookLevinAssembly
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept

/-! ## The write family, and the full tableau formula (with the write clauses) -/

/-- All tape-write clauses for `t < B`, every state index, `p ≤ P`, `b ∈ {false,true}`. -/
noncomputable def writeFamily (M : Machine) (P B : ℕ) : Formula :=
  bigAnd ((List.range B).map (fun t =>
    bigAnd ((List.finRange (Fintype.card M.State)).map (fun q =>
      bigAnd ((List.range (P + 1)).map (fun p =>
        bigAnd ([false, true].map (fun b => writeClause M t q p b))))))))

theorem writeFamily_sound (M : Machine) (x : List Bool) (P B : ℕ) :
    evalFormula (fullAssign M x) (writeFamily M P B) = true := by
  rw [writeFamily, bigAnd_map_iff]
  intro t _
  rw [bigAnd_map_iff]
  intro q _
  rw [bigAnd_map_iff]
  intro p _
  rw [bigAnd_map_iff]
  intro b _
  exact writeClause_sound M x t q p b

/-- The full tableau formula, including the head-cell write clauses (which the converse needs). -/
noncomputable def fullTableau (M : Machine) (x : List Bool) (P B : ℕ) : Formula :=
  fullFormula M x P B ++ writeFamily M P B

/-- **Soundness (`⇐`).**  An accepting run (head bounded by `P`) makes the full tableau satisfiable, via `fullAssign`. -/
theorem fullTableau_satisfiable (M : Machine) (x : List Bool) (P B : ℕ)
    (hb : ∀ t, t ≤ B → (run M t (init M x)).hd ≤ P)
    (hhalt : M.halt (run M B (init M x)).st = true) (hacc : M.accept (run M B (init M x)).st = true) :
    Satisfiable (fullTableau M x P B) := by
  refine ⟨fullAssign M x, ?_⟩
  rw [fullTableau, fullFormula, assembledFormula, evalFormula_append, evalFormula_append, evalFormula_append,
    evalFormula_append, evalFormula_append, evalFormula_append, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨initFormula_sound M x P,
      ⟨⟨⟨headFamily_sound M x P B hb, stateFamily_sound M x B⟩, tapeFamily_sound M x P B⟩,
        dynamicsFamily_sound M x P B⟩⟩,
      acceptFormula_sound M x B hhalt hacc⟩,
    writeFamily_sound M x P B⟩

/-! ## Extracting a single clause from a satisfied family -/

theorem get_headOneHot (a : ℕ → Bool) (P B t : ℕ) (h : evalFormula a (headFamily P B) = true) (ht : t ≤ B) :
    evalFormula a (headOneHot t P) = true := by
  rw [headFamily, bigAnd_map_iff] at h
  exact h t (List.mem_range.mpr (by omega))

theorem get_stateOneHot (a : ℕ → Bool) (M : Machine) (B t : ℕ) (h : evalFormula a (stateFamily M B) = true)
    (ht : t ≤ B) : evalFormula a (stateOneHot M t) = true := by
  rw [stateFamily, bigAnd_map_iff] at h
  exact h t (List.mem_range.mpr (by omega))

theorem get_cellCopy (a : ℕ → Bool) (P B t p : ℕ) (h : evalFormula a (tapeFamily P B) = true)
    (ht : t < B) (hp : p ≤ P) : evalFormula a (cellCopyClause t p) = true := by
  rw [tapeFamily, bigAnd_map_iff] at h
  have h1 := h t (List.mem_range.mpr ht)
  rw [bigAnd_map_iff] at h1
  exact h1 p (List.mem_range.mpr (by omega))

theorem get_dynamics (a : ℕ → Bool) (M : Machine) (P B t : ℕ) (q : Fin (Fintype.card M.State)) (p : ℕ)
    (b : Bool) (h : evalFormula a (dynamicsFamily M P B) = true) (ht : t < B) (hp : p ≤ P) :
    evalFormula a (dynamicsClause M t q p b) = true := by
  rw [dynamicsFamily, bigAnd_map_iff] at h
  have h1 := h t (List.mem_range.mpr ht)
  rw [bigAnd_map_iff] at h1
  have h2 := h1 q (List.mem_finRange _)
  rw [bigAnd_map_iff] at h2
  have h3 := h2 p (List.mem_range.mpr (by omega))
  rw [bigAnd_map_iff] at h3
  exact h3 b (by cases b <;> simp)

theorem get_write (a : ℕ → Bool) (M : Machine) (P B t : ℕ) (q : Fin (Fintype.card M.State)) (p : ℕ)
    (b : Bool) (h : evalFormula a (writeFamily M P B) = true) (ht : t < B) (hp : p ≤ P) :
    evalFormula a (writeClause M t q p b) = true := by
  rw [writeFamily, bigAnd_map_iff] at h
  have h1 := h t (List.mem_range.mpr ht)
  rw [bigAnd_map_iff] at h1
  have h2 := h1 q (List.mem_finRange _)
  rw [bigAnd_map_iff] at h2
  have h3 := h2 p (List.mem_range.mpr (by omega))
  rw [bigAnd_map_iff] at h3
  exact h3 b (by cases b <;> simp)

/-! ## One-hot forces the other bits off -/

theorem headOneHot_off (a : ℕ → Bool) (t P : ℕ) (h : evalFormula a (headOneHot t P) = true)
    {p p' : ℕ} (hp : p ≤ P) (hp' : p' ≤ P) (hne : p ≠ p') (ht : a (headVar t p) = true) :
    a (headVar t p') = false := by
  rw [headOneHot, oneHot_iff] at h
  have hmem : headVar t p ∈ (List.range (P + 1)).map (headVar t) :=
    List.mem_map.mpr ⟨p, List.mem_range.mpr (by omega), rfl⟩
  have hmem' : headVar t p' ∈ (List.range (P + 1)).map (headVar t) :=
    List.mem_map.mpr ⟨p', List.mem_range.mpr (by omega), rfl⟩
  have hvne : headVar t p ≠ headVar t p' := fun heq => hne (headVar_injective t heq)
  have hrel := h.2.forall (fun {_ _} hh => Or.symm hh) hmem hmem' hvne
  rcases hrel with h1 | h2
  · rw [ht] at h1; exact absurd h1 (by decide)
  · exact h2

theorem stateOneHot_off (a : ℕ → Bool) (M : Machine) (t : ℕ) (h : evalFormula a (stateOneHot M t) = true)
    {q q' : ℕ} (hq : q < Fintype.card M.State) (hq' : q' < Fintype.card M.State) (hne : q ≠ q')
    (ht : a (stateVar t q) = true) : a (stateVar t q') = false := by
  rw [stateOneHot, oneHot_iff] at h
  have hmem : stateVar t q ∈ (List.range (Fintype.card M.State)).map (stateVar t) :=
    List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩
  have hmem' : stateVar t q' ∈ (List.range (Fintype.card M.State)).map (stateVar t) :=
    List.mem_map.mpr ⟨q', List.mem_range.mpr hq', rfl⟩
  have hvne : stateVar t q ≠ stateVar t q' := fun heq => hne (stateVar_injective t heq)
  have hrel := h.2.forall (fun {_ _} hh => Or.symm hh) hmem hmem' hvne
  rcases hrel with h1 | h2
  · rw [ht] at h1; exact absurd h1 (by decide)
  · exact h2

/-! ## The decode invariant -/

/-- On row `t`, the assignment `a` agrees with the real run: the run's state bit is on, the run's head bit is on,
and every cell (up to `P`) reads the real tape cell. -/
def Decoded (M : Machine) (x : List Bool) (a : ℕ → Bool) (P t : ℕ) : Prop :=
  a (stateVar t (Fintype.equivFin M.State (run M t (init M x)).st).val) = true
  ∧ a (headVar t (run M t (init M x)).hd) = true
  ∧ ∀ p, p ≤ P → a (cellVar t p) = (run M t (init M x)).tp.getD p false

/-- The next state index / head equal the run's, once the local window is the real one. -/
theorem next_state_head (M : Machine) (x : List Bool) (t : ℕ) :
    nextStateIdx M (Fintype.equivFin M.State (run M t (init M x)).st) (run M t (init M x)).hd
        ((run M t (init M x)).tp.getD (run M t (init M x)).hd false)
      = (Fintype.equivFin M.State (run M (t + 1) (init M x)).st).val
    ∧ nextHead M (Fintype.equivFin M.State (run M t (init M x)).st) (run M t (init M x)).hd
        ((run M t (init M x)).tp.getD (run M t (init M x)).hd false)
      = (run M (t + 1) (init M x)).hd := by
  obtain ⟨hst, hhd⟩ := step_via_stepStateHead M (run M t (init M x))
  refine ⟨?_, ?_⟩
  · unfold nextStateIdx
    rw [Equiv.symm_apply_apply, ← hst, run_succ]
  · unfold nextHead
    rw [Equiv.symm_apply_apply, ← hhd, run_succ]

/-! ## Base case -/

theorem decoded_zero (a : ℕ → Bool) (M : Machine) (x : List Bool) (P : ℕ)
    (hinit : evalFormula a (initFormula M x P) = true) : Decoded M x a P 0 := by
  rw [initFormula, fixBits_iff] at hinit
  refine ⟨?_, ?_, ?_⟩
  · have h1 := hinit (stateVar 0 (Fintype.equivFin M.State M.start).val, true) (List.mem_cons.mpr (Or.inl rfl))
    simpa [run_zero, init] using h1
  · have h2 := hinit (headVar 0 0, true) (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
    simpa [run_zero, init] using h2
  · intro p hp
    have h3 := hinit (cellVar 0 p, x.getD p false)
      (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
        (List.mem_map.mpr ⟨p, List.mem_range.mpr (by omega), rfl⟩)))))
    simpa [run_zero, init] using h3

/-! ## Step case -/

theorem decoded_succ (a : ℕ → Bool) (M : Machine) (x : List Bool) (P B t : ℕ)
    (hbt : (run M t (init M x)).hd ≤ P)
    (hdec : Decoded M x a P t)
    (hone : evalFormula a (headOneHot t P) = true)
    (htape : ∀ p, p ≤ P → evalFormula a (cellCopyClause t p) = true)
    (hdyn : evalFormula a (dynamicsClause M t (Fintype.equivFin M.State (run M t (init M x)).st)
              (run M t (init M x)).hd ((run M t (init M x)).tp.getD (run M t (init M x)).hd false)) = true)
    (hwrite : evalFormula a (writeClause M t (Fintype.equivFin M.State (run M t (init M x)).st)
              (run M t (init M x)).hd ((run M t (init M x)).tp.getD (run M t (init M x)).hd false)) = true) :
    Decoded M x a P (t + 1) := by
  obtain ⟨hstate, hhead, hcell⟩ := hdec
  have gc : a (cellVar t (run M t (init M x)).hd) = (run M t (init M x)).tp.getD (run M t (init M x)).hd false :=
    hcell _ hbt
  have hguards : evalLit a (stateVar t (Fintype.equivFin M.State (run M t (init M x)).st).val, true) = true
      ∧ evalLit a (headVar t (run M t (init M x)).hd, true) = true
      ∧ evalLit a (cellVar t (run M t (init M x)).hd,
          (run M t (init M x)).tp.getD (run M t (init M x)).hd false) = true := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [evalLit, beq_iff_eq]
    exacts [hstate, hhead, gc]
  rw [dynamicsClause, evalFormula_cons, evalFormula_cons, evalFormula, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at hdyn
  have hc1 := (implClause_iff a _ _ _ _).mp hdyn.1 hguards
  have hc2 := (implClause_iff a _ _ _ _).mp hdyn.2 hguards
  simp only [evalLit, beq_iff_eq] at hc1 hc2
  rw [writeClause, evalFormula_cons, evalFormula, List.all_nil, Bool.and_true] at hwrite
  obtain ⟨hns, hnh⟩ := next_state_head M x t
  refine ⟨?_, ?_, ?_⟩
  · rw [hns] at hc1; exact hc1
  · rw [hnh] at hc2; exact hc2
  · intro p hp
    by_cases hpp : p = (run M t (init M x)).hd
    · subst hpp
      have cw := (implClause_iff a _ _ _ _).mp hwrite hguards
      simp only [evalLit, beq_iff_eq] at cw
      rw [cw, Equiv.symm_apply_apply, run_succ, step_tape_getD_head]
    · have hoff : a (headVar t p) = false :=
        headOneHot_off a t P hone hbt hp (fun heq => hpp heq.symm) hhead
      have hcopy := (cellCopyClause_iff a t p).mp (htape p hp) hoff
      rw [hcopy, hcell p hp, run_succ, step_tape_getD_ne_all M (run M t (init M x)) p hpp]

/-! ## The induction and the converse -/

theorem decoded_all (a : ℕ → Bool) (M : Machine) (x : List Bool) (P B : ℕ)
    (hb : ∀ t, t ≤ B → (run M t (init M x)).hd ≤ P)
    (hinit : evalFormula a (initFormula M x P) = true)
    (hheadF : evalFormula a (headFamily P B) = true)
    (htapeF : evalFormula a (tapeFamily P B) = true)
    (hdynF : evalFormula a (dynamicsFamily M P B) = true)
    (hwriteF : evalFormula a (writeFamily M P B) = true) :
    ∀ t, t ≤ B → Decoded M x a P t := by
  intro t
  induction t with
  | zero => intro _; exact decoded_zero a M x P hinit
  | succ t ih =>
    intro ht
    refine decoded_succ a M x P B t (hb t (by omega)) (ih (by omega))
      (get_headOneHot a P B t hheadF (by omega))
      (fun p hp => get_cellCopy a P B t p htapeF (by omega) hp)
      (get_dynamics a M P B t _ _ _ hdynF (by omega) (hb t (by omega)))
      (get_write a M P B t _ _ _ hwriteF (by omega) (hb t (by omega)))

/-- **The reduction is complete (`⇒`).**  Any assignment satisfying the full tableau (with the head bounded by `P`
over `[0,B]`) forces the real run to halt-and-accept by step `B`. -/
theorem fullTableau_converse (M : Machine) (x : List Bool) (P B : ℕ) (a : ℕ → Bool)
    (hb : ∀ t, t ≤ B → (run M t (init M x)).hd ≤ P)
    (hsat : evalFormula a (fullTableau M x P B) = true) :
    M.halt (run M B (init M x)).st = true ∧ M.accept (run M B (init M x)).st = true := by
  rw [fullTableau, fullFormula, assembledFormula, evalFormula_append, evalFormula_append, evalFormula_append,
    evalFormula_append, evalFormula_append, evalFormula_append, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hsat
  obtain ⟨⟨⟨hinit, ⟨⟨⟨hheadF, hstateF⟩, htapeF⟩, hdynF⟩⟩, haccept⟩, hwriteF⟩ := hsat
  obtain ⟨hstateB, _, _⟩ := decoded_all a M x P B hb hinit hheadF htapeF hdynF hwriteF B (le_refl B)
  rw [acceptFormula, evalFormula, List.all_cons, List.all_nil, Bool.and_true, atLeastOne_iff] at haccept
  obtain ⟨v, hvmem, hvtrue⟩ := haccept
  obtain ⟨q', hq'mem, rfl⟩ := List.mem_map.mp hvmem
  have hqeq : q' = Fintype.equivFin M.State (run M B (init M x)).st := by
    by_contra hne
    have hfalse : a (stateVar B q'.val) = false :=
      stateOneHot_off a M B (get_stateOneHot a M B B hstateF (le_refl B)) (Fin.isLt _) (Fin.isLt _)
        (fun hveq => hne (Fin.ext hveq).symm) hstateB
    rw [hfalse] at hvtrue
    exact absurd hvtrue (by decide)
  rw [acceptStates, List.mem_filter] at hq'mem
  have hpred := hq'mem.2
  rw [hqeq, Equiv.symm_apply_apply, Bool.and_eq_true] at hpred
  exact ⟨hpred.2, hpred.1⟩

/-- **Tableau reduction correctness.**  With the head bounded by `P` over `[0,B]`, the full tableau formula is
satisfiable *iff* the real run halts-and-accepts by step `B`.  Both directions: `⇐` witnesses satisfiability by the
real-run assignment; `⇒` decodes any satisfying assignment back to the run. -/
theorem fullTableau_correct (M : Machine) (x : List Bool) (P B : ℕ)
    (hb : ∀ t, t ≤ B → (run M t (init M x)).hd ≤ P) :
    Satisfiable (fullTableau M x P B)
      ↔ (M.halt (run M B (init M x)).st = true ∧ M.accept (run M B (init M x)).st = true) := by
  constructor
  · rintro ⟨a, ha⟩
    exact fullTableau_converse M x P B a hb ha
  · rintro ⟨hh, hacc⟩
    exact fullTableau_satisfiable M x P B hb hh hacc

end PallLean.Paper93.DeepMath.PathB.CookLevinConverse
