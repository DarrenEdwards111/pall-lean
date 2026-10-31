import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinDynamics

/-!
# Cook–Levin M2 — assembling the clause families (soundness direction)

The tableau formula `φ` is one big conjunction of all clauses across the variable range: the head/state one-hots at
every time, the tape cell-copies at every `(t, p)`, and the δ-dynamics at every `(t, q, p, b)`.  This file builds the
**gathering** (`bigAnd`) and proves the **soundness direction** of the reduction: the assignment reading the real run
(`fullAssign`) satisfies the whole assembled formula.  It combines the individual clause soundnesses over the ranges.

The converse (a *satisfying* assignment reconstructs an accepting run) and the poly emitter remain the deferred
research-scale remainder; per `SCOPE_COOKLEVIN.md` this is one more genuine, non-circular brick — the `⇐` half of
`Satisfiable ⟺ accepting`, assembled.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinAssembly

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinTableau
open PallLean.Paper93.DeepMath.PathB.CookLevinTransition
open PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics

/-! ## Gathering a list of formulas -/

/-- The conjunction of a list of formulas (concatenate their clause lists). -/
def bigAnd (fs : List Formula) : Formula := fs.flatten

/-- **Gathering correctness.**  `bigAnd fs` holds iff every member formula holds. -/
theorem bigAnd_iff (a : ℕ → Bool) (fs : List Formula) :
    evalFormula a (bigAnd fs) = true ↔ ∀ φ ∈ fs, evalFormula a φ = true := by
  induction fs with
  | nil => simp [bigAnd, evalFormula]
  | cons φ fs ih =>
    rw [bigAnd, List.flatten_cons, evalFormula_append, Bool.and_eq_true, show fs.flatten = bigAnd fs from rfl,
      ih, List.forall_mem_cons]

/-- Every clause of a mapped-and-gathered family holds iff each instance holds. -/
theorem bigAnd_map_iff {α : Type} (a : ℕ → Bool) (l : List α) (f : α → Formula) :
    evalFormula a (bigAnd (l.map f)) = true ↔ ∀ i ∈ l, evalFormula a (f i) = true := by
  rw [bigAnd_iff]
  constructor
  · intro h i hi; exact h (f i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · rintro h φ hφ; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hφ; exact h i hi

/-! ## The tape cell-copy family, for `fullAssign` -/

/-- The tape cell-copy clause is satisfied by the real-run assignment (via full tape locality). -/
theorem cellCopyClause_sound_full (M : Machine) (x : List Bool) (t p : ℕ) :
    evalFormula (fullAssign M x) (cellCopyClause t p) = true := by
  rw [cellCopyClause_iff]
  intro hh
  rw [fullAssign_head] at hh
  rw [fullAssign_cell, fullAssign_cell, run_succ]
  exact step_tape_getD_ne_all M (run M t (init M x)) p (Ne.symm (of_decide_eq_false hh))

/-! ## The clause families and their soundness -/

/-- All head one-hots for times `0 … B`. -/
def headFamily (P B : ℕ) : Formula := bigAnd ((List.range (B + 1)).map (fun t => headOneHot t P))

/-- All state one-hots for times `0 … B`. -/
noncomputable def stateFamily (M : Machine) (B : ℕ) : Formula :=
  bigAnd ((List.range (B + 1)).map (fun t => stateOneHot M t))

/-- All tape cell-copies for `t < B`, `p ≤ P`. -/
def tapeFamily (P B : ℕ) : Formula :=
  bigAnd ((List.range B).map (fun t => bigAnd ((List.range (P + 1)).map (fun p => cellCopyClause t p))))

/-- All δ-dynamics for `t < B`, every state index, `p ≤ P`, `b ∈ {false,true}`. -/
noncomputable def dynamicsFamily (M : Machine) (P B : ℕ) : Formula :=
  bigAnd ((List.range B).map (fun t =>
    bigAnd ((List.finRange (Fintype.card M.State)).map (fun q =>
      bigAnd ((List.range (P + 1)).map (fun p =>
        bigAnd ([false, true].map (fun b => dynamicsClause M t q p b))))))))

theorem headFamily_sound (M : Machine) (x : List Bool) (P B : ℕ)
    (hb : ∀ t, t ≤ B → (run M t (init M x)).hd ≤ P) :
    evalFormula (fullAssign M x) (headFamily P B) = true := by
  rw [headFamily, bigAnd_map_iff]
  intro t ht
  exact headOneHot_sound M x t P (hb t (by have := List.mem_range.mp ht; omega))

theorem stateFamily_sound (M : Machine) (x : List Bool) (B : ℕ) :
    evalFormula (fullAssign M x) (stateFamily M B) = true := by
  rw [stateFamily, bigAnd_map_iff]
  intro t _
  exact stateOneHot_sound M x t

theorem tapeFamily_sound (M : Machine) (x : List Bool) (P B : ℕ) :
    evalFormula (fullAssign M x) (tapeFamily P B) = true := by
  rw [tapeFamily, bigAnd_map_iff]
  intro t _
  rw [bigAnd_map_iff]
  intro p _
  exact cellCopyClause_sound_full M x t p

theorem dynamicsFamily_sound (M : Machine) (x : List Bool) (P B : ℕ) :
    evalFormula (fullAssign M x) (dynamicsFamily M P B) = true := by
  rw [dynamicsFamily, bigAnd_map_iff]
  intro t _
  rw [bigAnd_map_iff]
  intro q _
  rw [bigAnd_map_iff]
  intro p _
  rw [bigAnd_map_iff]
  intro b _
  exact dynamicsClause_sound M x t q p b

/-! ## The assembled transition formula and its soundness -/

/-- The assembled formula: head + state one-hots, tape cell-copies, and δ-dynamics, over the whole `[0,B] × [0,P]`
range.  (Init and accept clauses — a few more `fixBits`/disjunction clauses — are the remaining assembly.) -/
noncomputable def assembledFormula (M : Machine) (P B : ℕ) : Formula :=
  headFamily P B ++ stateFamily M B ++ tapeFamily P B ++ dynamicsFamily M P B

/-- **Assembly soundness (`⇐` half).**  With the head bounded by `P` over `[0,B]`, the real-run assignment satisfies
the entire assembled transition formula — every one-hot, tape, and δ-dynamics clause at once. -/
theorem assembledFormula_sound (M : Machine) (x : List Bool) (P B : ℕ)
    (hb : ∀ t, t ≤ B → (run M t (init M x)).hd ≤ P) :
    evalFormula (fullAssign M x) (assembledFormula M P B) = true := by
  rw [assembledFormula, evalFormula_append, evalFormula_append, evalFormula_append, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨headFamily_sound M x P B hb, stateFamily_sound M x B⟩, tapeFamily_sound M x P B⟩,
    dynamicsFamily_sound M x P B⟩

end PallLean.Paper93.DeepMath.PathB.CookLevinAssembly
