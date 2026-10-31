import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinConverse

/-!
# Cook–Levin M2 — the reduction map: unconditional correctness and polynomial output size

The tableau correctness (`fullTableau_correct`) took a hypothesis "the head stays within `P` over `[0,B]`".  That
hypothesis is **free**: by `run_bounds` the head is always within `|x| + t ≤ |x| + B`.  So with `P := |x| + clock`
the reduction map

    tableauReduction M x clock := fullTableau M x (|x| + clock) clock

is **unconditionally** correct:

    Satisfiable (tableauReduction M x clock)  ⟺  M halts-and-accepts x within `clock` steps.

We also bound its **output size**: `(tableauReduction M x clock).length` is polynomial in `|x|`, `clock`, and
`card M.State` (a constant for a fixed machine).  A poly-time transducer can only emit poly-size output, so this is
a necessary half of the "poly transducer" obligation, and the size bound the emitter's time bound would rest on.

What is **not** here (and, per `SCOPE_COOKLEVIN.md`, is the research-scale remainder): the reduction map realised as
an actual `ComposableMachine` transducer (`PolyComputable`) — a machine that *writes* the clause list on a tape — and
its poly-*time* bound.  That emitter machine is a second M1-scale construction; it is honestly deferred, not faked.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinReduce

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinTransition
open PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics
open PallLean.Paper93.DeepMath.PathB.CookLevinWrite
open PallLean.Paper93.DeepMath.PathB.CookLevinAssembly
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
open PallLean.Paper93.DeepMath.PathB.CookLevinConverse

/-! ## The head bound is free -/

/-- The tableau head bound is discharged unconditionally by `run_bounds`: `P := |x| + B` always works. -/
theorem head_bound (M : Machine) (x : List Bool) (B : ℕ) :
    ∀ t, t ≤ B → (run M t (init M x)).hd ≤ x.length + B := by
  intro t ht
  exact le_trans (run_bounds M x t).1 (by omega)

/-! ## The reduction map and its unconditional correctness -/

/-- The tableau reduction of `(M, x, clock)`: the full tableau over `[0, clock]` with cell width `|x| + clock`. -/
noncomputable def tableauReduction (M : Machine) (x : List Bool) (clock : ℕ) : Formula :=
  fullTableau M x (x.length + clock) clock

/-- **Unconditional reduction correctness.**  The tableau of `(M, x, clock)` is satisfiable iff `M` halts-and-accepts
`x` within `clock` steps.  (The head bound is discharged by `run_bounds`.) -/
theorem tableauReduction_correct (M : Machine) (x : List Bool) (clock : ℕ) :
    Satisfiable (tableauReduction M x clock)
      ↔ (HaltsBy M x clock ∧ decideOut M x clock = true) := by
  unfold tableauReduction HaltsBy decideOut
  exact fullTableau_correct M x (x.length + clock) clock (head_bound M x clock)

/-! ## Clause-length facts -/

theorem cellCopyClause_length (t p : ℕ) : (cellCopyClause t p).length = 2 := rfl

theorem dynamicsClause_length (M : Machine) (t : ℕ) (q : Fin (Fintype.card M.State)) (p : ℕ) (b : Bool) :
    (dynamicsClause M t q p b).length = 2 := rfl

theorem writeClause_length (M : Machine) (t : ℕ) (q : Fin (Fintype.card M.State)) (p : ℕ) (b : Bool) :
    (writeClause M t q p b).length = 1 := rfl

/-! ## Size lemmas for the gathering primitives -/

/-- `atMostOne` over `n` variables has at most `n²` clauses (the triangular number `n(n-1)/2 ≤ n²`). -/
theorem atMostOne_length_le (vars : List ℕ) : (atMostOne vars).length ≤ vars.length * vars.length := by
  induction vars with
  | nil => simp [atMostOne]
  | cons v vs ih =>
    rw [atMostOne, List.length_append, List.length_map, List.length_cons]
    nlinarith [ih]

/-- `oneHot` over `n` variables has at most `n² + 1` clauses. -/
theorem oneHot_length_le (vars : List ℕ) : (oneHot vars).length ≤ vars.length * vars.length + 1 := by
  rw [oneHot, List.length_cons]
  have := atMostOne_length_le vars
  omega

/-- A gathered family `bigAnd (l.map f)` has at most `|l| · K` clauses when each member has `≤ K`. -/
theorem bigAnd_map_length_le {α : Type} (l : List α) (f : α → Formula) (K : ℕ)
    (h : ∀ i ∈ l, (f i).length ≤ K) : (bigAnd (l.map f)).length ≤ l.length * K := by
  rw [bigAnd, List.length_flatten, List.map_map]
  have hb : (l.map (List.length ∘ f)).sum ≤ (l.map (List.length ∘ f)).length • K := by
    apply List.sum_le_card_nsmul
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    exact h i hi
  rwa [List.length_map, smul_eq_mul] at hb

/-! ## Per-family size bounds -/

theorem initFormula_length_le (M : Machine) (x : List Bool) (P : ℕ) :
    (initFormula M x P).length ≤ P + 3 := by
  simp only [initFormula, fixBits, List.length_map, List.length_cons, List.length_range]
  omega

theorem acceptFormula_length_le (M : Machine) (B : ℕ) : (acceptFormula M B).length ≤ 1 := by
  simp [acceptFormula]

theorem headFamily_length_le (P B : ℕ) :
    (headFamily P B).length ≤ (B + 1) * ((P + 1) * (P + 1) + 1) := by
  rw [headFamily]
  have := bigAnd_map_length_le (List.range (B + 1)) (fun t => headOneHot t P) ((P + 1) * (P + 1) + 1) (by
    intro t _
    unfold headOneHot
    exact le_trans (oneHot_length_le _) (le_of_eq (by rw [List.length_map, List.length_range])))
  rwa [List.length_range] at this

theorem stateFamily_length_le (M : Machine) (B : ℕ) :
    (stateFamily M B).length ≤ (B + 1) * (Fintype.card M.State * Fintype.card M.State + 1) := by
  rw [stateFamily]
  have := bigAnd_map_length_le (List.range (B + 1)) (fun t => stateOneHot M t)
    (Fintype.card M.State * Fintype.card M.State + 1) (by
      intro t _
      unfold stateOneHot
      exact le_trans (oneHot_length_le _) (le_of_eq (by rw [List.length_map, List.length_range])))
  rwa [List.length_range] at this

theorem tapeFamily_length_le (P B : ℕ) : (tapeFamily P B).length ≤ B * ((P + 1) * 2) := by
  rw [tapeFamily]
  have := bigAnd_map_length_le (List.range B)
    (fun t => bigAnd ((List.range (P + 1)).map (fun p => cellCopyClause t p))) ((P + 1) * 2) (by
      intro t _
      have h2 := bigAnd_map_length_le (List.range (P + 1)) (fun p => cellCopyClause t p) 2 (by
        intro p _; exact le_of_eq (cellCopyClause_length t p))
      rwa [List.length_range] at h2)
  rwa [List.length_range] at this

theorem dynamicsFamily_length_le (M : Machine) (P B : ℕ) :
    (dynamicsFamily M P B).length ≤ B * (Fintype.card M.State * ((P + 1) * 4)) := by
  rw [dynamicsFamily]
  have := bigAnd_map_length_le (List.range B)
    (fun t => bigAnd ((List.finRange (Fintype.card M.State)).map (fun q =>
      bigAnd ((List.range (P + 1)).map (fun p => bigAnd ([false, true].map (fun b => dynamicsClause M t q p b)))))))
    (Fintype.card M.State * ((P + 1) * 4)) (by
      intro t _
      have h2 := bigAnd_map_length_le (List.finRange (Fintype.card M.State))
        (fun q => bigAnd ((List.range (P + 1)).map (fun p =>
          bigAnd ([false, true].map (fun b => dynamicsClause M t q p b)))))
        ((P + 1) * 4) (by
          intro q _
          have h3 := bigAnd_map_length_le (List.range (P + 1))
            (fun p => bigAnd ([false, true].map (fun b => dynamicsClause M t q p b))) 4 (by
              intro p _
              have h4 := bigAnd_map_length_le [false, true] (fun b => dynamicsClause M t q p b) 2 (by
                intro b _; exact le_of_eq (dynamicsClause_length M t q p b))
              simpa using h4)
          rwa [List.length_range] at h3)
      rwa [List.length_finRange] at h2)
  rwa [List.length_range] at this

theorem writeFamily_length_le (M : Machine) (P B : ℕ) :
    (writeFamily M P B).length ≤ B * (Fintype.card M.State * ((P + 1) * 2)) := by
  rw [writeFamily]
  have := bigAnd_map_length_le (List.range B)
    (fun t => bigAnd ((List.finRange (Fintype.card M.State)).map (fun q =>
      bigAnd ((List.range (P + 1)).map (fun p => bigAnd ([false, true].map (fun b => writeClause M t q p b)))))))
    (Fintype.card M.State * ((P + 1) * 2)) (by
      intro t _
      have h2 := bigAnd_map_length_le (List.finRange (Fintype.card M.State))
        (fun q => bigAnd ((List.range (P + 1)).map (fun p =>
          bigAnd ([false, true].map (fun b => writeClause M t q p b)))))
        ((P + 1) * 2) (by
          intro q _
          have h3 := bigAnd_map_length_le (List.range (P + 1))
            (fun p => bigAnd ([false, true].map (fun b => writeClause M t q p b))) 2 (by
              intro p _
              have h4 := bigAnd_map_length_le [false, true] (fun b => writeClause M t q p b) 1 (by
                intro b _; exact le_of_eq (writeClause_length M t q p b))
              simpa using h4)
          rwa [List.length_range] at h3)
      rwa [List.length_finRange] at h2)
  rwa [List.length_range] at this

/-! ## The polynomial output-size bound -/

/-- An explicit polynomial bound on the tableau size in `(P, B, s = card State)`. -/
def tableauSizeBound (P B s : ℕ) : ℕ :=
  (P + 3) + (B + 1) * ((P + 1) * (P + 1) + 1) + (B + 1) * (s * s + 1) + B * ((P + 1) * 2)
    + B * (s * ((P + 1) * 4)) + 1 + B * (s * ((P + 1) * 2))

theorem fullTableau_length_le (M : Machine) (x : List Bool) (P B : ℕ) :
    (fullTableau M x P B).length ≤ tableauSizeBound P B (Fintype.card M.State) := by
  have h1 := initFormula_length_le M x P
  have h2 := headFamily_length_le P B
  have h3 := stateFamily_length_le M B
  have h4 := tapeFamily_length_le P B
  have h5 := dynamicsFamily_length_le M P B
  have h6 := acceptFormula_length_le M B
  have h7 := writeFamily_length_le M P B
  simp only [fullTableau, fullFormula, assembledFormula, List.length_append]
  unfold tableauSizeBound
  omega

/-- **Polynomial output size.**  The reduction's output has size bounded by an explicit polynomial in `|x|`, `clock`,
and `card M.State` — degree `≤ 3`, and (for a fixed machine, `card` constant) polynomial in the input size. -/
theorem tableauReduction_length_le (M : Machine) (x : List Bool) (clock : ℕ) :
    (tableauReduction M x clock).length
      ≤ tableauSizeBound (x.length + clock) clock (Fintype.card M.State) :=
  fullTableau_length_le M x (x.length + clock) clock

end PallLean.Paper93.DeepMath.PathB.CookLevinReduce
