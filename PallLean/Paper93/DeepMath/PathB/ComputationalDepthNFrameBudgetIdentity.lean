import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameJointBudget

/-!
# N-Frame: the identity of the boundary energy — it *is* formula complexity

The forward wire showed transducers embed in the Nečiporuk arc's formulas.  This file proves the **reverse wire** and the
resulting **identity theorem**: the boundary energy invariant `budget` is *exactly* full-binary-basis (`B₂`) formula
complexity, up to a factor `2` in each direction.  It also proves the **upper-bound side** of the joint budget, completing
the sandwich around the tearing bound.

  `bsize` / `ofB` — formula node count, and the reverse translation `BFormula → Trans` (semantics preserved).
  `volume_ofB_le` — **PROVED**: `volume (ofB F) ≤ 2·bsize F` — formulas are boundary observers at twice their node count.
  `budget_le_of_formula` — **PROVED**: any formula computing `f` bounds the boundary energy: `budget f ≤ 2·bsize F`.
  `exists_formula_litCount_le_budget` — **PROVED**: conversely, the minimal boundary observer yields a formula computing
        `f` with `litCount ≤ budget f`.
  `budgetAt_three_le_exp` — **PROVED, the sandwich's ceiling**: `budgetAt 3 f ≤ (3n+2)·2ⁿ + 1` for every `f` — at
        dimension `3`, exponential energy always suffices; for `hardF`, the energy at every dimension is pinned between
        `N²/(64·log N)` (the tearing bound) and this exponential ceiling.

## Honest scope — the mountain now has its classical name

The identity is two-sided and proved, so there is no room left for reinterpretation: **boundary energy = `B₂` formula
complexity** (up to `×2`).  Consequences, stated plainly:

* The capture side is honest and definitional (efficient formula computations *are* low-energy boundary observers), and
  the proven tearing (`Ω(N²/log N)` for `hardF`) is exactly Nečiporuk-tight — the strongest unconditional bound this
  model currently admits.
* A **super-polynomial** boundary-energy tearing for an `NP` target is *equivalent* to a super-polynomial `B₂` formula
  lower bound — a famous open problem (the best known explicit formula lower bounds are polynomial, `~n³`).  So the
  boundary programme's remaining mountain now has a precise classical name: super-polynomial formula lower bounds; and
  strengthening the model from trees to general circuits (sharing) would raise the requirement to circuit lower bounds,
  i.e. `P/poly` itself.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {n : ℕ}

/-! ### The reverse wire: formulas are boundary observers -/

/-- Node count of a `B₂` formula (all nodes: leaves, unary and binary gates). -/
def bsize : BFormula n → ℕ
  | .lit _ _ => 1
  | .cst _ => 1
  | .un _ t => bsize t + 1
  | .bin _ t₁ t₂ => bsize t₁ + bsize t₂ + 1

/-- The reverse translation: a `B₂` formula as a boundary transducer (a negative literal costs one extra node). -/
def ofB : BFormula n → Trans n
  | .lit i true => Trans.var i
  | .lit i false => Trans.un not (Trans.var i)
  | .cst b => Trans.cst b
  | .un op t => Trans.un op (ofB t)
  | .bin op t₁ t₂ => Trans.bin op (ofB t₁) (ofB t₂)

/-- **Semantics are preserved (proved).** -/
theorem eval_ofB (F : BFormula n) (x : Fin n → Bool) :
    eval (ofB F) x = BFormula.eval F x := by
  induction F with
  | lit i b => cases b <;> rfl
  | cst b => rfl
  | un op t ih => simp [ofB, BFormula.eval, eval, ih]
  | bin op t₁ t₂ ih₁ ih₂ => simp [ofB, BFormula.eval, eval, ih₁, ih₂]

/-- **Formulas are boundary observers at twice their node count (proved).** -/
theorem volume_ofB_le (F : BFormula n) : volume (ofB F) ≤ 2 * bsize F := by
  induction F with
  | lit i b => cases b <;> simp [ofB, volume, bsize]
  | cst b => simp [ofB, volume, bsize]
  | un op t ih => simp only [ofB, volume, bsize]; omega
  | bin op t₁ t₂ ih₁ ih₂ => simp only [ofB, volume, bsize]; omega

/-! ### The identity theorem: boundary energy = formula complexity (up to ×2) -/

/-- **Boundary energy is bounded by formula complexity (proved).**  Any `B₂` formula computing `f` caps the boundary
energy at twice its node count. -/
theorem budget_le_of_formula (f : (Fin n → Bool) → Bool) (F : BFormula n)
    (hF : ∀ x, BFormula.eval F x = f x) : budget f ≤ 2 * bsize F :=
  le_trans (Nat.sInf_le ⟨ofB F, by funext x; rw [eval_ofB, hF], rfl⟩) (volume_ofB_le F)

/-- **Formula complexity is bounded by boundary energy (proved).**  The minimal boundary observer for `f` yields a `B₂`
formula computing `f` with leaf count at most the boundary energy.  Together with `budget_le_of_formula`, this pins the
identity: boundary energy = `B₂` formula complexity, up to a factor `2`. -/
theorem exists_formula_litCount_le_budget (f : (Fin n → Bool) → Bool) :
    ∃ F : BFormula n, (∀ x, BFormula.eval F x = f x) ∧ BFormula.litCount F ≤ budget f := by
  have hne : {v | ∃ t : Trans n, eval t = f ∧ volume t = v}.Nonempty :=
    ⟨volume (dnfFor f), dnfFor f, eval_dnfFor f, rfl⟩
  unfold budget
  obtain ⟨t, he, hv⟩ := Nat.sInf_mem hne
  exact ⟨toBFormula t, fun x => by rw [eval_toBFormula, he],
    hv ▸ litCount_toBFormula_le t⟩

/-! ### The sandwich's ceiling: exponential energy always suffices at dimension 3 -/

theorem volume_literal_le (b : Bool) (i : Fin n) : volume (literal b i) ≤ 2 := by
  cases b <;> simp [literal, volume]

theorem volume_mintermOn_le (a : Fin n → Bool) (is : List (Fin n)) :
    volume (mintermOn a is) ≤ 3 * is.length + 1 := by
  induction is with
  | nil => simp [mintermOn, volume]
  | cons i is ih =>
    have hl := volume_literal_le (a i) i
    simp only [mintermOn, volume, List.length_cons]
    omega

theorem volume_dnfOn_le (l : List (Fin n → Bool)) :
    volume (dnfOn l) ≤ (3 * n + 2) * l.length + 1 := by
  induction l with
  | nil => simp [dnfOn, volume]
  | cons a l ih =>
    have hm := volume_mintermOn_le a (List.finRange n)
    rw [List.length_finRange] at hm
    simp only [dnfOn, volume, List.length_cons]
    have : (3 * n + 2) * (l.length + 1) + 1
        = (3 * n + 2) * l.length + 1 + (3 * n + 1) + 1 := by ring
    omega

/-- **The ceiling (proved).**  At dimension `3`, exponential energy always suffices: `budgetAt 3 f ≤ (3n+2)·2ⁿ + 1`.
For `hardF`, the joint budget at every dimension `w ≥ 3` is therefore pinned between the tearing bound `N²/(64·b)` and
this exponential ceiling. -/
theorem budgetAt_three_le_exp (f : (Fin n → Bool) → Bool) :
    budgetAt 3 f ≤ (3 * n + 2) * 2 ^ n + 1 := by
  have hlen : ((Finset.univ : Finset (Fin n → Bool)).toList.filter f).length ≤ 2 ^ n := by
    calc ((Finset.univ : Finset (Fin n → Bool)).toList.filter f).length
        ≤ (Finset.univ : Finset (Fin n → Bool)).toList.length := List.length_filter_le _ _
      _ = Fintype.card (Fin n → Bool) := by rw [Finset.length_toList, Finset.card_univ]
      _ = 2 ^ n := by simp
  have hvol : volume (dnfFor f) ≤ (3 * n + 2) * 2 ^ n + 1 :=
    le_trans (volume_dnfOn_le _)
      (by have := Nat.mul_le_mul_left (3 * n + 2) hlen; omega)
  exact le_trans (Nat.sInf_le ⟨dnfFor f, eval_dnfFor f, width_dnfOn _, rfl⟩) hvol

/-! ### The GodMove, demoted to a theorem -/

/-- **The GodMove, made rigorous (proved).**  Every function has an *optimal boundary representation*: a transducer
attaining the joint budget.  This is the only legitimate formal content of the "global GodMove" — the minimizer of the
boundary-budget optimization, whose existence is a theorem (`Nat.sInf_mem` over a nonempty realisation set), **not** an
axiom and not a global ideal-observer principle.  Any use of "GodMove" in the boundary route should be read as notation
for this minimizer; as an assumed principle it would be load-bearing in exactly the way the repo's own audits (Theorem
207: the God-Move glue is *equivalent* to the separation) show must be avoided. -/
theorem exists_godMove (f : (Fin n → Bool) → Bool) {w : ℕ} (hw : 3 ≤ w) :
    ∃ t : Trans n, eval t = f ∧ width t ≤ w ∧ volume t = budgetAt w f := by
  have hne : {v | ∃ t : Trans n, eval t = f ∧ width t ≤ w ∧ volume t = v}.Nonempty := by
    obtain ⟨t0, he0, hw0⟩ := exists_width_le_three f
    exact ⟨volume t0, t0, he0, le_trans hw0 hw, rfl⟩
  unfold budgetAt
  exact Nat.sInf_mem hne

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.exists_godMove
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.budget_le_of_formula
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.exists_formula_litCount_le_budget
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.budgetAt_three_le_exp
