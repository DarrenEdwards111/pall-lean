import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3OneRoundDual
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3IteratedReduction

/-!
# AC⁰ reduction, foundation 39: the depth-3 assembly — and the vacuity it exposes (branch only)

The depth-3 pipeline assembled end-to-end (it compiles cleanly), **and the precise gap it exposes**.  The
structural chain runs:

1. **round 1 (dual)** — one switching round (`one_round_dual_p_fifth`, brick 38) collapses the
   `OR`-of-`CNF`s to a single bottom `DNF` `D₁` on a restriction `ρ₁`, keeping `> k₁` survivors;
2. **terminal round** — a second switching (`one_round_exists_p_fifth_dim`, brick 36) on the single gate
   `{D₁}` makes its canonical tree shallow on `ρ₂ ⊇ ρ₁`, keeping `> k₂ ≥ s₂` survivors;
3. **chaining** — `iterated_not_parity` (brick 37) folds the reduction `C₀ ⟶ dnf D₁` and the shallow
   terminal tree into: `C₀` does not compute parity on `ρ₂`'s subcube.

* `parity_not_depth3` — `∃ x, (gOr (Cs.map cnf)).eval x ≠ parity x`, **conditional on** the size/dimension
  budgets.

## HONEST STATUS — this is NOT yet a genuine lower bound

The budgets of `parity_not_depth3` are **jointly unsatisfiable** under the current label count, proved in
`depth3_budgets_unsatisfiable`.  Root cause: the canonical tree's eval-correctness forces the fuel `n < F`,
so the label count `(4^w+1)^F ≥ 2^F` makes the terminal budget force `s₂ > F > n`, while the dimension /
`s₂ ≤ k₂` budgets force `s₂ ≤ k₂ < k₁ < n` — contradiction.  Hence `parity_not_depth3` is **vacuous**: the
pipeline is structurally assembled, but it certifies nothing about real circuits yet.

What's missing is the **tighter `(2w)^s` switching count** (tied to the canonical tree's *depth* `s`, not
its *fuel* `F`), the long-flagged remaining gate of the canonical-tree bricks.  With that count the budget
becomes `s ≳ log(#gates)` (independent of `F`), survivors `≈ p·n > s` for large `n`, and the bound is
genuine.  We state this honestly rather than present a vacuous theorem as a result.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered Classical

variable {n : ℕ}

/-- **The depth-3 assembly (conditional; budgets vacuous — see `depth3_budgets_unsatisfiable`).**  An `OR`
of `CNF` gates `Cs` (each `Consistent`, distinct-variable, width `≤ w`) does not compute parity, *given* the
round-1 budget (`hdeep₁`, `hdim₁`), the terminal budget (`hdeep₂`, `hdim₂`), and `s₂ ≤ k₂`.  The pipeline is
structurally complete, but these budgets cannot all hold under the current `(4^w+1)^F` label count, so this
is not yet a genuine bound — the tighter `(2w)^s` count is required. -/
theorem parity_not_depth3 (w F s₁ s₂ k₁ k₂ : ℕ) (hF : n < F)
    (Cs : List (List (Clause n)))
    (hcons : ∀ c ∈ Cs, ∀ C ∈ c, Consistent C)
    (hnd : ∀ c ∈ Cs, ∀ C ∈ c, (C.lits.map litVarOf).Nodup)
    (hw : ∀ c ∈ Cs, ∀ C ∈ c, C.lits.length ≤ w)
    (hdeep₁ : 2 * ((Cs.toFinset.image negDNF).card
        * Fintype.card (Fin F → Option (Fin w → Option (Option Bool)))) < 2 ^ s₁)
    (hdim₁ : 7 * (k₁ + 1) ≤ n)
    (hdeep₂ : 2 * (1 * Fintype.card (Fin F → Option (Fin s₁ → Option (Option Bool)))) < 2 ^ s₂)
    (hdim₂ : 7 * (k₂ + 1) ≤ k₁)
    (hs₂ : s₂ ≤ k₂) :
    ∃ x : Fin n → Bool, (gOr (Cs.map cnf)).eval x ≠ DTree.parity x := by
  have hstars0 : stars (fun _ : Fin n => (none : Option Bool)) = n := by
    rw [stars, freeVars]
    simp
  -- round 1: collapse OR-of-CNFs to a single DNF D₁
  obtain ⟨ρ₁, _hext₁, heq₁, hstars₁, hwidth₁, hwf₁⟩ :=
    one_round_dual_p_fifth w F s₁ k₁ hF (fun _ => none) Cs hcons hnd hw hdeep₁
      (by rw [hstars0]; exact hdim₁)
  set D₁ : List (Clause n) :=
    Cs.flatMap (fun c => dtreeToDNF (DTree.negTree (canonicalDTree (negDNF c) w F ρ₁))) with hD₁
  -- terminal round: switch the single gate D₁ shallow on ρ₂ ⊇ ρ₁
  obtain ⟨ρ₂, hext₂, hshallow₂, hstars₂⟩ :=
    one_round_exists_p_fifth_dim s₁ F s₂ k₂ ρ₁ {D₁}
      (fun g hg T hT => by rw [Finset.mem_singleton] at hg; subst hg; exact (hwf₁ T hT).1)
      (fun g hg T hT => by rw [Finset.mem_singleton] at hg; subst hg; exact (hwf₁ T hT).2)
      (fun g hg T hT => by rw [Finset.mem_singleton] at hg; subst hg; exact le_of_lt (hwidth₁ T hT))
      (by rw [Finset.card_singleton]; exact hdeep₂)
      (by omega)
  have hshD₁ : (canonicalDTree D₁ s₁ F ρ₂).depth < s₂ :=
    hshallow₂ D₁ (Finset.mem_singleton.mpr rfl)
  -- assemble the round sequence
  let C : ℕ → Layered n := fun i => match i with | 0 => gOr (Cs.map cnf) | _ + 1 => dnf D₁
  let ρ : ℕ → (Fin n → Option Bool) := fun i => match i with | 0 => ρ₁ | _ + 1 => ρ₂
  have hext : ∀ i, Extends (ρ i) ρ₂ := by
    intro i; cases i with
    | zero => exact hext₂
    | succ j => exact fun v b hb => hb
  have heq : ∀ i, EquivOn (ρ i) (C i) (C (i + 1)) := by
    intro i; cases i with
    | zero => exact heq₁
    | succ j => exact fun x _ => rfl
  have hsf : stars ρ₂ < F :=
    lt_of_le_of_lt (by rw [stars]; exact le_trans (Finset.card_le_univ _) (by simp)) hF
  have hfinal := iterated_not_parity C ρ ρ₂ 1 D₁ s₁ F hext heq rfl hsf (by omega)
  have hfinal' : ¬ ∀ x, DTree.agreeRestriction ρ₂ x → (gOr (Cs.map cnf)).eval x = DTree.parity x :=
    hfinal
  push_neg at hfinal'
  obtain ⟨x, _, hx⟩ := hfinal'
  exact ⟨x, hx⟩

/-- **The depth-3 budgets are jointly UNSATISFIABLE under the current `(4^w+1)^F` label count.**  The fuel
must exceed the survivors (`n < F`), so the terminal label count `(4^{s₁}+1)^F` forces `s₂` above `F > n`;
but `s₂ ≤ k₂ < k₁ < n` via the dimension/`s₂≤k₂` budgets — contradiction.  Hence `parity_not_depth3` is
**vacuous**: it is the structurally-assembled pipeline, not yet a genuine lower bound.  Closing it needs the
tighter `(2w)^s` switching count (tied to tree depth, not fuel) — the long-flagged remaining gate. -/
theorem depth3_budgets_unsatisfiable (F s₁ s₂ k₁ k₂ : ℕ) (hF : n < F)
    (hdeep₂ : 2 * (1 * Fintype.card (Fin F → Option (Fin s₁ → Option (Option Bool)))) < 2 ^ s₂)
    (hdim₁ : 7 * (k₁ + 1) ≤ n) (hdim₂ : 7 * (k₂ + 1) ≤ k₁) (hs₂ : s₂ ≤ k₂) : False := by
  have hpos : 0 < Fintype.card (Fin s₁ → Option (Option Bool)) := Fintype.card_pos
  -- |Labels| = (card (Option (Fin s₁ → Option (Option Bool))))^F ≥ 2^F
  have hcard : 2 ^ F ≤ Fintype.card (Fin F → Option (Fin s₁ → Option (Option Bool))) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    refine Nat.pow_le_pow_left ?_ F
    rw [Fintype.card_option]; omega
  have hFs₂ : 2 ^ F < 2 ^ s₂ := by omega
  have hlt : F < s₂ := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hFs₂
  -- F < s₂ ≤ k₂ < k₁ < n < F : contradiction
  omega

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_depth3
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.depth3_budgets_unsatisfiable
