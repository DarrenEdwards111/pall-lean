import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestSatSeqClause
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestStep

/-!
# Concrete clause-enumeration from the leaf

The block decoder must list the clauses of `deepestSatSeq` in `cs`-order, from the end-state.  This
file gives the concrete enumeration `leafClauses` — the `cs`-clauses that are falsified at the leaf or
are the leaf's active clause — and locates `deepestSatSeq`'s clauses inside it.

* `deepestSatSeq_clause_mem_cs` — every clause recorded in `deepestSatSeq` is a member of `cs`.
* `leafClauses cs π` — the `cs`-clauses falsified at `π` or active at `π` (in `cs`-order).
* `deepestSatSeq_clause_mem_leafClauses` — every clause of `deepestSatSeq` (leaf unsatisfied) appears
  in `leafClauses cs (deepestEnd …)`.

So the decoder's clause list is the concrete, end-state-computable `leafClauses`; what remains is
assigning the label's position-runs to its (relevant, ordered) entries.  Not faked.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- `Clause n` is a single-field structure over `List (Rung4Literal n)`, hence has decidable equality. -/
instance instDecidableEqClause : DecidableEq (Clause n) := fun a b =>
  decidable_of_iff (a.lits = b.lits) (by cases a; cases b; simp)

/-- Every clause recorded in `deepestSatSeq` is a member of `cs` (it is an active clause). -/
theorem deepestSatSeq_clause_mem_cs (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) {C : Clause n} {p : ℕ},
      (C, p) ∈ deepestSatSeq cs F σ → C ∈ cs := by
  intro F
  induction F with
  | zero => intro σ C p hmem; rw [deepestSatSeq] at hmem; exact absurd hmem (by simp)
  | succ F ih =>
    intro σ C p hmem
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => rw [deepestSatSeq] at hmem; simp only [hany, if_true] at hmem; exact absurd hmem (by simp)
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        rw [deepestSatSeq] at hmem
        simp only [hany, Bool.false_eq_true, if_false, hact] at hmem; exact absurd hmem (by simp)
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none =>
          rw [deepestSatSeq] at hmem
          simp only [hany, Bool.false_eq_true, if_false, hact, hh] at hmem; exact absurd hmem (by simp)
        | some ℓ =>
          have body : ∀ b : Bool,
              deepestSatSeq cs (F + 1) σ =
                (if SwitchingCounting.litFalse (fixVar σ (litVar ℓ) b) ℓ
                  then id else List.cons (T, SwitchingCounting.pivotPosOf cs σ))
                  (deepestSatSeq cs F (fixVar σ (litVar ℓ) b)) → C ∈ cs := by
            intro b hSeq
            rw [hSeq] at hmem
            by_cases hf : SwitchingCounting.litFalse (fixVar σ (litVar ℓ) b) ℓ = true
            · rw [if_pos hf, id_eq] at hmem; exact ih (fixVar σ (litVar ℓ) b) hmem
            · rw [Bool.not_eq_true] at hf
              rw [if_neg (by rw [hf]; simp), List.mem_cons] at hmem
              rcases hmem with heq | htl
              · have hCT : C = T := congrArg Prod.fst heq
                rw [hCT]; exact SwitchingCounting.activeTerm_mem hact
              · exact ih (fixVar σ (litVar ℓ) b) htl
          by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
              (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
          · refine body false ?_
            rw [deepestSatSeq]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]; rw [if_pos hd]
          · refine body true ?_
            rw [deepestSatSeq]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]; rw [if_neg hd]

/-- The `cs`-clauses readable from the end-state `π`: those falsified at `π` or active at `π`. -/
def leafClauses (cs : List (Clause n)) (π : Fin n → Option Bool) : List (Clause n) :=
  cs.filter (fun C => SwitchingCounting.termFalsified π C ||
    decide (SwitchingCounting.activeTerm cs π = some C))

/-- **The decode's clauses are enumerated by `leafClauses`.**  Every clause of `deepestSatSeq` (when
the leaf is unsatisfied) appears in `leafClauses cs (deepestEnd cs F σ)`. -/
theorem deepestSatSeq_clause_mem_leafClauses (cs : List (Clause n)) (F : ℕ)
    (σ : Fin n → Option Bool) {C : Clause n} {p : ℕ}
    (hmem : (C, p) ∈ deepestSatSeq cs F σ)
    (hsat : SwitchingCounting.anyTermSat cs (deepestEnd cs F σ) = false) :
    C ∈ leafClauses cs (deepestEnd cs F σ) := by
  have hCcs : C ∈ cs := deepestSatSeq_clause_mem_cs cs F σ hmem
  have hleaf := deepestSatSeq_clause_leaf cs F σ hmem hsat
  rw [leafClauses, List.mem_filter]
  refine ⟨hCcs, ?_⟩
  rcases hleaf with hf | ha
  · rw [hf]; rfl
  · rw [ha]; simp

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSatSeq_clause_mem_cs
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSatSeq_clause_mem_leafClauses
