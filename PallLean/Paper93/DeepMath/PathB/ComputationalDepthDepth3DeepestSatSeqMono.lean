import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ActiveMonotone
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LeafClauses

/-!
# Clause-order monotonicity of `deepestSatSeq` (branch `razborov-recoverRho-wip`)

The forward-replay reconstruction (`deepestSatSeq_recover`) processes clauses in `cs`-order.  This
file proves the structural fact that *justifies* that: along the deepest branch the active clause
**never backtracks**, so every clause recorded in `deepestSatSeq cs F σ` lies in the **active suffix**
`activeSuffix cs σ` — the tail of `cs` headed by the current active clause.  Equivalently, no recorded
clause precedes the active clause, and the active region only shrinks from the front as the path
descends.  This is the clause-order monotonicity the dynamic-block simulation relies on; it is the
deepestSatSeq-level lift of the proved per-step `activeTerm_fixVar_no_backtrack`.

* `activeSuffix cs σ` — `cs.dropWhile (¬ activePred σ)`, the tail of `cs` from the active clause
  (`head?_activeSuffix`: its head is `activeTerm cs σ`).  Position-based, so it composes under the
  recursion via `IsSuffix` transitivity — no clause-distinctness (`Nodup`) hypothesis is needed.
* `activeSuffix_fixVar_suffix` — **per-step monotonicity**: fixing a free variable can only move the
  active clause forward, so `activeSuffix cs (fixVar σ v b) <:+ activeSuffix cs σ`.  Driven by the
  pointwise antitonicity `activePred_anti` (`termFalsified` is monotone and `freeLits` antitone under
  `fixVar`) plus the generic `dropWhile_suffix_of_imp`.
* `deepestSatSeq_clause_mem_activeSuffix` — **the monotonicity**: every clause of `deepestSatSeq cs F σ`
  is in `activeSuffix cs σ`.  Induction on the canonical fuel recursion mirroring
  `deepestSatSeq_clause_mem_cs`; the satisfy-step head is the active clause (front of the suffix), and
  the recursive clauses transport back along `activeSuffix_fixVar_suffix`.

Clean axioms target; no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-! ## Generic `List.dropWhile` lemmas -/

/-- If the drop-condition `q` implies `q'` pointwise, then `dropWhile q'` drops at least as far, so it
is a suffix of `dropWhile q`. -/
theorem dropWhile_suffix_of_imp {α : Type*} {q q' : α → Bool}
    (himp : ∀ x, q x = true → q' x = true) :
    ∀ (l : List α), l.dropWhile q' <:+ l.dropWhile q
  | [] => by simp
  | a :: t => by
    by_cases hq : q a = true
    · rw [List.dropWhile_cons_of_pos (by simp [himp a hq]),
          List.dropWhile_cons_of_pos (by simp [hq])]
      exact dropWhile_suffix_of_imp himp t
    · simp only [Bool.not_eq_true] at hq
      by_cases hq' : q' a = true
      · rw [List.dropWhile_cons_of_pos (by simp [hq']),
            List.dropWhile_cons_of_neg (by simp [hq])]
        exact (List.dropWhile_suffix q').trans (List.suffix_cons a t)
      · simp only [Bool.not_eq_true] at hq'
        rw [List.dropWhile_cons_of_neg (by simp [hq']),
            List.dropWhile_cons_of_neg (by simp [hq])]

/-- `find? p` is the head of `dropWhile (¬ p)`: both name the first element satisfying `p`. -/
theorem find?_eq_head?_dropWhile_not {α : Type*} (p : α → Bool) :
    ∀ (l : List α), l.find? p = (l.dropWhile (fun x => !p x)).head?
  | [] => rfl
  | a :: t => by
    by_cases h : p a = true
    · rw [List.find?_cons_of_pos h, List.dropWhile_cons_of_neg (by simp [h])]; rfl
    · simp only [Bool.not_eq_true] at h
      rw [List.find?_cons_of_neg (by simp [h]), List.dropWhile_cons_of_pos (by simp [h])]
      exact find?_eq_head?_dropWhile_not p t

/-! ## Antitonicity of the active predicate under `fixVar` -/

/-- A literal free after a step was free before it (fixing one more variable cannot free a literal). -/
theorem litFree_fixVar_imp {σ : Fin n → Option Bool} {v : Fin n} {b : Bool} {ℓ : Rung4Literal n}
    (h : Depth3.litFree (fixVar σ v b) ℓ = true) : Depth3.litFree σ ℓ = true := by
  rw [litFree_var] at h ⊢
  by_cases hv : litVar ℓ = v
  · rw [hv, fixVar, Function.update_self] at h; simp at h
  · rw [fixVar, Function.update_of_ne hv] at h; exact h

/-- The free literals of a clause shrink under a `fixVar` step. -/
theorem freeLits_fixVar_subset {σ : Fin n → Option Bool} {v : Fin n} {b : Bool} {C : Clause n} :
    SwitchingCounting.freeLits (fixVar σ v b) C ⊆ SwitchingCounting.freeLits σ C := by
  intro ℓ h
  rw [SwitchingCounting.freeLits, List.mem_filter] at h ⊢
  exact ⟨h.1, litFree_fixVar_imp h.2⟩

/-- The `find?` predicate identifying the active clause: not falsified and has a free literal. -/
def activePred (σ : Fin n → Option Bool) (U : Clause n) : Bool :=
  !SwitchingCounting.termFalsified σ U && decide (0 < (SwitchingCounting.freeLits σ U).length)

/-- **Antitonicity.**  If a clause is active (passes the predicate) after fixing a free variable, it
was active before: `termFalsified` is monotone (a falsified clause stays falsified) and `freeLits` is
antitone (`freeLits_fixVar_subset`). -/
theorem activePred_anti {σ : Fin n → Option Bool} {v : Fin n} {b : Bool} (hv : σ v = none)
    {U : Clause n} (h : activePred (fixVar σ v b) U = true) : activePred σ U = true := by
  simp only [activePred, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h ⊢
  obtain ⟨hf, hfree⟩ := h
  refine ⟨?_, ?_⟩
  · cases hcx : SwitchingCounting.termFalsified σ U with
    | false => rfl
    | true => rw [termFalsified_fixVar_of_free hcx hv] at hf; exact absurd hf (by simp)
  · obtain ⟨ℓ, hℓ⟩ := List.exists_mem_of_ne_nil _ (List.length_pos_iff_ne_nil.mp hfree)
    exact List.length_pos_of_mem (freeLits_fixVar_subset hℓ)

/-! ## The active suffix and its monotonicity -/

/-- **The active suffix.**  The tail of `cs` starting at the active clause: every clause before it
fails the active predicate (is falsified / has no free literal). -/
def activeSuffix (cs : List (Clause n)) (σ : Fin n → Option Bool) : List (Clause n) :=
  cs.dropWhile (fun U => !activePred σ U)

/-- The head of the active suffix is the active clause. -/
theorem head?_activeSuffix {cs : List (Clause n)} {σ : Fin n → Option Bool}
    (hns : SwitchingCounting.anyTermSat cs σ = false) :
    (activeSuffix cs σ).head? = SwitchingCounting.activeTerm cs σ := by
  rw [activeSuffix, SwitchingCounting.activeTerm_eq_find hns]
  exact (find?_eq_head?_dropWhile_not (activePred σ) cs).symm

/-- **Per-step clause-order monotonicity.**  Fixing a free variable moves the active clause only
forward: the active suffix at `fixVar σ v b` is a suffix of the active suffix at `σ`. -/
theorem activeSuffix_fixVar_suffix {cs : List (Clause n)} {σ : Fin n → Option Bool}
    {v : Fin n} {b : Bool} (hv : σ v = none) :
    activeSuffix cs (fixVar σ v b) <:+ activeSuffix cs σ := by
  rw [activeSuffix, activeSuffix]
  apply dropWhile_suffix_of_imp
  intro U hU
  simp only [Bool.not_eq_true'] at hU ⊢
  cases hca : activePred (fixVar σ v b) U with
  | true => rw [activePred_anti hv hca] at hU; exact absurd hU (by simp)
  | false => rfl

/-! ## The monotonicity of `deepestSatSeq` -/

/-- **Clause-order monotonicity of `deepestSatSeq`.**  Every clause recorded in `deepestSatSeq cs F σ`
lies in the active suffix `activeSuffix cs σ` — no recorded clause precedes the active clause, and the
active region only advances along the descent.  Induction on the canonical fuel recursion: the
satisfy-step head is the active clause (the front of the suffix), and the recursive clauses transport
back across `activeSuffix_fixVar_suffix`. -/
theorem deepestSatSeq_clause_mem_activeSuffix (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) {C : Clause n} {p : ℕ},
      (C, p) ∈ deepestSatSeq cs F σ → C ∈ activeSuffix cs σ := by
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
          -- the head free literal's variable is free under `σ`
          have hℓmem : ℓ ∈ SwitchingCounting.freeLits σ T := List.mem_of_mem_head? hh
          have hℓfree : Depth3.litFree σ ℓ = true := (List.mem_filter.mp hℓmem).2
          have hv : σ (litVar ℓ) = none := by
            rw [litFree_var] at hℓfree
            cases hσ : σ (litVar ℓ) with
            | none => rfl
            | some _ => rw [hσ] at hℓfree; simp at hℓfree
          -- `T` is the head of the active suffix
          have hThead : T ∈ activeSuffix cs σ := by
            have hhd := head?_activeSuffix (cs := cs) (σ := σ) hany
            rw [hact] at hhd
            exact List.mem_of_mem_head? hhd
          -- the canonical recursion body for either deepest bit
          have body : ∀ b : Bool,
              deepestSatSeq cs (F + 1) σ =
                (if SwitchingCounting.litFalse (fixVar σ (litVar ℓ) b) ℓ
                  then id else List.cons (T, SwitchingCounting.pivotPosOf cs σ))
                  (deepestSatSeq cs F (fixVar σ (litVar ℓ) b)) → C ∈ activeSuffix cs σ := by
            intro b hSeq
            rw [hSeq] at hmem
            by_cases hf : SwitchingCounting.litFalse (fixVar σ (litVar ℓ) b) ℓ = true
            · rw [if_pos hf, id_eq] at hmem
              exact (activeSuffix_fixVar_suffix hv).subset (ih (fixVar σ (litVar ℓ) b) hmem)
            · rw [Bool.not_eq_true] at hf
              rw [if_neg (by rw [hf]; simp), List.mem_cons] at hmem
              rcases hmem with heq | htl
              · have hCT : C = T := congrArg Prod.fst heq
                rw [hCT]; exact hThead
              · exact (activeSuffix_fixVar_suffix hv).subset (ih (fixVar σ (litVar ℓ) b) htl)
          by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
              (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
          · refine body false ?_
            rw [deepestSatSeq]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]; rw [if_pos hd]
          · refine body true ?_
            rw [deepestSatSeq]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]; rw [if_neg hd]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.activeSuffix_fixVar_suffix
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSatSeq_clause_mem_activeSuffix
