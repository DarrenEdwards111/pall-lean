import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestSatSeqMono

/-!
# Clause-order contiguity of `deepestSatSeq` (branch `razborov-recoverRho-wip`)

Strengthens the monotonicity of `ComputationalDepthDepth3DeepestSatSeqMono` to the definitive
**clause-order** statement: for `cs` with distinct clauses (`cs.Nodup`, which holds for the Tseitin/DNF
terms), the `cs`-indices of the clauses recorded in `deepestSatSeq cs F σ` are **non-decreasing**:

  `List.Pairwise (· ≤ ·) ((deepestSatSeq cs F σ).map (fun e => cs.idxOf e.1))`.

Sorted indices encode both facts the forward simulation needs at once:
* **order** — the clauses are visited in `cs`-order (never backtracking), and
* **contiguity** — equal indices are adjacent, so each clause's satisfy steps form one contiguous
  block (the dynamic block the simulation consumes label positions into until the clause resolves).

The proof lifts the per-step suffix monotonicity (`activeSuffix_fixVar_suffix`) and the membership
invariant (`deepestSatSeq_clause_mem_activeSuffix`) through the canonical fuel recursion: at a satisfy
step the head clause is the active clause `T`, at the front of `activeSuffix cs σ`, and every later
recorded clause lies in `activeSuffix cs σ`, hence at a `cs`-index `≥ idxOf T`
(`idxOf_activeTerm_le_of_mem_activeSuffix`, via the two `Nodup` tail-index lemmas).

Clean axioms target; no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-! ## Generic `Nodup` tail-index lemmas -/

/-- In a `Nodup` list, a member of `dropWhile p` sits at index `≥` the length of `takeWhile p`. -/
theorem takeWhile_len_le_idxOf {α : Type*} [DecidableEq α] {cs : List α} (hnd : cs.Nodup)
    {p : α → Bool} {C : α} (hC : C ∈ cs.dropWhile p) :
    (cs.takeWhile p).length ≤ cs.idxOf C := by
  have hsplit : cs.takeWhile p ++ cs.dropWhile p = cs := List.takeWhile_append_dropWhile
  have hCnt : C ∉ cs.takeWhile p := by
    intro hin
    rw [← hsplit] at hnd
    exact (List.disjoint_of_nodup_append hnd) hin hC
  calc (cs.takeWhile p).length
      ≤ (cs.takeWhile p).length + (cs.dropWhile p).idxOf C := Nat.le_add_right _ _
    _ = (cs.takeWhile p ++ cs.dropWhile p).idxOf C := (List.idxOf_append_of_notMem hCnt).symm
    _ = cs.idxOf C := by rw [hsplit]

/-- In a `Nodup` list, the head of `dropWhile p` sits at index `= takeWhile p` length. -/
theorem idxOf_head_dropWhile {α : Type*} [DecidableEq α] {cs : List α} (hnd : cs.Nodup)
    {p : α → Bool} {T : α} {t : List α} (hd : cs.dropWhile p = T :: t) :
    cs.idxOf T = (cs.takeWhile p).length := by
  have hsplit : cs.takeWhile p ++ cs.dropWhile p = cs := List.takeWhile_append_dropWhile
  have hTnt : T ∉ cs.takeWhile p := by
    intro hin
    rw [← hsplit, hd] at hnd
    exact (List.disjoint_of_nodup_append hnd) hin List.mem_cons_self
  have hT : cs.idxOf T = (cs.takeWhile p ++ cs.dropWhile p).idxOf T := by rw [hsplit]
  rw [hT, List.idxOf_append_of_notMem hTnt, hd]
  simp

/-! ## The active clause is `cs`-minimal in its active suffix -/

/-- The active clause has the least `cs`-index among the clauses of its active suffix. -/
theorem idxOf_activeTerm_le_of_mem_activeSuffix {cs : List (Clause n)} {σ : Fin n → Option Bool}
    {T C : Clause n} (hnd : cs.Nodup) (hns : SwitchingCounting.anyTermSat cs σ = false)
    (hact : SwitchingCounting.activeTerm cs σ = some T) (hC : C ∈ activeSuffix cs σ) :
    cs.idxOf T ≤ cs.idxOf C := by
  have hhd := head?_activeSuffix (cs := cs) (σ := σ) hns
  rw [hact, activeSuffix] at hhd
  rw [activeSuffix] at hC
  cases hdw : cs.dropWhile (fun U => !activePred σ U) with
  | nil => rw [hdw] at hhd; simp at hhd
  | cons a t =>
    rw [hdw] at hhd
    simp only [List.head?_cons, Option.some.injEq] at hhd
    subst hhd
    rw [idxOf_head_dropWhile hnd hdw]
    exact takeWhile_len_le_idxOf hnd hC

/-! ## Clause-order contiguity of `deepestSatSeq` -/

/-- **Clause-order contiguity of `deepestSatSeq`.**  For distinct clauses (`cs.Nodup`), the `cs`-indices
of the recorded clauses are non-decreasing — the clauses are visited in `cs`-order and each clause's
satisfy steps form one contiguous block.  Induction on the canonical fuel recursion: the satisfy-step
head is the active clause (front of its suffix) and every later recorded clause lies in that suffix,
hence at a `cs`-index `≥`. -/
theorem deepestSatSeq_idxOf_pairwise (cs : List (Clause n)) (hnd : cs.Nodup) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool),
      List.Pairwise (· ≤ ·) ((deepestSatSeq cs F σ).map (fun e => cs.idxOf e.1)) := by
  intro F
  induction F with
  | zero => intro σ; simp [deepestSatSeq]
  | succ F ih =>
    intro σ
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => rw [deepestSatSeq]; simp only [hany, if_true]; simp
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        rw [deepestSatSeq]; simp only [hany, Bool.false_eq_true, if_false, hact]; simp
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none =>
          rw [deepestSatSeq]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]; simp
        | some ℓ =>
          have hℓmem : ℓ ∈ SwitchingCounting.freeLits σ T := List.mem_of_mem_head? hh
          have hℓfree : Depth3.litFree σ ℓ = true := (List.mem_filter.mp hℓmem).2
          have hv : σ (litVar ℓ) = none := by
            rw [litFree_var] at hℓfree
            cases hσ : σ (litVar ℓ) with
            | none => rfl
            | some _ => rw [hσ] at hℓfree; simp at hℓfree
          have body : ∀ b : Bool,
              deepestSatSeq cs (F + 1) σ =
                (if SwitchingCounting.litFalse (fixVar σ (litVar ℓ) b) ℓ
                  then id else List.cons (T, SwitchingCounting.pivotPosOf cs σ))
                  (deepestSatSeq cs F (fixVar σ (litVar ℓ) b)) →
              List.Pairwise (· ≤ ·)
                ((deepestSatSeq cs (F + 1) σ).map (fun e => cs.idxOf e.1)) := by
            intro b hSeq
            rw [hSeq]
            by_cases hf : SwitchingCounting.litFalse (fixVar σ (litVar ℓ) b) ℓ = true
            · rw [if_pos hf, id_eq]; exact ih (fixVar σ (litVar ℓ) b)
            · rw [Bool.not_eq_true] at hf
              rw [if_neg (by rw [hf]; simp), List.map_cons]
              refine List.Pairwise.cons ?_ (ih (fixVar σ (litVar ℓ) b))
              intro x hx
              rw [List.mem_map] at hx
              obtain ⟨⟨C, p⟩, he, hex⟩ := hx
              have hCAS' : C ∈ activeSuffix cs (fixVar σ (litVar ℓ) b) :=
                deepestSatSeq_clause_mem_activeSuffix cs F (fixVar σ (litVar ℓ) b) he
              have hCAS : C ∈ activeSuffix cs σ :=
                (activeSuffix_fixVar_suffix hv).subset hCAS'
              rw [← hex]
              exact idxOf_activeTerm_le_of_mem_activeSuffix hnd hany hact hCAS
          by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
              (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
          · exact body false (by
              rw [deepestSatSeq]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]
              rw [if_pos hd])
          · exact body true (by
              rw [deepestSatSeq]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]
              rw [if_neg hd])

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.idxOf_activeTerm_le_of_mem_activeSuffix
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSatSeq_idxOf_pairwise
