import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingHastad
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingDnfCount

/-!
# The flattened active-term replay path (tightening route)

**STATUS: REAL.  THE FLATTENED PER-VARIABLE REPLAY ON THE DNF FOOTING.**

Codex's structural route (`termPath` → `circuitPath` → `Count`) gives the *loose*
switching count `|Bad| ≤ |Short| · ((2^w)^m)^numTerms`, and states that tightening to
`(2w)^s` needs *the active-clause replay that removes the per-clause-count factor*.  This
is that replay: a **flattened** path that fixes **one** variable per step — the first free
literal of the active term — so a path of `s` steps has exactly `s` selected coordinates
(not `numClauses · width` per term).  Combined with the DNF soundness
(`activeTerm_prefix_falsified`), each step is a `Fin w × Bool` choice, giving the `(2w)^s`
label rather than the per-clause product.

Distinct names (`replayStep`/`replayPath`/`replaySel`) from Codex's structural `termPath`;
the two routes compose — Codex's count is loose, this replay tightens it.

* `replayPath` / `replaySel`: the flattened fold and its selected coordinates;
* `freeOn_replayPath`: `freeOn (replayPath cs σ k) (replaySel cs σ k) = σ`;
* `replayPath_inj`: `σ ↦ (replayPath, replaySel)` injective.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The literal falsified at one flattened step: the first free literal of the active term. -/
def activeTermLit (cs : List (Clause n)) (σ : Restriction n) : Option (Rung4Literal n) :=
  match activeTerm cs σ with
  | none => none
  | some T => (freeLits σ T).head?

/-- The chosen literal is genuinely free. -/
theorem activeTermLit_free {cs : List (Clause n)} {σ : Restriction n} {ℓ : Rung4Literal n}
    (h : activeTermLit cs σ = some ℓ) : Depth3.litFree σ ℓ = true := by
  unfold activeTermLit at h
  cases hT : activeTerm cs σ with
  | none => rw [hT] at h; exact absurd h (by simp)
  | some T => rw [hT] at h; exact (List.mem_filter.mp (List.mem_of_mem_head? h)).2

/-- One flattened step: falsify the first free literal of the active term. -/
def replayStep (cs : List (Clause n)) (σ : Restriction n) : Restriction n :=
  match activeTermLit cs σ with
  | none => σ
  | some ℓ => falFix σ ℓ

theorem replayStep_eq_outside (cs : List (Clause n)) (σ : Restriction n) {j : Fin n}
    (hj : ∀ ℓ, activeTermLit cs σ = some ℓ → j ≠ litVar ℓ) : replayStep cs σ j = σ j := by
  rw [replayStep]
  cases h : activeTermLit cs σ with
  | none => rfl
  | some ℓ => exact falFix_eq_outside σ ℓ (hj ℓ h)

theorem freeVars_replayStep_subset (cs : List (Clause n)) (σ : Restriction n) :
    freeVars (replayStep cs σ) ⊆ freeVars σ := by
  intro j hj
  rw [mem_freeVars] at hj ⊢
  by_cases hc : ∀ ℓ, activeTermLit cs σ = some ℓ → j ≠ litVar ℓ
  · rw [replayStep_eq_outside cs σ hc] at hj; exact hj
  · push_neg at hc
    obtain ⟨ℓ, hℓ, hjv⟩ := hc
    rw [replayStep, hℓ, hjv] at hj
    simp [falFix, Function.update_self] at hj

/-- The flattened path after `k` steps. -/
def replayPath (cs : List (Clause n)) (σ : Restriction n) : ℕ → Restriction n
  | 0 => σ
  | k + 1 => replayStep cs (replayPath cs σ k)

/-- The selected coordinates after `k` steps (one per step). -/
def replaySel (cs : List (Clause n)) (σ : Restriction n) : ℕ → Finset (Fin n)
  | 0 => ∅
  | k + 1 => replaySel cs σ k ∪
      (match activeTermLit cs (replayPath cs σ k) with | none => ∅ | some ℓ => {litVar ℓ})

theorem freeVars_replayPath_subset (cs : List (Clause n)) (σ : Restriction n) (k : ℕ) :
    freeVars (replayPath cs σ k) ⊆ freeVars σ := by
  induction k with
  | zero => exact Finset.Subset.refl _
  | succ k ih => intro j hj; exact ih (freeVars_replayStep_subset cs (replayPath cs σ k) hj)

theorem replayPath_eq_outside (cs : List (Clause n)) (σ : Restriction n) (k : ℕ) {j : Fin n}
    (hj : j ∉ replaySel cs σ k) : replayPath cs σ k j = σ j := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [replaySel, Finset.mem_union, not_or] at hj
    have hstep : replayStep cs (replayPath cs σ k) j = replayPath cs σ k j := by
      refine replayStep_eq_outside cs (replayPath cs σ k) (fun ℓ hℓ hjv => ?_)
      apply hj.2; rw [hℓ, hjv]; exact Finset.mem_singleton_self _
    rw [replayPath, hstep]
    exact ih hj.1

theorem replaySel_subset_freeVars (cs : List (Clause n)) (σ : Restriction n) (k : ℕ) :
    replaySel cs σ k ⊆ freeVars σ := by
  induction k with
  | zero => simp [replaySel]
  | succ k ih =>
    intro j hj
    rw [replaySel, Finset.mem_union] at hj
    rcases hj with h | h
    · exact ih h
    · cases hs : activeTermLit cs (replayPath cs σ k) with
      | none => rw [hs] at h; simp at h
      | some ℓ =>
        rw [hs, Finset.mem_singleton] at h
        subst h
        apply freeVars_replayPath_subset cs σ k
        rw [mem_freeVars]
        have := activeTermLit_free hs
        rw [litFree_var] at this
        exact Option.isNone_iff_eq_none.mp this

/-- **`decode_encode_id` (set level), flattened replay.** -/
theorem freeOn_replayPath (cs : List (Clause n)) (σ : Restriction n) (k : ℕ) :
    freeOn (replayPath cs σ k) (replaySel cs σ k) = σ := by
  funext j
  simp only [freeOn]
  by_cases hj : j ∈ replaySel cs σ k
  · rw [if_pos hj]
    exact (mem_freeVars.mp (replaySel_subset_freeVars cs σ k hj)).symm
  · rw [if_neg hj]
    exact replayPath_eq_outside cs σ k hj

/-- **Injectivity.**  `σ` is determined by its flattened replay path and selected set. -/
theorem replayPath_inj (cs : List (Clause n)) (k : ℕ) {σ τ : Restriction n}
    (hp : replayPath cs σ k = replayPath cs τ k) (hs : replaySel cs σ k = replaySel cs τ k) :
    σ = τ := by
  rw [← freeOn_replayPath cs σ k, hp, hs, freeOn_replayPath cs τ k]

/-- **Tight set size: one coordinate per step.**  After `k` flattened steps the selected set
has at most `k` coordinates — each step adds at most one variable (the active term's first free
literal).  This is the tight-`s` handle the block route lacks: the flattened path fixes
exactly one variable per step, so a depth-`s` path selects `≤ s` coordinates (no
`(term, position)` overcount).  It is what makes a `(2w)^s` label sufficient at the *set*
level; the remaining open piece is the per-step *decoder* recovering the active term from the
(falsify) end-state, which is the known reverse-recovery obstruction. -/
theorem replaySel_card_le (cs : List (Clause n)) (σ : Restriction n) (k : ℕ) :
    (replaySel cs σ k).card ≤ k := by
  induction k with
  | zero => simp [replaySel]
  | succ k ih =>
    have hstep : (match activeTermLit cs (replayPath cs σ k) with
        | none => (∅ : Finset (Fin n)) | some ℓ => {litVar ℓ}).card ≤ 1 := by
      cases activeTermLit cs (replayPath cs σ k) with
      | none => simp
      | some ℓ => simp
    calc (replaySel cs σ (k + 1)).card
        = (replaySel cs σ k ∪
            (match activeTermLit cs (replayPath cs σ k) with
              | none => ∅ | some ℓ => {litVar ℓ})).card := by rw [replaySel]
      _ ≤ (replaySel cs σ k).card +
            (match activeTermLit cs (replayPath cs σ k) with
              | none => (∅ : Finset (Fin n)) | some ℓ => {litVar ℓ}).card :=
          Finset.card_union_le _ _
      _ ≤ k + 1 := Nat.add_le_add ih hstep

/-- `falFix` leaves a literal on another variable's forced-false status unchanged. -/
theorem litFalse_falFix_ne (σ : Restriction n) {ℓ ℓ'' : Rung4Literal n}
    (h : litVar ℓ'' ≠ litVar ℓ) : litFalse (falFix σ ℓ) ℓ'' = litFalse σ ℓ'' := by
  unfold litFalse; rw [litFixedVal_falFix_ne σ h]

/-- A false literal stays false after one flattened step (the step only fixes a *free*
variable, distinct from the fixed variable carrying the false literal). -/
theorem litFalse_replayStep {cs : List (Clause n)} {σ : Restriction n} {ℓ'' : Rung4Literal n}
    (h : litFalse σ ℓ'' = true) : litFalse (replayStep cs σ) ℓ'' = true := by
  rw [replayStep]
  cases ha : activeTermLit cs σ with
  | none => exact h
  | some ℓ =>
    have hfree : σ (litVar ℓ) = none := by
      have hf := activeTermLit_free ha
      rw [litFree_var] at hf; exact Option.isNone_iff_eq_none.mp hf
    have hne : litVar ℓ'' ≠ litVar ℓ := fun he => litFalse_litVar_fixed h (he ▸ hfree)
    rw [litFalse_falFix_ne σ hne]; exact h

/-- **Monotonicity: a falsified term stays falsified after one step.**  In the falsify path one
false literal kills the whole term (a conjunction), and the step only touches a free variable,
so it cannot revive a falsified term. -/
theorem termFalsified_replayStep_of {cs : List (Clause n)} {σ : Restriction n} {T : Clause n}
    (h : termFalsified σ T = true) : termFalsified (replayStep cs σ) T = true := by
  rw [termFalsified, List.any_eq_true] at h ⊢
  obtain ⟨ℓ'', hmem, hf⟩ := h
  exact ⟨ℓ'', hmem, litFalse_replayStep hf⟩

/-- **Monotonicity along the whole path.**  A term falsified at the start stays falsified after
any number of flattened steps — so the active-term positions never revisit a processed term
(the structural basis for boundary recovery). -/
theorem termFalsified_replayPath_of {cs : List (Clause n)} {σ : Restriction n} {T : Clause n}
    (k : ℕ) (h : termFalsified σ T = true) :
    termFalsified (replayPath cs σ k) T = true := by
  induction k with
  | zero => exact h
  | succ k ih => rw [replayPath]; exact termFalsified_replayStep_of ih

/-- **Each step falsifies any term containing the stepped literal.**  The step fixes the
chosen literal `ℓ` to false, so every term having `ℓ` becomes falsified.  In particular (with
`ℓ` the active term's first free literal) the step *consumes* its own active term; combined with
`termFalsified_replayPath_of`, that term then stays falsified — active-term positions advance
monotonically and never revisit. -/
theorem replayStep_falsifies {cs : List (Clause n)} {σ : Restriction n} {ℓ : Rung4Literal n}
    (h : activeTermLit cs σ = some ℓ) {T : Clause n} (hℓT : ℓ ∈ T.lits) :
    termFalsified (replayStep cs σ) T = true := by
  rw [replayStep, h, termFalsified, List.any_eq_true]
  exact ⟨ℓ, hℓT, by simp [litFalse, falFix_forces_false]⟩

/-- The active term satisfies the selector predicate: it is not falsified and has a free
literal. -/
theorem activeTerm_pred {cs : List (Clause n)} {σ : Restriction n} {T : Clause n}
    (h : activeTerm cs σ = some T) :
    termFalsified σ T = false ∧ 0 < (freeLits σ T).length := by
  have hns := activeTerm_anyTermSat_false h
  have hfind : cs.find? (fun T => !termFalsified σ T && decide (0 < (freeLits σ T).length))
      = some T := activeTerm_eq_find hns ▸ h
  have hpred := List.find?_some hfind
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hpred
  exact hpred

/-- **The active term changes every step.**  Since the step falsifies the active term's first
free literal, that term is falsified afterwards and so cannot be the active term again.  With
`termFalsified_replayPath_of` (it stays falsified), the path therefore visits *distinct* active
terms — each consumed permanently, positions never revisited.  This is the precise "advance"
statement underneath boundary recovery. -/
theorem activeTerm_replayStep_ne {cs : List (Clause n)} {σ : Restriction n} {T : Clause n}
    (h : activeTerm cs σ = some T) : activeTerm cs (replayStep cs σ) ≠ some T := by
  intro hcontra
  obtain ⟨hnf, hlen⟩ := activeTerm_pred h
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, (freeLits σ T).head? = some ℓ := by
    cases hh : freeLits σ T with
    | nil => rw [hh] at hlen; simp at hlen
    | cons a _ => exact ⟨a, rfl⟩
  have hatl : activeTermLit cs σ = some ℓ := by unfold activeTermLit; rw [h]; exact hℓ
  have hℓT : ℓ ∈ T.lits := (List.mem_filter.mp (List.mem_of_mem_head? hℓ)).1
  have hfals : termFalsified (replayStep cs σ) T = true := replayStep_falsifies hatl hℓT
  rw [(activeTerm_pred hcontra).1] at hfals
  simp at hfals

/-- **Per-step reverse inverse.**  Freeing the falsified variable undoes one flattened step:
if the active term's chosen literal is `ℓ`, then re-freeing `litVar ℓ` from `replayStep cs σ`
recovers `σ` exactly.  This is the foundational brick of any reverse decoder for the flattened
route (the analog of the clause path's `freeOn_actStep_recover`): the *single-step* recovery is
clean; what is not yet proved is identifying `ℓ` (the active term) from the end-state across
term boundaries (`hdec` in `replay_switching_count`). -/
theorem freeOn_replayStep_recover {cs : List (Clause n)} {σ : Restriction n}
    {ℓ : Rung4Literal n} (h : activeTermLit cs σ = some ℓ) :
    freeOn (replayStep cs σ) {litVar ℓ} = σ := by
  funext j
  simp only [freeOn]
  by_cases hj : j = litVar ℓ
  · rw [if_pos (by rw [hj]; exact Finset.mem_singleton_self _)]
    have hfree := activeTermLit_free h
    rw [litFree_var] at hfree
    rw [hj]; exact (Option.isNone_iff_eq_none.mp hfree).symm
  · rw [if_neg (by rw [Finset.mem_singleton]; exact hj), replayStep, h]
    exact falFix_eq_outside σ ℓ hj

/-- **The `(2w)^s` count for the flattened route, modulo the per-step decoder.**  This is the
honest *conditional wrapper* the arc has been pointing at: it names *exactly* the single open
hypothesis — a per-step decoder `D` that recovers the selected set from the (falsify) end-state
and a `(2w)^s` label — and discharges everything else from proved results
(`replayPath_inj` for injectivity, `card_bad_le_encoding` for the `(2w)^s` label cardinality).

The hypothesis `hdec` is the genuine open core: `D (replayPath cs ρ s) (lab ρ) = replaySel cs ρ s`.
Its difficulty is **active-term recovery under mid-completion** — at the end-state the last
term may be only partially falsified, so it is neither `termSat` nor falsified, and the sound
block selector does not apply.  Cracking `hdec` (constructing such a `D` and `lab` with a
`(2w)^s` label) is the remaining research target; this theorem isolates it cleanly and shows
nothing else stands in the way of the tight count. -/
theorem replay_switching_count {w s : ℕ} {cs : List (Clause n)}
    (lab : Restriction n → PathLabel w s)
    (D : Restriction n → PathLabel w s → Finset (Fin n))
    {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, replayPath cs ρ s ∈ Short)
    (hdec : ∀ ρ ∈ Bad, D (replayPath cs ρ s) (lab ρ) = replaySel cs ρ s) :
    Bad.card ≤ Short.card * (2 * w) ^ s := by
  refine card_bad_le_encoding (fun ρ => replayPath cs ρ s) lab hmem ?_
  intro ρ hρ σ hσ hE hlab
  have hE' : replayPath cs ρ s = replayPath cs σ s := hE
  refine replayPath_inj cs s hE' ?_
  rw [← hdec ρ hρ, ← hdec σ hσ, hE', hlab]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.freeOn_replayPath
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replayPath_inj
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replaySel_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.termFalsified_replayPath_of
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replayStep_falsifies
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.activeTerm_replayStep_ne
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.freeOn_replayStep_recover
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replay_switching_count
