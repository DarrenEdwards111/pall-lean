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
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replay_switching_count
