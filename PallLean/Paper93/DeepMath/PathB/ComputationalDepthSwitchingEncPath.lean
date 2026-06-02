import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCompletionRecover
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingHastad
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCounting
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingTermWalk

/-!
# The encoder canonical block path (satisfying-completion tracked)

**STATUS: REAL.  THE ENCODER PRODUCING THE PATH-LITERAL LIST.**

The canonical path processes terms left to right against the *accumulating satisfying
completion* `σ` (so the global completion is `complete ρ (encLits ρ cs)`).  At each term:

* if the term is already **falsified** under `σ`, it is **skipped** (its literals must not
  enter the path — a falsified term is not satisfied under the completion, so including its
  literals would break the `hterm` cover);
* otherwise it contributes its **current** free literals `freeLits σ T`, and the state
  advances by satisfying them (`complete σ (freeLits σ T)`).

This produces the path-literal list `encLits` — with distinct variables across terms (later
terms' current-free literals are on still-free variables, disjoint from already-fixed ones).
This file builds the path and proves it lies in the starting `ρ`'s free variables and has
distinct variables (the foundations for the `hterm` cover).
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- A variable touched by the satisfying completion is fixed (never `none`). -/
theorem complete_ne_none_of_mem (l : List (Rung4Literal n)) :
    ∀ (ρ : Restriction n) {v : Fin n}, v ∈ l.map litVar → complete ρ l v ≠ none := by
  induction l with
  | nil => intro ρ v h; simp at h
  | cons a t ih =>
    intro ρ v h
    rw [List.map_cons, List.mem_cons] at h
    rw [complete_cons]
    rcases h with rfl | h
    · by_cases hvt : litVar a ∈ t.map litVar
      · exact ih (satFix ρ a) hvt
      · rw [complete_apply_eq_of_not_mem (satFix ρ a) t (litVar a) hvt, satFix,
          Function.update_self]; simp
    · exact ih (satFix ρ a) h

/-- Satisfying-completing a literal list only shrinks the free set. -/
theorem freeVars_complete_subset (ρ : Restriction n) (l : List (Rung4Literal n)) :
    freeVars (complete ρ l) ⊆ freeVars ρ := by
  intro j hj
  rw [mem_freeVars] at hj ⊢
  by_cases h : j ∈ l.map litVar
  · exact absurd hj (complete_ne_none_of_mem l ρ h)
  · rw [complete_apply_eq_of_not_mem ρ l j h] at hj; exact hj

/-- The encoder path: process terms left to right against the accumulating satisfying
completion, skipping terms already falsified, contributing each live term's current free
literals. -/
def encLits (ρ : Restriction n) : List (Clause n) → List (Rung4Literal n)
  | [] => []
  | T :: ts =>
      if termFalsified ρ T then encLits ρ ts
      else freeLits ρ T ++ encLits (complete ρ (freeLits ρ T)) ts

/-- **Encoder literals are `ρ`-free.**  Every variable of the encoder path was free in the
starting restriction. -/
theorem encLits_subset_freeVars (ρ : Restriction n) (cs : List (Clause n)) :
    ((encLits ρ cs).map litVar).toFinset ⊆ freeVars ρ := by
  induction cs generalizing ρ with
  | nil => simp [encLits]
  | cons T ts ih =>
    simp only [encLits]
    split
    · exact ih ρ
    · intro v hv
      simp only [List.map_append, List.toFinset_append, Finset.mem_union] at hv
      rcases hv with h | h
      · rw [List.mem_toFinset, List.mem_map] at h
        obtain ⟨ℓ, hℓ, hℓv⟩ := h
        rw [mem_freeVars, ← hℓv]
        have := (List.mem_filter.mp hℓ).2
        rw [litFree_var] at this
        exact Option.isNone_iff_eq_none.mp this
      · exact freeVars_complete_subset ρ _ (ih (complete ρ (freeLits ρ T)) h)

/-- The current-free literals of a single term have distinct variables (a sublist of the
term's literals). -/
theorem freeLits_map_litVar_nodup (ρ : Restriction n) (T : Clause n)
    (hT : (T.lits.map litVar).Nodup) : ((freeLits ρ T).map litVar).Nodup := by
  have hsub : (freeLits ρ T).Sublist T.lits := List.filter_sublist
  exact hT.sublist (List.Sublist.map litVar hsub)

/-- **Distinct variables across the whole encoder path.**  Each live term contributes only
its *current* free literals, on still-free variables disjoint from already-fixed ones, so the
full path-literal list has no repeated variable.  (Requires each term to have distinct-variable
literals.) -/
theorem encLits_nodup (ρ : Restriction n) (cs : List (Clause n))
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup) :
    ((encLits ρ cs).map litVar).Nodup := by
  induction cs generalizing ρ with
  | nil => simp [encLits]
  | cons T ts ih =>
    simp only [encLits]
    split
    · exact ih ρ (fun T' hT' => hcs T' (List.mem_cons.mpr (Or.inr hT')))
    · simp only [List.map_append]
      rw [List.nodup_append]
      refine ⟨freeLits_map_litVar_nodup ρ T (hcs T (List.mem_cons.mpr (Or.inl rfl))),
              ih (complete ρ (freeLits ρ T))
                (fun T' hT' => hcs T' (List.mem_cons.mpr (Or.inr hT'))), ?_⟩
      intro v hv1 b hb hvb
      subst hvb
      have hfree : complete ρ (freeLits ρ T) v = none :=
        mem_freeVars.mp (encLits_subset_freeVars (complete ρ (freeLits ρ T)) ts
          (List.mem_toFinset.mpr hb))
      exact complete_ne_none_of_mem (freeLits ρ T) ρ hv1 hfree

/-- The satisfying completion distributes over concatenation (it is a left fold). -/
theorem complete_append (ρ : Restriction n) (a b : List (Rung4Literal n)) :
    complete ρ (a ++ b) = complete (complete ρ a) b := by
  simp only [complete, List.foldl_append]

/-- The defining equation of `encLits` on a cons (unfolds only the head). -/
theorem encLits_cons (ρ : Restriction n) (T : Clause n) (ts : List (Clause n)) :
    encLits ρ (T :: ts) =
      if termFalsified ρ T then encLits ρ ts
      else freeLits ρ T ++ encLits (complete ρ (freeLits ρ T)) ts := rfl

/-- **The `hterm` cover.**  Every literal of the encoder path lies in a term that is
*satisfied* under the global completion `complete ρ (encLits ρ cs)`.  The recursion makes this
clean: each term, when processed, is the head of its remaining list, so its current free
literals are exactly the prefix block — `term_processed_termSat` applies directly (no
cross-block conflict). Skipped (falsified) terms contribute no literals.  This is exactly the
hypothesis `termWalk_decode_of_hterm` consumes. -/
theorem encLits_hterm (ρ : Restriction n) (cs : List (Clause n))
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup) :
    ∀ ℓ ∈ encLits ρ cs, ∃ T ∈ cs, ℓ ∈ T.lits ∧
      termSat (complete ρ (encLits ρ cs)) T = true := by
  induction cs generalizing ρ with
  | nil => intro ℓ h; simp [encLits] at h
  | cons T ts ih =>
    rw [encLits_cons]
    split
    · -- skipped term: literals come from the tail
      intro ℓ hℓ
      obtain ⟨T', hT', hℓT', hsat⟩ :=
        ih ρ (fun T'' h'' => hcs T'' (List.mem_cons.mpr (Or.inr h''))) ℓ hℓ
      exact ⟨T', List.mem_cons.mpr (Or.inr hT'), hℓT', hsat⟩
    · rename_i hf
      have hnf : termFalsified ρ T = false := by simpa using hf
      have hlive : ∀ ℓ' ∈ T.lits, litFalse ρ ℓ' = false := by
        intro ℓ' hℓ'
        by_contra hc
        have htrue : litFalse ρ ℓ' = true := by simpa using hc
        have : termFalsified ρ T = true := by
          rw [termFalsified]; exact List.any_eq_true.mpr ⟨ℓ', hℓ', htrue⟩
        rw [this] at hnf; simp at hnf
      have hnd : ((freeLits ρ T ++ encLits (complete ρ (freeLits ρ T)) ts).map litVar).Nodup := by
        have := encLits_nodup ρ (T :: ts) hcs
        rwa [encLits_cons, if_neg hf] at this
      have hfree : ∀ v ∈ (freeLits ρ T ++ encLits (complete ρ (freeLits ρ T)) ts).map litVar,
          ρ v = none := by
        intro v hv
        have hsub := encLits_subset_freeVars ρ (T :: ts)
        rw [encLits_cons, if_neg hf] at hsub
        exact mem_freeVars.mp (hsub (List.mem_toFinset.mpr hv))
      intro ℓ hℓ
      rw [List.mem_append] at hℓ
      rcases hℓ with hb | hr
      · -- literal in the head term's block
        refine ⟨T, List.mem_cons.mpr (Or.inl rfl), (List.mem_filter.mp hb).1, ?_⟩
        refine term_processed_termSat (fun ℓ' hℓ' hfr => ?_) hlive hnd hfree
        exact List.mem_append_left _ (List.mem_filter.mpr ⟨hℓ', hfr⟩)
      · -- literal in the tail, processed at the advanced state
        obtain ⟨T', hT', hℓT', hsat⟩ :=
          ih (complete ρ (freeLits ρ T))
            (fun T'' h'' => hcs T'' (List.mem_cons.mpr (Or.inr h''))) ℓ hr
        refine ⟨T', List.mem_cons.mpr (Or.inr hT'), hℓT', ?_⟩
        rw [complete_append]
        exact hsat

/-- **The encoder discharges `hdecode`.**  For the concrete canonical path `litList =
encLits ρ cs`, the sound decoder recovers `ρ` from its completion — with *no* extra
hypothesis beyond each term having distinct-variable literals.  This is exactly the
`hdecode` field of `dnf_switching_interface`/`dnf_switching_bound'`, now supplied by a
concrete encoder rather than assumed.  Fuel `cs.length` suffices (at most one block per
term). -/
theorem encLits_decode (ρ : Restriction n) (cs : List (Clause n))
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup) :
    freeOn (complete ρ (encLits ρ cs))
      (termWalkVars (complete ρ (encLits ρ cs)) (termBlock (encLits ρ cs)) cs cs.length) = ρ := by
  refine termWalk_decode_of_hterm ?_ ?_ (encLits_hterm ρ cs hcs)
  · intro v hv
    exact mem_freeVars.mp (encLits_subset_freeVars ρ cs (List.mem_toFinset.mpr hv))
  · exact List.length_filter_le _ _

/-- **The completion frees exactly the complement of the path variables.**  The completion
fixes precisely the (`ρ`-free, distinct) path variables and leaves everything else as in `ρ`.
This is the structural fact behind `hmem`: the completion lands in a controlled, smaller
restriction. -/
theorem freeVars_complete_encLits (ρ : Restriction n) (cs : List (Clause n)) :
    freeVars (complete ρ (encLits ρ cs))
      = freeVars ρ \ ((encLits ρ cs).map litVar).toFinset := by
  ext v
  rw [mem_freeVars, Finset.mem_sdiff, mem_freeVars]
  by_cases hv : v ∈ ((encLits ρ cs).map litVar).toFinset
  · constructor
    · intro h
      exact absurd h (complete_ne_none_of_mem _ ρ (List.mem_toFinset.mp hv))
    · intro hh; exact absurd hv hh.2
  · rw [complete_apply_eq_of_not_mem ρ _ v (fun hh => hv (List.mem_toFinset.mpr hh))]
    exact ⟨fun h => ⟨h, hv⟩, fun hh => hh.1⟩

/-- **The completion fixes exactly `(encLits ρ cs).length` more stars.**  So a bad `ρ` whose
canonical path has length `s` maps to a completion with exactly `s` fewer free coordinates —
the standard switching-lemma `hmem` content, pinning `Short` to the restrictions reachable by
fixing `s` coordinates. -/
theorem stars_complete_encLits (ρ : Restriction n) (cs : List (Clause n))
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup) :
    stars (complete ρ (encLits ρ cs)) = stars ρ - (encLits ρ cs).length := by
  rw [stars, stars, freeVars_complete_encLits,
    Finset.card_sdiff_of_subset (encLits_subset_freeVars ρ cs),
    List.toFinset_card_of_nodup (encLits_nodup ρ cs hcs), List.length_map]

/-- The `termBlock` walk output lies in the path variables (each block is `⊆` the path
variable set). -/
theorem termWalkVars_subset_pathvars (σstar : Restriction n)
    (litList : List (Rung4Literal n)) (cs : List (Clause n)) (k : ℕ) :
    termWalkVars σstar (termBlock litList) cs k ⊆ (litList.map litVar).toFinset := by
  intro v hv
  rw [mem_termWalkVars] at hv
  obtain ⟨T, _, hvT⟩ := hv
  rw [termBlock, Finset.mem_inter] at hvT
  exact hvT.2

/-- **The decoder output is exactly the path variable set.**  Running the decoder on the
concrete encoder recovers precisely the set of path variables — the `s` fixed stars.  Combined
with `stars_complete_encLits`, this confirms the decode is over exactly the star-reduction set
(`|recovered| = (encLits ρ cs).length`). -/
theorem termWalkVars_encLits_eq_pathvars (ρ : Restriction n) (cs : List (Clause n))
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup) :
    termWalkVars (complete ρ (encLits ρ cs)) (termBlock (encLits ρ cs)) cs cs.length
      = ((encLits ρ cs).map litVar).toFinset := by
  refine Finset.Subset.antisymm (termWalkVars_subset_pathvars _ _ _ _) ?_
  intro v hv
  by_contra hvR
  have hvnone : ρ v = none := mem_freeVars.mp (encLits_subset_freeVars ρ cs hv)
  have hσ : complete ρ (encLits ρ cs) v ≠ none :=
    complete_ne_none_of_mem _ ρ (List.mem_toFinset.mp hv)
  have h1 := congrFun (encLits_decode ρ cs hcs) v
  simp only [freeOn, if_neg hvR] at h1
  rw [hvnone] at h1
  exact hσ h1

/-- **The recovered set has cardinality = the star reduction.**  The decoder recovers exactly
`(encLits ρ cs).length` coordinates — which by `stars_complete_encLits` is exactly the number
of stars fixed (`stars ρ - stars (complete ρ (encLits ρ cs))`).  So the decode is over a set of
size precisely the star reduction, unconditionally (no clause-disjointness needed) — this is
the tight star count at the *set* level for the working route. -/
theorem card_termWalkVars_encLits (ρ : Restriction n) (cs : List (Clause n))
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup) :
    (termWalkVars (complete ρ (encLits ρ cs)) (termBlock (encLits ρ cs)) cs cs.length).card
      = (encLits ρ cs).length := by
  rw [termWalkVars_encLits_eq_pathvars ρ cs hcs,
    List.toFinset_card_of_nodup (encLits_nodup ρ cs hcs), List.length_map]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.encLits_subset_freeVars
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.encLits_nodup
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.encLits_hterm
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.encLits_decode
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.stars_complete_encLits
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.termWalkVars_encLits_eq_pathvars
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_termWalkVars_encLits
