import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PWeightStars

/-!
# Block-DT model, foundation 57: branching holography, step 4o — the freed count is ≥ the path length (branch only)

The structural reconciliation that quantifies the measure gain to `s`.  The satisfying boundary
`descentSat` fixes at least `pathLen` variables: `pathLen + stars (descentSat …) ≤ stars σ`.  Combined with
the deepest input (`pathLen = depth ≥ s` on the bad event, brick 39), the boundary fixes `≥ s` variables —
so `stars σ − stars (descentSat σ) ≥ s`, the exponent in the star-gain identity (brick 56).

* `stars_descentSat_succ` — `descentSat` at a block has the same free variables as its recursion (the
  block's freed variables are fixed in both, to satisfying resp. path values).
* `pathLen_add_stars_descentSat_le` — `pathLen cs w F σ x + stars (descentSat cs w F σ x) ≤ stars σ`.
* `freed_ge_of_depth_ge` — on the bad event (`s ≤ depth`), `s + stars (descentSat σ x) ≤ stars σ` for the
  deepest input `x`: the boundary fixes `≥ s` more variables.

This is the last *structural* input to the probability bound; only the `Finset.sum`-over-injection step
(summing the brick-54 injection against `pweight`) then remains.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- A block of `descentSat` does not change which variables are free (its freed variables are fixed in
both the boundary and its recursion). -/
theorem stars_descentSat_succ (cs : List (Clause n)) (w F : ℕ) {σ : Fin n → Option Bool} {T : Clause n}
    (x : Fin n → Bool) (hany : anyTermSat cs σ = false) (hact : activeTerm cs σ = some T) :
    stars (descentSat cs w (F + 1) σ x) = stars (descentSat cs w F (extendσ σ T x) x) := by
  rw [stars, stars]
  congr 1
  apply Finset.ext
  intro v
  rw [mem_freeVars, mem_freeVars, descentSat_succ_apply x hany hact]
  by_cases hc : σ v = none ∧ ((Rung4Literal.pos v) ∈ T.lits ∨ (Rung4Literal.neg v) ∈ T.lits)
  · have hvf : v ∈ freeVarsOf σ T := by
      rcases hc.2 with hp | hn
      · exact litVar_mem_freeVarsOf hp (by simp [DTree.freeLit, hc.1])
      · exact litVar_mem_freeVarsOf hn (by simp [DTree.freeLit, hc.1])
    have hext : descentSat cs w F (extendσ σ T x) x v = some (x v) :=
      descentSat_extends cs w F (extendσ σ T x) x v (x v) (by rw [extendσ, if_pos hvf])
    rw [if_pos hc, hext]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · split at h <;> simp at h
    · simp at h
  · rw [if_neg hc]

/-- **The boundary fixes at least `pathLen` variables.** -/
theorem pathLen_add_stars_descentSat_le (cs : List (Clause n)) (w : ℕ)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      pathLen cs w F σ x + stars (descentSat cs w F σ x) ≤ stars σ := by
  intro F
  induction F with
  | zero => intro σ x; simp [pathLen, descentSat]
  | succ F ih =>
    intro σ x
    cases hany : anyTermSat cs σ with
    | true => rw [pathLen, descentSat]; simp [hany]
    | false =>
      cases hact : activeTerm cs σ with
      | none => rw [pathLen, descentSat]; simp [hany, hact]
      | some T =>
        have hpl : pathLen cs w (F + 1) σ x
            = (freeVarsOf σ T).length
              + (if (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) then 0
                 else pathLen cs w F (extendσ σ T x) x) := by
          rw [pathLen]; simp only [hany, Bool.false_eq_true, if_false, hact]
        have hsucc := stars_descentSat_succ cs w F x hany hact
        have hndT : (freeVarsOf σ T).Nodup := freeVarsOf_nodup (hnd T (activeTerm_mem hact))
        have hlen : (freeVarsOf σ T).toFinset.card = (freeVarsOf σ T).length :=
          List.toFinset_card_of_nodup hndT
        have hsub : (freeVarsOf σ T).toFinset ⊆ freeVars σ := freeVarsOf_toFinset_subset
        have hlen_le : (freeVarsOf σ T).length ≤ stars σ := by
          rw [← hlen, stars]; exact Finset.card_le_card hsub
        have hext : stars (extendσ σ T x) = stars σ - (freeVarsOf σ T).length := by
          rw [stars_extendσ_eq, hlen]
        have hIH := ih (extendσ σ T x) x
        rw [hext] at hIH
        rw [hpl, hsucc]
        split <;> omega

/-- **On the bad event, the boundary fixes `≥ s` variables.** -/
theorem freed_ge_of_depth_ge (cs : List (Clause n)) (w : ℕ)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) (F : ℕ) (σ : Fin n → Option Bool) (s : ℕ)
    (hs : s ≤ (canonicalDTree cs w F σ).depth) :
    ∃ x, s + stars (descentSat cs w F σ x) ≤ stars σ := by
  obtain ⟨x, hx⟩ := exists_deep_input cs w hnd F σ
  refine ⟨x, ?_⟩
  have hpl := pathLen_add_stars_descentSat_le cs w hnd F σ x
  have : s ≤ pathLen cs w F σ x := le_trans hs hx
  omega

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.freed_ge_of_depth_ge
