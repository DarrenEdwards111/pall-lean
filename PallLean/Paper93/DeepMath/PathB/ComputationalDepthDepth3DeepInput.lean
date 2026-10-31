import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PathLocality

/-!
# Block-DT model, foundation 39: branching holography, step 2b — the deepest input (branch only)

The canonical tree's height is *realised* by some input: `∃ x, depth ≤ pathLen x`.  Combined with
`pathLen_le_depth` (brick 36) this gives `depth = max_x pathLen x` — so `{ρ : depth ≥ s}` is exactly the
set of restrictions with a depth-`≥ s` per-input path, the object the branching count encodes.

Requires the distinct-variable hypothesis (clauses' literal-variables are `Nodup`, so the canonical
tree never re-queries — brick 38's locality + brick 32's `freeVarsOf_nodup`).

* `applyOn_congr` — the per-block leaf assignment depends only on the input's values at the queried vars.
* `exists_queryAll_deep` — a `queryAll` block's height is realised by some input's leaf.
* `exists_deep_input` — `∃ x, canonicalDTree.depth ≤ pathLen x`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The accumulated leaf assignment depends only on the input's values at the queried variables. -/
theorem applyOn_congr (vars : List (Fin n)) (x y : Fin n → Bool) (h : ∀ u ∈ vars, x u = y u) :
    ∀ init : Fin n → Bool,
      vars.foldl (fun a u => Function.update a u (x u)) init
        = vars.foldl (fun a u => Function.update a u (y u)) init := by
  induction vars with
  | nil => intro init; rfl
  | cons u vars ih =>
    intro init
    simp only [List.foldl_cons]
    rw [h u (List.mem_cons_self ..)]
    exact ih (fun w hw => h w (List.mem_cons_of_mem _ hw)) (Function.update init u (y u))

/-- **A `queryAll` block's height is realised by some input's leaf.** -/
theorem exists_queryAll_deep (k : (Fin n → Bool) → DTree n) :
    ∀ (vars : List (Fin n)), vars.Nodup → ∀ (acc : Fin n → Bool),
      ∃ x : Fin n → Bool, (DTree.queryAll vars acc k).depth
        ≤ vars.length + (k (vars.foldl (fun a u => Function.update a u (x u)) acc)).depth := by
  intro vars
  induction vars with
  | nil => intro _ acc; exact ⟨fun _ => false, by simp [DTree.queryAll]⟩
  | cons v vars ih =>
    intro hnd acc
    rw [List.nodup_cons] at hnd
    obtain ⟨hv, hndv⟩ := hnd
    rcases le_total (DTree.queryAll vars (Function.update acc v false) k).depth
        (DTree.queryAll vars (Function.update acc v true) k).depth with hle | hle
    · obtain ⟨x_h, hx_h⟩ := ih hndv (Function.update acc v true)
      refine ⟨Function.update x_h v true, ?_⟩
      have hfoldl : vars.foldl (fun a u => Function.update a u (Function.update x_h v true u)) (Function.update acc v true)
          = vars.foldl (fun a u => Function.update a u (x_h u)) (Function.update acc v true) :=
        applyOn_congr vars _ _ (fun u hu => Function.update_of_ne (by rintro rfl; exact hv hu) _ _) _
      simp only [DTree.queryAll, DTree.depth, List.foldl_cons, List.length_cons,
        Function.update_self, hfoldl]
      rw [Nat.max_eq_right hle]
      omega
    · obtain ⟨x_h, hx_h⟩ := ih hndv (Function.update acc v false)
      refine ⟨Function.update x_h v false, ?_⟩
      have hfoldl : vars.foldl (fun a u => Function.update a u (Function.update x_h v false u)) (Function.update acc v false)
          = vars.foldl (fun a u => Function.update a u (x_h u)) (Function.update acc v false) :=
        applyOn_congr vars _ _ (fun u hu => Function.update_of_ne (by rintro rfl; exact hv hu) _ _) _
      simp only [DTree.queryAll, DTree.depth, List.foldl_cons, List.length_cons,
        Function.update_self, hfoldl]
      rw [Nat.max_eq_left hle]
      omega

/-- **The deepest input.**  For distinct-variable clauses, the canonical tree's height is realised by
some input. -/
theorem exists_deep_input (cs : List (Clause n)) (w : ℕ)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool),
      ∃ x, (canonicalDTree cs w F σ).depth ≤ pathLen cs w F σ x := by
  intro F
  induction F with
  | zero => intro σ; exact ⟨fun _ => false, by simp [canonicalDTree, pathLen, DTree.depth]⟩
  | succ F ih =>
    intro σ
    cases hany : anyTermSat cs σ with
    | true => exact ⟨fun _ => false, by rw [canonicalDTree, pathLen]; simp [hany, DTree.depth]⟩
    | false =>
      cases hact : activeTerm cs σ with
      | none => exact ⟨fun _ => false, by rw [canonicalDTree, pathLen]; simp [hany, hact, DTree.depth]⟩
      | some T =>
        classical
        have hndT : (freeVarsOf σ T).Nodup := freeVarsOf_nodup (hnd T (activeTerm_mem hact))
        obtain ⟨x₀, hx₀⟩ := exists_queryAll_deep
          (fun a => if (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ a)
                    then DTree.leaf true else canonicalDTree cs w F (extendσ σ T a))
          (freeVarsOf σ T) hndT (fun _ => false)
        -- the leaf assignment of x₀ agrees with x₀ on the free variables
        set leaf₀ := (freeVarsOf σ T).foldl (fun a u => Function.update a u (x₀ u)) (fun _ => false)
          with hleaf
        have hcd : canonicalDTree cs w (F + 1) σ
            = DTree.queryAll (freeVarsOf σ T) (fun _ => false)
                (fun a => if (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ a)
                          then DTree.leaf true else canonicalDTree cs w F (extendσ σ T a)) := by
          rw [canonicalDTree]; simp only [hany, Bool.false_eq_true, if_false, hact]
        rw [hcd]
        -- the leaf condition / extension reduce to x₀'s
        rw [cond_leaf_eq σ T x₀, extendσ_leaf_eq σ T x₀] at hx₀
        by_cases hcx : (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x₀) = true
        · -- x₀ already satisfies: leaf true, depth ≤ #freeVars = pathLen x₀
          refine ⟨x₀, ?_⟩
          have hpl : pathLen cs w (F + 1) σ x₀ = (freeVarsOf σ T).length := by
            rw [pathLen]; simp only [hany, Bool.false_eq_true, if_false, hact, hcx, if_true, Nat.add_zero]
          rw [hpl]
          simp only [hcx, if_true, DTree.depth] at hx₀
          omega
        · -- x₀ falsifies: recurse via IH at extendσ σ T x₀, splice the inputs
          rw [Bool.not_eq_true] at hcx
          obtain ⟨x', hx'⟩ := ih (extendσ σ T x₀)
          refine ⟨fun i => if i ∈ freeVarsOf σ T then x₀ i else x' i, ?_⟩
          set x := fun i => if i ∈ freeVarsOf σ T then x₀ i else x' i with hxdef
          have hxfree : ∀ i ∈ freeVarsOf σ T, x i = x₀ i := fun i hi => by rw [hxdef]; simp [hi]
          have hcondx : (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x)
              = (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x₀) := by
            apply all_eq_of_pointwise
            intro ℓ hℓ
            rw [List.mem_filter] at hℓ
            exact eval_eq_of_var x x₀ ℓ (hxfree _ (litVar_mem_freeVarsOf hℓ.1 hℓ.2))
          have hextx : extendσ σ T x = extendσ σ T x₀ := by
            funext i
            rw [extendσ, extendσ]
            by_cases hi : i ∈ freeVarsOf σ T
            · rw [if_pos hi, if_pos hi, hxfree i hi]
            · rw [if_neg hi, if_neg hi]
          have hplx : pathLen cs w (F + 1) σ x = (freeVarsOf σ T).length + pathLen cs w F (extendσ σ T x₀) x := by
            rw [pathLen]
            simp only [hany, Bool.false_eq_true, if_false, hact, hcondx, hcx, hextx]
          have hloc : pathLen cs w F (extendσ σ T x₀) x = pathLen cs w F (extendσ σ T x₀) x' := by
            apply pathLen_eq_of_agree_on_free
            intro i hi
            rw [extendσ] at hi
            by_cases hiv : i ∈ freeVarsOf σ T
            · rw [if_pos hiv] at hi; simp at hi
            · rw [if_neg hiv] at hi; rw [hxdef]; simp [hiv]
          rw [hplx, hloc]
          simp only [hcx, Bool.false_eq_true, if_false] at hx₀
          omega

/-- **The branching-holography characterisation.**  For distinct-variable clauses, the canonical tree
has depth `≥ s` iff some input has a per-input path of length `≥ s`.  This is the object the branching
count encodes: `{ρ : depth ≥ s} = {ρ : ∃ x, pathLen ≥ s}`. -/
theorem depth_ge_iff_exists_pathLen_ge (cs : List (Clause n)) (w : ℕ)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) (F : ℕ) (σ : Fin n → Option Bool) (s : ℕ) :
    s ≤ (canonicalDTree cs w F σ).depth ↔ ∃ x, s ≤ pathLen cs w F σ x := by
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := exists_deep_input cs w hnd F σ
    exact ⟨x, le_trans hs hx⟩
  · rintro ⟨x, hx⟩
    exact le_trans hx (pathLen_le_depth cs w F σ x)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_deep_input
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.depth_ge_iff_exists_pathLen_ge
