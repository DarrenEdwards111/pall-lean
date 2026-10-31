import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalDepthStars

/-!
# Block-DT model, foundation 33: the bridge obstruction, formally (branch only)

The obstruction of `...SwitchingBridgeObstruction` turned into a **proved theorem**: the single
`killTerm` path that `blockStream` follows is one branch of the branching `canonicalDTree`, so

> `blockStream.length ≤ canonicalDTree.depth`.

A *lower* bound on the depth — so the switching count (which bounds `blockStream.length`) cannot prove
`canonicalDTree` **shallow**.  This is the formal no-go, not a faked bridge.

* `queryAll_depth_ge` — `queryAll`'s depth is `≥ #vars + (depth of the continuation at any leaf)`.
* `extendσ_eq_killTerm` — the `killTerm` leaf of a block is `extendσ` at the falsifying assignment.
* `blockStream_length_le_canonicalDTree_depth` — the no-go inequality.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **`queryAll` depth lower bound.**  Querying `vars` then a continuation `k` is at least `#vars`
deep plus the depth of `k` at the leaf any input selects. -/
theorem queryAll_depth_ge (vars : List (Fin n)) (k : (Fin n → Bool) → DTree n) (x : Fin n → Bool) :
    ∀ (acc : Fin n → Bool),
      vars.length + (k (vars.foldl (fun a v => Function.update a v (x v)) acc)).depth
        ≤ (DTree.queryAll vars acc k).depth := by
  induction vars with
  | nil => intro acc; simp [DTree.queryAll]
  | cons v vars ih =>
    intro acc
    simp only [DTree.queryAll, DTree.depth, List.foldl_cons, List.length_cons]
    cases hxv : x v with
    | true =>
      have ih' := ih (Function.update acc v true)
      have hle := le_max_right (DTree.depth (DTree.queryAll vars (Function.update acc v false) k))
        (DTree.depth (DTree.queryAll vars (Function.update acc v true) k))
      omega
    | false =>
      have ih' := ih (Function.update acc v false)
      have hle := le_max_left (DTree.depth (DTree.queryAll vars (Function.update acc v false) k))
        (DTree.depth (DTree.queryAll vars (Function.update acc v true) k))
      omega

/-- The falsifying value of a variable for term `T` (what `killTerm` assigns to free coordinates). -/
def killVal (T : Clause n) (v : Fin n) : Option Bool :=
  if (Rung4Literal.pos v) ∈ T.lits then some false
  else if (Rung4Literal.neg v) ∈ T.lits then some true else none

/-- The "all-literals-false" input for term `T`. -/
def killInput (T : Clause n) : Fin n → Bool := fun v => (killVal T v).getD false

/-- A free variable of `T` has `killVal = some _`. -/
theorem killVal_isSome_of_mem_freeVarsOf {σ : Fin n → Option Bool} {T : Clause n} {v : Fin n}
    (hv : v ∈ freeVarsOf σ T) : (killVal T v).isSome := by
  rw [freeVarsOf, List.mem_filterMap] at hv
  obtain ⟨ℓ, hℓ, he⟩ := hv
  have hvar : litVarOf ℓ = v := by
    split at he <;> [injection he; simp at he]
  subst hvar
  cases ℓ with
  | pos i => simp only [killVal, litVarOf]; rw [if_pos hℓ]; rfl
  | neg i =>
    simp only [killVal, litVarOf]
    by_cases hp : (Rung4Literal.pos i) ∈ T.lits
    · rw [if_pos hp]; rfl
    · rw [if_neg hp, if_pos hℓ]; rfl

/-- A `none`-valued, non-free-of-`T` coordinate is not a variable of `T`'s literals. -/
theorem killVal_none_of_not_free {σ : Fin n → Option Bool} {T : Clause n} {v : Fin n}
    (hσ : σ v = none) (hv : v ∉ freeVarsOf σ T) : killVal T v = none := by
  by_contra hc
  rw [killVal] at hc
  have hmem : (Rung4Literal.pos v) ∈ T.lits ∨ (Rung4Literal.neg v) ∈ T.lits := by
    by_cases hp : (Rung4Literal.pos v) ∈ T.lits
    · exact Or.inl hp
    · by_cases hq : (Rung4Literal.neg v) ∈ T.lits
      · exact Or.inr hq
      · rw [if_neg hp, if_neg hq] at hc; exact absurd rfl hc
  apply hv
  rw [freeVarsOf, List.mem_filterMap]
  rcases hmem with hp | hq
  · exact ⟨Rung4Literal.pos v, hp, by simp only [litVarOf, hσ]; rfl⟩
  · exact ⟨Rung4Literal.neg v, hq, by simp only [litVarOf, hσ]; rfl⟩

/-- **The `killTerm` leaf is `extendσ` at the falsifying input.**  For the leaf assignment that agrees
with `killInput` on the queried variables, `extendσ` reproduces `killTerm`. -/
theorem extendσ_eq_killTerm {σ : Fin n → Option Bool} {T : Clause n} {acc : Fin n → Bool} :
    extendσ σ T (freeVarsOf σ T |>.foldl
        (fun a v => Function.update a v (killInput T v)) acc)
      = killTerm σ T := by
  funext v
  have hkill : killTerm σ T v = if σ v = none then killVal T v else σ v := rfl
  rw [extendσ, hkill]
  by_cases hv : v ∈ freeVarsOf σ T
  · rw [if_pos hv]
    have hσv : σ v = none := mem_freeVarsOf_none hv
    rw [foldl_update_mem (freeVarsOf σ T) (killInput T) acc v hv, if_pos hσv, killInput]
    have hsome := killVal_isSome_of_mem_freeVarsOf hv
    cases hk : killVal T v with
    | none => rw [hk] at hsome; simp at hsome
    | some b => rfl
  · rw [if_neg hv]
    by_cases hσv : σ v = none
    · rw [if_pos hσv, killVal_none_of_not_free hσv hv]; exact hσv
    · rw [if_neg hσv]

/-- The active term has a free variable (so its block queries at least one variable). -/
theorem freeVarsOf_length_pos {cs : List (Clause n)} {σ : Fin n → Option Bool} {T : Clause n}
    (hact : activeTerm cs σ = some T) : 0 < (freeVarsOf σ T).length := by
  obtain ⟨v, hv, _⟩ := activeTerm_exists_free hact
  exact List.length_pos_of_mem hv

/-- **The bridge no-go.**  The single `killTerm` path is a branch of the branching canonical tree, so its
length lower-bounds the tree's depth. -/
theorem blockStream_length_le_canonicalDTree_depth (cs : List (Clause n)) (w : ℕ) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool),
      (blockStream cs F σ).length ≤ (canonicalDTree cs w F σ).depth := by
  intro F
  induction F with
  | zero => intro σ; simp [blockStream]
  | succ F ih =>
    intro σ
    rw [canonicalDTree, blockStream]
    cases hany : anyTermSat cs σ with
    | true => simp [DTree.depth]
    | false =>
      cases hact : activeTerm cs σ with
      | none => simp [DTree.depth]
      | some T =>
        simp only [Bool.false_eq_true, if_false, List.length_cons]
        -- depth of queryAll ≥ |freeVarsOf| + depth(k at killInput leaf)
        have hge := queryAll_depth_ge (freeVarsOf σ T)
          (fun a => if (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ a)
                    then DTree.leaf true else canonicalDTree cs w F (extendσ σ T a))
          (killInput T) (fun _ => false)
        -- the killInput leaf falsifies T, so the continuation recurses with killTerm σ T
        have hcondfalse : (T.lits.filter (DTree.freeLit σ)).all
            (fun ℓ => Rung4Literal.eval ℓ
              ((freeVarsOf σ T).foldl (fun b v => Function.update b v (killInput T v))
                (fun _ => false))) = false := by
          obtain ⟨v, hvfree, hvnone⟩ := activeTerm_exists_free hact
          rw [List.all_eq_false]
          have hav : (freeVarsOf σ T).foldl (fun b v => Function.update b v (killInput T v))
              (fun _ => false) v = killInput T v :=
            foldl_update_mem (freeVarsOf σ T) (killInput T) _ _ hvfree
          have hfp : DTree.freeLit σ (Rung4Literal.pos v) = true := by
            simp [DTree.freeLit, hvnone]
          have hfn : DTree.freeLit σ (Rung4Literal.neg v) = true := by
            simp [DTree.freeLit, hvnone]
          by_cases hp : (Rung4Literal.pos v) ∈ T.lits
          · refine ⟨Rung4Literal.pos v, List.mem_filter.mpr ⟨hp, hfp⟩, ?_⟩
            have heval : Rung4Literal.eval (Rung4Literal.pos v)
                ((freeVarsOf σ T).foldl (fun b v => Function.update b v (killInput T v))
                  (fun _ => false)) = false := by
              simp only [Rung4Literal.eval]
              rw [hav, killInput, killVal, if_pos hp]
              rfl
            rw [heval]; decide
          · have hq : (Rung4Literal.neg v) ∈ T.lits := by
              have hsome := killVal_isSome_of_mem_freeVarsOf hvfree
              rw [killVal, if_neg hp] at hsome
              by_contra hqn; rw [if_neg hqn] at hsome; simp at hsome
            refine ⟨Rung4Literal.neg v, List.mem_filter.mpr ⟨hq, hfn⟩, ?_⟩
            have heval : Rung4Literal.eval (Rung4Literal.neg v)
                ((freeVarsOf σ T).foldl (fun b v => Function.update b v (killInput T v))
                  (fun _ => false)) = false := by
              simp only [Rung4Literal.eval]
              rw [hav, killInput, killVal, if_neg hp, if_pos hq]
              rfl
            rw [heval]; decide
        simp only [hcondfalse, Bool.false_eq_true, if_false] at hge
        rw [show extendσ σ T ((freeVarsOf σ T).foldl
              (fun b v => Function.update b v (killInput T v)) (fun _ => false)) = killTerm σ T
            from extendσ_eq_killTerm] at hge
        have hpos := freeVarsOf_length_pos hact
        have hih := ih (killTerm σ T)
        omega

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.blockStream_length_le_canonicalDTree_depth
