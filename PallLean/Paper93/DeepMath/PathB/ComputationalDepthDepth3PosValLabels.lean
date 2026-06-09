import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PosLabels
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PosRecover
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DescentInject
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ExtendSat

/-!
# Block-DT model, route-2 step [155b]: the value-augmented freed-position label + injectivity (branch `razborov-recoverRho-wip`)

The audit (logged) found that the positions-only label `descentPosLabels` is **not injective when the deep
input `x` varies per restriction** — and the switching count uses `x = xσ(σ)`, which does vary.  The fix,
verified computationally (0 collisions under varying `x`), is to record the **freed value** `x v` alongside
each freed variable's in-term position.  This file builds that label and proves its injectivity.

* `descentPosValLabels` — `descentLabels` with each block's freed vars mapped to `(posInTerm, x v)` pairs.
* `descentPosValLabels_flatten_length` / `_block_nonempty` — content `= pathLen`, non-empty blocks.
* `descentPosValLabels_card_le` — `≤ (4·w+1)^k` over a fixed-content (`pathLen = k`) bad set, `F`-independent.
* `descentPosValLabels_injective` — `σ ↦ (descentSat …, descentPosValLabels …)` is injective, **even with the
  deep input varying per restriction**.

The injectivity proof is a **direct induction** comparing `σ₁` and `σ₂` (not a `recoverσ` left-inverse, which
fails on shared variables): equal boundaries give the same active term (`descentSat_firstSat`); equal labels
force equal freed-variable sets (`posInTerm_recover`) *and* equal freed values, so the depth-`F` boundaries
agree and the induction hypothesis closes the step.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The value-augmented freed-position label: `descentLabels` with each block's freed variables mapped to
their `(Fin w` position, freed value `x v)` pair. -/
def descentPosValLabels (cs : List (Clause n)) (w : ℕ) [NeZero w] :
    ℕ → (Fin n → Option Bool) → (Fin n → Bool) → List (List (Fin w × Bool))
  | 0, _, _ => []
  | F + 1, σ, x =>
    if anyTermSat cs σ then []
    else match activeTerm cs σ with
      | none => []
      | some T =>
        if (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) then
          [(freeVarsOf σ T).map (fun v => (posInTerm w T v, x v))]
        else (freeVarsOf σ T).map (fun v => (posInTerm w T v, x v))
              :: descentPosValLabels cs w F (extendσ σ T x) x

/-- **Content equals the path length.**  Mapping vars to `(position, value)` preserves block lengths. -/
theorem descentPosValLabels_flatten_length (cs : List (Clause n)) (w : ℕ) [NeZero w] :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      (descentPosValLabels cs w F σ x).flatten.length = pathLen cs w F σ x := by
  intro F
  induction F with
  | zero => intro σ x; simp [descentPosValLabels, pathLen]
  | succ F ih =>
    intro σ x
    rw [descentPosValLabels, pathLen]
    cases hany : anyTermSat cs σ with
    | true => simp [hany]
    | false =>
      cases hact : activeTerm cs σ with
      | none => simp [hany, hact]
      | some T =>
        simp only [hany, Bool.false_eq_true, if_false, hact]
        by_cases hsat : (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) = true
        · rw [if_pos hsat, if_pos hsat]; simp [List.length_map]
        · rw [if_neg hsat, if_neg hsat]
          rw [List.flatten_cons, List.length_append, List.length_map, ih (extendσ σ T x) x]

/-- **Every block is non-empty.** -/
theorem descentPosValLabels_block_nonempty (cs : List (Clause n)) (w : ℕ) [NeZero w] :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      ∀ b ∈ descentPosValLabels cs w F σ x, b ≠ [] := by
  intro F
  induction F with
  | zero => intro σ x b hb; rw [descentPosValLabels] at hb; simp at hb
  | succ F ih =>
    intro σ x b hb
    rw [descentPosValLabels] at hb
    cases hany : anyTermSat cs σ with
    | true => rw [hany] at hb; simp at hb
    | false =>
      cases hact : activeTerm cs σ with
      | none => simp only [hany, Bool.false_eq_true, if_false, hact] at hb; simp at hb
      | some T =>
        obtain ⟨v, hv, _⟩ := activeTerm_exists_free hact
        have hne : (freeVarsOf σ T).map (fun v => (posInTerm w T v, x v)) ≠ [] := by
          simp only [ne_eq, List.map_eq_nil_iff]; exact List.ne_nil_of_mem hv
        simp only [hany, Bool.false_eq_true, if_false, hact] at hb
        by_cases hsat : (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) = true
        · rw [if_pos hsat] at hb; rw [List.mem_singleton.mp hb]; exact hne
        · rw [if_neg hsat, List.mem_cons] at hb
          cases hb with
          | inl h => rw [h]; exact hne
          | inr h => exact ih (extendσ σ T x) x b h

/-- **The value-augmented label count is `(4·w+1)^k`, `F`-independent.** -/
theorem descentPosValLabels_card_le (cs : List (Clause n)) (w : ℕ) [NeZero w] (F : ℕ) (x : Fin n → Bool)
    (k : ℕ) {Bad : Finset (Fin n → Option Bool)}
    (hk : ∀ σ ∈ Bad, pathLen cs w F σ x = k) :
    (Bad.image (fun σ => descentPosValLabels cs w F σ x)).card ≤ (4 * w + 1) ^ k := by
  classical
  have hbound := nonempty_block_streams_card_le (α := Fin w × Bool) k
    (S := Bad.image (fun σ => descentPosValLabels cs w F σ x))
    (fun L hL b hb => by
      obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hL
      exact descentPosValLabels_block_nonempty cs w F σ x b hb)
    (fun L hL => by
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hL
      rw [descentPosValLabels_flatten_length, hk σ hσ])
  have hcard : Fintype.card (Fin w × Bool) = 2 * w := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; ring
  rw [hcard] at hbound
  calc (Bad.image (fun σ => descentPosValLabels cs w F σ x)).card
      ≤ (2 * (2 * w) + 1) ^ k := hbound
    _ = (4 * w + 1) ^ k := by ring_nf

/-! ### Injectivity (the centerpiece) -/

/-- A satisfied boundary produces no further labels. -/
theorem descentPosValLabels_nil_of_anySat (cs : List (Clause n)) (w : ℕ) [NeZero w]
    (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool) (h : anyTermSat cs σ = true) :
    descentPosValLabels cs w F σ x = [] := by
  cases F with
  | zero => rfl
  | succ F => rw [descentPosValLabels]; simp [h]

/-- **Uniform cons form.**  At an active step the label is `blk :: (tail)`, where the tail is the recursive
label on `extendσ` — this holds for *both* the satisfying step (where the tail is `[]`, since `extendσ`
satisfies the family) and the non-satisfying step. -/
theorem descentPosValLabels_succ_cons (cs : List (Clause n)) (w : ℕ) [NeZero w]
    (F : ℕ) {σ : Fin n → Option Bool} {T : Clause n} (x : Fin n → Bool)
    (hany : anyTermSat cs σ = false) (hact : activeTerm cs σ = some T) :
    descentPosValLabels cs w (F + 1) σ x
      = ((freeVarsOf σ T).map (fun v => (posInTerm w T v, x v)))
        :: descentPosValLabels cs w F (extendσ σ T x) x := by
  rw [descentPosValLabels]
  simp only [hany, Bool.false_eq_true, if_false, hact]
  by_cases hsat : (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) = true
  · rw [if_pos hsat,
      descentPosValLabels_nil_of_anySat cs w F (extendσ σ T x) x
        (extendσ_anyTermSat_of_allTrue hact hsat)]
  · rw [if_neg hsat]

/-- An empty label means the boundary is unchanged. -/
theorem descentSat_eq_self_of_posval_nil (cs : List (Clause n)) (w : ℕ) [NeZero w]
    (F : ℕ) {σ : Fin n → Option Bool} (x : Fin n → Bool)
    (h : descentPosValLabels cs w (F + 1) σ x = []) : descentSat cs w (F + 1) σ x = σ := by
  cases hany : anyTermSat cs σ with
  | true => rw [descentSat]; simp [hany]
  | false =>
    cases hact : activeTerm cs σ with
    | none => rw [descentSat]; simp [hany, hact]
    | some T =>
      exfalso
      rw [descentPosValLabels_succ_cons cs w F x hany hact] at h
      exact absurd h (List.cons_ne_nil _ _)

/-- **The value-augmented label is injective.**  `σ ↦ (descentSat …, descentPosValLabels …)` is injective,
**even with the deep input `x` varying per restriction** — the freed value recorded in each block forces the
depth-`F` boundaries to agree, so the induction closes. -/
theorem descentPosValLabels_injective (cs : List (Clause n)) (w : ℕ) [NeZero w]
    (hcons : ∀ T ∈ cs, Consistent T) (hw : ∀ T ∈ cs, T.lits.length ≤ w) :
    ∀ (F : ℕ) (σ₁ σ₂ : Fin n → Option Bool) (x₁ x₂ : Fin n → Bool),
      descentSat cs w F σ₁ x₁ = descentSat cs w F σ₂ x₂ →
      descentPosValLabels cs w F σ₁ x₁ = descentPosValLabels cs w F σ₂ x₂ →
      σ₁ = σ₂ := by
  intro F
  induction F with
  | zero => intro σ₁ σ₂ x₁ x₂ henc _; simpa only [descentSat] using henc
  | succ F ih =>
    intro σ₁ σ₂ x₁ x₂ henc hlbl
    -- σ₁: if no active term, the label is empty and the boundary is σ₁ itself.
    cases hany1 : anyTermSat cs σ₁ with
    | true =>
      have h1 : descentPosValLabels cs w (F + 1) σ₁ x₁ = [] :=
        descentPosValLabels_nil_of_anySat cs w (F + 1) σ₁ x₁ hany1
      have hs1 : descentSat cs w (F + 1) σ₁ x₁ = σ₁ := by rw [descentSat]; simp [hany1]
      have hs2 : descentSat cs w (F + 1) σ₂ x₂ = σ₂ :=
        descentSat_eq_self_of_posval_nil cs w F x₂ (h1 ▸ hlbl).symm
      rw [hs1, hs2] at henc; exact henc
    | false =>
      cases hact1 : activeTerm cs σ₁ with
      | none =>
        have h1 : descentPosValLabels cs w (F + 1) σ₁ x₁ = [] := by
          rw [descentPosValLabels]; simp [hany1, hact1]
        have hs1 : descentSat cs w (F + 1) σ₁ x₁ = σ₁ := by rw [descentSat]; simp [hany1, hact1]
        have hs2 : descentSat cs w (F + 1) σ₂ x₂ = σ₂ :=
          descentSat_eq_self_of_posval_nil cs w F x₂ (h1 ▸ hlbl).symm
        rw [hs1, hs2] at henc; exact henc
      | some T =>
        have hTmem : T ∈ cs := activeTerm_mem hact1
        -- σ₂ must also be active (the label is non-empty).
        have hcons1 := descentPosValLabels_succ_cons cs w F x₁ hany1 hact1
        have hl1ne : descentPosValLabels cs w (F + 1) σ₁ x₁ ≠ [] := by
          rw [hcons1]; exact List.cons_ne_nil _ _
        have hl2ne : descentPosValLabels cs w (F + 1) σ₂ x₂ ≠ [] := hlbl ▸ hl1ne
        cases hany2 : anyTermSat cs σ₂ with
        | true => exact absurd (descentPosValLabels_nil_of_anySat cs w (F + 1) σ₂ x₂ hany2) hl2ne
        | false =>
          cases hact2 : activeTerm cs σ₂ with
          | none =>
            exact absurd (by rw [descentPosValLabels]; simp [hany2, hact2] :
              descentPosValLabels cs w (F + 1) σ₂ x₂ = []) hl2ne
          | some T₂ =>
            -- the two active terms coincide: both are `find? termSat` of the common boundary.
            have hT1 : cs.find? (termSat (descentSat cs w (F + 1) σ₁ x₁)) = some T :=
              descentSat_firstSat x₁ (hcons T hTmem) hany1 hact1
            have hT2 : cs.find? (termSat (descentSat cs w (F + 1) σ₂ x₂)) = some T₂ :=
              descentSat_firstSat x₂ (hcons T₂ (activeTerm_mem hact2)) hany2 hact2
            have hTeq : T₂ = T := by
              have := hT1; rw [henc, hT2] at this; exact Option.some.inj this
            subst T₂
            -- peel the head block and the tail.
            have hcons2 := descentPosValLabels_succ_cons cs w F x₂ hany2 hact2
            rw [hcons1, hcons2, List.cons.injEq] at hlbl
            obtain ⟨hblk, htail⟩ := hlbl
            -- the freed-variable sets agree (positions round-trip to variables).
            have hfst : (freeVarsOf σ₁ T).map (posInTerm w T) = (freeVarsOf σ₂ T).map (posInTerm w T) := by
              have := congrArg (List.map Prod.fst) hblk
              simpa [List.map_map, Function.comp] using this
            have hrec : ∀ (σ : Fin n → Option Bool),
                ((freeVarsOf σ T).map (posInTerm w T)).map (fun p => (T.lits[p.val]?).map litVarOf)
                  = (freeVarsOf σ T).map some := by
              intro σ
              rw [List.map_map]
              apply List.map_congr_left
              intro u hu
              exact posInTerm_recover w (hw T hTmem) hu
            have hFV : freeVarsOf σ₁ T = freeVarsOf σ₂ T := by
              have h1 := hrec σ₁
              have h2 := hrec σ₂
              rw [hfst] at h1
              have : (freeVarsOf σ₁ T).map some = (freeVarsOf σ₂ T).map some := by rw [← h1, h2]
              exact List.map_injective_iff.mpr (Option.some_injective _) this
            -- the freed values agree (recorded in the block).
            have hvals : ∀ v ∈ freeVarsOf σ₁ T, x₁ v = x₂ v := by
              intro v hv
              have hb : (freeVarsOf σ₁ T).map (fun v => (posInTerm w T v, x₁ v))
                  = (freeVarsOf σ₁ T).map (fun v => (posInTerm w T v, x₂ v)) := by
                rw [hblk]; rw [hFV]
              have hpair : (posInTerm w T v, x₁ v) = (posInTerm w T v, x₂ v) :=
                (List.map_inj_left.mp hb) v hv
              exact congrArg Prod.snd hpair
            -- the depth-`F` boundaries agree (off the freed set by `henc`; on it by the recorded values).
            have hBeq : descentSat cs w F (extendσ σ₁ T x₁) x₁ = descentSat cs w F (extendσ σ₂ T x₂) x₂ := by
              funext v
              by_cases hv : v ∈ freeVarsOf σ₁ T
              · have e1 : descentSat cs w F (extendσ σ₁ T x₁) x₁ v = some (x₁ v) :=
                  descentSat_extends cs w F (extendσ σ₁ T x₁) x₁ v (x₁ v) (by rw [extendσ, if_pos hv])
                have hv2 : v ∈ freeVarsOf σ₂ T := hFV ▸ hv
                have e2 : descentSat cs w F (extendσ σ₂ T x₂) x₂ v = some (x₂ v) :=
                  descentSat_extends cs w F (extendσ σ₂ T x₂) x₂ v (x₂ v) (by rw [extendσ, if_pos hv2])
                rw [e1, e2, hvals v hv]
              · have hv2 : v ∉ freeVarsOf σ₂ T := fun hc => hv (hFV ▸ hc)
                have e1 : descentSat cs w (F + 1) σ₁ x₁ v = descentSat cs w F (extendσ σ₁ T x₁) x₁ v := by
                  rw [descentSat_succ_apply x₁ hany1 hact1, if_neg (not_cond_of_not_mem_free hv)]
                have e2 : descentSat cs w (F + 1) σ₂ x₂ v = descentSat cs w F (extendσ σ₂ T x₂) x₂ v := by
                  rw [descentSat_succ_apply x₂ hany2 hact2, if_neg (not_cond_of_not_mem_free hv2)]
                rw [← e1, ← e2, henc]
            -- recurse, then undo `extendσ`.
            have hext : extendσ σ₁ T x₁ = extendσ σ₂ T x₂ := ih _ _ x₁ x₂ hBeq htail
            funext v
            by_cases hv : v ∈ freeVarsOf σ₁ T
            · have hv2 : v ∈ freeVarsOf σ₂ T := hFV ▸ hv
              rw [mem_freeVarsOf_none hv, mem_freeVarsOf_none hv2]
            · have hv2 : v ∉ freeVarsOf σ₂ T := fun hc => hv (hFV ▸ hc)
              have hc := congrFun hext v
              rwa [extendσ_outside (x := x₁) hv, extendσ_outside (x := x₂) hv2] at hc

end PallLean.Paper93.DeepMath.PathB.Depth3
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descentPosValLabels_injective
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descentPosValLabels_card_le
