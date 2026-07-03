import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameRestrictionSchedule

/-!
# N-Frame: multi-kill steps — the mechanism, the conditional theorem, and the B₂ obstruction

Superlinear gate elimination needs restrictions that kill **several** gates per step.  This file proves the
mechanism at full strength, the conditional multi-kill theorem it yields, and — honestly — the structural
obstruction that delimits it over the full binary basis.

  `occCount` / `subst_reduce_many` — **PROVED, the mechanism**: restricting a variable kills at least as many
        nodes as it has occurrences — every `var i` leaf becomes a constant absorbed into its parent operator
        (the absorption is proved leaf-by-leaf in one induction, parents folding constants as they arise).
  `budget_multikill` — **PROVED, the conditional theorem**: if every *volume-minimal* tree for `f` reads `xᵢ` at
        least `k ≥ 2` times, then `budget (f|ᵢ₌b) + k ≤ budget f` — a genuine `k`-kill.
  `read_once_normal_form` — **PROVED, the B₂ obstruction**: for *every* `f` and *every* `i` there is a tree
        computing `f` that reads `xᵢ` **once** — the Shannon-xor form `f = f₀ ⊕ (xᵢ ∧ (f₀ ⊕ f₁))`.  Hence
        `no_unconditional_occurrence_forcing`: occurrence bounds over all trees are impossible; the multi-kill
        premise can only come from **minimality analysis** — exactly why classical superlinear gate elimination
        retreats to restricted bases (no ⊕) or delicate optimal-circuit case analysis.

## Honest scope

The multi-kill engine is now complete and calibrated: mechanism proved, conditional theorem proved, and the
precise reason it cannot fire unconditionally proved.  What remains open for W2 is supplying the premise — a
minimality-exploiting occurrence bound for a concrete target (or the basis-restricted/DAG analogue) — the genuine
research core of superlinear circuit lower bounds.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Occurrences -/

/-- The number of `var i` leaves. -/
def occCount {n : ℕ} (i : Fin n) : Trans n → ℕ
  | .var j => if j = i then 1 else 0
  | .cst _ => 0
  | .un _ s => occCount i s
  | .bin _ s t => occCount i s + occCount i t

theorem occCount_substVar_self {n : ℕ} (i : Fin n) (b : Bool) (t : Trans n) :
    occCount i (substVar i b t) = 0 := by
  induction t with
  | var j =>
    by_cases hj : j = i
    · show occCount i (if j = i then Trans.cst b else Trans.var j) = 0
      rw [if_pos hj]
      rfl
    · show occCount i (if j = i then Trans.cst b else Trans.var j) = 0
      rw [if_neg hj]
      show (if j = i then 1 else 0) = 0
      rw [if_neg hj]
  | cst c => rfl
  | un op s ih =>
    show occCount i (substVar i b s) = 0
    exact ih
  | bin op s t ihs iht =>
    show occCount i (substVar i b s) + occCount i (substVar i b t) = 0
    omega

/-! ### The mechanism: restriction kills one node per occurrence -/

/-- **The multi-kill mechanism (proved)**: substituting `xᵢ ← b` admits an equivalent tree smaller by the full
occurrence count — every `var i` leaf is absorbed into its parent operator (a bare `var i` root is the only
exception, reported explicitly). -/
theorem subst_reduce_many {n : ℕ} (i : Fin n) (b : Bool) :
    ∀ t : Trans n, t = Trans.var i ∨
      ∃ t' : Trans n, eval t' = eval (substVar i b t) ∧
        volume t' + occCount i t ≤ volume t := by
  intro t
  induction t with
  | var j =>
    by_cases hj : j = i
    · left
      rw [hj]
    · right
      refine ⟨Trans.var j, ?_, ?_⟩
      · funext x
        show x j = eval (if j = i then Trans.cst b else Trans.var j) x
        rw [if_neg hj]
        rfl
      · show 1 + (if j = i then 1 else 0) ≤ 1
        rw [if_neg hj]
  | cst c =>
    right
    exact ⟨Trans.cst c, rfl, by
      show 1 + 0 ≤ 1
      omega⟩
  | un op s ih =>
    right
    rcases ih with hvar | ⟨s', hse, hsv⟩
    · subst hvar
      refine ⟨Trans.cst (op b), ?_, ?_⟩
      · funext x
        show op b = op (eval (if i = i then Trans.cst b else Trans.var i) x)
        rw [if_pos rfl]
        rfl
      · show 1 + (if i = i then 1 else 0) ≤ 1 + 1
        rw [if_pos rfl]
    · refine ⟨Trans.un op s', ?_, ?_⟩
      · funext x
        show op (eval s' x) = op (eval (substVar i b s) x)
        rw [hse]
      · show volume s' + 1 + occCount i s ≤ volume s + 1
        omega
  | bin op s t ihs iht =>
    right
    rcases ihs with hvs | ⟨s', hse, hsv⟩
    · rcases iht with hvt | ⟨t', hte, htv⟩
      · subst hvs
        subst hvt
        refine ⟨Trans.cst (op b b), ?_, ?_⟩
        · funext x
          show op b b = op (eval (if i = i then Trans.cst b else Trans.var i) x)
              (eval (if i = i then Trans.cst b else Trans.var i) x)
          rw [if_pos rfl]
          rfl
        · show 1 + ((if i = i then 1 else 0) + (if i = i then 1 else 0)) ≤ 1 + 1 + 1
          rw [if_pos rfl]
      · subst hvs
        refine ⟨Trans.un (fun a => op b a) t', ?_, ?_⟩
        · funext x
          show op b (eval t' x)
              = op (eval (if i = i then Trans.cst b else Trans.var i) x)
                (eval (substVar i b t) x)
          rw [if_pos rfl, hte]
          rfl
        · show volume t' + 1 + ((if i = i then 1 else 0) + occCount i t)
              ≤ 1 + volume t + 1
          rw [if_pos rfl]
          omega
    · rcases iht with hvt | ⟨t', hte, htv⟩
      · subst hvt
        refine ⟨Trans.un (fun a => op a b) s', ?_, ?_⟩
        · funext x
          show op (eval s' x) b
              = op (eval (substVar i b s) x)
                (eval (if i = i then Trans.cst b else Trans.var i) x)
          rw [if_pos rfl, hse]
          rfl
        · show volume s' + 1 + (occCount i s + (if i = i then 1 else 0))
              ≤ volume s + 1 + 1
          rw [if_pos rfl]
          omega
      · refine ⟨Trans.bin op s' t', ?_, ?_⟩
        · funext x
          show op (eval s' x) (eval t' x)
              = op (eval (substVar i b s) x) (eval (substVar i b t) x)
          rw [hse, hte]
        · show volume s' + volume t' + 1 + (occCount i s + occCount i t)
              ≤ volume s + volume t + 1
          omega

/-! ### The conditional multi-kill theorem -/

/-- **The multi-kill theorem (proved)**: a minimality-level occurrence bound converts into a genuine `k`-gate
kill: if every volume-minimal tree for `f` reads `xᵢ` at least `k ≥ 2` times, then
`budget (f|ᵢ₌b) + k ≤ budget f`. -/
theorem budget_multikill {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) (b : Bool)
    (k : ℕ) (hk : 2 ≤ k)
    (hocc : ∀ t : Trans n, eval t = f → volume t = budget f → k ≤ occCount i t) :
    budget (restrictF f i b) + k ≤ budget f := by
  have hne : {v | ∃ t : Trans n, eval t = f ∧ volume t = v}.Nonempty :=
    ⟨volume (dnfFor f), dnfFor f, eval_dnfFor f, rfl⟩
  obtain ⟨t, hte, htv⟩ := Nat.sInf_mem hne
  have hbud : volume t = budget f := htv
  have hoc := hocc t hte hbud
  rcases subst_reduce_many i b t with hvar | ⟨t', he, hv⟩
  · exfalso
    subst hvar
    have h1 : occCount i (Trans.var i) = 1 := by
      show (if i = i then 1 else 0) = 1
      rw [if_pos rfl]
    omega
  · have hcomp : eval t' = restrictF f i b := by
      funext x
      rw [he, substVar_eval, show eval t = f from hte]
      rfl
    have hb : budget (restrictF f i b) ≤ volume t' :=
      Nat.sInf_le ⟨t', hcomp, rfl⟩
    omega

/-! ### The B₂ obstruction: the read-once normal form -/

/-- **The read-once normal form (proved)**: for every `f` and every `i` there is a tree computing `f` reading
`xᵢ` exactly once — the Shannon-xor decomposition `f = f₀ ⊕ (xᵢ ∧ (f₀ ⊕ f₁))`. -/
theorem read_once_normal_form {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) :
    ∃ t : Trans n, eval t = f ∧ occCount i t ≤ 1 := by
  set g₀ : (Fin n → Bool) → Bool := fun x => f (Function.update x i false) with hg₀
  set g₁ : (Fin n → Bool) → Bool := fun x => f (Function.update x i true) with hg₁
  set T₀ : Trans n := substVar i false (dnfFor g₀) with hT₀
  set T₁ : Trans n := substVar i false (dnfFor g₁) with hT₁
  have hT₀e : ∀ x, eval T₀ x = g₀ x := by
    intro x
    rw [hT₀, substVar_eval, eval_dnfFor]
    show f (Function.update (Function.update x i false) i false) = f (Function.update x i false)
    rw [Function.update_idem]
  have hT₁e : ∀ x, eval T₁ x = g₁ x := by
    intro x
    rw [hT₁, substVar_eval, eval_dnfFor]
    show f (Function.update (Function.update x i false) i true) = f (Function.update x i true)
    rw [Function.update_idem]
  refine ⟨Trans.bin xor T₀ (Trans.bin and (Trans.var i) (Trans.bin xor T₀ T₁)), ?_, ?_⟩
  · funext x
    show xor (eval T₀ x) ((x i) && xor (eval T₀ x) (eval T₁ x)) = f x
    rw [hT₀e x, hT₁e x]
    cases hxi : x i
    · -- x i = false : f x = g₀ x
      have hxx : Function.update x i false = x := by
        rw [← hxi]
        exact Function.update_eq_self i x
      show xor (g₀ x) (false && xor (g₀ x) (g₁ x)) = f x
      rw [hg₀]
      show xor (f (Function.update x i false)) (false && _) = f x
      rw [hxx]
      cases f x <;> rfl
    · -- x i = true : f x = g₁ x
      have hxx : Function.update x i true = x := by
        rw [← hxi]
        exact Function.update_eq_self i x
      show xor (g₀ x) (true && xor (g₀ x) (g₁ x)) = f x
      rw [hg₀, hg₁]
      show xor (f (Function.update x i false)) (true && xor (f (Function.update x i false)) (f (Function.update x i true))) = f x
      rw [hxx]
      cases f (Function.update x i false) <;> cases f x <;> rfl
  · have h0 : occCount i T₀ = 0 := occCount_substVar_self i false (dnfFor g₀)
    have h1 : occCount i T₁ = 0 := occCount_substVar_self i false (dnfFor g₁)
    show occCount i T₀ + ((if i = i then 1 else 0) + (occCount i T₀ + occCount i T₁)) ≤ 1
    rw [if_pos rfl, h0, h1]

/-- **The delineation (proved)**: occurrence forcing over *all* trees is impossible — the multi-kill premise can
only come from minimality analysis. -/
theorem no_unconditional_occurrence_forcing {n : ℕ} (f : (Fin n → Bool) → Bool)
    (i : Fin n) :
    ¬(∀ t : Trans n, eval t = f → 2 ≤ occCount i t) := by
  intro h
  obtain ⟨t, ht, hocc⟩ := read_once_normal_form f i
  have := h t ht
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.subst_reduce_many
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.budget_multikill
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.read_once_normal_form
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.no_unconditional_occurrence_forcing
