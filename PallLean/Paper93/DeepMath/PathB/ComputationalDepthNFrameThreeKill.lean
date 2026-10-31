import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTwoKillSchedule

/-!
# N-Frame: the cascade theorem — `occ + 1` kills, and the conditional three-kill

The two-kill sharpens into a **cascade**: restricting a variable of a non-top-decomposable function loses one node
per occurrence *plus one more* — every occurrence's constant absorbs into its parent, and at least one freed head
folds or fuses further up.  The five-clause invariant (`cascade_collapse`) tracks: full cascade (loss `≥ occ+1`),
a fusable head at loss `≥ occ` (constant head carrying a unarity witness, unary head carrying the
direct-child-of-root shape), the bare leaf, and the occurrence-free case.  Heads never survive combination: every
binary node folds or fuses them, so the fusable clauses reach the root only in the top-decomposable shapes.

  `cascade_collapse` — **PROVED, the invariant** (for every restriction value).
  `budget_cascade` — **PROVED**: `DependsOnF f i → ¬TopDecomp f i → ∀ b`, every volume-minimal tree `t` gives
        `budget (f|ᵢ₌b) + occCount i t + 1 ≤ budget f`.
  `budget_threekill` — **PROVED, the conditional three-kill**: if additionally every minimal tree reads `xᵢ`
        twice, then `budget (f|ᵢ₌b) + 3 ≤ budget f` for every `b`.

## Honest scope

The mechanism is now exact: `occ + 1` kills, unconditionally beyond top decomposition.  The three-kill premise —
minimal trees read the variable twice — is precisely the delicate classical ingredient: the read-once normal form
(`no_unconditional_occurrence_forcing`) shows it can never hold for all trees, so it must come from minimality
analysis of a concrete target; no sat3 instance is claimed here.  Superlinear still requires the DAG analogue.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The cascade invariant -/

/-- **The cascade collapse (proved)**: beyond the occurrence-free, bare-leaf, and fusable-head cases, restriction
loses `occCount + 1` nodes. -/
theorem cascade_collapse {n : ℕ} (i : Fin n) (b : Bool) :
    ∀ t : Trans n,
      occCount i t = 0 ∨ t = Trans.var i ∨
      ∃ t' : Trans n, eval t' = eval (substVar i b t) ∧
        (volume t' + occCount i t + 1 ≤ volume t ∨
         (volume t' + occCount i t ≤ volume t ∧
           ((∃ cc, t' = Trans.cst cc) ∧ (∃ u : Bool → Bool, ∀ x, eval t x = u (x i)) ∨
            (∃ u₀ s₀, t' = Trans.un u₀ s₀) ∧
              ∃ (op : Bool → Bool → Bool) (s : Trans n),
                (t = Trans.bin op (Trans.var i) s ∨ t = Trans.bin op s (Trans.var i)) ∧
                occCount i s = 0))) := by
  intro t
  induction t with
  | var j =>
    by_cases hj : j = i
    · right; left
      rw [hj]
    · left
      show (if j = i then 1 else 0) = 0
      rw [if_neg hj]
  | cst c => left; rfl
  | un u₁ s ih =>
    rcases ih with hE | hD | ⟨s', hse, hcase⟩
    · left
      exact hE
    · -- unary over the bare leaf: constant head with unarity witness
      right; right
      subst hD
      refine ⟨Trans.cst (u₁ b), ?_, Or.inr ⟨?_, Or.inl ⟨⟨u₁ b, rfl⟩, u₁, fun x => rfl⟩⟩⟩
      · funext x
        show u₁ b = u₁ (eval (if i = i then Trans.cst b else Trans.var i) x)
        rw [if_pos rfl]
        rfl
      · show 1 + (if i = i then 1 else 0) ≤ 1 + 1
        rw [if_pos rfl]
    · right; right
      rcases hcase with hA | ⟨hle, hPc | hPu⟩
      · -- child cascade: wrap
        refine ⟨Trans.un u₁ s', ?_, Or.inl ?_⟩
        · funext x
          show u₁ (eval s' x) = u₁ (eval (substVar i b s) x)
          rw [hse]
        · show volume s' + 1 + occCount i s + 1 ≤ volume s + 1
          omega
      · -- constant head folds: one more kill
        obtain ⟨⟨cc, rfl⟩, u, hu⟩ := hPc
        refine ⟨Trans.cst (u₁ cc), ?_, Or.inl ?_⟩
        · funext x
          show u₁ cc = u₁ (eval (substVar i b s) x)
          rw [← hse]
          rfl
        · show 1 + occCount i s + 1 ≤ volume s + 1
          have h1 : volume (Trans.cst cc : Trans n) = 1 := rfl
          omega
      · -- unary head fuses: one more kill
        obtain ⟨⟨u₀, s₀, rfl⟩, -⟩ := hPu
        refine ⟨Trans.un (fun a => u₁ (u₀ a)) s₀, ?_, Or.inl ?_⟩
        · funext x
          show u₁ (u₀ (eval s₀ x)) = u₁ (eval (substVar i b s) x)
          rw [← hse]
          rfl
        · show volume s₀ + 1 + occCount i s + 1 ≤ volume s + 1
          have h1 : volume (Trans.un u₀ s₀) = volume s₀ + 1 := rfl
          omega
  | bin op s₁ s₂ ih₁ ih₂ =>
    have hocc : occCount i (Trans.bin op s₁ s₂) = occCount i s₁ + occCount i s₂ := rfl
    rcases ih₁ with hE₁ | hD₁ | ⟨t₁', he₁, hc₁⟩
    · -- left side occurrence-free: use its plain substitution
      rcases ih₂ with hE₂ | hD₂ | ⟨t₂', he₂, hc₂⟩
      · left
        show occCount i s₁ + occCount i s₂ = 0
        omega
      · -- E/D: absorb the right leaf, unary head with shape
        right; right
        subst hD₂
        refine ⟨Trans.un (fun a => op a b) (substVar i b s₁), ?_,
          Or.inr ⟨?_, Or.inr ⟨⟨fun a => op a b, substVar i b s₁, rfl⟩,
            op, s₁, Or.inr rfl, hE₁⟩⟩⟩
        · funext x
          show op (eval (substVar i b s₁) x) b
              = op (eval (substVar i b s₁) x)
                (eval (if i = i then Trans.cst b else Trans.var i) x)
          rw [if_pos rfl]
          rfl
        · show volume (substVar i b s₁) + 1 + (occCount i s₁ + (if i = i then 1 else 0))
              ≤ volume s₁ + 1 + 1
          rw [substVar_volume, if_pos rfl]
          omega
      · rcases hc₂ with hA₂ | ⟨hle₂, hPc₂ | hPu₂⟩
        · -- E/A
          right; right
          refine ⟨Trans.bin op (substVar i b s₁) t₂', ?_, Or.inl ?_⟩
          · funext x
            show op (eval (substVar i b s₁) x) (eval t₂' x)
                = op (eval (substVar i b s₁) x) (eval (substVar i b s₂) x)
            rw [he₂]
          · show volume (substVar i b s₁) + volume t₂' + 1
                + (occCount i s₁ + occCount i s₂) + 1 ≤ volume s₁ + volume s₂ + 1
            rw [substVar_volume]
            omega
        · -- E/Pc: absorb the constant head
          obtain ⟨⟨cc, rfl⟩, -⟩ := hPc₂
          right; right
          refine ⟨Trans.un (fun a => op a cc) (substVar i b s₁), ?_, Or.inl ?_⟩
          · funext x
            show op (eval (substVar i b s₁) x) cc
                = op (eval (substVar i b s₁) x) (eval (substVar i b s₂) x)
            rw [← he₂]
            rfl
          · show volume (substVar i b s₁) + 1
                + (occCount i s₁ + occCount i s₂) + 1 ≤ volume s₁ + volume s₂ + 1
            rw [substVar_volume]
            have h1 : volume (Trans.cst cc : Trans n) = 1 := rfl
            omega
        · -- E/Pu: fuse the unary head
          obtain ⟨⟨u₀, s₀, rfl⟩, -⟩ := hPu₂
          right; right
          refine ⟨Trans.bin (fun a c => op a (u₀ c)) (substVar i b s₁) s₀, ?_, Or.inl ?_⟩
          · funext x
            show op (eval (substVar i b s₁) x) (u₀ (eval s₀ x))
                = op (eval (substVar i b s₁) x) (eval (substVar i b s₂) x)
            rw [← he₂]
            rfl
          · show volume (substVar i b s₁) + volume s₀ + 1
                + (occCount i s₁ + occCount i s₂) + 1 ≤ volume s₁ + volume s₂ + 1
            rw [substVar_volume]
            have h1 : volume (Trans.un u₀ s₀) = volume s₀ + 1 := rfl
            omega
    · -- left side is the bare leaf
      subst hD₁
      rcases ih₂ with hE₂ | hD₂ | ⟨t₂', he₂, hc₂⟩
      · -- D/E: absorb the left leaf, unary head with shape
        right; right
        refine ⟨Trans.un (fun c => op b c) (substVar i b s₂), ?_,
          Or.inr ⟨?_, Or.inr ⟨⟨fun c => op b c, substVar i b s₂, rfl⟩,
            op, s₂, Or.inl rfl, hE₂⟩⟩⟩
        · funext x
          show op b (eval (substVar i b s₂) x)
              = op (eval (if i = i then Trans.cst b else Trans.var i) x)
                (eval (substVar i b s₂) x)
          rw [if_pos rfl]
          rfl
        · show volume (substVar i b s₂) + 1 + ((if i = i then 1 else 0) + occCount i s₂)
              ≤ 1 + volume s₂ + 1
          rw [substVar_volume, if_pos rfl]
          omega
      · -- D/D: both leaves fold to one constant, unarity witness
        subst hD₂
        right; right
        refine ⟨Trans.cst (op b b), ?_, Or.inr ⟨?_,
          Or.inl ⟨⟨op b b, rfl⟩, fun a => op a a, fun x => rfl⟩⟩⟩
        · funext x
          show op b b = op (eval (if i = i then Trans.cst b else Trans.var i) x)
              (eval (if i = i then Trans.cst b else Trans.var i) x)
          rw [if_pos rfl]
          rfl
        · show 1 + ((if i = i then 1 else 0) + (if i = i then 1 else 0)) ≤ 1 + 1 + 1
          rw [if_pos rfl]
      · rcases hc₂ with hA₂ | ⟨hle₂, hPc₂ | hPu₂⟩
        · -- D/A: absorb left leaf onto the cascaded right
          right; right
          refine ⟨Trans.un (fun c => op b c) t₂', ?_, Or.inl ?_⟩
          · funext x
            show op b (eval t₂' x)
                = op (eval (if i = i then Trans.cst b else Trans.var i) x)
                  (eval (substVar i b s₂) x)
            rw [if_pos rfl, he₂]
            rfl
          · show volume t₂' + 1 + ((if i = i then 1 else 0) + occCount i s₂) + 1
                ≤ 1 + volume s₂ + 1
            rw [if_pos rfl]
            omega
        · -- D/Pc: fold everything to one constant
          obtain ⟨⟨cc, rfl⟩, -⟩ := hPc₂
          right; right
          refine ⟨Trans.cst (op b cc), ?_, Or.inl ?_⟩
          · funext x
            show op b cc
                = op (eval (if i = i then Trans.cst b else Trans.var i) x)
                  (eval (substVar i b s₂) x)
            rw [if_pos rfl, ← he₂]
            rfl
          · show 1 + ((if i = i then 1 else 0) + occCount i s₂) + 1
                ≤ 1 + volume s₂ + 1
            rw [if_pos rfl]
            have h1 : volume (Trans.cst cc : Trans n) = 1 := rfl
            omega
        · -- D/Pu: absorb left leaf, fuse right head
          obtain ⟨⟨u₀, s₀, rfl⟩, -⟩ := hPu₂
          right; right
          refine ⟨Trans.un (fun c => op b (u₀ c)) s₀, ?_, Or.inl ?_⟩
          · funext x
            show op b (u₀ (eval s₀ x))
                = op (eval (if i = i then Trans.cst b else Trans.var i) x)
                  (eval (substVar i b s₂) x)
            rw [if_pos rfl, ← he₂]
            rfl
          · show volume s₀ + 1 + ((if i = i then 1 else 0) + occCount i s₂) + 1
                ≤ 1 + volume s₂ + 1
            rw [if_pos rfl]
            have h1 : volume (Trans.un u₀ s₀) = volume s₀ + 1 := rfl
            omega
    · -- left side carries occurrences with a result
      rcases ih₂ with hE₂ | hD₂ | ⟨t₂', he₂, hc₂⟩
      · rcases hc₁ with hA₁ | ⟨hle₁, hPc₁ | hPu₁⟩
        · -- A/E
          right; right
          refine ⟨Trans.bin op t₁' (substVar i b s₂), ?_, Or.inl ?_⟩
          · funext x
            show op (eval t₁' x) (eval (substVar i b s₂) x)
                = op (eval (substVar i b s₁) x) (eval (substVar i b s₂) x)
            rw [he₁]
          · show volume t₁' + volume (substVar i b s₂) + 1
                + (occCount i s₁ + occCount i s₂) + 1 ≤ volume s₁ + volume s₂ + 1
            rw [substVar_volume]
            omega
        · -- Pc/E
          obtain ⟨⟨cc, rfl⟩, -⟩ := hPc₁
          right; right
          refine ⟨Trans.un (fun c => op cc c) (substVar i b s₂), ?_, Or.inl ?_⟩
          · funext x
            show op cc (eval (substVar i b s₂) x)
                = op (eval (substVar i b s₁) x) (eval (substVar i b s₂) x)
            rw [← he₁]
            rfl
          · show volume (substVar i b s₂) + 1
                + (occCount i s₁ + occCount i s₂) + 1 ≤ volume s₁ + volume s₂ + 1
            rw [substVar_volume]
            have h1 : volume (Trans.cst cc : Trans n) = 1 := rfl
            omega
        · -- Pu/E
          obtain ⟨⟨u₀, s₀, rfl⟩, -⟩ := hPu₁
          right; right
          refine ⟨Trans.bin (fun a c => op (u₀ a) c) s₀ (substVar i b s₂), ?_, Or.inl ?_⟩
          · funext x
            show op (u₀ (eval s₀ x)) (eval (substVar i b s₂) x)
                = op (eval (substVar i b s₁) x) (eval (substVar i b s₂) x)
            rw [← he₁]
            rfl
          · show volume s₀ + volume (substVar i b s₂) + 1
                + (occCount i s₁ + occCount i s₂) + 1 ≤ volume s₁ + volume s₂ + 1
            rw [substVar_volume]
            have h1 : volume (Trans.un u₀ s₀) = volume s₀ + 1 := rfl
            omega
      · -- right side is the bare leaf
        subst hD₂
        rcases hc₁ with hA₁ | ⟨hle₁, hPc₁ | hPu₁⟩
        · -- A/D
          right; right
          refine ⟨Trans.un (fun a => op a b) t₁', ?_, Or.inl ?_⟩
          · funext x
            show op (eval t₁' x) b
                = op (eval (substVar i b s₁) x)
                  (eval (if i = i then Trans.cst b else Trans.var i) x)
            rw [if_pos rfl, he₁]
            rfl
          · show volume t₁' + 1 + (occCount i s₁ + (if i = i then 1 else 0)) + 1
                ≤ volume s₁ + 1 + 1
            rw [if_pos rfl]
            omega
        · -- Pc/D
          obtain ⟨⟨cc, rfl⟩, -⟩ := hPc₁
          right; right
          refine ⟨Trans.cst (op cc b), ?_, Or.inl ?_⟩
          · funext x
            show op cc b
                = op (eval (substVar i b s₁) x)
                  (eval (if i = i then Trans.cst b else Trans.var i) x)
            rw [if_pos rfl, ← he₁]
            rfl
          · show 1 + (occCount i s₁ + (if i = i then 1 else 0)) + 1
                ≤ volume s₁ + 1 + 1
            rw [if_pos rfl]
            have h1 : volume (Trans.cst cc : Trans n) = 1 := rfl
            omega
        · -- Pu/D
          obtain ⟨⟨u₀, s₀, rfl⟩, -⟩ := hPu₁
          right; right
          refine ⟨Trans.un (fun a => op (u₀ a) b) s₀, ?_, Or.inl ?_⟩
          · funext x
            show op (u₀ (eval s₀ x)) b
                = op (eval (substVar i b s₁) x)
                  (eval (if i = i then Trans.cst b else Trans.var i) x)
            rw [if_pos rfl, ← he₁]
            rfl
          · show volume s₀ + 1 + (occCount i s₁ + (if i = i then 1 else 0)) + 1
                ≤ volume s₁ + 1 + 1
            rw [if_pos rfl]
            have h1 : volume (Trans.un u₀ s₀) = volume s₀ + 1 := rfl
            omega
      · -- both sides carry results
        rcases hc₁ with hA₁ | ⟨hle₁, hPc₁ | hPu₁⟩ <;>
          rcases hc₂ with hA₂ | ⟨hle₂, hPc₂ | hPu₂⟩
        · -- A/A
          right; right
          refine ⟨Trans.bin op t₁' t₂', ?_, Or.inl ?_⟩
          · funext x
            show op (eval t₁' x) (eval t₂' x)
                = op (eval (substVar i b s₁) x) (eval (substVar i b s₂) x)
            rw [he₁, he₂]
          · show volume t₁' + volume t₂' + 1
                + (occCount i s₁ + occCount i s₂) + 1 ≤ volume s₁ + volume s₂ + 1
            omega
        · -- A/Pc
          obtain ⟨⟨cc, rfl⟩, -⟩ := hPc₂
          right; right
          refine ⟨Trans.un (fun a => op a cc) t₁', ?_, Or.inl ?_⟩
          · funext x
            show op (eval t₁' x) cc
                = op (eval (substVar i b s₁) x) (eval (substVar i b s₂) x)
            rw [he₁, ← he₂]
            rfl
          · show volume t₁' + 1 + (occCount i s₁ + occCount i s₂) + 1
                ≤ volume s₁ + volume s₂ + 1
            have h1 : volume (Trans.cst cc : Trans n) = 1 := rfl
            omega
        · -- A/Pu
          obtain ⟨⟨u₀, s₀, rfl⟩, -⟩ := hPu₂
          right; right
          refine ⟨Trans.bin (fun a c => op a (u₀ c)) t₁' s₀, ?_, Or.inl ?_⟩
          · funext x
            show op (eval t₁' x) (u₀ (eval s₀ x))
                = op (eval (substVar i b s₁) x) (eval (substVar i b s₂) x)
            rw [he₁, ← he₂]
            rfl
          · show volume t₁' + volume s₀ + 1 + (occCount i s₁ + occCount i s₂) + 1
                ≤ volume s₁ + volume s₂ + 1
            have h1 : volume (Trans.un u₀ s₀) = volume s₀ + 1 := rfl
            omega
        · -- Pc/A
          obtain ⟨⟨cc, rfl⟩, -⟩ := hPc₁
          right; right
          refine ⟨Trans.un (fun c => op cc c) t₂', ?_, Or.inl ?_⟩
          · funext x
            show op cc (eval t₂' x)
                = op (eval (substVar i b s₁) x) (eval (substVar i b s₂) x)
            rw [he₂, ← he₁]
            rfl
          · show volume t₂' + 1 + (occCount i s₁ + occCount i s₂) + 1
                ≤ volume s₁ + volume s₂ + 1
            have h1 : volume (Trans.cst cc : Trans n) = 1 := rfl
            omega
        · -- Pc/Pc
          obtain ⟨⟨c₁, rfl⟩, -⟩ := hPc₁
          obtain ⟨⟨c₂, rfl⟩, -⟩ := hPc₂
          right; right
          refine ⟨Trans.cst (op c₁ c₂), ?_, Or.inl ?_⟩
          · funext x
            show op c₁ c₂
                = op (eval (substVar i b s₁) x) (eval (substVar i b s₂) x)
            rw [← he₁, ← he₂]
            rfl
          · show 1 + (occCount i s₁ + occCount i s₂) + 1
                ≤ volume s₁ + volume s₂ + 1
            have h1 : volume (Trans.cst c₁ : Trans n) = 1 := rfl
            have h2 : volume (Trans.cst c₂ : Trans n) = 1 := rfl
            omega
        · -- Pc/Pu
          obtain ⟨⟨c₁, rfl⟩, -⟩ := hPc₁
          obtain ⟨⟨u₀, s₀, rfl⟩, -⟩ := hPu₂
          right; right
          refine ⟨Trans.un (fun c => op c₁ (u₀ c)) s₀, ?_, Or.inl ?_⟩
          · funext x
            show op c₁ (u₀ (eval s₀ x))
                = op (eval (substVar i b s₁) x) (eval (substVar i b s₂) x)
            rw [← he₁, ← he₂]
            rfl
          · show volume s₀ + 1 + (occCount i s₁ + occCount i s₂) + 1
                ≤ volume s₁ + volume s₂ + 1
            have h1 : volume (Trans.cst c₁ : Trans n) = 1 := rfl
            have h2 : volume (Trans.un u₀ s₀) = volume s₀ + 1 := rfl
            omega
        · -- Pu/A
          obtain ⟨⟨u₀, s₀, rfl⟩, -⟩ := hPu₁
          right; right
          refine ⟨Trans.bin (fun a c => op (u₀ a) c) s₀ t₂', ?_, Or.inl ?_⟩
          · funext x
            show op (u₀ (eval s₀ x)) (eval t₂' x)
                = op (eval (substVar i b s₁) x) (eval (substVar i b s₂) x)
            rw [he₂, ← he₁]
            rfl
          · show volume s₀ + volume t₂' + 1 + (occCount i s₁ + occCount i s₂) + 1
                ≤ volume s₁ + volume s₂ + 1
            have h1 : volume (Trans.un u₀ s₀) = volume s₀ + 1 := rfl
            omega
        · -- Pu/Pc
          obtain ⟨⟨u₀, s₀, rfl⟩, -⟩ := hPu₁
          obtain ⟨⟨c₂, rfl⟩, -⟩ := hPc₂
          right; right
          refine ⟨Trans.un (fun a => op (u₀ a) c₂) s₀, ?_, Or.inl ?_⟩
          · funext x
            show op (u₀ (eval s₀ x)) c₂
                = op (eval (substVar i b s₁) x) (eval (substVar i b s₂) x)
            rw [← he₁, ← he₂]
            rfl
          · show volume s₀ + 1 + (occCount i s₁ + occCount i s₂) + 1
                ≤ volume s₁ + volume s₂ + 1
            have h1 : volume (Trans.un u₀ s₀) = volume s₀ + 1 := rfl
            have h2 : volume (Trans.cst c₂ : Trans n) = 1 := rfl
            omega
        · -- Pu/Pu
          obtain ⟨⟨u₁, s₀₁, rfl⟩, -⟩ := hPu₁
          obtain ⟨⟨u₂, s₀₂, rfl⟩, -⟩ := hPu₂
          right; right
          refine ⟨Trans.bin (fun a c => op (u₁ a) (u₂ c)) s₀₁ s₀₂, ?_, Or.inl ?_⟩
          · funext x
            show op (u₁ (eval s₀₁ x)) (u₂ (eval s₀₂ x))
                = op (eval (substVar i b s₁) x) (eval (substVar i b s₂) x)
            rw [← he₁, ← he₂]
            rfl
          · show volume s₀₁ + volume s₀₂ + 1 + (occCount i s₁ + occCount i s₂) + 1
                ≤ volume s₁ + volume s₂ + 1
            have h1 : volume (Trans.un u₁ s₀₁) = volume s₀₁ + 1 := rfl
            have h2 : volume (Trans.un u₂ s₀₂) = volume s₀₂ + 1 := rfl
            omega

/-! ### The function-level cascade and the conditional three-kill -/

/-- **The cascade at the budget level (proved)**: for dependent, non-top-decomposable `f`, every minimal tree's
occurrence count converts, plus one, into killed gates — for every restriction value. -/
theorem budget_cascade {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n)
    (hdep : DependsOnF f i) (hnt : ¬TopDecomp f i) (b : Bool) :
    ∀ t : Trans n, eval t = f → volume t = budget f →
      budget (restrictF f i b) + occCount i t + 1 ≤ budget f := by
  intro t hte htv
  obtain ⟨x₁, x₀, hd, hnev⟩ := hdep
  have hvar : hasVar i t = true := by
    apply hasVar_of_depends i t x₁ x₀ (fun c hc => by
      by_contra hcc
      exact hc (hd c hcc))
    rw [show eval t = f from hte]
    exact hnev
  have hocc := hasVar_occ_pos i t hvar
  rcases cascade_collapse i b t with hE | hD | ⟨t', he, hcase⟩
  · omega
  · exfalso
    apply hnt
    subst hD
    refine ⟨fun a _ => a, fun _ => false, ?_, fun _ _ => rfl⟩
    intro x
    rw [← hte]
    rfl
  · have hcomp : eval t' = restrictF f i b := by
      funext x
      rw [he, substVar_eval, show eval t = f from hte]
      rfl
    have hb : budget (restrictF f i b) ≤ volume t' :=
      Nat.sInf_le ⟨t', hcomp, rfl⟩
    rcases hcase with hA | ⟨hle, hPc | hPu⟩
    · omega
    · exfalso
      apply hnt
      obtain ⟨-, u, hu⟩ := hPc
      refine ⟨fun a _ => u a, fun _ => false, ?_, fun _ _ => rfl⟩
      intro x
      rw [← hte]
      exact hu x
    · exfalso
      apply hnt
      obtain ⟨-, op, s, hshape, hocc₀⟩ := hPu
      rcases hshape with rfl | rfl
      · refine ⟨op, eval s, ?_, ?_⟩
        · intro x
          rw [← hte]
          rfl
        · intro x bb
          exact eval_update_of_hasVar_false i s (occ_zero_hasVar_false i s hocc₀) x bb
      · refine ⟨fun a c => op c a, eval s, ?_, ?_⟩
        · intro x
          rw [← hte]
          rfl
        · intro x bb
          exact eval_update_of_hasVar_false i s (occ_zero_hasVar_false i s hocc₀) x bb

/-- **The conditional three-kill (proved)**: if every minimal tree reads `xᵢ` twice, restriction kills three
gates — for every value. -/
theorem budget_threekill {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n)
    (hdep : DependsOnF f i) (hnt : ¬TopDecomp f i)
    (hocc : ∀ t : Trans n, eval t = f → volume t = budget f → 2 ≤ occCount i t)
    (b : Bool) :
    budget (restrictF f i b) + 3 ≤ budget f := by
  have hne : {v | ∃ t : Trans n, eval t = f ∧ volume t = v}.Nonempty :=
    ⟨volume (dnfFor f), dnfFor f, eval_dnfFor f, rfl⟩
  obtain ⟨t, hte, htv⟩ := Nat.sInf_mem hne
  have h1 := budget_cascade f i hdep hnt b t hte htv
  have h2 := hocc t hte htv
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cascade_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.budget_cascade
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.budget_threekill
