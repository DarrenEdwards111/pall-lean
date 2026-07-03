import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameXorFreeOcc

/-!
# N-Frame: the xor-free three-kill schedule for SAT

The min-occurrence premise is a theorem in the xor-free basis (`sat3_xorfree_min_occ`), so the cascade can now be
cashed there.  Three steps, all proved:

1. **The cascade preserves xor-freeness** (`cascade_collapse_xf`): every fusion rewrite in the cascade produces a
   constant, a unary head (no gate constraint), or a binary gate of the form `op (u₁ ·) (u₂ ·)` — and composing a
   xor-free gate with unary functions can never manufacture a xor (`notOppPol_comp`: a xor-like composite forces
   both unaries bijective, and then the base gate was already xor-like).

2. **The xor-free budget and its unconditional three-kill** (`xbudget`, `xbudget_threekill_of_min_occ`): with the
   *all-trees* min-occurrence premise the escape branches of the cascade die without any `¬TopDecomp` hypothesis —
   the bare leaf and the top shapes each *are* a one-read xor-free tree, and the unarity case *builds* one
   (`un u (var i)`), so each contradicts the premise directly.  `dnfFor` is an OR-of-AND-of-literals caterpillar,
   hence xor-free (`xorFreeT_dnfFor`), so the xor-free budget is total and `budget ≤ xbudget`.

3. **The schedule on SAT** (`sat3_xf_threekill_chain`): freezing the slot-0 sign bits of clauses `1..m−2` to `true`
   one at a time, each step still shows both orientations — the orientation contexts pin *other* blocks with
   slot-0 signs `!bvec j`, which is `true` at every pin except the probe pin `j₀ = 0` (block `0`, never frozen),
   so both contexts live inside the frozen cube (`sat3_freeze_compliant`).  Hence:

  `sat3_xorfree_threekill_schedule` — **PROVED**: `3·(m−2) + 1 ≤ xbudget (sat3Family N)` — every restriction
        in the schedule kills **three** nodes: the first schedule where premise and cascade fire together.
  `sat3_xbudget_twokill_transfer` — **PROVED**: `2·m·v + 1 ≤ xbudget (sat3Family N)` for free via
        `budget ≤ xbudget` — the general-basis record transfers.

## Honest scope

The three-kill schedule runs over the `Θ(m) ≈ √N/3` sign bits, not the `Θ(m·v) ≈ N/3` selector bits: sat3 is
*monotone* in every selector coordinate (turning a selector on only adds a literal to a clause), so all selector
orientations agree and the polarity-clash refutation is structurally confined to sign bits — a `~3·m·v` three-kill
via this route is not just unproved but blocked (formalising that monotonicity no-go is a named next rung).
Numerically `2·m·v + 1` therefore remains the record even in the xor-free basis; the new content is the
*mechanism* — a per-step loss of three, premise discharged for **all** trees, no minimality or `¬TopDecomp` needed.
The interleaved schedule (`2·m·v` selector two-kills **plus** `3·(m−2)` sign-bit three-kills inside `xbudget`)
needs the xor-free replay of the `¬TopDecomp` two-kill and is the immediate next rung.  In the observer taxonomy
this is the restricted-basis tree observer; the DAG/`cbudget` observer (sharing-aware wire surgery) is untouched.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Unary composition cannot manufacture a xor -/

/-- **Composition no-go (proved)**: pre-composing a gate's arguments with unary functions preserves xor-freeness —
a xor-like composite forces both unaries bijective, and then the base gate was already xor-like. -/
theorem notOppPol_comp (op : Bool → Bool → Bool) (u₁ u₂ : Bool → Bool)
    (hnp : ¬OppPol op) : ¬OppPol (fun a c => op (u₁ a) (u₂ c)) := by
  intro hop
  apply hnp
  obtain ⟨h1, h2, h3⟩ := hop
  have h1' : op (u₁ true) (u₂ false) ≠ op (u₁ false) (u₂ false) := h1
  have h2' : op (u₁ true) (u₂ true) ≠ op (u₁ false) (u₂ true) := h2
  have h3' : op (u₁ false) (u₂ false) ≠ op (u₁ false) (u₂ true) := h3
  clear h1 h2 h3
  show (op true false ≠ op false false) ∧ (op true true ≠ op false true) ∧
    (op false false ≠ op false true)
  revert h1' h2' h3'
  cases hu₁t : u₁ true <;> cases hu₁f : u₁ false <;>
    cases hu₂t : u₂ true <;> cases hu₂f : u₂ false <;>
    cases hoff : op false false <;> cases hoft : op false true <;>
    cases hotf : op true false <;> cases hott : op true true <;>
    decide

/-- Binary gates built by pre-composing a xor-free gate stay xor-free in both argument positions. -/
theorem xorFreeBin_comp {n : ℕ} (op : Bool → Bool → Bool) (uu₁ uu₂ : Bool → Bool)
    (hnp1 : ¬OppPol op) (hnp2 : ¬OppPol (fun a c => op c a))
    (s₁ s₂ : Trans n) (hx1 : XorFreeT s₁) (hx2 : XorFreeT s₂) :
    XorFreeT (Trans.bin (fun a c => op (uu₁ a) (uu₂ c)) s₁ s₂) := by
  refine ⟨?_, ?_, hx1, hx2⟩
  · exact notOppPol_comp op uu₁ uu₂ hnp1
  · exact notOppPol_comp (fun p q => op q p) uu₂ uu₁ hnp2

/-- Substitution preserves xor-freeness. -/
theorem xorFreeT_substVar {n : ℕ} (i : Fin n) (b : Bool) :
    ∀ t : Trans n, XorFreeT t → XorFreeT (substVar i b t) := by
  intro t
  induction t with
  | var j =>
    intro _
    show XorFreeT (if j = i then Trans.cst b else Trans.var j)
    by_cases hj : j = i
    · rw [if_pos hj]
      trivial
    · rw [if_neg hj]
      trivial
  | cst c => intro h; exact h
  | un u s ih => intro h; exact ih h
  | bin op s₁ s₂ ih₁ ih₂ =>
    intro h
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h1, h2, ih₁ h3, ih₂ h4⟩

/-! ### The xor-free basis is complete: the DNF caterpillar is xor-free -/

theorem notOppPol_and : ¬OppPol (· && ·) := fun h => h.1 rfl

theorem notOppPol_and_flip : ¬OppPol (fun a c => c && a) := fun h => h.1 rfl

theorem notOppPol_or : ¬OppPol (· || ·) := fun h => h.2.1 rfl

theorem notOppPol_or_flip : ¬OppPol (fun a c => c || a) := fun h => h.2.1 rfl

theorem xorFreeT_literal {n : ℕ} (b : Bool) (i : Fin n) : XorFreeT (literal b i) := by
  show XorFreeT (if b then Trans.var i else Trans.un not (Trans.var i))
  cases b
  · trivial
  · trivial

theorem xorFreeT_mintermOn {n : ℕ} (a : Fin n → Bool) :
    ∀ l : List (Fin n), XorFreeT (mintermOn a l) := by
  intro l
  induction l with
  | nil => trivial
  | cons i is ih =>
    show XorFreeT (Trans.bin (· && ·) (literal (a i) i) (mintermOn a is))
    exact ⟨notOppPol_and, notOppPol_and_flip, xorFreeT_literal (a i) i, ih⟩

theorem xorFreeT_dnfOn {n : ℕ} :
    ∀ l : List (Fin n → Bool), XorFreeT (dnfOn l) := by
  intro l
  induction l with
  | nil => trivial
  | cons a l ih =>
    show XorFreeT (Trans.bin (· || ·) (mintermOn a (List.finRange n)) (dnfOn l))
    exact ⟨notOppPol_or, notOppPol_or_flip, xorFreeT_mintermOn a (List.finRange n), ih⟩

/-- **Completeness of the xor-free basis (proved)**: the DNF transducer is xor-free. -/
theorem xorFreeT_dnfFor {n : ℕ} (f : (Fin n → Bool) → Bool) : XorFreeT (dnfFor f) :=
  xorFreeT_dnfOn _

/-! ### The cascade preserves xor-freeness -/

/-- **The xor-free cascade (proved)**: the cascade collapse with the xor-free invariant threaded through every
fusion — beyond the occurrence-free, bare-leaf, and fusable-head cases, restriction of a xor-free tree loses
`occCount + 1` nodes *within the xor-free basis*. -/
theorem cascade_collapse_xf {n : ℕ} (i : Fin n) (b : Bool) :
    ∀ t : Trans n, XorFreeT t →
      occCount i t = 0 ∨ t = Trans.var i ∨
      ∃ t' : Trans n, eval t' = eval (substVar i b t) ∧ XorFreeT t' ∧
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
    intro _
    by_cases hj : j = i
    · right; left
      rw [hj]
    · left
      show (if j = i then 1 else 0) = 0
      rw [if_neg hj]
  | cst c => intro _; left; rfl
  | un u₁ s ih =>
    intro hxf
    rcases ih hxf with hE | hD | ⟨s', hse, hxfs', hcase⟩
    · left
      exact hE
    · -- unary over the bare leaf: constant head with unarity witness
      right; right
      subst hD
      refine ⟨Trans.cst (u₁ b), ?_, True.intro,
        Or.inr ⟨?_, Or.inl ⟨⟨u₁ b, rfl⟩, u₁, fun x => rfl⟩⟩⟩
      · funext x
        show u₁ b = u₁ (eval (if i = i then Trans.cst b else Trans.var i) x)
        rw [if_pos rfl]
        rfl
      · show 1 + (if i = i then 1 else 0) ≤ 1 + 1
        rw [if_pos rfl]
    · right; right
      rcases hcase with hA | ⟨hle, hPc | hPu⟩
      · -- child cascade: wrap
        refine ⟨Trans.un u₁ s', ?_, hxfs', Or.inl ?_⟩
        · funext x
          show u₁ (eval s' x) = u₁ (eval (substVar i b s) x)
          rw [hse]
        · show volume s' + 1 + occCount i s + 1 ≤ volume s + 1
          omega
      · -- constant head folds: one more kill
        obtain ⟨⟨cc, rfl⟩, u, hu⟩ := hPc
        refine ⟨Trans.cst (u₁ cc), ?_, True.intro, Or.inl ?_⟩
        · funext x
          show u₁ cc = u₁ (eval (substVar i b s) x)
          rw [← hse]
          rfl
        · show 1 + occCount i s + 1 ≤ volume s + 1
          have h1 : volume (Trans.cst cc : Trans n) = 1 := rfl
          omega
      · -- unary head fuses: one more kill
        obtain ⟨⟨u₀, s₀, rfl⟩, -⟩ := hPu
        refine ⟨Trans.un (fun a => u₁ (u₀ a)) s₀, ?_, hxfs', Or.inl ?_⟩
        · funext x
          show u₁ (u₀ (eval s₀ x)) = u₁ (eval (substVar i b s) x)
          rw [← hse]
          rfl
        · show volume s₀ + 1 + occCount i s + 1 ≤ volume s + 1
          have h1 : volume (Trans.un u₀ s₀) = volume s₀ + 1 := rfl
          omega
  | bin op s₁ s₂ ih₁ ih₂ =>
    intro hxf
    obtain ⟨hnp1, hnp2, hxf1, hxf2⟩ := hxf
    have hocc : occCount i (Trans.bin op s₁ s₂) = occCount i s₁ + occCount i s₂ := rfl
    rcases ih₁ hxf1 with hE₁ | hD₁ | ⟨t₁', he₁, hxf₁', hc₁⟩
    · -- left side occurrence-free: use its plain substitution
      rcases ih₂ hxf2 with hE₂ | hD₂ | ⟨t₂', he₂, hxf₂', hc₂⟩
      · left
        show occCount i s₁ + occCount i s₂ = 0
        omega
      · -- E/D: absorb the right leaf, unary head with shape
        right; right
        subst hD₂
        refine ⟨Trans.un (fun a => op a b) (substVar i b s₁), ?_,
          xorFreeT_substVar i b s₁ hxf1,
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
          refine ⟨Trans.bin op (substVar i b s₁) t₂', ?_,
            ⟨hnp1, hnp2, xorFreeT_substVar i b s₁ hxf1, hxf₂'⟩, Or.inl ?_⟩
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
          refine ⟨Trans.un (fun a => op a cc) (substVar i b s₁), ?_,
            xorFreeT_substVar i b s₁ hxf1, Or.inl ?_⟩
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
          refine ⟨Trans.bin (fun a c => op a (u₀ c)) (substVar i b s₁) s₀, ?_,
            xorFreeBin_comp op (fun a => a) u₀ hnp1 hnp2 _ _
              (xorFreeT_substVar i b s₁ hxf1) hxf₂', Or.inl ?_⟩
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
      rcases ih₂ hxf2 with hE₂ | hD₂ | ⟨t₂', he₂, hxf₂', hc₂⟩
      · -- D/E: absorb the left leaf, unary head with shape
        right; right
        refine ⟨Trans.un (fun c => op b c) (substVar i b s₂), ?_,
          xorFreeT_substVar i b s₂ hxf2,
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
        refine ⟨Trans.cst (op b b), ?_, True.intro, Or.inr ⟨?_,
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
          refine ⟨Trans.un (fun c => op b c) t₂', ?_, hxf₂', Or.inl ?_⟩
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
          refine ⟨Trans.cst (op b cc), ?_, True.intro, Or.inl ?_⟩
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
          refine ⟨Trans.un (fun c => op b (u₀ c)) s₀, ?_, hxf₂', Or.inl ?_⟩
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
      rcases ih₂ hxf2 with hE₂ | hD₂ | ⟨t₂', he₂, hxf₂', hc₂⟩
      · rcases hc₁ with hA₁ | ⟨hle₁, hPc₁ | hPu₁⟩
        · -- A/E
          right; right
          refine ⟨Trans.bin op t₁' (substVar i b s₂), ?_,
            ⟨hnp1, hnp2, hxf₁', xorFreeT_substVar i b s₂ hxf2⟩, Or.inl ?_⟩
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
          refine ⟨Trans.un (fun c => op cc c) (substVar i b s₂), ?_,
            xorFreeT_substVar i b s₂ hxf2, Or.inl ?_⟩
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
          refine ⟨Trans.bin (fun a c => op (u₀ a) c) s₀ (substVar i b s₂), ?_,
            xorFreeBin_comp op u₀ (fun c => c) hnp1 hnp2 _ _
              hxf₁' (xorFreeT_substVar i b s₂ hxf2), Or.inl ?_⟩
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
          refine ⟨Trans.un (fun a => op a b) t₁', ?_, hxf₁', Or.inl ?_⟩
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
          refine ⟨Trans.cst (op cc b), ?_, True.intro, Or.inl ?_⟩
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
          refine ⟨Trans.un (fun a => op (u₀ a) b) s₀, ?_, hxf₁', Or.inl ?_⟩
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
          refine ⟨Trans.bin op t₁' t₂', ?_, ⟨hnp1, hnp2, hxf₁', hxf₂'⟩, Or.inl ?_⟩
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
          refine ⟨Trans.un (fun a => op a cc) t₁', ?_, hxf₁', Or.inl ?_⟩
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
          refine ⟨Trans.bin (fun a c => op a (u₀ c)) t₁' s₀, ?_,
            xorFreeBin_comp op (fun a => a) u₀ hnp1 hnp2 _ _ hxf₁' hxf₂', Or.inl ?_⟩
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
          refine ⟨Trans.un (fun c => op cc c) t₂', ?_, hxf₂', Or.inl ?_⟩
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
          refine ⟨Trans.cst (op c₁ c₂), ?_, True.intro, Or.inl ?_⟩
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
          refine ⟨Trans.un (fun c => op c₁ (u₀ c)) s₀, ?_, hxf₂', Or.inl ?_⟩
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
          refine ⟨Trans.bin (fun a c => op (u₀ a) c) s₀ t₂', ?_,
            xorFreeBin_comp op u₀ (fun c => c) hnp1 hnp2 _ _ hxf₁' hxf₂', Or.inl ?_⟩
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
          refine ⟨Trans.un (fun a => op (u₀ a) c₂) s₀, ?_, hxf₁', Or.inl ?_⟩
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
          obtain ⟨⟨uu₁, s₀₁, rfl⟩, -⟩ := hPu₁
          obtain ⟨⟨uu₂, s₀₂, rfl⟩, -⟩ := hPu₂
          right; right
          refine ⟨Trans.bin (fun a c => op (uu₁ a) (uu₂ c)) s₀₁ s₀₂, ?_,
            xorFreeBin_comp op uu₁ uu₂ hnp1 hnp2 _ _ hxf₁' hxf₂', Or.inl ?_⟩
          · funext x
            show op (uu₁ (eval s₀₁ x)) (uu₂ (eval s₀₂ x))
                = op (eval (substVar i b s₁) x) (eval (substVar i b s₂) x)
            rw [← he₁, ← he₂]
            rfl
          · show volume s₀₁ + volume s₀₂ + 1 + (occCount i s₁ + occCount i s₂) + 1
                ≤ volume s₁ + volume s₂ + 1
            have h1 : volume (Trans.un uu₁ s₀₁) = volume s₀₁ + 1 := rfl
            have h2 : volume (Trans.un uu₂ s₀₂) = volume s₀₂ + 1 := rfl
            omega

/-! ### The xor-free budget -/

/-- The xor-free budget: minimal volume over xor-free trees computing `f`. -/
noncomputable def xbudget {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {v | ∃ t : Trans n, eval t = f ∧ XorFreeT t ∧ volume t = v}

theorem xbudget_set_nonempty {n : ℕ} (f : (Fin n → Bool) → Bool) :
    {v | ∃ t : Trans n, eval t = f ∧ XorFreeT t ∧ volume t = v}.Nonempty :=
  ⟨volume (dnfFor f), dnfFor f, eval_dnfFor f, xorFreeT_dnfFor f, rfl⟩

theorem xbudget_pos {n : ℕ} (f : (Fin n → Bool) → Bool) : 1 ≤ xbudget f := by
  obtain ⟨t, -, -, hvt⟩ := Nat.sInf_mem (xbudget_set_nonempty f)
  have hvt' : volume t = xbudget f := hvt
  have h1 := volume_pos t
  omega

/-- The general-basis budget never exceeds the xor-free budget: every restricted lower bound must beat the
unrestricted record before it means anything new — and every unrestricted record transfers for free. -/
theorem budget_le_xbudget {n : ℕ} (f : (Fin n → Bool) → Bool) : budget f ≤ xbudget f := by
  obtain ⟨t, hte, -, hvt⟩ := Nat.sInf_mem (xbudget_set_nonempty f)
  have hvt' : volume t = xbudget f := hvt
  have hb : budget f ≤ volume t := Nat.sInf_le ⟨t, hte, rfl⟩
  omega

/-! ### The unconditional xor-free three-kill -/

/-- The polarity clash packaged: two sensitive points with opposite orientations force every xor-free tree to read
the variable twice. -/
theorem xorfree_min_occ_of_orientations {n : ℕ} (g : (Fin n → Bool) → Bool) (i : Fin n)
    (x y : Fin n → Bool)
    (hsx : g (Function.update x i true) ≠ g (Function.update x i false))
    (hsy : g (Function.update y i true) ≠ g (Function.update y i false))
    (hxy : g (Function.update x i true) ≠ g (Function.update y i true)) :
    ∀ t : Trans n, XorFreeT t → eval t = g → 2 ≤ occCount i t := by
  intro t hxf hte
  by_contra hcon
  push_neg at hcon
  have hocc : occCount i t ≤ 1 := by omega
  have horient := xorfree_orientation i t hxf hocc x y
    (by rw [hte]; exact hsx) (by rw [hte]; exact hsy)
  rw [hte] at horient
  exact hxy horient

/-- **The xor-free three-kill (proved), no `¬TopDecomp` needed**: with the all-trees min-occurrence premise the
cascade's escape hatches each exhibit a one-read xor-free tree — the bare leaf and the top shapes *are* one, the
unarity witness *builds* one — so every one contradicts the premise, and restriction kills three nodes of the
xor-free budget for every value. -/
theorem xbudget_threekill_of_min_occ {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n)
    (hocc2 : ∀ t : Trans n, XorFreeT t → eval t = f → 2 ≤ occCount i t) (b : Bool) :
    xbudget (restrictF f i b) + 3 ≤ xbudget f := by
  obtain ⟨t, hte, hxf, htv⟩ := Nat.sInf_mem (xbudget_set_nonempty f)
  have htv' : volume t = xbudget f := htv
  have h2 := hocc2 t hxf hte
  rcases cascade_collapse_xf i b t hxf with hE | hD | ⟨t', he, hxf', hcase⟩
  · omega
  · exfalso
    subst hD
    have h1 : occCount i (Trans.var i) = 1 := by
      show (if i = i then 1 else 0) = 1
      rw [if_pos rfl]
    omega
  · have hcomp : eval t' = restrictF f i b := by
      funext x
      rw [he, substVar_eval, show eval t = f from hte]
      rfl
    have hb : xbudget (restrictF f i b) ≤ volume t' :=
      Nat.sInf_le ⟨t', hcomp, hxf', rfl⟩
    rcases hcase with hA | ⟨hle, hPc | hPu⟩
    · omega
    · -- unarity: the one-read xor-free tree `un u (var i)` computes `f`
      exfalso
      obtain ⟨-, u, hu⟩ := hPc
      have hteq : eval (Trans.un u (Trans.var i)) = f := by
        funext x
        show u (x i) = f x
        rw [← hu x]
        exact congrFun hte x
      have hocc1 := hocc2 (Trans.un u (Trans.var i)) True.intro hteq
      have h1 : occCount i (Trans.un u (Trans.var i)) = (if i = i then 1 else 0) := rfl
      rw [if_pos rfl] at h1
      omega
    · -- top shape: `t` itself reads once
      exfalso
      obtain ⟨-, op, s, hshape, hocc₀⟩ := hPu
      rcases hshape with rfl | rfl
      · have h1 : occCount i (Trans.bin op (Trans.var i) s)
            = (if i = i then 1 else 0) + occCount i s := rfl
        rw [if_pos rfl] at h1
        omega
      · have h1 : occCount i (Trans.bin op s (Trans.var i))
            = occCount i s + (if i = i then 1 else 0) := rfl
        rw [if_pos rfl] at h1
        omega

/-! ### Schedule calculus for the frozen cube -/

theorem restrictAll_append {n : ℕ} :
    ∀ (L₁ L₂ : List (Fin n × Bool)) (f : (Fin n → Bool) → Bool),
      restrictAll f (L₁ ++ L₂) = restrictAll (restrictAll f L₁) L₂ := by
  intro L₁
  induction L₁ with
  | nil => intro L₂ f; rfl
  | cons s rest ih =>
    intro L₂ f
    show restrictAll (restrictF f s.1 s.2) (rest ++ L₂) = _
    exact ih L₂ (restrictF f s.1 s.2)

/-- A schedule is invisible at points already carrying the scheduled values. -/
theorem restrictAll_agree {n : ℕ} :
    ∀ (L : List (Fin n × Bool)) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool),
      (∀ p ∈ L, x p.1 = p.2) → restrictAll f L x = f x := by
  intro L
  induction L with
  | nil => intro f x _; rfl
  | cons s rest ih =>
    intro f x hx
    show restrictAll (restrictF f s.1 s.2) rest x = f x
    rw [ih (restrictF f s.1 s.2) x (fun p hp => hx p (List.mem_cons_of_mem s hp))]
    have h2 : Function.update x s.1 s.2 = x := by
      rw [← hx s List.mem_cons_self]
      exact Function.update_eq_self s.1 x
    show f (Function.update x s.1 s.2) = f x
    rw [h2]

/-! ### The SAT sign-bit freeze -/

/-- Freeze the slot-0 sign bits of the listed clauses to `true`. -/
def sat3SignFreeze (N : ℕ) (S : List (Fin (sat3M N))) : List (Fin N × Bool) :=
  S.map fun c => (sat3SignBit N c, true)

theorem sat3SignFreeze_append (N : ℕ) (S₁ S₂ : List (Fin (sat3M N))) :
    sat3SignFreeze N (S₁ ++ S₂) = sat3SignFreeze N S₁ ++ sat3SignFreeze N S₂ := by
  simp [sat3SignFreeze]

theorem sat3SignBit_ne (N : ℕ) {c c' : Fin (sat3M N)} (h : c' ≠ c) :
    sat3SignBit N c' ≠ sat3SignBit N c := by
  intro he
  apply h
  apply Fin.ext
  have h1 : (sat3SignBit N c').val / sat3D N = c'.val :=
    sat3Bit_clause N c' ⟨0, by omega⟩ (sat3V N) (by omega)
  have h2 : (sat3SignBit N c).val / sat3D N = c.val :=
    sat3Bit_clause N c ⟨0, by omega⟩ (sat3V N) (by omega)
  rw [← h1, ← h2, he]

/-- **Frozen-cube compliance (proved)**: the orientation contexts for block `c` read `true` at the slot-0 sign bit
of every other interior block — those blocks are pin clauses with sign `!bvec j`, and the schedule only ever needs
pins `j ≥ 1`, where both context vectors are `false`. -/
theorem sat3_freeze_compliant (N : ℕ)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (c c' : Fin (sat3M N)) (hne : c' ≠ c)
    (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ sat3M N - 2)
    (hc'1 : 1 ≤ c'.val) (hc'2 : c'.val ≤ sat3M N - 2)
    (bvec : Fin (sat3M N - 2) → Bool)
    (hbv : ∀ j : Fin (sat3M N - 2), 1 ≤ j.val → bvec j = false)
    (u : Fin N → Bool) :
    sat3Patch N c (sat3Context N c hk bvec) u (sat3SignBit N c') = true := by
  have hnv : c'.val ≠ c.val := fun h => hne (Fin.ext h)
  by_cases hlt : c'.val < c.val
  · obtain ⟨j', hj'⟩ : ∃ j' : Fin (sat3M N - 2), j'.val = c'.val :=
      ⟨⟨c'.val, by omega⟩, rfl⟩
    have hpc : sat3PinClause N c hk j' = c' := by
      apply Fin.ext
      rw [sat3PinClause_val, hj']
      rw [if_pos hlt]
    have h := pin_read_sign N c hk hkv bvec u j'
    rw [hpc, hbv j' (by omega)] at h
    exact h
  · obtain ⟨j', hj'⟩ : ∃ j' : Fin (sat3M N - 2), j'.val = c'.val - 1 :=
      ⟨⟨c'.val - 1, by omega⟩, rfl⟩
    have hpc : sat3PinClause N c hk j' = c' := by
      apply Fin.ext
      rw [sat3PinClause_val, hj']
      rw [if_neg (by omega)]
      omega
    have h := pin_read_sign N c hk hkv bvec u j'
    rw [hpc, hbv j' (by omega)] at h
    exact h

/-- **The premise survives the freeze (proved)**: after freezing any set of interior slot-0 sign bits to `true`,
every remaining interior sign bit still shows both orientations inside the frozen cube, so every xor-free tree for
the frozen function reads it at least twice. -/
theorem sat3_frozen_min_occ (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (S : List (Fin (sat3M N))) (hS : ∀ c' ∈ S, 1 ≤ c'.val ∧ c'.val ≤ sat3M N - 2)
    (c : Fin (sat3M N)) (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ sat3M N - 2) (hcS : c ∉ S) :
    ∀ t : Trans N, XorFreeT t →
      eval t = restrictAll (sat3Family N) (sat3SignFreeze N S) →
      2 ≤ occCount (sat3SignBit N c) t := by
  have hk : (sat3M N - 2) + 1 ≤ sat3M N := by omega
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set j₀ : Fin (sat3M N - 2) := ⟨0, by omega⟩ with hj₀
  set vj : Fin (sat3V N) := ⟨0, hv⟩ with hvj
  set bvec₂ : Fin (sat3M N - 2) → Bool :=
    Function.update (fun _ => false) j₀ true with hbvec₂
  -- the frozen cube is respected by both contexts
  have hcomp : ∀ (bvec : Fin (sat3M N - 2) → Bool),
      (∀ j : Fin (sat3M N - 2), 1 ≤ j.val → bvec j = false) → ∀ a : Bool,
      ∀ p ∈ sat3SignFreeze N S,
        Function.update (sat3Patch N c (sat3Context N c hk bvec) (sat3Probe N vj false))
          (sat3SignBit N c) a p.1 = p.2 := by
    intro bvec hbv a p hp
    obtain ⟨c', hc'S, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hc'1, hc'2⟩ := hS c' hc'S
    have hnec : c' ≠ c := fun h => hcS (h ▸ hc'S)
    show Function.update (sat3Patch N c (sat3Context N c hk bvec) (sat3Probe N vj false))
      (sat3SignBit N c) a (sat3SignBit N c') = true
    rw [Function.update_of_ne (sat3SignBit_ne N hnec)]
    exact sat3_freeze_compliant N hk hkv c c' hnec hc1 hc2 hc'1 hc'2 bvec hbv _
  have hbvA : ∀ j : Fin (sat3M N - 2), 1 ≤ j.val →
      (fun _ : Fin (sat3M N - 2) => false) j = false := fun j _ => rfl
  have hbvB : ∀ j : Fin (sat3M N - 2), 1 ≤ j.val → bvec₂ j = false := by
    intro j hj
    have hne : j ≠ j₀ := by
      rw [hj₀]
      intro he
      have hval : j.val = 0 := congrArg Fin.val he
      omega
    rw [hbvec₂]
    rw [Function.update_of_ne hne]
  -- the two behaviors inside the frozen cube
  have hbeh₁ : ∀ a : Bool,
      restrictAll (sat3Family N) (sat3SignFreeze N S)
        (Function.update (sat3Patch N c (sat3Context N c hk (fun _ => false))
          (sat3Probe N vj false)) (sat3SignBit N c) a) = a := by
    intro a
    rw [restrictAll_agree _ _ _ (hcomp (fun _ => false) hbvA a), patch_probe_update]
    have hval := sat3Context_probe_eval N hv hk hkv c (fun _ => false) j₀ vj rfl a
    rw [hval]
    cases a <;> rfl
  have hbeh₂ : ∀ a : Bool,
      restrictAll (sat3Family N) (sat3SignFreeze N S)
        (Function.update (sat3Patch N c (sat3Context N c hk bvec₂)
          (sat3Probe N vj false)) (sat3SignBit N c) a) = !a := by
    intro a
    rw [restrictAll_agree _ _ _ (hcomp bvec₂ hbvB a), patch_probe_update]
    have hval := sat3Context_probe_eval N hv hk hkv c bvec₂ j₀ vj rfl a
    rw [hval]
    have hb : bvec₂ j₀ = true := by
      rw [hbvec₂, Function.update_self]
    rw [hb]
    cases a <;> rfl
  intro t hxf hte
  refine xorfree_min_occ_of_orientations
    (restrictAll (sat3Family N) (sat3SignFreeze N S)) (sat3SignBit N c)
    (sat3Patch N c (sat3Context N c hk (fun _ => false)) (sat3Probe N vj false))
    (sat3Patch N c (sat3Context N c hk bvec₂) (sat3Probe N vj false))
    ?_ ?_ ?_ t hxf hte
  · rw [hbeh₁ true, hbeh₁ false]
    decide
  · rw [hbeh₂ true, hbeh₂ false]
    decide
  · rw [hbeh₁ true, hbeh₂ true]
    decide

/-! ### The chain and the schedule -/

/-- **The xor-free three-kill chain (proved)**: every interior clause scheduled once loses three nodes of the
xor-free budget. -/
theorem sat3_xf_threekill_chain (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N) :
    ∀ (L S : List (Fin (sat3M N))),
      (∀ c ∈ S, 1 ≤ c.val ∧ c.val ≤ sat3M N - 2) →
      (∀ c ∈ L, 1 ≤ c.val ∧ c.val ≤ sat3M N - 2) →
      (∀ c ∈ L, c ∉ S) → L.Nodup →
      3 * L.length + 1 ≤ xbudget (restrictAll (sat3Family N) (sat3SignFreeze N S)) := by
  intro L
  induction L with
  | nil =>
    intro S hS hL hLS hnd
    have h := xbudget_pos (restrictAll (sat3Family N) (sat3SignFreeze N S))
    have hlen : ([] : List (Fin (sat3M N))).length = 0 := rfl
    rw [hlen]
    omega
  | cons c L' ih =>
    intro S hS hL hLS hnd
    have hc := hL c List.mem_cons_self
    have hcS : c ∉ S := hLS c List.mem_cons_self
    have hstep := xbudget_threekill_of_min_occ
      (restrictAll (sat3Family N) (sat3SignFreeze N S)) (sat3SignBit N c)
      (sat3_frozen_min_occ N hv hm3 S hS c hc.1 hc.2 hcS) true
    have hres : restrictF (restrictAll (sat3Family N) (sat3SignFreeze N S))
        (sat3SignBit N c) true
        = restrictAll (sat3Family N) (sat3SignFreeze N (S ++ [c])) := by
      rw [sat3SignFreeze_append, restrictAll_append]
      rfl
    rw [hres] at hstep
    have hS' : ∀ c' ∈ S ++ [c], 1 ≤ c'.val ∧ c'.val ≤ sat3M N - 2 := by
      intro c' hc'
      rcases List.mem_append.mp hc' with h | h
      · exact hS c' h
      · rw [List.mem_singleton] at h
        exact h ▸ hc
    have hL' : ∀ c' ∈ L', 1 ≤ c'.val ∧ c'.val ≤ sat3M N - 2 :=
      fun c' hc' => hL c' (List.mem_cons_of_mem c hc')
    have hLS' : ∀ c' ∈ L', c' ∉ S ++ [c] := by
      intro c' hc' hmem
      rcases List.mem_append.mp hmem with h | h
      · exact hLS c' (List.mem_cons_of_mem c hc') h
      · rw [List.mem_singleton] at h
        subst h
        exact (List.nodup_cons.mp hnd).1 hc'
    have hnd' : L'.Nodup := (List.nodup_cons.mp hnd).2
    have hih := ih (S ++ [c]) hS' hL' hLS' hnd'
    show 3 * (L'.length + 1) + 1 ≤ _
    omega

/-- **THE XOR-FREE THREE-KILL SCHEDULE (proved)**: `3·(m−2) + 1 ≤ xbudget (sat3Family)` — the first schedule in
the arc where every restriction provably kills **three** nodes: the min-occurrence premise (for all trees) and the
cascade fire together, inside the xor-free basis. -/
theorem sat3_xorfree_threekill_schedule (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N) :
    3 * (sat3M N - 2) + 1 ≤ xbudget (sat3Family N) := by
  have hinj : Function.Injective
      (fun j : Fin (sat3M N - 2) =>
        (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin (sat3M N))) := by
    intro j j' h
    have hval : j.val + 1 = j'.val + 1 := congrArg Fin.val h
    exact Fin.ext (by omega)
  have h := sat3_xf_threekill_chain N hv hm3
    ((List.finRange (sat3M N - 2)).map
      (fun j : Fin (sat3M N - 2) =>
        (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin (sat3M N))))
    []
    (fun c hc => absurd hc List.not_mem_nil)
    (by
      intro c hc
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hc
      have := j.isLt
      constructor
      · show 1 ≤ j.val + 1
        omega
      · show j.val + 1 ≤ sat3M N - 2
        omega)
    (fun c _ hc => absurd hc List.not_mem_nil)
    ((List.nodup_finRange _).map hinj)
  rw [List.length_map, List.length_finRange] at h
  exact h

/-- **The record transfers (proved)**: the general-basis two-kill schedule bound holds a fortiori for the xor-free
budget — `2·m·v + 1 ≤ xbudget (sat3Family)`, which remains the numerically dominant record. -/
theorem sat3_xbudget_twokill_transfer (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N) :
    2 * (sat3M N * sat3V N) + 1 ≤ xbudget (sat3Family N) :=
  le_trans (sat3_twokill_schedule N hv hm2) (budget_le_xbudget _)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.notOppPol_comp
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cascade_collapse_xf
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.xorFreeT_dnfFor
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.budget_le_xbudget
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.xbudget_threekill_of_min_occ
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_frozen_min_occ
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_xf_threekill_chain
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_xorfree_threekill_schedule
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_xbudget_twokill_transfer
