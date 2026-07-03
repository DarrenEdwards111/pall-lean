import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMultiKill

/-!
# N-Frame: the minimality-exploiting two-kill — the dichotomy, and it fires on SAT

The multi-kill premise demanded a minimality-exploiting occurrence bound.  Working the single-read case analysis
to the end yields something stronger: an **unconditional dichotomy**.

**The collapse analysis (proved).**  In a single-read tree, restricting the variable turns its leaf into a
constant; the constant absorbs into its parent gate, leaving a *unary head* — which then **fuses into the next
gate up**, killing a second node.  The A/B/C induction (`single_read_collapse`) tracks this: the collapse yields
loss `≥ 2` (A) unless the fusion never happens — which occurs only when the variable's gate *is the root* (B: `t =
bin op (var i) s`, so `f = op(xᵢ, h)`), or the whole tree is a unary chain over the leaf (C: `f` unary in `xᵢ`).

  `budget_twokill` — **PROVED, the dichotomy**: if `f` depends on `i` and is not *top-decomposable* at `i`
        (`¬∃ op h, f = op(xᵢ, h)` with `h` free of `i`), then some restriction kills **two** gates:
        `∃ b, budget (f|ᵢ₌b) + 2 ≤ budget f`.  With `occCount ≥ 2` the mechanism kills two anyway; with a single
        read the collapse does; top-decomposition is the exact residue.
  `sat3_not_topDecomp` — **PROVED**: the SAT family is not top-decomposable at any sign bit — it shows **three**
        distinct behaviors there (identity, negation, and constant, via two pin contexts and an empty-clause
        context), while `op(·, h y)` admits at most two.
  `sat3_twokill` — **PROVED, the two-kill fires on the target**:
        `∃ b, budget (sat3Family|sign₌b) + 2 ≤ budget (sat3Family N)`.

## Honest scope

This is the Schnorr-style case analysis, tree-model clean, with its exact boundary (`TopDecomp`) carried as a
theorem instead of a wlog.  Iterating two-kills along a schedule is how classical `2n − O(1)` bounds arise; the
schedule form needs dependence *and* non-top-decomposability preserved along restrictions — the next delicate
rung.  Superlinear still further requires the DAG analogue.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Occurrence and variable-presence links -/

theorem hasVar_occ_pos {n : ℕ} (i : Fin n) (t : Trans n) (h : hasVar i t = true) :
    1 ≤ occCount i t := by
  induction t with
  | var j =>
    have hj : j = i := of_decide_eq_true (show decide (j = i) = true from h)
    show 1 ≤ (if j = i then 1 else 0)
    rw [if_pos hj]
  | cst c => exact absurd h (by simp [hasVar])
  | un op s ih => exact ih h
  | bin op s t ihs iht =>
    have hor : (hasVar i s || hasVar i t) = true := h
    rw [Bool.or_eq_true] at hor
    show 1 ≤ occCount i s + occCount i t
    rcases hor with h1 | h1
    · have := ihs h1
      omega
    · have := iht h1
      omega

theorem occ_zero_hasVar_false {n : ℕ} (i : Fin n) (t : Trans n)
    (h : occCount i t = 0) : hasVar i t = false := by
  induction t with
  | var j =>
    have hj : ¬(j = i) := by
      intro hji
      have h' : (if j = i then 1 else 0) = 0 := h
      rw [if_pos hji] at h'
      omega
    show decide (j = i) = false
    rw [decide_eq_false_iff_not]
    exact hj
  | cst c => rfl
  | un op s ih => exact ih h
  | bin op s t ihs iht =>
    have h' : occCount i s + occCount i t = 0 := h
    show (hasVar i s || hasVar i t) = false
    rw [ihs (by omega), iht (by omega)]
    rfl

/-! ### The single-read collapse -/

/-- **The single-read collapse (proved)**: restricting the unique occurrence loses two nodes (A) unless the
variable's gate is the root (B, exposing the top decomposition) or the tree is a unary chain over the leaf (C). -/
theorem single_read_collapse {n : ℕ} (i : Fin n) (b : Bool) :
    ∀ t : Trans n, occCount i t = 1 →
      ∃ t' : Trans n, eval t' = eval (substVar i b t) ∧
        (volume t' + 2 ≤ volume t ∨
          (volume t' + 1 ≤ volume t ∧
            ∃ (op₂ : Bool → Bool → Bool) (s₂ : Trans n),
              t = Trans.bin op₂ (Trans.var i) s₂ ∨ t = Trans.bin op₂ s₂ (Trans.var i)) ∨
          (∃ u : Bool → Bool, ∀ x, eval t x = u (x i))) := by
  intro t
  induction t with
  | var j =>
    intro hocc
    have hj : j = i := by
      by_contra hji
      have h' : (if j = i then 1 else 0) = 1 := hocc
      rw [if_neg hji] at h'
      omega
    subst hj
    refine ⟨Trans.cst b, ?_, Or.inr (Or.inr ⟨id, fun x => rfl⟩)⟩
    funext x
    show b = eval (if j = j then Trans.cst b else Trans.var j) x
    rw [if_pos rfl]
    rfl
  | cst c =>
    intro hocc
    exact absurd hocc (by simp [occCount])
  | un u₁ s ih =>
    intro hocc
    have hs : occCount i s = 1 := hocc
    obtain ⟨s', hse, hcase⟩ := ih hs
    rcases hcase with hA | ⟨hB, op₂, s₂, hshape⟩ | ⟨u, hu⟩
    · refine ⟨Trans.un u₁ s', ?_, Or.inl ?_⟩
      · funext x
        show u₁ (eval s' x) = u₁ (eval (substVar i b s) x)
        rw [hse]
      · show volume s' + 1 + 2 ≤ volume s + 1
        omega
    · -- the child was a root-shaped bin: its collapse is un-headed; here we can refuse precision and
      -- simply reuse the child's tree with the outer unary — still a 2-loss via re-absorption is not
      -- available generically, but the child's B-bound plus this unary node gives a 2-loss directly:
      -- volume s' + 1 ≤ volume s, so (un u₁ s') has volume s' + 1 + 1 ≤ volume s + 1 = volume t: 1-loss;
      -- instead, fuse: the child collapse for shape bin op₂ (var i) s₂ is un-headed by construction, but
      -- the clause does not expose it.  Re-derive the collapsed child concretely from the shape.
      rcases hshape with rfl | rfl
      · -- s = bin op₂ (var i) s₂ : substituted child evaluates to op₂ b ∘ (substVar s₂)
        refine ⟨Trans.un (fun a => u₁ (op₂ b a)) (substVar i b s₂), ?_, Or.inl ?_⟩
        · funext x
          show u₁ (op₂ b (eval (substVar i b s₂) x))
              = u₁ (eval (substVar i b (Trans.bin op₂ (Trans.var i) s₂)) x)
          show u₁ (op₂ b (eval (substVar i b s₂) x))
              = u₁ (op₂ (eval (if i = i then Trans.cst b else Trans.var i) x)
                (eval (substVar i b s₂) x))
          rw [if_pos rfl]
          rfl
        · show volume (substVar i b s₂) + 1 + 2 ≤ 1 + volume s₂ + 1 + 1
          rw [substVar_volume]
          omega
      · refine ⟨Trans.un (fun a => u₁ (op₂ a b)) (substVar i b s₂), ?_, Or.inl ?_⟩
        · funext x
          show u₁ (op₂ (eval (substVar i b s₂) x) b)
              = u₁ (eval (substVar i b (Trans.bin op₂ s₂ (Trans.var i))) x)
          show u₁ (op₂ (eval (substVar i b s₂) x) b)
              = u₁ (op₂ (eval (substVar i b s₂) x)
                (eval (if i = i then Trans.cst b else Trans.var i) x))
          rw [if_pos rfl]
          rfl
        · show volume (substVar i b s₂) + 1 + 2 ≤ volume s₂ + 1 + 1 + 1
          rw [substVar_volume]
    · -- unary chain: stays a unary chain
      refine ⟨Trans.un u₁ s', ?_, Or.inr (Or.inr ⟨u₁ ∘ u, ?_⟩)⟩
      · funext x
        show u₁ (eval s' x) = u₁ (eval (substVar i b s) x)
        rw [hse]
      · intro x
        show u₁ (eval s x) = u₁ (u (x i))
        rw [hu x]
  | bin op₂ s₁ s₂ ih₁ ih₂ =>
    intro hocc
    have hsum : occCount i s₁ + occCount i s₂ = 1 := hocc
    have hsplit : (occCount i s₁ = 1 ∧ occCount i s₂ = 0) ∨
        (occCount i s₁ = 0 ∧ occCount i s₂ = 1) := by omega
    rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨s₁', hse, hcase⟩ := ih₁ h1
      rcases hcase with hA | ⟨hB, op₃, s₃, hshape⟩ | ⟨u, hu⟩
      · refine ⟨Trans.bin op₂ s₁' (substVar i b s₂), ?_, Or.inl ?_⟩
        · funext x
          show op₂ (eval s₁' x) (eval (substVar i b s₂) x)
              = op₂ (eval (substVar i b s₁) x) (eval (substVar i b s₂) x)
          rw [hse]
        · show volume s₁' + volume (substVar i b s₂) + 1 + 2
              ≤ volume s₁ + volume s₂ + 1
          rw [substVar_volume]
          omega
      · -- the left child is itself a root-shaped bin: collapse it concretely and fuse here
        rcases hshape with rfl | rfl
        · refine ⟨Trans.bin (fun a c => op₂ (op₃ b a) c) (substVar i b s₃)
            (substVar i b s₂), ?_, Or.inl ?_⟩
          · funext x
            show op₂ (op₃ b (eval (substVar i b s₃) x)) (eval (substVar i b s₂) x)
                = op₂ (eval (substVar i b (Trans.bin op₃ (Trans.var i) s₃)) x)
                  (eval (substVar i b s₂) x)
            show op₂ (op₃ b (eval (substVar i b s₃) x)) (eval (substVar i b s₂) x)
                = op₂ (op₃ (eval (if i = i then Trans.cst b else Trans.var i) x)
                    (eval (substVar i b s₃) x)) (eval (substVar i b s₂) x)
            rw [if_pos rfl]
            rfl
          · show volume (substVar i b s₃) + volume (substVar i b s₂) + 1 + 2
                ≤ (1 + volume s₃ + 1) + volume s₂ + 1
            rw [substVar_volume, substVar_volume]
            omega
        · refine ⟨Trans.bin (fun a c => op₂ (op₃ a b) c) (substVar i b s₃)
            (substVar i b s₂), ?_, Or.inl ?_⟩
          · funext x
            show op₂ (op₃ (eval (substVar i b s₃) x) b) (eval (substVar i b s₂) x)
                = op₂ (eval (substVar i b (Trans.bin op₃ s₃ (Trans.var i))) x)
                  (eval (substVar i b s₂) x)
            show op₂ (op₃ (eval (substVar i b s₃) x) b) (eval (substVar i b s₂) x)
                = op₂ (op₃ (eval (substVar i b s₃) x)
                    (eval (if i = i then Trans.cst b else Trans.var i) x))
                  (eval (substVar i b s₂) x)
            rw [if_pos rfl]
            rfl
          · show volume (substVar i b s₃) + volume (substVar i b s₂) + 1 + 2
                ≤ (volume s₃ + 1 + 1) + volume s₂ + 1
            rw [substVar_volume, substVar_volume]
            omega
      · -- the left child is a unary chain over the leaf
        by_cases hv1 : volume s₁ = 1
        · -- it is the bare leaf: the top decomposition surfaces
          have hs₁ : s₁ = Trans.var i := by
            cases s₁ with
            | var j =>
              have hj : j = i := by
                by_contra hji
                have h' : (if j = i then 1 else 0) = 1 := h1
                rw [if_neg hji] at h'
                omega
              rw [hj]
            | cst c => exact absurd h1 (by simp [occCount])
            | un op s => exact absurd hv1 (by
                show ¬(volume s + 1 = 1)
                have := volume_pos s
                omega)
            | bin op s t => exact absurd hv1 (by
                show ¬(volume s + volume t + 1 = 1)
                have := volume_pos s
                have := volume_pos t
                omega)
          subst hs₁
          refine ⟨Trans.un (fun a => op₂ b a) (substVar i b s₂), ?_,
            Or.inr (Or.inl ⟨?_, op₂, s₂, Or.inl rfl⟩)⟩
          · funext x
            show op₂ b (eval (substVar i b s₂) x)
                = op₂ (eval (if i = i then Trans.cst b else Trans.var i) x)
                  (eval (substVar i b s₂) x)
            rw [if_pos rfl]
            rfl
          · show volume (substVar i b s₂) + 1 + 1 ≤ 1 + volume s₂ + 1
            rw [substVar_volume]
            omega
        · -- a genuine chain: its substitution is the constant `u b`, and the whole chain dies
          refine ⟨Trans.un (fun a => op₂ (u b) a) (substVar i b s₂), ?_, Or.inl ?_⟩
          · funext x
            show op₂ (u b) (eval (substVar i b s₂) x)
                = op₂ (eval (substVar i b s₁) x) (eval (substVar i b s₂) x)
            have hval : eval (substVar i b s₁) x = u b := by
              rw [substVar_eval, hu (Function.update x i b), Function.update_self]
            rw [hval]
          · show volume (substVar i b s₂) + 1 + 2 ≤ volume s₁ + volume s₂ + 1
            rw [substVar_volume]
            have := volume_pos s₁
            omega
    · -- mirrored: the right child carries the occurrence
      obtain ⟨s₂', hse, hcase⟩ := ih₂ h2
      rcases hcase with hA | ⟨hB, op₃, s₃, hshape⟩ | ⟨u, hu⟩
      · refine ⟨Trans.bin op₂ (substVar i b s₁) s₂', ?_, Or.inl ?_⟩
        · funext x
          show op₂ (eval (substVar i b s₁) x) (eval s₂' x)
              = op₂ (eval (substVar i b s₁) x) (eval (substVar i b s₂) x)
          rw [hse]
        · show volume (substVar i b s₁) + volume s₂' + 1 + 2
              ≤ volume s₁ + volume s₂ + 1
          rw [substVar_volume]
          omega
      · rcases hshape with rfl | rfl
        · refine ⟨Trans.bin (fun a c => op₂ a (op₃ b c)) (substVar i b s₁)
            (substVar i b s₃), ?_, Or.inl ?_⟩
          · funext x
            show op₂ (eval (substVar i b s₁) x) (op₃ b (eval (substVar i b s₃) x))
                = op₂ (eval (substVar i b s₁) x)
                  (eval (substVar i b (Trans.bin op₃ (Trans.var i) s₃)) x)
            show op₂ (eval (substVar i b s₁) x) (op₃ b (eval (substVar i b s₃) x))
                = op₂ (eval (substVar i b s₁) x)
                  (op₃ (eval (if i = i then Trans.cst b else Trans.var i) x)
                    (eval (substVar i b s₃) x))
            rw [if_pos rfl]
            rfl
          · show volume (substVar i b s₁) + volume (substVar i b s₃) + 1 + 2
                ≤ volume s₁ + (1 + volume s₃ + 1) + 1
            rw [substVar_volume, substVar_volume]
            omega
        · refine ⟨Trans.bin (fun a c => op₂ a (op₃ c b)) (substVar i b s₁)
            (substVar i b s₃), ?_, Or.inl ?_⟩
          · funext x
            show op₂ (eval (substVar i b s₁) x) (op₃ (eval (substVar i b s₃) x) b)
                = op₂ (eval (substVar i b s₁) x)
                  (eval (substVar i b (Trans.bin op₃ s₃ (Trans.var i))) x)
            show op₂ (eval (substVar i b s₁) x) (op₃ (eval (substVar i b s₃) x) b)
                = op₂ (eval (substVar i b s₁) x)
                  (op₃ (eval (substVar i b s₃) x)
                    (eval (if i = i then Trans.cst b else Trans.var i) x))
            rw [if_pos rfl]
            rfl
          · show volume (substVar i b s₁) + volume (substVar i b s₃) + 1 + 2
                ≤ volume s₁ + (volume s₃ + 1 + 1) + 1
            rw [substVar_volume, substVar_volume]
            omega
      · by_cases hv2 : volume s₂ = 1
        · have hs₂ : s₂ = Trans.var i := by
            cases s₂ with
            | var j =>
              have hj : j = i := by
                by_contra hji
                have h' : (if j = i then 1 else 0) = 1 := h2
                rw [if_neg hji] at h'
                omega
              rw [hj]
            | cst c => exact absurd h2 (by simp [occCount])
            | un op s => exact absurd hv2 (by
                show ¬(volume s + 1 = 1)
                have := volume_pos s
                omega)
            | bin op s t => exact absurd hv2 (by
                show ¬(volume s + volume t + 1 = 1)
                have := volume_pos s
                have := volume_pos t
                omega)
          subst hs₂
          refine ⟨Trans.un (fun a => op₂ a b) (substVar i b s₁), ?_,
            Or.inr (Or.inl ⟨?_, op₂, s₁, Or.inr rfl⟩)⟩
          · funext x
            show op₂ (eval (substVar i b s₁) x) b
                = op₂ (eval (substVar i b s₁) x)
                  (eval (if i = i then Trans.cst b else Trans.var i) x)
            rw [if_pos rfl]
            rfl
          · show volume (substVar i b s₁) + 1 + 1 ≤ volume s₁ + 1 + 1
            rw [substVar_volume]
        · refine ⟨Trans.un (fun a => op₂ a (u b)) (substVar i b s₁), ?_, Or.inl ?_⟩
          · funext x
            show op₂ (eval (substVar i b s₁) x) (u b)
                = op₂ (eval (substVar i b s₁) x) (eval (substVar i b s₂) x)
            have hval : eval (substVar i b s₂) x = u b := by
              rw [substVar_eval, hu (Function.update x i b), Function.update_self]
            rw [hval]
          · show volume (substVar i b s₁) + 1 + 2 ≤ volume s₁ + volume s₂ + 1
            rw [substVar_volume]
            have := volume_pos s₂
            omega

/-! ### The dichotomy -/

/-- `f` is top-decomposable at `i`: a single gate separates `xᵢ` from the rest. -/
def TopDecomp {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  ∃ (op : Bool → Bool → Bool) (h : (Fin n → Bool) → Bool),
    (∀ x, f x = op (x i) (h x)) ∧ (∀ x b, h (Function.update x i b) = h x)

/-- **THE TWO-KILL DICHOTOMY (proved)**: a function depending on `i` that is not top-decomposable at `i` has a
restriction killing two gates. -/
theorem budget_twokill {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n)
    (hdep : DependsOnF f i) (hnt : ¬TopDecomp f i) :
    ∃ b : Bool, budget (restrictF f i b) + 2 ≤ budget f := by
  have hne : {v | ∃ t : Trans n, eval t = f ∧ volume t = v}.Nonempty :=
    ⟨volume (dnfFor f), dnfFor f, eval_dnfFor f, rfl⟩
  obtain ⟨t, hte, htv⟩ := Nat.sInf_mem hne
  have hbud : volume t = budget f := htv
  obtain ⟨x₁, x₀, hd, hnev⟩ := hdep
  have hvar : hasVar i t = true := by
    apply hasVar_of_depends i t x₁ x₀ (fun c hc => by
      by_contra hcc
      exact hc (hd c hcc))
    rw [show eval t = f from hte]
    exact hnev
  have hocc := hasVar_occ_pos i t hvar
  by_cases h1 : occCount i t = 1
  · obtain ⟨t', he, hcase⟩ := single_read_collapse i false t h1
    rcases hcase with hA | ⟨hB, op₂, s₂, hshape⟩ | ⟨u, hu⟩
    · refine ⟨false, ?_⟩
      have hcomp : eval t' = restrictF f i false := by
        funext x
        rw [he, substVar_eval, show eval t = f from hte]
        rfl
      have hb : budget (restrictF f i false) ≤ volume t' :=
        Nat.sInf_le ⟨t', hcomp, rfl⟩
      omega
    · -- top decomposition surfaces: contradiction
      exfalso
      apply hnt
      rcases hshape with rfl | rfl
      · have hocc₂ : occCount i s₂ = 0 := by
          have h' : (if i = i then 1 else 0) + occCount i s₂ = 1 := h1
          rw [if_pos rfl] at h'
          omega
        refine ⟨op₂, eval s₂, ?_, ?_⟩
        · intro x
          rw [← hte]
          rfl
        · intro x bb
          exact eval_update_of_hasVar_false i s₂ (occ_zero_hasVar_false i s₂ hocc₂) x bb
      · have hocc₂ : occCount i s₂ = 0 := by
          have h' : occCount i s₂ + (if i = i then 1 else 0) = 1 := h1
          rw [if_pos rfl] at h'
          omega
        refine ⟨fun a c => op₂ c a, eval s₂, ?_, ?_⟩
        · intro x
          rw [← hte]
          rfl
        · intro x bb
          exact eval_update_of_hasVar_false i s₂ (occ_zero_hasVar_false i s₂ hocc₂) x bb
    · -- unary chain: f is unary in xᵢ, hence top-decomposable
      exfalso
      apply hnt
      refine ⟨fun a _ => u a, fun _ => false, ?_, fun _ _ => rfl⟩
      intro x
      rw [← hte]
      exact hu x
  · -- two or more occurrences: the mechanism kills two
    have h2 : 2 ≤ occCount i t := by omega
    rcases subst_reduce_many i false t with hvart | ⟨t', he, hv⟩
    · exfalso
      subst hvart
      have h' : occCount i (Trans.var i) = 1 := by
        show (if i = i then 1 else 0) = 1
        rw [if_pos rfl]
      omega
    · refine ⟨false, ?_⟩
      have hcomp : eval t' = restrictF f i false := by
        funext x
        rw [he, substVar_eval, show eval t = f from hte]
        rfl
      have hb : budget (restrictF f i false) ≤ volume t' :=
        Nat.sInf_le ⟨t', hcomp, rfl⟩
      omega

/-! ### SAT is not top-decomposable at its sign bits -/

/-- Updating the sign bit swaps the probe. -/
theorem patch_probe_update (N : ℕ) (c : Fin (sat3M N)) (ctx : Fin N → Bool)
    (vj : Fin (sat3V N)) (sgn a : Bool) :
    Function.update (sat3Patch N c ctx (sat3Probe N vj sgn)) (sat3SignBit N c) a
      = sat3Patch N c ctx (sat3Probe N vj a) := by
  funext bb
  by_cases hbb : bb = sat3SignBit N c
  · subst hbb
    rw [Function.update_self]
    exact (probe_sign_read N c ctx vj a).symm
  · rw [Function.update_of_ne hbb]
    show (if bb.val / sat3D N = c.val then sat3Probe N vj sgn bb else ctx bb)
        = (if bb.val / sat3D N = c.val then sat3Probe N vj a bb else ctx bb)
    by_cases hd : bb.val / sat3D N = c.val
    · rw [if_pos hd, if_pos hd]
      have hr : bb.val % sat3D N ≠ sat3V N := by
        intro hrv
        apply hbb
        apply Fin.ext
        have hdm := Nat.div_add_mod bb.val (sat3D N)
        rw [hd, hrv] at hdm
        show bb.val = (sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega)).val
        rw [sat3Bit_val]
        show bb.val = c.val * sat3D N + (0 : ℕ) * (sat3V N + 1) + sat3V N
        have hcomm : sat3D N * c.val = c.val * sat3D N := Nat.mul_comm _ _
        omega
      show decide _ = decide _
      rw [decide_eq_decide]
      constructor
      · rintro (h | ⟨h, -⟩)
        · exact Or.inl h
        · exact absurd h hr
      · rintro (h | ⟨h, -⟩)
        · exact Or.inl h
        · exact absurd h hr
    · rw [if_neg hd, if_neg hd]

/-- **SAT has three behaviors at a sign bit (proved)** — so it is not top-decomposable there. -/
theorem sat3_not_topDecomp (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (c : Fin (sat3M N)) :
    ¬TopDecomp (sat3Family N) (sat3SignBit N c) := by
  rintro ⟨op, h, hfeq, hfree⟩
  have hk : (sat3M N - 2) + 1 ≤ sat3M N := by omega
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set j₀ : Fin (sat3M N - 2) := ⟨0, by omega⟩ with hj₀
  set vj : Fin (sat3V N) := ⟨0, hv⟩ with hvj
  -- context 1: identity behavior
  set y₁ : Fin N → Bool :=
    sat3Patch N c (sat3Context N c hk (fun _ => false)) (sat3Probe N vj false) with hy₁
  have hbeh₁ : ∀ a : Bool, sat3Family N (Function.update y₁ (sat3SignBit N c) a)
      = a := by
    intro a
    rw [hy₁, patch_probe_update]
    have := sat3Context_probe_eval N hv hk hkv c (fun _ => false) j₀ vj rfl a
    rw [this]
    cases a <;> rfl
  -- context 2: negation behavior
  set bvec₂ : Fin (sat3M N - 2) → Bool :=
    Function.update (fun _ => false) j₀ true with hbvec₂
  set y₂ : Fin N → Bool :=
    sat3Patch N c (sat3Context N c hk bvec₂) (sat3Probe N vj false) with hy₂
  have hbeh₂ : ∀ a : Bool, sat3Family N (Function.update y₂ (sat3SignBit N c) a)
      = !a := by
    intro a
    rw [hy₂, patch_probe_update]
    have := sat3Context_probe_eval N hv hk hkv c bvec₂ j₀ vj rfl a
    rw [this]
    have hb : bvec₂ j₀ = true := by
      rw [hbvec₂]
      exact Function.update_self j₀ true (fun _ => false) ▸ rfl
    rw [hb]
    cases a <;> rfl
  -- context 3: constant behavior via a foreign empty clause
  set c' : Fin (sat3M N) := if c.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩ with hc'
  have hc'ne : c'.val ≠ c.val := by
    rw [hc']
    split
    · next hz =>
        rw [hz]
        show (1 : ℕ) ≠ 0
        omega
    · next hz =>
        show (0 : ℕ) ≠ c.val
        omega
  set y₃ : Fin N → Bool := fun bb =>
    decide (bb.val % sat3D N = 0 ∧ bb.val / sat3D N ≠ c'.val ∧
      bb.val / sat3D N < sat3M N) with hy₃
  have hbeh₃ : ∀ a : Bool, sat3Family N (Function.update y₃ (sat3SignBit N c) a)
      = false := by
    intro a
    apply sat3Family_false_of_empty_clause N _ c'
    intro t i
    have hne : sat3Bit N c' t i.val (by have := i.isLt; omega) ≠ sat3SignBit N c := by
      intro hcontra
      apply hc'ne
      rw [← sat3Bit_clause N c' t i.val (by have := i.isLt; omega), hcontra]
      show (sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega)).val / sat3D N = c.val
      exact sat3Bit_clause N c ⟨0, by omega⟩ (sat3V N) (by omega)
    rw [Function.update_of_ne hne]
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro ⟨-, hdiv, -⟩
    exact hdiv (sat3Bit_clause N c' t i.val (by have := i.isLt; omega))
  -- top decomposition allows at most two behaviors: extract the six op-facts
  have hgen : ∀ (y : Fin N → Bool) (a : Bool),
      sat3Family N (Function.update y (sat3SignBit N c) a) = op a (h y) := by
    intro y a
    rw [hfeq (Function.update y (sat3SignBit N c) a)]
    congr 1
    · exact Function.update_self _ _ _
    · exact hfree y a
  have F1 : op false (h y₁) = false := (hgen y₁ false).symm.trans (hbeh₁ false)
  have F2 : op true (h y₁) = true := (hgen y₁ true).symm.trans (hbeh₁ true)
  have F3 : op false (h y₂) = true := (hgen y₂ false).symm.trans (hbeh₂ false)
  have F4 : op true (h y₂) = false := (hgen y₂ true).symm.trans (hbeh₂ true)
  have F5 : op false (h y₃) = false := (hgen y₃ false).symm.trans (hbeh₃ false)
  have F6 : op true (h y₃) = false := (hgen y₃ true).symm.trans (hbeh₃ true)
  -- three behaviors, two possible columns: pigeonhole
  cases hv1 : h y₁ <;> cases hv2 : h y₂ <;> cases hv3 : h y₃ <;>
    rw [hv1] at F1 F2 <;> rw [hv2] at F3 F4 <;> rw [hv3] at F5 F6 <;>
    first
      | exact Bool.noConfusion (F1.symm.trans F3)
      | exact Bool.noConfusion (F2.symm.trans F4)
      | exact Bool.noConfusion (F2.symm.trans F6)
      | exact Bool.noConfusion (F3.symm.trans F5)

/-- **The two-kill fires on the SAT target (proved)**: at every sign bit, some restriction of `sat3Family` kills
two gates. -/
theorem sat3_twokill (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (c : Fin (sat3M N)) :
    ∃ b : Bool, budget (restrictF (sat3Family N) (sat3SignBit N c) b) + 2
      ≤ budget (sat3Family N) := by
  obtain ⟨x₁, x₀, h1, h0, hforce⟩ := sat3_forcing_pair N hv hm3 c
  refine budget_twokill (sat3Family N) (sat3SignBit N c) ⟨x₁, x₀, hforce, ?_⟩
    (sat3_not_topDecomp N hv hm3 c)
  rw [h1, h0]
  decide

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.single_read_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.budget_twokill
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_not_topDecomp
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_twokill
