import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameThreeKill

/-!
# N-Frame: the min-occurrence premise for SAT — delivered in the xor-free basis

The three-kill premise (`min-occ ≥ 2`) cannot hold over the full binary basis for any function
(`read_once_normal_form`).  The classical resolution is the basis restriction: exclude the two xor-like gates.
There the premise becomes a theorem — via a **polarity invariant**.

**The invariant (proved).**  In a xor-free tree reading `xᵢ` at most once, the variable's influence travels one
path; at each gate the sibling value selects a column, and xor-freeness (`¬OppPol`) says a gate's two non-constant
columns share one polarity.  Hence *all sensitive points have the same orientation*
(`xorfree_orientation`): `eval t (x[i↦1])` agrees across every `x` where the tree is sensitive to `i`.

**The refutation (proved).**  `sat3Family` shows **both orientations** at every sign bit — the identity behavior
(all-false pins) and the negation behavior (flipped pin), exactly the data behind `¬TopDecomp` — so:

  `sat3_xorfree_min_occ` — **PROVED, the premise**: every xor-free tree computing `sat3Family` reads every sign
        bit **at least twice** — for all trees, not merely minimal ones.
  `sat3_xorfree_twokill_alltrees` — **PROVED**: hence every xor-free tree loses two nodes under every sign-bit
        restriction, by the mechanism alone.

## Honest scope

This is the classical basis-restricted occurrence bound (the `U₂` move behind Schnorr/Zwick-style constants),
formal and exact: over `B₂` the premise stays open — and provably must (the read-once normal form) — while over
the xor-free basis it holds for *every* tree.  Cashing it into a xor-free three-kill *schedule* requires replaying
the cascade inside the xor-free submodel (the fusion rewrites preserve xor-freeness — a checkable next rung).
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Xor-freeness -/

/-- Opposite-polarity columns in the first argument: the xor-like signature. -/
def OppPol (op : Bool → Bool → Bool) : Prop :=
  (op true false ≠ op false false) ∧ (op true true ≠ op false true) ∧
    (op false false ≠ op false true)

/-- A tree over the xor-free basis: no gate is xor-like in either argument. -/
def XorFreeT {n : ℕ} : Trans n → Prop
  | .var _ => True
  | .cst _ => True
  | .un _ s => XorFreeT s
  | .bin op s₁ s₂ =>
      ¬OppPol op ∧ ¬OppPol (fun a c => op c a) ∧ XorFreeT s₁ ∧ XorFreeT s₂

/-- Two non-constant columns of a xor-free gate agree on every row. -/
theorem xorfree_col_eq (op : Bool → Bool → Bool) (hnp : ¬OppPol op)
    (c₁ c₂ G : Bool) (h₁ : op true c₁ ≠ op false c₁) (h₂ : op true c₂ ≠ op false c₂) :
    op G c₁ = op G c₂ := by
  cases c₁ <;> cases c₂
  · rfl
  · -- columns false, true: same polarity forced
    have hdd : op false false = op false true := by
      by_contra hne
      exact hnp ⟨h₁, h₂, hne⟩
    cases G
    · exact hdd
    · have e₁ : op true false = !(op false false) := bool_eq_not_of_ne (Ne.symm h₁)
      have e₂ : op true true = !(op false true) := bool_eq_not_of_ne (Ne.symm h₂)
      rw [e₁, e₂, hdd]
  · have hdd : op false false = op false true := by
      by_contra hne
      exact hnp ⟨h₂, h₁, hne⟩
    cases G
    · exact hdd.symm
    · have e₁ : op true true = !(op false true) := bool_eq_not_of_ne (Ne.symm h₁)
      have e₂ : op true false = !(op false false) := bool_eq_not_of_ne (Ne.symm h₂)
      rw [e₁, e₂, hdd]
  · rfl

/-! ### The polarity invariant -/

/-- **The orientation invariant (proved)**: a xor-free tree reading `xᵢ` at most once gives every sensitive point
the same orientation. -/
theorem xorfree_orientation {n : ℕ} (i : Fin n) :
    ∀ t : Trans n, XorFreeT t → occCount i t ≤ 1 →
      ∀ x y : Fin n → Bool,
        eval t (Function.update x i true) ≠ eval t (Function.update x i false) →
        eval t (Function.update y i true) ≠ eval t (Function.update y i false) →
        eval t (Function.update x i true) = eval t (Function.update y i true) := by
  intro t
  induction t with
  | var j =>
    intro _ _ x y hsx hsy
    by_cases hj : j = i
    · subst hj
      show Function.update x j true j = Function.update y j true j
      rw [Function.update_self, Function.update_self]
    · exfalso
      apply hsx
      show Function.update x i true j = Function.update x i false j
      rw [Function.update_of_ne hj, Function.update_of_ne hj]
  | cst c =>
    intro _ _ x y hsx hsy
    exact absurd rfl hsx
  | un u s ih =>
    intro hxf hocc x y hsx hsy
    have hgx : eval s (Function.update x i true) ≠ eval s (Function.update x i false) := by
      intro hc
      apply hsx
      show u (eval s (Function.update x i true)) = u (eval s (Function.update x i false))
      rw [hc]
    have hgy : eval s (Function.update y i true) ≠ eval s (Function.update y i false) := by
      intro hc
      apply hsy
      show u (eval s (Function.update y i true)) = u (eval s (Function.update y i false))
      rw [hc]
    have hIH := ih hxf hocc x y hgx hgy
    show u (eval s (Function.update x i true)) = u (eval s (Function.update y i true))
    rw [hIH]
  | bin op s₁ s₂ ih₁ ih₂ =>
    intro hxf hocc x y hsx hsy
    obtain ⟨hnp1, hnp2, hxf1, hxf2⟩ := hxf
    have hsum : occCount i s₁ + occCount i s₂ ≤ 1 := hocc
    by_cases h2z : occCount i s₂ = 0
    · -- the path is in the left child
      have hfree2 : ∀ (z : Fin n → Bool) (b : Bool),
          eval s₂ (Function.update z i b) = eval s₂ z :=
        fun z b => eval_update_of_hasVar_false i s₂ (occ_zero_hasVar_false i s₂ h2z) z b
      have hx1 : eval (Trans.bin op s₁ s₂) (Function.update x i true)
          = op (eval s₁ (Function.update x i true)) (eval s₂ x) := by
        show op (eval s₁ (Function.update x i true)) (eval s₂ (Function.update x i true)) = _
        rw [hfree2 x true]
      have hx0 : eval (Trans.bin op s₁ s₂) (Function.update x i false)
          = op (eval s₁ (Function.update x i false)) (eval s₂ x) := by
        show op (eval s₁ (Function.update x i false)) (eval s₂ (Function.update x i false)) = _
        rw [hfree2 x false]
      have hy1 : eval (Trans.bin op s₁ s₂) (Function.update y i true)
          = op (eval s₁ (Function.update y i true)) (eval s₂ y) := by
        show op (eval s₁ (Function.update y i true)) (eval s₂ (Function.update y i true)) = _
        rw [hfree2 y true]
      have hy0 : eval (Trans.bin op s₁ s₂) (Function.update y i false)
          = op (eval s₁ (Function.update y i false)) (eval s₂ y) := by
        show op (eval s₁ (Function.update y i false)) (eval s₂ (Function.update y i false)) = _
        rw [hfree2 y false]
      rw [hx1, hx0] at hsx
      rw [hy1, hy0] at hsy
      have hg1x : eval s₁ (Function.update x i true) ≠ eval s₁ (Function.update x i false) := by
        intro hc
        apply hsx
        rw [hc]
      have hg1y : eval s₁ (Function.update y i true) ≠ eval s₁ (Function.update y i false) := by
        intro hc
        apply hsy
        rw [hc]
      have hIH := ih₁ hxf1 (by omega) x y hg1x hg1y
      -- the false-values also agree
      have hFx : eval s₁ (Function.update x i false)
          = !(eval s₁ (Function.update x i true)) := bool_eq_not_of_ne hg1x
      have hFy : eval s₁ (Function.update y i false)
          = !(eval s₁ (Function.update y i true)) := bool_eq_not_of_ne hg1y
      -- non-constant columns
      have hcolx : op true (eval s₂ x) ≠ op false (eval s₂ x) := by
        cases hGx : eval s₁ (Function.update x i true)
        · intro hc
          apply hsx
          rw [hGx, hFx, hGx]
          exact hc.symm
        · intro hc
          apply hsx
          rw [hGx, hFx, hGx]
          exact hc
      have hcoly : op true (eval s₂ y) ≠ op false (eval s₂ y) := by
        cases hGy : eval s₁ (Function.update y i true)
        · intro hc
          apply hsy
          rw [hGy, hFy, hGy]
          exact hc.symm
        · intro hc
          apply hsy
          rw [hGy, hFy, hGy]
          exact hc
      rw [hx1, hy1, hIH]
      exact xorfree_col_eq op hnp1 (eval s₂ x) (eval s₂ y)
        (eval s₁ (Function.update y i true)) hcolx hcoly
    · -- the path is in the right child
      have h1z : occCount i s₁ = 0 := by omega
      have hfree1 : ∀ (z : Fin n → Bool) (b : Bool),
          eval s₁ (Function.update z i b) = eval s₁ z :=
        fun z b => eval_update_of_hasVar_false i s₁ (occ_zero_hasVar_false i s₁ h1z) z b
      have hx1 : eval (Trans.bin op s₁ s₂) (Function.update x i true)
          = op (eval s₁ x) (eval s₂ (Function.update x i true)) := by
        show op (eval s₁ (Function.update x i true)) (eval s₂ (Function.update x i true)) = _
        rw [hfree1 x true]
      have hx0 : eval (Trans.bin op s₁ s₂) (Function.update x i false)
          = op (eval s₁ x) (eval s₂ (Function.update x i false)) := by
        show op (eval s₁ (Function.update x i false)) (eval s₂ (Function.update x i false)) = _
        rw [hfree1 x false]
      have hy1 : eval (Trans.bin op s₁ s₂) (Function.update y i true)
          = op (eval s₁ y) (eval s₂ (Function.update y i true)) := by
        show op (eval s₁ (Function.update y i true)) (eval s₂ (Function.update y i true)) = _
        rw [hfree1 y true]
      have hy0 : eval (Trans.bin op s₁ s₂) (Function.update y i false)
          = op (eval s₁ y) (eval s₂ (Function.update y i false)) := by
        show op (eval s₁ (Function.update y i false)) (eval s₂ (Function.update y i false)) = _
        rw [hfree1 y false]
      rw [hx1, hx0] at hsx
      rw [hy1, hy0] at hsy
      have hg2x : eval s₂ (Function.update x i true) ≠ eval s₂ (Function.update x i false) := by
        intro hc
        apply hsx
        rw [hc]
      have hg2y : eval s₂ (Function.update y i true) ≠ eval s₂ (Function.update y i false) := by
        intro hc
        apply hsy
        rw [hc]
      have hIH := ih₂ hxf2 (by omega) x y hg2x hg2y
      have hFx : eval s₂ (Function.update x i false)
          = !(eval s₂ (Function.update x i true)) := bool_eq_not_of_ne hg2x
      have hFy : eval s₂ (Function.update y i false)
          = !(eval s₂ (Function.update y i true)) := bool_eq_not_of_ne hg2y
      -- rows are the flipped gate's columns
      have hcolx : (fun a c => op c a) true (eval s₁ x)
          ≠ (fun a c => op c a) false (eval s₁ x) := by
        show op (eval s₁ x) true ≠ op (eval s₁ x) false
        cases hGx : eval s₂ (Function.update x i true)
        · intro hc
          apply hsx
          rw [hGx, hFx, hGx]
          exact hc.symm
        · intro hc
          apply hsx
          rw [hGx, hFx, hGx]
          exact hc
      have hcoly : (fun a c => op c a) true (eval s₁ y)
          ≠ (fun a c => op c a) false (eval s₁ y) := by
        show op (eval s₁ y) true ≠ op (eval s₁ y) false
        cases hGy : eval s₂ (Function.update y i true)
        · intro hc
          apply hsy
          rw [hGy, hFy, hGy]
          exact hc.symm
        · intro hc
          apply hsy
          rw [hGy, hFy, hGy]
          exact hc
      rw [hx1, hy1, hIH]
      exact xorfree_col_eq (fun a c => op c a) hnp2 (eval s₁ x) (eval s₁ y)
        (eval s₂ (Function.update y i true)) hcolx hcoly

/-! ### Both orientations at the SAT sign bits -/

/-- **THE PREMISE, DELIVERED (proved)**: every xor-free tree computing `sat3Family` reads every sign bit at least
twice — all trees, not merely minimal ones. -/
theorem sat3_xorfree_min_occ (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (c : Fin (sat3M N)) (t : Trans N) (hxf : XorFreeT t)
    (hte : eval t = sat3Family N) :
    2 ≤ occCount (sat3SignBit N c) t := by
  by_contra hcon
  push_neg at hcon
  have hocc : occCount (sat3SignBit N c) t ≤ 1 := by omega
  -- the two orientation contexts
  have hk : (sat3M N - 2) + 1 ≤ sat3M N := by omega
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set j₀ : Fin (sat3M N - 2) := ⟨0, by omega⟩ with hj₀
  set vj : Fin (sat3V N) := ⟨0, hv⟩ with hvj
  set y₁ : Fin N → Bool :=
    sat3Patch N c (sat3Context N c hk (fun _ => false)) (sat3Probe N vj false) with hy₁
  have hbeh₁ : ∀ a : Bool, sat3Family N (Function.update y₁ (sat3SignBit N c) a) = a := by
    intro a
    rw [hy₁, patch_probe_update]
    have := sat3Context_probe_eval N hv hk hkv c (fun _ => false) j₀ vj rfl a
    rw [this]
    cases a <;> rfl
  set bvec₂ : Fin (sat3M N - 2) → Bool :=
    Function.update (fun _ => false) j₀ true with hbvec₂
  set y₂ : Fin N → Bool :=
    sat3Patch N c (sat3Context N c hk bvec₂) (sat3Probe N vj false) with hy₂
  have hbeh₂ : ∀ a : Bool, sat3Family N (Function.update y₂ (sat3SignBit N c) a) = !a := by
    intro a
    rw [hy₂, patch_probe_update]
    have := sat3Context_probe_eval N hv hk hkv c bvec₂ j₀ vj rfl a
    rw [this]
    have hb : bvec₂ j₀ = true := by
      rw [hbvec₂, Function.update_self]
    rw [hb]
    cases a <;> rfl
  -- sensitivities and the orientation clash
  have hsx : eval t (Function.update y₁ (sat3SignBit N c) true)
      ≠ eval t (Function.update y₁ (sat3SignBit N c) false) := by
    rw [hte, hbeh₁ true, hbeh₁ false]
    decide
  have hsy : eval t (Function.update y₂ (sat3SignBit N c) true)
      ≠ eval t (Function.update y₂ (sat3SignBit N c) false) := by
    rw [hte, hbeh₂ true, hbeh₂ false]
    decide
  have horient := xorfree_orientation (sat3SignBit N c) t hxf hocc y₁ y₂ hsx hsy
  rw [hte, hbeh₁ true, hbeh₂ true] at horient
  exact Bool.noConfusion horient

/-- **The two-kill for every xor-free tree (proved)**: with the occurrence premise supplied, the mechanism alone
loses two nodes under every sign-bit restriction. -/
theorem sat3_xorfree_twokill_alltrees (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (c : Fin (sat3M N)) (t : Trans N) (hxf : XorFreeT t)
    (hte : eval t = sat3Family N) (b : Bool) :
    ∃ t' : Trans N, eval t' = eval (substVar (sat3SignBit N c) b t) ∧
      volume t' + 2 ≤ volume t := by
  have hocc := sat3_xorfree_min_occ N hv hm3 c t hxf hte
  rcases subst_reduce_many (sat3SignBit N c) b t with hvar | ⟨t', he, hV⟩
  · exfalso
    subst hvar
    have h1 : occCount (sat3SignBit N c) (Trans.var (sat3SignBit N c)) = 1 := by
      show (if sat3SignBit N c = sat3SignBit N c then 1 else 0) = 1
      rw [if_pos rfl]
    omega
  · exact ⟨t', he, by omega⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.xorfree_col_eq
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.xorfree_orientation
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_xorfree_min_occ
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_xorfree_twokill_alltrees
