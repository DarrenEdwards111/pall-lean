import Mathlib

/-!
# The circuit-approximation framework (PROVED) — error accounting for the gate-by-gate approximation

The remaining input to `MOD_q ∉ AC⁰[p]` is the **circuit-approximation direction**: an `AC⁰[p]` circuit is
approximated, on all but a small "bad" set of inputs, by a low-degree `𝔽_p`-polynomial — obtained by approximating
each gate (the probabilistic OR/AND approximation of `ComputationalDepthOrApprox`, exact for `MOD_p`/`NOT`) and
composing up the circuit, the error accumulating by a union bound.

This file proves the **error-accounting framework** the induction runs on:

  `ApproxOn f g bad` — `f` and `g` agree outside `bad`.
  `ApproxOn.unary` / `ApproxOn.comp₂` — composition: applying a unary op preserves the bad set; a binary op's
        bad set is the *union* of the two (the inductive steps for `NOT` and for binary gates).
  `ApproxOn.comp₂_card_le` — the **union bound**: the composite bad set has size `≤` the sum.
  `ApproxOn.agree_on_compl` / `card_compl` — the **agreement set** `univ \ bad` carries `f = g` and has size
        exactly `2ⁿ - |bad|` — the large set `G` that `boosting_surjection` consumes.

So once each gate is approximated with a `2⁻ᵗ`-fraction bad set, the whole circuit (size `s`) is approximated off
a bad set of size `≤ s·2⁻ᵗ·2ⁿ`, and the agreement set has size `≥ (1 - s·2⁻ᵗ)·2ⁿ`.  The probabilistic per-gate
approximation and the nested-`Circuit` induction remain the targets; this is their accounting backbone.
-/

namespace PallLean.Paper93.DeepMath.PathB.CircuitApprox

variable {n : ℕ} {F : Type*}

/-- `f` is approximated by `g` outside the finite "bad" set: they agree on every input not in `bad`. -/
def ApproxOn (f g : (Fin n → Bool) → F) (bad : Finset (Fin n → Bool)) : Prop :=
  ∀ x, x ∉ bad → f x = g x

/-- Enlarging the bad set preserves approximation. -/
theorem ApproxOn.mono {f g : (Fin n → Bool) → F} {bad bad' : Finset (Fin n → Bool)}
    (h : ApproxOn f g bad) (hsub : bad ⊆ bad') : ApproxOn f g bad' :=
  fun x hx => h x (fun hb => hx (hsub hb))

/-- An exact equality is an approximation with empty bad set. -/
theorem ApproxOn.exact {f g : (Fin n → Bool) → F} (h : ∀ x, f x = g x) : ApproxOn f g ∅ :=
  fun x _ => h x

/-- **Unary composition** (e.g. `NOT`, `g ↦ 1 - g`): applying a unary operation preserves the bad set. -/
theorem ApproxOn.unary {f g : (Fin n → Bool) → F} {bad : Finset (Fin n → Bool)} (op : F → F)
    (h : ApproxOn f g bad) : ApproxOn (fun x => op (f x)) (fun x => op (g x)) bad :=
  fun x hx => congrArg op (h x hx)

/-- **Binary composition**: a binary operation's bad set is the union of the two operands' bad sets — outside
their union both agree, so the combination agrees.  (The inductive step for binary gates.) -/
theorem ApproxOn.comp₂ {G : Type*} {f₁ g₁ f₂ g₂ : (Fin n → Bool) → F}
    {b₁ b₂ : Finset (Fin n → Bool)} (op : F → F → G)
    (h₁ : ApproxOn f₁ g₁ b₁) (h₂ : ApproxOn f₂ g₂ b₂) :
    ApproxOn (fun x => op (f₁ x) (f₂ x)) (fun x => op (g₁ x) (g₂ x)) (b₁ ∪ b₂) := by
  intro x hx
  rw [Finset.mem_union, not_or] at hx
  show op (f₁ x) (f₂ x) = op (g₁ x) (g₂ x)
  rw [h₁ x hx.1, h₂ x hx.2]

/-- **The union bound.**  The composite bad set is no larger than the sum of the operands'. -/
theorem ApproxOn.comp₂_card_le (b₁ b₂ : Finset (Fin n → Bool)) :
    (b₁ ∪ b₂).card ≤ b₁.card + b₂.card := Finset.card_union_le b₁ b₂

/-- The approximation holds on the **agreement set** `univ \ bad`. -/
theorem ApproxOn.agree_on_compl {f g : (Fin n → Bool) → F} {bad : Finset (Fin n → Bool)}
    (h : ApproxOn f g bad) (x : Fin n → Bool) (hx : x ∈ Finset.univ \ bad) : f x = g x :=
  h x (Finset.mem_sdiff.mp hx).2

/-- The agreement set has size exactly `2ⁿ - |bad|`: the large set `G` consumed by `boosting_surjection`. -/
theorem card_compl (bad : Finset (Fin n → Bool)) :
    (Finset.univ \ bad).card = 2 ^ n - bad.card := by
  have h1 : (Finset.univ \ bad).card + bad.card = 2 ^ n := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ bad)]
    simp [Finset.card_univ, Fintype.card_bool, Fintype.card_fin]
  omega

end PallLean.Paper93.DeepMath.PathB.CircuitApprox

#print axioms PallLean.Paper93.DeepMath.PathB.CircuitApprox.ApproxOn.comp₂
#print axioms PallLean.Paper93.DeepMath.PathB.CircuitApprox.card_compl
