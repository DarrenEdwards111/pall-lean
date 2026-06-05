import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukHardFunctionLB

/-!
# Nečiporuk concrete hard function (Stage 3): the explicit formula-size bound, headline form

Stage 2 produced `m·(2^b − 1) ≤ 2·clog₂(|Tok|+1)·litCount F + 2·(m+1)` with the alphabet cardinality
`|Tok (nn b m)|` left abstract.  This file resolves the alphabet count and states the headline
**formula-size lower bound** in division form.

* `NF.card_Tok_eq` — `|Tok n| = 16 + 2n` (the comment in the counting lemma, now a theorem): the
  serialization alphabet is `(Bool→Bool→Bool) ⊕ (Fin n × Bool)`, of size `2^4 + 2n`.
* `hardF_litCount_lower_explicit` — the bound with the alphabet count substituted, denominator
  `2·clog₂(2·nn + 17)`.
* `hardF_litCount_lower_div` — **the headline**: any `B₂` formula `F` computing `hardF` has
      `litCount F ≥ (m·(2^b − 1) − 2(m+1)) / (2·clog₂(2·nn + 17))`.

This is a genuine, fully explicit Nečiporuk formula-size lower bound: numerator `≈ m·2^b` (super-linear
in the `nn = m·b + 2^b` variables when `b ≈ log m`), denominator `≈ log nn`.  Ceiling: `n²/log²n`
formula size — a real *restricted* lower bound, **not** P vs NP.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-! ## The serialization alphabet has `16 + 2n` tokens -/

/-- `Tok n ≃ (Bool→Bool→Bool) ⊕ (Fin n × Bool)` — a gate token or a variable literal. -/
def NF.tokEquiv (n : ℕ) : NF.Tok n ≃ (Bool → Bool → Bool) ⊕ (Fin n × Bool) where
  toFun := fun t => match t with
    | .gate g => Sum.inl g
    | .lit i b => Sum.inr (i, b)
  invFun := fun s => match s with
    | Sum.inl g => .gate g
    | Sum.inr (i, b) => .lit i b
  left_inv := fun t => by cases t <;> rfl
  right_inv := fun s => by rcases s with g | ⟨i, b⟩ <;> rfl

/-- **The serialization alphabet has `16 + 2n` tokens.**  `2^4` binary gates plus `2n` signed
literals. -/
theorem NF.card_Tok_eq (n : ℕ) : Fintype.card (NF.Tok n) = 16 + 2 * n := by
  rw [Fintype.card_congr (NF.tokEquiv n), Fintype.card_sum, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_bool]
  have h16 : Fintype.card (Bool → Bool → Bool) = 16 := by decide
  rw [h16]; ring

namespace NecHard

open scoped BigOperators

variable {b m : ℕ}

/-- **The bound, fully explicit.**  As `hardF_litCount_lower` but with the alphabet cardinality
resolved: denominator `2·clog₂(2·nn + 17)`. -/
theorem hardF_litCount_lower_explicit (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = hardF x) :
    m * (Dsize b - 1) ≤
      2 * Nat.clog 2 (2 * nn b m + 17) * BFormula.litCount F + 2 * (m + 1) := by
  have h := hardF_litCount_lower F hF
  rwa [NF.card_Tok_eq, show 16 + 2 * nn b m + 1 = 2 * nn b m + 17 from by ring] at h

/-- **Headline formula-size lower bound (division form).**  Any `B₂` formula `F` computing the
explicit function `hardF` satisfies
  `litCount F ≥ (m·(2^b − 1) − 2(m+1)) / (2·clog₂(2·nn + 17))`,
a fully proved Nečiporuk lower bound (`≈ n²/log²n` for `b ≈ log m`, `m ≈ n/b`). -/
theorem hardF_litCount_lower_div (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = hardF x) :
    (m * (Dsize b - 1) - 2 * (m + 1)) / (2 * Nat.clog 2 (2 * nn b m + 17))
      ≤ BFormula.litCount F := by
  set D := 2 * Nat.clog 2 (2 * nn b m + 17) with hD
  have hcpos : 0 < Nat.clog 2 (2 * nn b m + 17) := Nat.clog_pos (by norm_num) (by omega)
  have hDpos : 0 < D := by rw [hD]; omega
  have h := hardF_litCount_lower_explicit F hF
  rw [← hD] at h
  have key : m * (Dsize b - 1) - 2 * (m + 1) ≤ D * BFormula.litCount F := by omega
  calc (m * (Dsize b - 1) - 2 * (m + 1)) / D
      ≤ (D * BFormula.litCount F) / D := Nat.div_le_div_right key
    _ = BFormula.litCount F := Nat.mul_div_cancel_left _ hDpos

end NecHard

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.NF.card_Tok_eq
#print axioms PallLean.Paper93.DeepMath.PathB.NecHard.hardF_litCount_lower_div
