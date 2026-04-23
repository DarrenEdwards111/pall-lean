/-
  PallLean/Paper93/Bridge/PerTypeInterfaceSpace.lean

  Per-type interface space `W_τ` for the Cook-Levin bridge layer.

  Agent H1 of 10 (parallel) — paper §9 Lemma 31 bridge-layer fix:
  Agent A's uniform `realInterfaceSpace` (span of active-type generators)
  does *not* contain the constant `1`, which forced the G1/G2 bridge
  constructions to carry a separate `1 ∈ ambient` hypothesis. The fix in
  this file is to provide a per-τ local interface space `W_τ` that
  natively contains the constant `1` along with the specific
  `cookLevinQ`-factor generators for that constraint type:

    * booleanity τ = 0:    span { 1, X₀, X₀² }           dim ≤ 3
    * adjacency τ = 1:     span { 1, X₀·X₁ }            dim ≤ 2
    * transitionLeft τ = 2: span { 1, X₀ }              dim ≤ 2
    * transitionRight τ = 3: ⊥ (dormant, dim = 0)

  Each variant satisfies dim ≤ 3 unconditionally, and every active
  variant contains the constant 1 by construction. This removes the
  `1 ∈ ambient` side hypothesis from downstream bridge constructions.

  No axioms are introduced beyond the Lean kernel's; no `sorry` occurs.
-/
import PallLean.SymmetricPowerBound

namespace PallLean.Paper93.Bridge

open SymmetricPowerBound (ConstraintType)

/-- **Per-type W_τ.** Each variant has dim ≤ 3 AND (on the three active
constraint types) contains the constant `1`. The dormant
`transitionRight` case is the zero submodule, consistent with the
dormancy convention of paper §9 Lemma 31.

Generators:
* booleanity: `{1, X₀, X₀²}` — covers the Boolean idempotence factor
  `X₀·(1 − X₀)` and its constant coefficient.
* adjacency: `{1, X₀·X₁}` — covers the bilinear adjacency factor and
  the constant coefficient.
* transitionLeft: `{1, X₀}` — covers the linear left-lookup factor and
  the constant coefficient.
* transitionRight: `⊥` — dormant.
-/
noncomputable def perTypeInterfaceSpace (τ : ConstraintType) :
    Submodule ℚ (MvPolynomial (Fin 4) ℚ) :=
  match τ with
  | .booleanity =>
      Submodule.span ℚ
        ({1, MvPolynomial.X 0, (MvPolynomial.X 0) ^ 2} :
          Set (MvPolynomial (Fin 4) ℚ))
  | .adjacency =>
      Submodule.span ℚ
        ({1, MvPolynomial.X 0 * MvPolynomial.X 1} :
          Set (MvPolynomial (Fin 4) ℚ))
  | .transitionLeft =>
      Submodule.span ℚ
        ({1, MvPolynomial.X 0} :
          Set (MvPolynomial (Fin 4) ℚ))
  | .transitionRight => ⊥

/-! ## Finrank bound: each per-type W_τ has dim ≤ 3

We use `finrank_span_le_card` to bound the dimension by the cardinality
of the generating set, then bound that cardinality above by 3 using
`Finset.card_insert_le` iteratively. For the dormant `transitionRight`
branch we use `finrank_bot`. -/

/-- A three-element finset `{a,b,c}` has cardinality at most 3. -/
private theorem triple_card_le_three
    {α : Type*} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Finset α).card ≤ 3 := by
  have h1 :
      (insert a (insert b ({c} : Finset α))).card
        ≤ (insert b ({c} : Finset α)).card + 1 :=
    Finset.card_insert_le _ _
  have h2 :
      (insert b ({c} : Finset α)).card
        ≤ ({c} : Finset α).card + 1 :=
    Finset.card_insert_le _ _
  have h3 : ({c} : Finset α).card = 1 := Finset.card_singleton _
  have hEq :
      ({a, b, c} : Finset α) = insert a (insert b ({c} : Finset α)) := rfl
  rw [hEq]
  calc (insert a (insert b ({c} : Finset α))).card
      ≤ (insert b ({c} : Finset α)).card + 1 := h1
    _ ≤ (({c} : Finset α).card + 1) + 1 := Nat.add_le_add_right h2 1
    _ = (1 + 1) + 1 := by rw [h3]
    _ = 3 := by norm_num

/-- A two-element finset `{a,b}` has cardinality at most 2. -/
private theorem pair_card_le_two
    {α : Type*} [DecidableEq α] (a b : α) :
    ({a, b} : Finset α).card ≤ 2 := by
  have h1 :
      (insert a ({b} : Finset α)).card
        ≤ ({b} : Finset α).card + 1 :=
    Finset.card_insert_le _ _
  have h2 : ({b} : Finset α).card = 1 := Finset.card_singleton _
  have hEq : ({a, b} : Finset α) = insert a ({b} : Finset α) := rfl
  rw [hEq]
  calc (insert a ({b} : Finset α)).card
      ≤ ({b} : Finset α).card + 1 := h1
    _ = 1 + 1 := by rw [h2]
    _ = 2 := by norm_num

/-- **Per-type dim ≤ 3.** Each `perTypeInterfaceSpace τ` has finrank
bounded by 3 over ℚ, by finset-cardinality of its explicit generating
set (with the dormant `transitionRight` branch trivially bounded via
`finrank_bot = 0 ≤ 3`). -/
theorem perTypeInterfaceSpace_finrank_le_three (τ : ConstraintType) :
    Module.finrank ℚ (perTypeInterfaceSpace τ) ≤ 3 := by
  classical
  cases τ with
  | booleanity =>
      unfold perTypeInterfaceSpace
      calc
        Module.finrank ℚ
            (Submodule.span ℚ
              ({1, MvPolynomial.X 0, (MvPolynomial.X 0) ^ 2} :
                Set (MvPolynomial (Fin 4) ℚ)))
            ≤ ({1, MvPolynomial.X 0, (MvPolynomial.X 0) ^ 2} :
                  Finset (MvPolynomial (Fin 4) ℚ)).card := by
          simpa using
            finrank_span_le_card (R := ℚ)
              (s := ({1, MvPolynomial.X 0, (MvPolynomial.X 0) ^ 2} :
                Set (MvPolynomial (Fin 4) ℚ)))
        _ ≤ 3 := triple_card_le_three 1 (MvPolynomial.X 0)
                    ((MvPolynomial.X 0) ^ 2)
  | adjacency =>
      unfold perTypeInterfaceSpace
      calc
        Module.finrank ℚ
            (Submodule.span ℚ
              ({1, MvPolynomial.X 0 * MvPolynomial.X 1} :
                Set (MvPolynomial (Fin 4) ℚ)))
            ≤ ({1, MvPolynomial.X 0 * MvPolynomial.X 1} :
                  Finset (MvPolynomial (Fin 4) ℚ)).card := by
          simpa using
            finrank_span_le_card (R := ℚ)
              (s := ({1, MvPolynomial.X 0 * MvPolynomial.X 1} :
                Set (MvPolynomial (Fin 4) ℚ)))
        _ ≤ 2 := pair_card_le_two 1 (MvPolynomial.X 0 * MvPolynomial.X 1)
        _ ≤ 3 := by norm_num
  | transitionLeft =>
      unfold perTypeInterfaceSpace
      calc
        Module.finrank ℚ
            (Submodule.span ℚ
              ({1, MvPolynomial.X 0} :
                Set (MvPolynomial (Fin 4) ℚ)))
            ≤ ({1, MvPolynomial.X 0} :
                  Finset (MvPolynomial (Fin 4) ℚ)).card := by
          simpa using
            finrank_span_le_card (R := ℚ)
              (s := ({1, MvPolynomial.X 0} :
                Set (MvPolynomial (Fin 4) ℚ)))
        _ ≤ 2 := pair_card_le_two 1 (MvPolynomial.X 0)
        _ ≤ 3 := by norm_num
  | transitionRight =>
      unfold perTypeInterfaceSpace
      have hbot :
          Module.finrank ℚ
            (⊥ : Submodule ℚ (MvPolynomial (Fin 4) ℚ)) = 0 :=
        finrank_bot ℚ _
      rw [hbot]
      exact Nat.zero_le _

/-! ## Constant `1` membership

Every active branch has the constant `1` as a generator, so `1` lies in
the spanned submodule by `Submodule.subset_span`. The dormant
`transitionRight` case is excluded by hypothesis `hτ`. -/

/-- **Constant `1` lives in each active `W_τ`.** For every active
constraint type `τ ∈ {booleanity, adjacency, transitionLeft}`, the
constant polynomial `1 : MvPolynomial (Fin 4) ℚ` lies in
`perTypeInterfaceSpace τ`. The dormant `transitionRight` case is
excluded by hypothesis. -/
theorem one_mem_perTypeInterfaceSpace
    (τ : ConstraintType) (hτ : τ ≠ .transitionRight) :
    (1 : MvPolynomial (Fin 4) ℚ) ∈ perTypeInterfaceSpace τ := by
  cases τ with
  | booleanity =>
      unfold perTypeInterfaceSpace
      exact Submodule.subset_span (by
        show (1 : MvPolynomial (Fin 4) ℚ) ∈
          ({1, MvPolynomial.X 0, (MvPolynomial.X 0) ^ 2} :
            Set (MvPolynomial (Fin 4) ℚ))
        simp)
  | adjacency =>
      unfold perTypeInterfaceSpace
      exact Submodule.subset_span (by
        show (1 : MvPolynomial (Fin 4) ℚ) ∈
          ({1, MvPolynomial.X 0 * MvPolynomial.X 1} :
            Set (MvPolynomial (Fin 4) ℚ))
        simp)
  | transitionLeft =>
      unfold perTypeInterfaceSpace
      exact Submodule.subset_span (by
        show (1 : MvPolynomial (Fin 4) ℚ) ∈
          ({1, MvPolynomial.X 0} : Set (MvPolynomial (Fin 4) ℚ))
        simp)
  | transitionRight =>
      exact absurd rfl hτ

end PallLean.Paper93.Bridge
