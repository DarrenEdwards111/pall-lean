import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RestrictedYBT

/-!
# Bounded-overlap `MOD`: small support footprint ⇒ exact `SYM∘AND` form

`…ACC0RestrictedYBT` bounded the exact `SYM∘AND` size by `maxBase ^ leafCount` (quasipoly only for *logarithmic* leaf
count).  This file gives the **sharp** criterion via the same multiplicative `psize` identity, in the form that
captures **bounded-overlap / disjoint `MOD` gates**: the size is `≤ 2^(baseSum C)`, where

```
baseSum (const) = 0   baseSum (var) = 1   baseSum (not c) = baseSum c
baseSum (and a b) = baseSum a + baseSum b   baseSum (or a b) = baseSum a + baseSum b
baseSum (mod q S t) = |S|
```

i.e. `baseSum C` is the circuit's **total support footprint** — the sum of all `MOD`-supports plus the number of
variable leaves.  Since `psize C ≤ 2^(baseSum C)` (each base `b ≤ 2^{b−1}`), a circuit whose footprint is `< n` has
an exact `SYM∘AND` form — *regardless of how many gates it has*.  This is exactly the bounded-overlap regime:
**disjoint (or low-overlap) `MOD` supports keep the footprint `≤ n`** (each variable counted once), so any
non-saturating disjoint-`MOD` circuit qualifies.

## What is proved (clean axioms, no `sorry`)

* `baseSum` and **`psize_le_two_pow_baseSum`** — `psize C ≤ 2^(baseSum C)` (the sharp size bound).
* **`acc0_exact_of_baseSum_lt`** — `baseSum C < n ⇒ HasExactSymAndForm C` (footprint criterion).
* `andOfModList` / `baseSum_andOfModList` — a depth-2 `AND` of a list of `MOD_q` gates, footprint `= ∑ |S_i|`.
* **`boundedOverlap_mod_exact`** — `∑ |S_i| < n ⇒` the `AND`-of-`MOD`s has an exact `SYM∘AND` form.
* `disjoint_mod_footprint_le` — **pairwise-disjoint** `MOD` supports have footprint `≤ n` (the bounded-overlap
  structural fact: disjoint supports never overflow the variable set).
* **`disjoint_mod_exact`** — pairwise-disjoint `MOD` gates whose supports don't cover *all* `n` variables have an
  exact `SYM∘AND` form.

## Honest scope

The footprint criterion is *sharp* for the mixed-radix construction (`baseSum = log₂ psize`), but it caps at `< n`:
it covers circuits reading `< n` literal-incidences (disjoint / bounded-overlap `MOD`, bounded total support).  A
*general* `ACC⁰` circuit reads all `n` variables many times over (footprint `≫ n`), so this does **not** touch the
full wall — it precisely characterises the fragment where the exact form is below `2^n`.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BoundedOverlapMOD

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACC0YBTSocket
open PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose
open PallLean.Paper93.DeepMath.PathB.ACC0RestrictedYBT

variable {n : ℕ}

/-- **`k + 1 ≤ 2^k` (proved).** -/
theorem succ_le_two_pow : ∀ k : ℕ, k + 1 ≤ 2 ^ k
  | 0 => le_refl 1
  | k + 1 => by
      have ih := succ_le_two_pow k
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
      rw [pow_succ]
      omega

/-- The circuit's **support footprint**: total `MOD`-support plus number of variable leaves. -/
def baseSum : ACC0Circuit n → ℕ
  | .const _ => 0
  | .var _ => 1
  | .not c => baseSum c
  | .and a b => baseSum a + baseSum b
  | .or a b => baseSum a + baseSum b
  | .mod _ S _ => S.card

/-- **The sharp size bound (proved): `psize C ≤ 2^(baseSum C)`.** -/
theorem psize_le_two_pow_baseSum (C : ACC0Circuit n) : psize C ≤ 2 ^ baseSum C := by
  induction C with
  | const _ => simp [psize, baseSum]
  | var _ => simp [psize, baseSum]
  | not c ih => simpa only [psize, baseSum] using ih
  | and a b iha ihb =>
      simp only [psize, baseSum, pow_add]
      exact Nat.mul_le_mul iha ihb
  | or a b iha ihb =>
      simp only [psize, baseSum, pow_add]
      exact Nat.mul_le_mul iha ihb
  | mod q S t => simpa only [psize, baseSum] using succ_le_two_pow S.card

/-- **The footprint criterion (proved): `baseSum C < n ⇒ HasExactSymAndForm C`.** -/
theorem acc0_exact_of_baseSum_lt (C : ACC0Circuit n) (h : baseSum C < n) :
    HasExactSymAndForm C :=
  restricted_acc0_has_exact_symAnd C
    (lt_of_le_of_lt (psize_le_two_pow_baseSum C) (Nat.pow_lt_pow_right (by norm_num) h))

/-- A depth-2 `AND` of a list of `MOD_q` gates `(support, target)`. -/
def andOfModList (q : ℕ) : List (Finset (Fin n) × ZMod q) → ACC0Circuit n
  | [] => ACC0Circuit.const true
  | g :: gs => ACC0Circuit.and (ACC0Circuit.mod q g.1 g.2) (andOfModList q gs)

/-- **The footprint of an `AND`-of-`MOD`s is the total support (proved).** -/
theorem baseSum_andOfModList (q : ℕ) (gates : List (Finset (Fin n) × ZMod q)) :
    baseSum (andOfModList q gates) = (gates.map (fun g => g.1.card)).sum := by
  induction gates with
  | nil => rfl
  | cons g gs ih => simp only [andOfModList, baseSum, ih, List.map_cons, List.sum_cons]

/-- **Bounded-overlap `MOD` (proved): if the total `MOD`-support is `< n`, the `AND`-of-`MOD`s has an exact
`SYM∘AND` form.** -/
theorem boundedOverlap_mod_exact (q : ℕ) (gates : List (Finset (Fin n) × ZMod q))
    (h : (gates.map (fun g => g.1.card)).sum < n) :
    HasExactSymAndForm (andOfModList q gates) :=
  acc0_exact_of_baseSum_lt _ (by rw [baseSum_andOfModList]; exact h)

/-- `S` disjoint from each member of `L` ⇒ disjoint from their union (proved). -/
theorem disjoint_foldr_union (S : Finset (Fin n)) :
    ∀ (L : List (Finset (Fin n))), (∀ T ∈ L, Disjoint S T) → Disjoint S (L.foldr (· ∪ ·) ∅)
  | [], _ => by simp
  | T :: L', h => by
      simp only [List.foldr_cons, Finset.disjoint_union_right]
      exact ⟨h T (List.mem_cons.mpr (Or.inl rfl)),
        disjoint_foldr_union S L' (fun U hU => h U (List.mem_cons.mpr (Or.inr hU)))⟩

/-- For pairwise-disjoint finsets, the total card equals the card of the union (proved). -/
theorem sum_card_eq_card_union :
    ∀ (L : List (Finset (Fin n))), L.Pairwise Disjoint →
      (L.map Finset.card).sum = (L.foldr (· ∪ ·) ∅).card
  | [], _ => by simp
  | S :: L', hd => by
      rw [List.pairwise_cons] at hd
      simp only [List.map_cons, List.sum_cons, List.foldr_cons]
      rw [sum_card_eq_card_union L' hd.2,
        Finset.card_union_of_disjoint (disjoint_foldr_union S L' hd.1)]

/-- **Pairwise-disjoint supports never overflow the variable set (proved): total card `≤ n`.** -/
theorem sum_card_le_of_pairwise_disjoint (L : List (Finset (Fin n))) (hd : L.Pairwise Disjoint) :
    (L.map Finset.card).sum ≤ Fintype.card (Fin n) := by
  rw [sum_card_eq_card_union L hd]
  exact Finset.card_le_univ _

/-- The footprint of an `AND`-of-`MOD`s equals the total card of the support list (proved). -/
theorem map_fst_card_eq {q : ℕ} (gates : List (Finset (Fin n) × ZMod q)) :
    (gates.map (fun g => g.1.card)) = (gates.map (fun g => g.1)).map Finset.card := by
  simp [List.map_map]

/-- **The bounded-overlap structural fact (proved): disjoint `MOD` supports have footprint `≤ n`.** -/
theorem disjoint_mod_footprint_le (q : ℕ) (gates : List (Finset (Fin n) × ZMod q))
    (hd : (gates.map (fun g => g.1)).Pairwise Disjoint) :
    baseSum (andOfModList q gates) ≤ Fintype.card (Fin n) := by
  rw [baseSum_andOfModList, map_fst_card_eq]
  exact sum_card_le_of_pairwise_disjoint _ hd

/-- **Disjoint-`MOD` exact form (proved): pairwise-disjoint `MOD` gates whose supports don't cover all `n` variables
have an exact `SYM∘AND` form.** -/
theorem disjoint_mod_exact (q : ℕ) (gates : List (Finset (Fin n) × ZMod q))
    (hd : (gates.map (fun g => g.1)).Pairwise Disjoint)
    (hne : (gates.map (fun g => g.1)).foldr (· ∪ ·) ∅ ≠ Finset.univ) :
    HasExactSymAndForm (andOfModList q gates) := by
  apply boundedOverlap_mod_exact
  rw [map_fst_card_eq, sum_card_eq_card_union _ hd]
  have h1 := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hne)
  simpa [Finset.card_univ, Fintype.card_fin] using h1

end PallLean.Paper93.DeepMath.PathB.ACC0BoundedOverlapMOD

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedOverlapMOD.psize_le_two_pow_baseSum
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedOverlapMOD.boundedOverlap_mod_exact
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedOverlapMOD.disjoint_mod_exact
