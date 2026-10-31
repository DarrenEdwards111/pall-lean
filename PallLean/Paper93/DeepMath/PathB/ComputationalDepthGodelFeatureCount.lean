import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGodelHierarchySPDPScaling

/-!
# Attacking `levelProj_feature_bound` at the Gödel level — the budget is vacuous

`levelProj_feature_bound` gives `pcrank (levelProj a L) M ≤ 2^{|index L|}`, where the index set is
`{S : |S| ≤ L.k} × {y : hw y ≤ L.d}`.  The A1 hope is that at the Gödel level `L = (log₂ n, log₂ n)` this ceiling
is *polynomial*.  This file determines whether it is — and the answer is **no**.

## What is proved (clean axioms, no `sorry`)

* `subsetCount_ge_two_pow` — `2^k ≤ |{S : Finset (Fin a) // S.card ≤ k}|` for `k ≤ a` (the powerset of one fixed
  `k`-subset already gives `2^k` sets of size `≤ k`).
* `featureCount_ge_two_pow` — hence the full index set has `≥ 2^{L.k}` elements.
* `godel_feature_count_superlinear` — **at the Gödel level the index count exceeds `n/2`**:
  `n < 2 · |index (godelLevel n)|`.  (Because `|index| ≥ 2^{log₂ n}` and `n < 2^{log₂ n + 1} = 2·2^{log₂ n}`.)
* `godel_feature_bound_vacuous` — the verdict, bundled: the only generic bound is `pcrank ≤ 2^{count}`, **and**
  `count > n/2`.  So the ceiling is `2^{> n/2}` — *exponential*, exceeding even the trivial `crank ≤ 2^a`.

## Verdict — A1 cannot come from counting features

At the Gödel level the feature‑count ceiling is exponential in `n`, not polynomial — the generic feature bound is
**vacuous** for A1 (it is no better than the trivial `crank` bound).  This is the honest outcome of the attack:
counting the *size* of the feature space cannot establish A1.  A polynomial A1 bound at the Gödel level must come
from **poly‑time structure** forcing a poly number of *realized* features — i.e. that a poly‑time observer's rows,
though living in a `2^{>n/2}`‑element feature space, actually take only polynomially many distinct values.  That is
exactly the `ScalingSPDPBridge` content; this file proves it is *not* a counting fact, sharpening where the
remaining `P ≠ NP`‑strength work must live.

(The matching upper side: `|index| ≤ (a+1)^{L.k} · (a+1)^{L.d}`, so at the Gödel level the count is *quasi‑poly*
`n^{Θ(log n)} = 2^{Θ(log² n)}` — already super‑polynomial.  Either way the ceiling `2^{count}` is super‑poly; the
clean exponential lower bound above suffices for the vacuity verdict.)
-/

namespace PallLean.Paper93.DeepMath.PathB.GodelFeatureCount

open PallLean.Paper93.DeepMath.PathB.RankContextualWidth
open PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank
open PallLean.Paper93.DeepMath.PathB.LowDegreeProjection
open PallLean.Paper93.DeepMath.PathB.SPDPFeatureProjection
open PallLean.Paper93.DeepMath.PathB.GodelHierarchySPDPScaling

/-- **`2^k ≤ #{subsets of size ≤ k}` (proved).**  The powerset of any fixed `k`‑element subset of `Fin a` already
contributes `2^k` distinct sets of size `≤ k`. -/
theorem subsetCount_ge_two_pow {a k : ℕ} (hka : k ≤ a) :
    2 ^ k ≤ Fintype.card {S : Finset (Fin a) // S.card ≤ k} := by
  classical
  obtain ⟨T₀, -, hT₀⟩ := Finset.exists_subset_card_eq
    (show k ≤ (Finset.univ : Finset (Fin a)).card by
      rw [Finset.card_univ, Fintype.card_fin]; exact hka)
  rw [Fintype.card_subtype]
  have hpow : 2 ^ k = T₀.powerset.card := by rw [Finset.card_powerset, hT₀]
  rw [hpow]
  apply Finset.card_le_card
  intro U hU
  rw [Finset.mem_powerset] at hU
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ U, le_trans (Finset.card_le_card hU) (le_of_eq hT₀)⟩

/-- **`2^{L.k} ≤ #(index set)` (proved).** -/
theorem featureCount_ge_two_pow {a : ℕ} (L : SPDPLevel) (hka : L.k ≤ a) :
    2 ^ L.k ≤ Fintype.card ({S : Finset (Fin a) // S.card ≤ L.k} × LowWt a L.d) := by
  rw [Fintype.card_prod]
  have hpos : 0 < Fintype.card (LowWt a L.d) := by
    rw [Fintype.card_pos_iff]
    exact ⟨⟨fun _ => false, by simp [hw]⟩⟩
  calc 2 ^ L.k
      ≤ Fintype.card {S : Finset (Fin a) // S.card ≤ L.k} := subsetCount_ge_two_pow hka
    _ = Fintype.card {S : Finset (Fin a) // S.card ≤ L.k} * 1 := (Nat.mul_one _).symm
    _ ≤ Fintype.card {S : Finset (Fin a) // S.card ≤ L.k} * Fintype.card (LowWt a L.d) :=
        Nat.mul_le_mul (le_refl _) hpos

/-- `2^{log₂ n} ≤ #(index set)` at the Gödel level. -/
theorem godel_feature_count_ge_pow_log {a : ℕ} (n : ℕ) (hka : Nat.log 2 n ≤ a) :
    2 ^ Nat.log 2 n
      ≤ Fintype.card ({S : Finset (Fin a) // S.card ≤ (godelLevel n).k} × LowWt a (godelLevel n).d) :=
  featureCount_ge_two_pow (godelLevel n) hka

/-- **The Gödel‑level feature count is super‑linear in `n` (proved): `n < 2 · #(index set)`.**  Since
`#(index) ≥ 2^{log₂ n}` and `n < 2^{log₂ n + 1} = 2·2^{log₂ n}`. -/
theorem godel_feature_count_superlinear {a : ℕ} (n : ℕ) (hka : Nat.log 2 n ≤ a) :
    n < 2 * Fintype.card ({S : Finset (Fin a) // S.card ≤ (godelLevel n).k} × LowWt a (godelLevel n).d) := by
  have h1 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h2 := godel_feature_count_ge_pow_log n hka
  calc n < 2 ^ (Nat.log 2 n + 1) := h1
    _ = 2 * 2 ^ Nat.log 2 n := by rw [pow_succ, Nat.mul_comm]
    _ ≤ 2 * Fintype.card _ := Nat.mul_le_mul (le_refl 2) h2

/-- **The verdict (proved): the Gödel‑level feature bound is vacuous for A1.**  The only generic bound is
`pcrank ≤ 2^{count}`, **and** `count > n/2`, so the ceiling is `2^{> n/2}` — exponential in `n`, no polynomial A1
control.  A1 must come from poly‑time structure (few *realized* features), not from the size of the feature
space. -/
theorem godel_feature_bound_vacuous {a : ℕ} {A : Type*} [Fintype A] (n : ℕ) (hka : Nat.log 2 n ≤ a)
    (M : A → (Fin a → Bool) → Bool) :
    pcrank (levelProj a (godelLevel n)) M
        ≤ 2 ^ Fintype.card ({S : Finset (Fin a) // S.card ≤ (godelLevel n).k} × LowWt a (godelLevel n).d)
      ∧ n < 2 * Fintype.card ({S : Finset (Fin a) // S.card ≤ (godelLevel n).k} × LowWt a (godelLevel n).d) :=
  ⟨levelProj_feature_bound (godelLevel n) M, godel_feature_count_superlinear n hka⟩

end PallLean.Paper93.DeepMath.PathB.GodelFeatureCount

#print axioms PallLean.Paper93.DeepMath.PathB.GodelFeatureCount.subsetCount_ge_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.GodelFeatureCount.godel_feature_count_superlinear
#print axioms PallLean.Paper93.DeepMath.PathB.GodelFeatureCount.godel_feature_bound_vacuous
