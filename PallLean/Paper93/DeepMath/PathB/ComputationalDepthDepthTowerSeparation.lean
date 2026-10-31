import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepthTowerKRW
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW9

/-!
# Closing the depth projection to `P ⊄ NC¹`: the arity bookkeeping

`DepthTowerKRW` derived `depth_grow` from `KRWConjectureDepth` + a scaling base, but the composed
family lives on `∏ ar j` bits (multiplicative arity), not `2^k`, so it did not reach the `NC¹`
statement.  This file supplies the missing arity control and closes the chain to `P ⊄ NC¹`.

The clean quantitative choice (avoiding `Nat.log`-of-products): a **quadratic-depth** scaling base
`hsq : k² ≤ dmdepth (g k)` with **loose arity** `har : ar k ≤ 2^k`.  Then

* depth accumulates to `∑_{i<k} i²` (cubic in `k`) — `scaleTower_dmdepth_ge_sq`;
* arity is `≤ 2^(∑_{i<k} i)`, so `log₂(arity) ≤ ∑_{i<k} i` (quadratic) — `scaleTower_log_arity_le`;
* cubic beats quadratic by **polynomial** domination — `sum_sq_dom` (no log lemmas), giving
  `dmdepth(fam k) > c·log₂(arity)` for some `k`, whatever the constant `c`.

With a language `L` realising the family (`RealizesG`), that is exactly `¬ NC1Depth L`, and feeding
`InP L` gives `∃ L ∈ InP, ¬ NC1Depth L` — **`P ⊄ NC¹`**.

**Honest scope.**  The chain is now end-to-end down to three explicit hypotheses, no `sorry`:
`H : KRWConjectureDepth`; the scaling base `S`/`hsq` (an explicit in-`P` quadratic-depth gadget = the
uniformity gap); and `RealizesG L S ∧ InP L` (the family is computed in `P`).  `har` is a genuine
mild property (arity ≤ 2^k), satisfiable jointly with `hsq` for large `k`.  The ceiling is
`P ≠ NC¹`, **not** `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DepthTowerSeparation

open PallLean.Paper93.DeepMath.PathB.Khrapchenko
open PallLean.Paper93.DeepMath.PathB.DepthTowerKRW

/-! ### Depth accumulates to the sum of squares (cubic) -/

/-- Quadratic-depth `depth_grow`: composing the level-`k` base (depth `≥ k²`) adds `k²`. -/
theorem scaleTower_depth_grow_sq (H : KRWConjectureDepth) (S : ScalingBase)
    (hsq : ∀ k, k * k ≤ dmdepth (S.g k)) (k : ℕ) :
    dmdepth (scaleTower S k).2 + k * k ≤ dmdepth (scaleTower S (k + 1)).2 := by
  have hlb := H (scaleTower S k).1 (S.ar k) (S.ar_pos k) (scaleTower S k).2 (S.g k)
    (scaleTower_nc S k) (S.g_nc k)
  have hgd := hsq k
  simp only [scaleTower]
  omega

/-- The cubic depth lower bound: `∑_{i<k} i² ≤ dmdepth(fam k)`. -/
theorem scaleTower_dmdepth_ge_sq (H : KRWConjectureDepth) (S : ScalingBase)
    (hsq : ∀ k, k * k ≤ dmdepth (S.g k)) (k : ℕ) :
    (∑ i ∈ Finset.range k, i * i) ≤ dmdepth (scaleTower S k).2 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact le_trans (Nat.add_le_add_right ih (n * n)) (scaleTower_depth_grow_sq H S hsq n)

/-! ### Arity is `≤ 2^(∑ i)`, so log-arity is `≤ ∑ i` (quadratic) -/

/-- With `ar k ≤ 2^k`, the composite arity is `≤ 2^(∑_{i<k} i)`. -/
theorem scaleTower_arity_le (S : ScalingBase) (har : ∀ k, S.ar k ≤ 2 ^ k) (k : ℕ) :
    (scaleTower S k).1 ≤ 2 ^ (∑ i ∈ Finset.range k, i) := by
  induction k with
  | zero => simpa using har 0
  | succ n ih =>
    simp only [scaleTower]
    rw [Finset.sum_range_succ, pow_add]
    exact Nat.mul_le_mul ih (har n)

/-- Hence `log₂(arity) ≤ ∑_{i<k} i`. -/
theorem scaleTower_log_arity_le (S : ScalingBase) (har : ∀ k, S.ar k ≤ 2 ^ k) (k : ℕ) :
    Nat.log 2 (scaleTower S k).1 ≤ ∑ i ∈ Finset.range k, i := by
  calc Nat.log 2 (scaleTower S k).1
      ≤ Nat.log 2 (2 ^ (∑ i ∈ Finset.range k, i)) :=
        Nat.log_mono_right (scaleTower_arity_le S har k)
    _ = ∑ i ∈ Finset.range k, i :=
        Nat.log_pow (by norm_num : (1 : ℕ) < 2) (∑ i ∈ Finset.range k, i)

/-! ### Cubic beats quadratic (polynomial domination, no logs) -/

/-- **`∑ i² ` outgrows `c·(∑ i + 1)` (proved).**  At `k = 4c+2` the sum of squares (via its top
half, `≥ (2c+1)³`) exceeds `c` times the sum of firsts (`= (2c+1)(4c+1)`). -/
theorem sum_sq_dom (c : ℕ) :
    ∃ k, c * ((∑ i ∈ Finset.range k, i) + 1) < ∑ i ∈ Finset.range k, i * i := by
  refine ⟨4 * c + 2, ?_⟩
  -- sum of firsts, doubled (Gauss)
  have h2sum : 2 * (∑ i ∈ Finset.range (4 * c + 2), i) = (4 * c + 2) * (4 * c + 1) := by
    have h := Finset.sum_range_id_mul_two (4 * c + 2)
    have he : 4 * c + 2 - 1 = 4 * c + 1 := by omega
    rw [he] at h; omega
  -- sum of squares ≥ top half ≥ (2c+1)³
  have hsub : Finset.Ico (2 * c + 1) (4 * c + 2) ⊆ Finset.range (4 * c + 2) := by
    intro x hx; rw [Finset.mem_Ico] at hx; rw [Finset.mem_range]; omega
  have hsq_ge : (2 * c + 1) * ((2 * c + 1) * (2 * c + 1))
      ≤ ∑ i ∈ Finset.range (4 * c + 2), i * i := by
    calc (2 * c + 1) * ((2 * c + 1) * (2 * c + 1))
        = (Finset.Ico (2 * c + 1) (4 * c + 2)).card * ((2 * c + 1) * (2 * c + 1)) := by
          rw [Nat.card_Ico]; congr 1; omega
      _ = ∑ _i ∈ Finset.Ico (2 * c + 1) (4 * c + 2), (2 * c + 1) * (2 * c + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ i ∈ Finset.Ico (2 * c + 1) (4 * c + 2), i * i :=
          Finset.sum_le_sum (fun i hi => by
            rw [Finset.mem_Ico] at hi; exact Nat.mul_le_mul hi.1 hi.1)
      _ ≤ ∑ i ∈ Finset.range (4 * c + 2), i * i := Finset.sum_le_sum_of_subset hsub
  nlinarith [h2sum, hsq_ge]

/-! ### Realization and the separation -/

/-- `L` realises the composed family at its composite lengths. -/
def RealizesG (L : List Bool → Bool) (S : ScalingBase) : Prop :=
  ∀ (k : ℕ) (x : Fin (scaleTower S k).1 → Bool), L (List.ofFn x) = (scaleTower S k).2 x

theorem realizesG_slice (L : List Bool → Bool) (S : ScalingBase) (hR : RealizesG L S) (k : ℕ) :
    langSlice L (scaleTower S k).1 = (scaleTower S k).2 := by
  funext x; exact hR k x

/-- **The family beats `NC¹` depth (proved).**  Cubic depth over quadratic log-arity forces
`¬ NC1Depth L` for any `L` realising the tower. -/
theorem scaleTower_not_nc1 (H : KRWConjectureDepth) (S : ScalingBase)
    (hsq : ∀ k, k * k ≤ dmdepth (S.g k)) (har : ∀ k, S.ar k ≤ 2 ^ k)
    (L : List Bool → Bool) (hR : RealizesG L S) : ¬ NC1Depth L := by
  rintro ⟨c, hc⟩
  obtain ⟨k, hk⟩ := sum_sq_dom c
  have hslice : langSlice L (scaleTower S k).1 = (scaleTower S k).2 := realizesG_slice L S hR k
  have hdepth : (∑ i ∈ Finset.range k, i * i) ≤ dmdepth (scaleTower S k).2 :=
    scaleTower_dmdepth_ge_sq H S hsq k
  have hlog : Nat.log 2 (scaleTower S k).1 ≤ ∑ i ∈ Finset.range k, i :=
    scaleTower_log_arity_le S har k
  have hc' := hc (scaleTower S k).1
  rw [hslice] at hc'
  have hmul : c * (Nat.log 2 (scaleTower S k).1 + 1) ≤ c * ((∑ i ∈ Finset.range k, i) + 1) :=
    Nat.mul_le_mul (le_refl c) (Nat.add_le_add_right hlog 1)
  have hchain : (∑ i ∈ Finset.range k, i * i) ≤ c * ((∑ i ∈ Finset.range k, i) + 1) :=
    le_trans hdepth (le_trans hc' hmul)
  exact absurd hchain (not_le.mpr hk)

/-- **`P ⊄ NC¹`, closed (proved).**  A `KRWConjectureDepth`-backed quadratic-depth scaling base
whose family is realised by an `InP` language gives a language in `InP` outside `NC1Depth`.  The
three explicit hypotheses (`H`, the scaling base `S`/`hsq`, and `InP L ∧ RealizesG L S`) are the
open KRW sockets; nothing here supplies them, and nothing is `P ≠ NP`. -/
theorem scaleTower_krw_separation (H : KRWConjectureDepth) (S : ScalingBase)
    (hsq : ∀ k, k * k ≤ dmdepth (S.g k)) (har : ∀ k, S.ar k ≤ 2 ^ k)
    (L : List Bool → Bool) (hInP : ComposableMachine.InP L) (hR : RealizesG L S) :
    ∃ L, ComposableMachine.InP L ∧ ¬ NC1Depth L :=
  ⟨L, hInP, scaleTower_not_nc1 H S hsq har L hR⟩

end PallLean.Paper93.DeepMath.PathB.DepthTowerSeparation

#print axioms PallLean.Paper93.DeepMath.PathB.DepthTowerSeparation.sum_sq_dom
#print axioms PallLean.Paper93.DeepMath.PathB.DepthTowerSeparation.scaleTower_not_nc1
#print axioms PallLean.Paper93.DeepMath.PathB.DepthTowerSeparation.scaleTower_krw_separation
