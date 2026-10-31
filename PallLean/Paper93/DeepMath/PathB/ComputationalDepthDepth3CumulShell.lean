import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingBridge

/-!
# Block-DT model, hbound-discharge lemma 1: the cumulative short-shell bound (branch `razborov-recoverRho-wip`)

The first of the three small lemmas discharging the union bound of `circuit_collapse_exists`
(`G·|{stars ≤ K-s}|·(2^w)^s < C(n,K)·2^{n-K}`).  The `|{stars ≤ K-s}|` is **cumulative**; this brick bounds it
by `(K-s+1)·|{stars = K-s}|` (the count times the top shell), using that the star-shells are **monotone
increasing** on `[0, K-s]` in the doubled regime `3(K-s) ≤ n+1`.

Star-shell cardinality is `|{stars = j}| = C(n,j)·2^{n-j}` (`card_stars_eq`).  The single-step monotonicity
`|{stars=j}| ≤ |{stars=j+1}|` reduces to `2·C(n,j) ≤ C(n,j+1)`, which holds when `3j+2 ≤ n` via the Pascal
identity `Nat.choose_succ_right_eq : C(n,k+1)·(k+1) = C(n,k)·(n-k)`.  Chaining (`stars_shell_mono`) and summing
the partition of `{stars ≤ K-s}` by star-value over `range (K-s+1)` gives the cumulative bound.

* `stars_shell_le_succ` — `|{stars=j}| ≤ |{stars=j+1}|` for `3j+2 ≤ n`.
* `stars_shell_mono` — `j ≤ m`, `3m ≤ n+1` ⟹ `|{stars=j}| ≤ |{stars=m}|`.
* `cumul_stars_le` — `3(K-s) ≤ n+1` ⟹ `|{stars ≤ K-s}| ≤ (K-s+1)·|{stars = K-s}|`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Single-step shell monotonicity.**  When `3j+2 ≤ n`, the `j`-star shell is no larger than the
`(j+1)`-star shell. -/
theorem stars_shell_le_succ (j : ℕ) (hj : 3 * j + 2 ≤ n) :
    (Finset.univ.filter (fun ρ : Restriction n => stars ρ = j)).card
      ≤ (Finset.univ.filter (fun ρ : Restriction n => stars ρ = j + 1)).card := by
  rw [card_stars_eq, card_stars_eq]
  -- `2·C(n,j) ≤ C(n,j+1)` from the Pascal identity and `2(j+1) ≤ n-j`.
  have hchoose : 2 * n.choose j ≤ n.choose (j + 1) := by
    have hid : n.choose (j + 1) * (j + 1) = n.choose j * (n - j) := Nat.choose_succ_right_eq n j
    have hmul : 2 * n.choose j * (j + 1) ≤ n.choose (j + 1) * (j + 1) := by
      rw [hid]
      calc 2 * n.choose j * (j + 1) = n.choose j * (2 * (j + 1)) := by ring
        _ ≤ n.choose j * (n - j) := Nat.mul_le_mul_left _ (by omega)
    exact Nat.le_of_mul_le_mul_right hmul (by omega)
  have hexp : n - j = (n - (j + 1)) + 1 := by omega
  rw [hexp, pow_succ]
  calc n.choose j * (2 ^ (n - (j + 1)) * 2) = (2 * n.choose j) * 2 ^ (n - (j + 1)) := by ring
    _ ≤ n.choose (j + 1) * 2 ^ (n - (j + 1)) := Nat.mul_le_mul_right _ hchoose

/-- **Chained shell monotonicity.**  For `j ≤ m` with `3m ≤ n+1`, the `j`-shell is no larger than the
`m`-shell (the shells increase up to `m`). -/
theorem stars_shell_mono : ∀ (m j : ℕ), j ≤ m → 3 * m ≤ n + 1 →
    (Finset.univ.filter (fun ρ : Restriction n => stars ρ = j)).card
      ≤ (Finset.univ.filter (fun ρ : Restriction n => stars ρ = m)).card := by
  intro m
  induction m with
  | zero => intro j hj _; rw [Nat.le_zero.mp hj]
  | succ m ih =>
    intro j hj hm
    by_cases hlt : j ≤ m
    · exact le_trans (ih j hlt (by omega)) (stars_shell_le_succ m (by omega))
    · rw [show j = m + 1 by omega]

/-- **The cumulative short-shell bound.**  Under `3(K-s) ≤ n+1`, the cumulative count of restrictions with
`≤ K-s` stars is at most `(K-s+1)` times the top shell `{stars = K-s}`. -/
theorem cumul_stars_le (K s : ℕ) (hreg : 3 * (K - s) ≤ n + 1) :
    (Finset.univ.filter (fun ρ : Restriction n => stars ρ ≤ K - s)).card
      ≤ (K - s + 1) * (Finset.univ.filter (fun ρ : Restriction n => stars ρ = K - s)).card := by
  classical
  have hpart : (Finset.univ.filter (fun ρ : Restriction n => stars ρ ≤ K - s)).card
      = ∑ j ∈ Finset.range (K - s + 1),
          ((Finset.univ.filter (fun ρ : Restriction n => stars ρ ≤ K - s)).filter
            (fun ρ => stars ρ = j)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun ρ hρ => Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hρ).2; omega))
  rw [hpart]
  calc ∑ j ∈ Finset.range (K - s + 1),
          ((Finset.univ.filter (fun ρ : Restriction n => stars ρ ≤ K - s)).filter
            (fun ρ => stars ρ = j)).card
      ≤ ∑ _j ∈ Finset.range (K - s + 1),
          (Finset.univ.filter (fun ρ : Restriction n => stars ρ = K - s)).card := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        have hsub : ((Finset.univ.filter (fun ρ : Restriction n => stars ρ ≤ K - s)).filter
            (fun ρ => stars ρ = j))
            ⊆ Finset.univ.filter (fun ρ : Restriction n => stars ρ = j) := by
          intro ρ hρ
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hρ).2⟩
        exact le_trans (Finset.card_le_card hsub)
          (stars_shell_mono (K - s) j (by rw [Finset.mem_range] at hj; omega) hreg)
    _ = (K - s + 1) * (Finset.univ.filter (fun ρ : Restriction n => stars ρ = K - s)).card := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.cumul_stars_le
