import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCRestrictionSwitchingVariance

/-!
# The star family: a concrete miniature of the high‑overlap wall

The bounded‑overlap variance bound (`…SwitchingVariance`) gave `Var ≤ d·k·s·p`.  To see *where* high overlap hurts,
this file isolates one extreme: a **star family** `S_j = core ∪ petal_j` with a common `core` and pairwise‑disjoint
`petals`.  All the overlap lives in the shared core (`S_i ∩ S_j = core` for `i ≠ j`).

Two facts pin down the phenomenon:

* **the covariance blows up through the core** — `Var[X] ≤ k·s·p + k²·|core|·p`: the off‑diagonal term is quadratic
  in `k`, scaled by the core size;
* **core surgery removes it** — killing the core (a restriction with `core` dead) drops every live coordinate's
  incidence to `≤ 1`, i.e. the petals are disjoint on the live set, so the disjoint pipeline (`d = 1`, `Var ≤ k·s·p`)
  fires.

So high overlap is bad **only while the shared core stays live** — the first concrete miniature of the Håstad wall.

## What is proved (clean axioms, no `sorry`)

* `starSupport`, `star_inter` — `S_i ∩ S_j = core` for `i ≠ j`.
* `star_cov_le` — `Cov(X_{S_i}, X_{S_j}) ≤ |core|·p` for `i ≠ j` (overlap through the core).
* `star_variance_le` — **`Var[X] ≤ k·s·p + k²·|core|·p`**: the quadratic core blowup.
* `core_surgery` — **killing the core makes the petals disjoint on the live set**: with `core` dead, every live
  coordinate lies in at most one star support.

## Honest reading

The `k²·|core|·p` term is exactly the high‑overlap covariance the second moment cannot absorb when `|core|` is large
— the miniature of the higher‑moment wall.  `core_surgery` shows it is *removable by a restriction*: kill the core
and overlap collapses to `1`.  So for star families the wall is not intrinsic — a depth‑reduction restriction that
hits the core defeats it.  The genuine `NP ⊄ ACC⁰` difficulty is the case where *no small set of killed coordinates*
disjointifies the supports (overlap that is not concentrated in a small core); the star is the solvable boundary
case that locates it.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACCOverlapStar

open PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingVariance

variable {n k : ℕ}

/-- A star support: the shared `core` together with the gate's own `petal`. -/
def starSupport (core : Finset (Fin n)) (petals : Fin k → Finset (Fin n)) (j : Fin k) : Finset (Fin n) :=
  core ∪ petals j

/-- **The overlap is exactly the core (proved): `S_i ∩ S_j = core` for `i ≠ j`.**  The petals are disjoint, so the
only shared coordinates are the core. -/
theorem star_inter (core : Finset (Fin n)) (petals : Fin k → Finset (Fin n))
    (hpet : ∀ i j, i ≠ j → Disjoint (petals i) (petals j)) (i j : Fin k) (hij : i ≠ j) :
    starSupport core petals i ∩ starSupport core petals j = core := by
  unfold starSupport
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hi, hj⟩
    rcases hi with hC | hPi
    · exact hC
    · rcases hj with hC | hPj
      · exact hC
      · exact absurd hPj (Finset.disjoint_left.mp (hpet i j hij) hPi)
  · intro hC
    exact ⟨Or.inl hC, Or.inl hC⟩

/-- **The pairwise covariance is bounded by the core (proved): `Cov ≤ |core|·p` for `i ≠ j`.** -/
theorem star_cov_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (core : Finset (Fin n))
    (petals : Fin k → Finset (Fin n)) (hpet : ∀ i j, i ≠ j → Disjoint (petals i) (petals j))
    (i j : Fin k) (hij : i ≠ j) :
    cov p (starSupport core petals i) (starSupport core petals j) ≤ (core.card : ℝ) * p := by
  have h := cov_le p hp0 hp1 (starSupport core petals i) (starSupport core petals j)
  rwa [star_inter core petals hpet i j hij] at h

/-- **The variance blows up through the core (proved): `Var[X] ≤ k·s·p + k²·|core|·p`.**  The off‑diagonal
covariances each contribute `|core|·p`, giving the quadratic‑in‑`k` core term. -/
theorem star_variance_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (core : Finset (Fin n))
    (petals : Fin k → Finset (Fin n)) (hpet : ∀ i j, i ≠ j → Disjoint (petals i) (petals j))
    (s : ℕ) (hfan : ∀ i, (starSupport core petals i).card ≤ s) :
    variance p (starSupport core petals) ≤ ((k * s + k ^ 2 * core.card : ℕ) : ℝ) * p := by
  have hrow : ∀ i, ∑ j, (starSupport core petals i ∩ starSupport core petals j).card
      ≤ s + k * core.card := by
    intro i
    rw [← Finset.add_sum_erase Finset.univ
        (fun j => (starSupport core petals i ∩ starSupport core petals j).card) (Finset.mem_univ i)]
    have he : ∑ j ∈ Finset.univ.erase i,
          (starSupport core petals i ∩ starSupport core petals j).card
        = ∑ _j ∈ Finset.univ.erase i, core.card :=
      Finset.sum_congr rfl (fun j hj => by
        rw [star_inter core petals hpet i j (Finset.ne_of_mem_erase hj).symm])
    rw [he, Finset.sum_const, smul_eq_mul, Finset.inter_self]
    have h2 : (Finset.univ.erase i).card ≤ k := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]; omega
    exact Nat.add_le_add (hfan i) (Nat.mul_le_mul h2 (le_refl _))
  have htot : ∑ i, ∑ j, (starSupport core petals i ∩ starSupport core petals j).card
      ≤ k * s + k ^ 2 * core.card := by
    calc ∑ i, ∑ j, (starSupport core petals i ∩ starSupport core petals j).card
        ≤ ∑ _i : Fin k, (s + k * core.card) := Finset.sum_le_sum (fun i _ => hrow i)
      _ = k * (s + k * core.card) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ = k * s + k ^ 2 * core.card := by ring
  unfold variance
  calc ∑ i, ∑ j, cov p (starSupport core petals i) (starSupport core petals j)
      ≤ ∑ i, ∑ j, ((starSupport core petals i ∩ starSupport core petals j).card : ℝ) * p :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => cov_le p hp0 hp1 _ _))
    _ = (∑ i, ∑ j, ((starSupport core petals i ∩ starSupport core petals j).card : ℝ)) * p := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_mul]
    _ = ((∑ i, ∑ j, (starSupport core petals i ∩ starSupport core petals j).card : ℕ) : ℝ) * p := by
        push_cast; ring
    _ ≤ ((k * s + k ^ 2 * core.card : ℕ) : ℝ) * p := by
        apply mul_le_mul_of_nonneg_right _ hp0; exact_mod_cast htot

/-- **Core surgery (proved): killing the core disjointifies the petals on the live set.**  If the `core` is dead
(disjoint from the live set `L`), then every live coordinate lies in at most one star support — overlap `1`, so the
disjoint pipeline (`Var ≤ k·s·p`) fires.  High overlap was due to the live core. -/
theorem core_surgery (core : Finset (Fin n)) (petals : Fin k → Finset (Fin n))
    (hpet : ∀ i j, i ≠ j → Disjoint (petals i) (petals j)) (L : Finset (Fin n))
    (hCL : Disjoint core L) (v : Fin n) (hv : v ∈ L) :
    (Finset.univ.filter (fun j => v ∈ starSupport core petals j)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  have hvC : v ∉ core := fun h => Finset.disjoint_left.mp hCL h hv
  have hva : v ∈ petals a := by
    have h := ha.2; unfold starSupport at h; rw [Finset.mem_union] at h
    exact h.resolve_left hvC
  have hvb : v ∈ petals b := by
    have h := hb.2; unfold starSupport at h; rw [Finset.mem_union] at h
    exact h.resolve_left hvC
  by_contra hab
  exact Finset.disjoint_left.mp (hpet a b hab) hva hvb

end PallLean.Paper93.DeepMath.PathB.ACCOverlapStar

#print axioms PallLean.Paper93.DeepMath.PathB.ACCOverlapStar.star_inter
#print axioms PallLean.Paper93.DeepMath.PathB.ACCOverlapStar.star_cov_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACCOverlapStar.star_variance_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACCOverlapStar.core_surgery
