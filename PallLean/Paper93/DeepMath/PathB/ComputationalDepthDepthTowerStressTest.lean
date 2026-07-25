import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepthTowerKRW
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW3

/-!
# Stress-test: is `hsq` satisfiable with an *explicit* in-`P` gadget?

The depth projection closed to `P ⊄ NC¹` modulo three sockets; the load-bearing one is `hsq`
(`k² ≤ dmdepth(g k)`, on `ar k ≤ 2^k` bits).  The NC¹ ceiling is a bound on the **ratio**
`ρ(f) := dmdepth f / log₂(arity f)` — `NC1Depth` = ratio bounded by a constant.  This file asks
whether KRW composition can *manufacture* an unbounded ratio from bounded (explicit, provable)
gadgets, and finds that it **cannot**, so `hsq` must already contain the super-NC¹ hardness.

* **`nat_log_mul_ge`** — `log₂ a + log₂ b ≤ log₂ (a·b)` (Nat floor-log is superadditive);
* **`comp_ratio_preserved` (proved)** — if `dmdepth f ≤ r·log₂ m` and `dmdepth g ≤ r·log₂ b` then
  `dmdepth (f⋄g) ≤ r·log₂ (m·b)`.  Composition **cannot raise the ratio** above `r` (the composite
  ratio is the mediant of the parts', hence `≤` their max).  Uses the *unconditional* depth upper
  bound `dmdepth_comp_le'` — this holds with **no** appeal to `KRWConjectureDepth`;
* **`scaleTower_nc1_of_bases_nc1` (proved)** — hence if every base is ratio-`r`-bounded, the whole
  composed tower is ratio-`r`-bounded: **composition adds no amplification**;
* **`hsq_bases_not_nc1` (proved)** — but `hsq` (with `har`) forces the bases to have *unbounded*
  ratio: for every `r` there is a level `k` with `r·log₂(ar k) < dmdepth(g k)`.

**Verdict (honest).**  Put together: the tower beats NC¹ *only* because `hsq` makes each gadget
`g k` already super-NC¹ (ratio `≥ k → ∞`); composition contributes none of the crossing.  An
**explicit** (in-`P`) gadget with super-logarithmic formula depth is exactly `P ⊄ NC¹` for the
gadget itself — so `hsq` + explicitness is **circular**, and socket #1 (`KRWConjectureDepth`) is not
what crosses the NC¹ line.  This mirrors the size route's collapse one level up: the hardness has to
be *put in* at the base, and putting it in explicitly is the open problem.  Nothing here is
`P ≠ NP`, and this does not refute the KRW *conjecture* — it locates where the real difficulty sits.
-/

namespace PallLean.Paper93.DeepMath.PathB.DepthTowerStressTest

open PallLean.Paper93.DeepMath.PathB.Khrapchenko
open PallLean.Paper93.DeepMath.PathB.DepthTowerKRW

/-- **Floor-log is superadditive (proved).**  `log₂ a + log₂ b ≤ log₂ (a·b)` for `a,b ≠ 0`. -/
theorem nat_log_mul_ge (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.log 2 a + Nat.log 2 b ≤ Nat.log 2 (a * b) := by
  have h1 : 2 ^ Nat.log 2 a ≤ a := Nat.pow_log_le_self 2 ha
  have h2 : 2 ^ Nat.log 2 b ≤ b := Nat.pow_log_le_self 2 hb
  have h3 : 2 ^ (Nat.log 2 a + Nat.log 2 b) ≤ a * b := by
    rw [pow_add]; exact Nat.mul_le_mul h1 h2
  exact Nat.le_log_of_pow_le (by norm_num) h3

/-- **Composition cannot raise the ratio (proved, unconditional — no KRW).**  If `f` and `g` are
each `NC¹` with ratio `≤ r` (`dmdepth ≤ r·log₂ arity`), so is `f ⋄ g`. -/
theorem comp_ratio_preserved {m b r : ℕ} (hm : 0 < m) (hb : 0 < b)
    (f : (Fin m → Bool) → Bool) (g : (Fin b → Bool) → Bool)
    (hf : dmdepth f ≤ r * Nat.log 2 m) (hg : dmdepth g ≤ r * Nat.log 2 b) :
    dmdepth (comp hb f g) ≤ r * Nat.log 2 (m * b) := by
  calc dmdepth (comp hb f g) ≤ dmdepth f + dmdepth g := dmdepth_comp_le' hm hb f g
    _ ≤ r * Nat.log 2 m + r * Nat.log 2 b := Nat.add_le_add hf hg
    _ = r * (Nat.log 2 m + Nat.log 2 b) := by ring
    _ ≤ r * Nat.log 2 (m * b) := Nat.mul_le_mul (le_refl r) (nat_log_mul_ge m b hm.ne' hb.ne')

/-- Composite arity is positive. -/
theorem scaleTower_arity_pos (S : ScalingBase) (k : ℕ) : 0 < (scaleTower S k).1 := by
  induction k with
  | zero => simpa only [scaleTower] using S.ar_pos 0
  | succ n ih => simp only [scaleTower]; exact Nat.mul_pos ih (S.ar_pos n)

/-- **Composition adds no amplification (proved).**  If every base is ratio-`r`-bounded, the whole
composed tower is ratio-`r`-bounded — so the tower can beat NC¹ only if some base already does. -/
theorem scaleTower_nc1_of_bases_nc1 (S : ScalingBase) (r : ℕ)
    (hbases : ∀ k, dmdepth (S.g k) ≤ r * Nat.log 2 (S.ar k)) (k : ℕ) :
    dmdepth (scaleTower S k).2 ≤ r * Nat.log 2 (scaleTower S k).1 := by
  induction k with
  | zero => simpa only [scaleTower] using hbases 0
  | succ n ih =>
    have h := comp_ratio_preserved (scaleTower_arity_pos S n) (S.ar_pos n)
      (scaleTower S n).2 (S.g n) ih (hbases n)
    simpa only [scaleTower] using h

/-- **`hsq` forces the bases to be super-NC¹ (proved).**  Under `hsq` and `har`, no fixed ratio `r`
bounds all bases: for every `r` there is a level `k` with `r·log₂(ar k) < dmdepth(g k)`.  So the
tower's escape from NC¹ comes entirely from `hsq`, not from composition. -/
theorem hsq_bases_not_nc1 (S : ScalingBase)
    (hsq : ∀ k, k * k ≤ dmdepth (S.g k)) (har : ∀ k, S.ar k ≤ 2 ^ k) (r : ℕ) :
    ∃ k, r * Nat.log 2 (S.ar k) < dmdepth (S.g k) := by
  refine ⟨r + 1, ?_⟩
  have hlog : Nat.log 2 (S.ar (r + 1)) ≤ r + 1 := by
    calc Nat.log 2 (S.ar (r + 1)) ≤ Nat.log 2 (2 ^ (r + 1)) :=
          Nat.log_mono_right (har (r + 1))
      _ = r + 1 := Nat.log_pow (by norm_num : (1 : ℕ) < 2) (r + 1)
  calc r * Nat.log 2 (S.ar (r + 1)) ≤ r * (r + 1) := Nat.mul_le_mul (le_refl r) hlog
    _ < (r + 1) * (r + 1) := by nlinarith
    _ ≤ dmdepth (S.g (r + 1)) := hsq (r + 1)

end PallLean.Paper93.DeepMath.PathB.DepthTowerStressTest

#print axioms PallLean.Paper93.DeepMath.PathB.DepthTowerStressTest.comp_ratio_preserved
#print axioms PallLean.Paper93.DeepMath.PathB.DepthTowerStressTest.scaleTower_nc1_of_bases_nc1
#print axioms PallLean.Paper93.DeepMath.PathB.DepthTowerStressTest.hsq_bases_not_nc1
