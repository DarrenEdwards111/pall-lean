import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRSAssembly
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoostingFinal
import Mathlib

/-!
# Hardness instantiation skeleton (PROVED shape + mechanism; deep core fenced)

`ACC0.Circuit.no_acp_circuit` turns a *hardness* fact about a function `f` into a circuit lower bound.  This file
makes the instantiation concrete and **honest**: it proves the separation *shape* and the boosting *mechanism*, and
fences — precisely, as documented gaps, not as silent sockets — what genuinely remains to reach `MOD_q ∉ AC⁰[p]`.

  `no_computing_circuit` — **the separation shape (PROVED).**  Repackages `no_acp_circuit`: if `f` is hard (no
        degree-`d` Walsh polynomial agrees with `f` on more than `B` points), then *no* well-formed AC⁰[p] circuit
        of degree `≤ d` with `size·2^(n-t) + B < 2ⁿ` computes `f`.

  `hard_of_walshFn_univ` — **the boosting mechanism is real (PROVED).**  `boosting_surjection` directly supplies a
        hardness predicate for the full parity `walshFn univ`, with bound `B = 2ⁿ − 1`.  So the hardness side of
        `no_acp_circuit` is genuinely inhabited, not hypothetical.

## The three gaps to a non-vacuous `MOD_q ∉ AC⁰[p]` (honestly fenced)

`hard_of_walshFn_univ` + `no_computing_circuit` do **not** yet give a real separation.  Three concrete gaps remain,
each a genuine piece of mathematics, none of them faked here:

1. **Range / affine bridge — CLOSED.**  `cf p C` is `{0,1}`-valued; `walshFn univ` is `{−1,+1}`-valued, so
   `cf p C = walshFn univ` is *unsatisfiable* (instantiating with `f = walshFn univ` is vacuous).  This is now
   resolved by `hard_of_affine`: any `{0,1}` function `f` with `walshFn univ = 1 − 2·f` inherits the parity
   hardness at the *same* degree and bound (a degree-`d` approximator of `f` becomes one of `walshFn univ` via
   `aCoef ↦ δ_∅ − 2·aCoef`).  What remains to a *concrete* `{0,1}` target is the arithmetic identity
   `walshFn univ x = 1 − 2·(0/1 parity)` — a packaging detail, not a barrier.

2. **Sharp dimension bound — CLOSED.**  `hard_of_walshFn_univ` exposes only `B = 2ⁿ − 1` (because
   `boosting_surjection`'s stated conclusion is `< 2ⁿ`), which makes `no_computing_circuit`'s
   `size·2^(n-t) + B < 2ⁿ` force `size·2^(n-t) < 1`, impossible.  This is now resolved:
   `WalshSpan.boosting_surjection_sharp` (via `RazborovSmolensky.dimension_argument_sharp`) keeps the exact bound
   `|G| ≤ Σ_{i ≤ n/2+d} C(n,i)`, and `hard_of_walshFn_univ_sharp` is the corresponding hardness predicate — a
   genuinely non-vacuous `B` (`< 2ⁿ` when `n/2+d < n`).

3. **The `MOD_q` reduction (the barriered core).**  Boosting handles `walshFn univ` (the full product = parity).
   `MOD_q` (`q ≠ 2`) is *not* the full product; reducing its non-approximability to parity's is the genuine,
   `MOD_q`-specific Razborov–Smolensky lower bound — the part subject to natural-proofs/algebrization barriers.
   It is **not** attempted here.

So this file is a skeleton: a compiled separation shape and a real hardness mechanism, with the deep core (3) and
the two quantitative bridges (1), (2) named as the precise remaining obligations.
-/

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.WalshSpan

namespace PallLean.Paper93.DeepMath.PathB.ACC0.Circuit

variable {n : ℕ}

/-- **The separation shape (PROVED).**  If `f` is hard (no degree-`d` Walsh polynomial agrees with `f` on more than
`B` points), then no well-formed AC⁰[p] circuit of degree `≤ d` and bad-set budget `size·2^(n-t) + B < 2ⁿ` computes
`f`.  A direct repackaging of `no_acp_circuit` as a non-existence statement. -/
theorem no_computing_circuit {p t : ℕ} [Fact p.Prime] (ht : 1 ≤ t) (htn : t ≤ n) (h2 : (2 : ZMod p) ≠ 0)
    (d B : ℕ) (f : (Fin n → Bool) → ZMod p)
    (hard : ∀ (aCoef : Finset (Fin n) → ZMod p) (G : Finset (Fin n → Bool)),
              (∀ T, d < T.card → aCoef T = 0) → (∀ x ∈ G, f x = evalW aCoef x) → G.card ≤ B) :
    ¬ ∃ C : Circuit n,
      WF p C ∧ (t * (p - 1)) ^ depth C ≤ d ∧ size C * 2 ^ (n - t) + B < 2 ^ n ∧ (∀ x, cf p C x = f x) := by
  rintro ⟨C, hC, hdeg, hsmall, hCf⟩
  exact no_acp_circuit ht htn h2 d B f hard C hC hdeg hCf hsmall

/-- **The boosting mechanism is real (PROVED).**  `boosting_surjection` directly yields a hardness predicate for the
full parity `walshFn univ`: any degree-`d` Walsh polynomial agreeing with `walshFn univ` on `G` (with `n/2+d < n`)
has `|G| ≤ 2ⁿ − 1`.  This inhabits the `hard` hypothesis of `no_computing_circuit` — the mechanism is not
hypothetical.  (The bound `2ⁿ − 1` is the *weak* one; see gap 2.) -/
theorem hard_of_walshFn_univ {p : ℕ} [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (d : ℕ) (hmn : n / 2 + d < n) :
    ∀ (aCoef : Finset (Fin n) → ZMod p) (G : Finset (Fin n → Bool)),
      (∀ T, d < T.card → aCoef T = 0) →
      (∀ x ∈ G, walshFn Finset.univ x = evalW aCoef x) → G.card ≤ 2 ^ n - 1 := by
  intro aCoef G hsupp hagree
  have h := boosting_surjection h2 aCoef hsupp G (fun b hb => (hagree b hb).symm) hmn
  omega

/-- **Sharp hardness for parity — gap (2) CLOSED.**  `boosting_surjection_sharp` gives the exact dimension bound:
any degree-`d` Walsh polynomial agreeing with `walshFn univ` on `G` has `|G| ≤ Σ_{i ≤ n/2+d} C(n,i)`.  This is the
non-vacuous bound (`< 2ⁿ` when `n/2+d < n`), so plugged into `no_computing_circuit` with
`B = Σ_{i ≤ n/2+d} C(n,i)` the budget `size·2^(n-t) + B < 2ⁿ` is genuinely satisfiable.  Gaps (1) range/affine and
(3) the `MOD_q` reduction remain. -/
theorem hard_of_walshFn_univ_sharp {p : ℕ} [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (d : ℕ) :
    ∀ (aCoef : Finset (Fin n) → ZMod p) (G : Finset (Fin n → Bool)),
      (∀ T, d < T.card → aCoef T = 0) →
      (∀ x ∈ G, walshFn Finset.univ x = evalW aCoef x) →
      G.card ≤ ∑ i ∈ Finset.range (n / 2 + d + 1), n.choose i := by
  intro aCoef G hsupp hagree
  exact boosting_surjection_sharp h2 aCoef hsupp G (fun b hb => (hagree b hb).symm)

/-- **The affine `0/1 ↔ ±1` bridge — gap (1) CLOSED.**  If a `{−1,+1}` function `h` is hard and a `{0,1}` function
`f` is its affine image `h = 1 − 2·f`, then `f` is hard with the *same* degree `d` and bound `B`.  A degree-`d`
Walsh approximator `aCoef` of `f` on `G` is turned into a degree-`d` approximator `δ_∅ − 2·aCoef` of `h` (the
constant `1 = walshFn ∅` adds only the degree-`0` term `∅`), so `h`'s hardness applies.  This is what lets the
`{−1,+1}` parity lower bound (`hard_of_walshFn_univ_sharp`) be transported to a genuine `{0,1}`-valued target — the
range mismatch in `no_computing_circuit`'s `cf p C = f`. -/
theorem hard_of_affine {p : ℕ} [Fact p.Prime] (h f : (Fin n → Bool) → ZMod p)
    (haff : ∀ x, h x = 1 - 2 * f x) (d B : ℕ)
    (hh : ∀ (aCoef : Finset (Fin n) → ZMod p) (G : Finset (Fin n → Bool)),
            (∀ T, d < T.card → aCoef T = 0) → (∀ x ∈ G, h x = evalW aCoef x) → G.card ≤ B) :
    ∀ (aCoef : Finset (Fin n) → ZMod p) (G : Finset (Fin n → Bool)),
      (∀ T, d < T.card → aCoef T = 0) → (∀ x ∈ G, f x = evalW aCoef x) → G.card ≤ B := by
  intro aCoef G hsupp hagree
  refine hh (fun T => (if T = ∅ then 1 else 0) - 2 * aCoef T) G ?_ ?_
  · intro T hT
    have hT0 : T ≠ ∅ := fun h0 => by rw [h0] at hT; simp at hT
    show (if T = ∅ then (1 : ZMod p) else 0) - 2 * aCoef T = 0
    rw [if_neg hT0, hsupp T hT]; ring
  · intro x hx
    have key : evalW (fun T => (if T = ∅ then (1 : ZMod p) else 0) - 2 * aCoef T) x
             = 1 - 2 * evalW aCoef x := by
      simp only [evalW, sub_mul, Finset.sum_sub_distrib]
      congr 1
      · simp [ite_mul, Finset.sum_ite_eq', walshFn]
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun S _ => by ring)
    rw [haff x, hagree x hx, key]

/-- The `{0,1}` parity of a Boolean input, as an element of `𝔽_p`: the number of `true` bits, mod `2`. -/
noncomputable def boolParity {p : ℕ} (x : Fin n → Bool) : ZMod p :=
  (((∑ i, (x i).toNat) % 2 : ℕ) : ZMod p)

/-- `(-1)^k = 1 − 2·(k mod 2)` in `ZMod p`: the sign `(-1)^k` is `1`/`-1` according to the parity of `k`. -/
theorem neg_one_pow_eq {p : ℕ} (k : ℕ) : (-1 : ZMod p) ^ k = 1 - 2 * ((k % 2 : ℕ) : ZMod p) := by
  rw [neg_one_pow_eq_pow_mod_two]
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> rw [h] <;> push_cast <;> ring

/-- **Parity packaging identity.**  The full parity `walshFn univ` (`{−1,+1}`-valued) is the affine image of the
`{0,1}` parity `boolParity`: `walshFn univ x = 1 − 2·boolParity x`.  Each bit contributes `(-1)^{xᵢ}`, so the
product is `(-1)^(Σ xᵢ)`, whose sign is `1 − 2·(Σxᵢ mod 2)`. -/
theorem walshFn_univ_eq {p : ℕ} [Fact p.Prime] (x : Fin n → Bool) :
    walshFn (Finset.univ) x = 1 - 2 * boolParity (p := p) x := by
  have h1 : walshFn (Finset.univ : Finset (Fin n)) x = (-1 : ZMod p) ^ (∑ i, (x i).toNat) := by
    rw [walshFn, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl (fun i _ => by cases x i <;> simp)
  rw [h1, boolParity, neg_one_pow_eq]

/-- **The `{0,1}` parity is hard (gaps (1)+(2) assembled, parity case).**  Any degree-`d` Walsh polynomial agreeing
with `boolParity` on `G` has `|G| ≤ Σ_{i ≤ n/2+d} C(n,i)`: `hard_of_affine` applied to the packaging identity and
the sharp parity bound.  The `hard` hypothesis of `no_computing_circuit`, now for the genuine `{0,1}`-valued
`boolParity` (matching `cf p C = f`).  No `MOD_q` reduction is needed — parity *is* the full product. -/
theorem hard_of_boolParity {p : ℕ} [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (d : ℕ) :
    ∀ (aCoef : Finset (Fin n) → ZMod p) (G : Finset (Fin n → Bool)),
      (∀ T, d < T.card → aCoef T = 0) → (∀ x ∈ G, boolParity x = evalW aCoef x) →
      G.card ≤ ∑ i ∈ Finset.range (n / 2 + d + 1), n.choose i :=
  hard_of_affine (walshFn Finset.univ) boolParity (fun x => walshFn_univ_eq x) d _
    (hard_of_walshFn_univ_sharp h2 d)

/-- **Parity lower bound (the `q = 2` Razborov–Smolensky case, assembled).**  No well-formed AC⁰[p] circuit of
degree `≤ d` with bad-set budget `size·2^(n-t) + Σ_{i≤n/2+d} C(n,i) < 2ⁿ` computes the `{0,1}` parity.  This is a
*genuine, non-vacuous* lower bound: it combines the upper-bound machinery (`no_computing_circuit`) with the parity
hardness (`hard_of_boolParity`), with no barriered hypothesis — the parity case needs no `MOD_q` reduction.  (For
poly-size constant-depth circuits, choosing `t ≈ c·log n` makes the budget hold and `d = (t(p−1))^depth` polylog,
so the conclusion is non-trivial; that parameter instantiation is the only quantitative step left for the parity
separation.  General `MOD_q`, `q ≠ 2`, still needs the reduction of gap (3).) -/
theorem no_boolParity_circuit {p t : ℕ} [Fact p.Prime] (ht : 1 ≤ t) (htn : t ≤ n)
    (h2 : (2 : ZMod p) ≠ 0) (d : ℕ) :
    ¬ ∃ C : Circuit n, WF p C ∧ (t * (p - 1)) ^ depth C ≤ d ∧
        size C * 2 ^ (n - t) + (∑ i ∈ Finset.range (n / 2 + d + 1), n.choose i) < 2 ^ n ∧
        (∀ x, cf p C x = boolParity x) :=
  no_computing_circuit ht htn h2 d _ boolParity (hard_of_boolParity h2 d)

/-- **Central-binomial concentration (`√`-free).**  `(centralBinom n)² · (2n+1) ≤ 16ⁿ` — the integer form of
`centralBinom n ≤ 4ⁿ/√(2n+1)` (Stirling concentration), proved by induction with no real analysis: the recurrence
`(n+1)·centralBinom(n+1) = 2(2n+1)·centralBinom n` (`succ_mul_centralBinom_succ`) squared, against
`(2n+1)(2n+3) ≤ 4(n+1)²` (tight, off by one).  This is the `√n` upper bound `Mathlib`'s `Choose/Bounds` lacks. -/
theorem centralBinom_sq_le (n : ℕ) : (Nat.centralBinom n) ^ 2 * (2 * n + 1) ≤ 16 ^ n := by
  induction n with
  | zero => simp [Nat.centralBinom_zero]
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring]
    have hsm : (n + 1) * Nat.centralBinom (n + 1) = 2 * (2 * n + 1) * Nat.centralBinom n :=
      Nat.succ_mul_centralBinom_succ n
    have h1 : (n + 1) ^ 2 * Nat.centralBinom (n + 1) ^ 2
            = (2 * (2 * n + 1)) ^ 2 * Nat.centralBinom n ^ 2 := by
      rw [← mul_pow, hsm, mul_pow]
    have hkey : (n + 1) ^ 2 * (Nat.centralBinom (n + 1) ^ 2 * (2 * n + 3))
              ≤ (n + 1) ^ 2 * 16 ^ (n + 1) := by
      calc (n + 1) ^ 2 * (Nat.centralBinom (n + 1) ^ 2 * (2 * n + 3))
          = ((n + 1) ^ 2 * Nat.centralBinom (n + 1) ^ 2) * (2 * n + 3) := by ring
        _ = (2 * (2 * n + 1)) ^ 2 * Nat.centralBinom n ^ 2 * (2 * n + 3) := by rw [h1]
        _ = (4 * (2 * n + 1) * (2 * n + 3)) * (Nat.centralBinom n ^ 2 * (2 * n + 1)) := by ring
        _ ≤ (4 * (2 * n + 1) * (2 * n + 3)) * 16 ^ n := Nat.mul_le_mul_left _ ih
        _ ≤ (16 * (n + 1) ^ 2) * 16 ^ n := Nat.mul_le_mul_right _ (by nlinarith)
        _ = (n + 1) ^ 2 * 16 ^ (n + 1) := by rw [pow_succ]; ring
    exact Nat.le_of_mul_le_mul_left hkey (by positivity)

/-- `2·C(2m+1,m) = centralBinom(m+1)`: the two equal central entries of row `2m+2` sum to it (Pascal + symmetry). -/
theorem two_mul_choose_mid (m : ℕ) : 2 * (2 * m + 1).choose m = Nat.centralBinom (m + 1) := by
  have hsymm : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := by
    rw [← Nat.choose_symm (by omega : m + 1 ≤ 2 * m + 1)]; congr 1; omega
  rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (m + 1) = (2 * m + 1) + 1 by ring,
    Nat.choose_succ_succ, hsymm]; ring

/-- The central binomial term `C(2m+1,m)` satisfies the `√`-free concentration `C(2m+1,m)²·(2m+3) ≤ 4·16^m`
(from `centralBinom_sq_le (m+1)` and `two_mul_choose_mid`). -/
theorem choose_mid_sq_le (m : ℕ) : ((2 * m + 1).choose m) ^ 2 * (2 * m + 3) ≤ 4 * 16 ^ m := by
  have h := centralBinom_sq_le (m + 1)
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring, ← two_mul_choose_mid] at h
  have h2 : 4 * (((2 * m + 1).choose m) ^ 2 * (2 * m + 3)) ≤ 4 * (4 * 16 ^ m) := by
    calc 4 * (((2 * m + 1).choose m) ^ 2 * (2 * m + 3))
        = (2 * (2 * m + 1).choose m) ^ 2 * (2 * m + 3) := by ring
      _ ≤ 16 ^ (m + 1) := h
      _ = 4 * (4 * 16 ^ m) := by rw [pow_succ]; ring
  exact Nat.le_of_mul_le_mul_left h2 (by norm_num)

/-- **The central binomial term is small when `d` is `O(√m)`.**  If `4d² ≤ 2m+2`, then `d·C(2m+1,m) < 4^m`.  Square
both sides and use `choose_mid_sq_le`: `(d·C)²·(2m+3) ≤ 4d²·16^m ≤ (2m+2)·16^m < (2m+3)·16^m`, so `(d·C)² < 16^m`,
i.e. `d·C < 4^m`.  This discharges the central-binomial term of the parity budget for `d` up to `~√m` (so polylog
`d` works for large `m`) — *unconditionally*, the Stirling gap closed. -/
theorem choose_mid_lt {m d : ℕ} (hd : 4 * d ^ 2 ≤ 2 * m + 2) :
    d * (2 * m + 1).choose m < 4 ^ m := by
  have hCsq := choose_mid_sq_le m
  have h16 : (16 : ℕ) ^ m = (4 ^ m) ^ 2 := by
    rw [show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; congr 1; ring
  have h1 : (d * (2 * m + 1).choose m) ^ 2 < (4 ^ m) ^ 2 := by
    have hstep : (d * (2 * m + 1).choose m) ^ 2 * (2 * m + 3) < 16 ^ m * (2 * m + 3) := by
      calc (d * (2 * m + 1).choose m) ^ 2 * (2 * m + 3)
          = d ^ 2 * (((2 * m + 1).choose m) ^ 2 * (2 * m + 3)) := by ring
        _ ≤ d ^ 2 * (4 * 16 ^ m) := Nat.mul_le_mul_left _ hCsq
        _ = (4 * d ^ 2) * 16 ^ m := by ring
        _ ≤ (2 * m + 2) * 16 ^ m := Nat.mul_le_mul_right _ hd
        _ < (2 * m + 3) * 16 ^ m := mul_lt_mul_of_pos_right (by omega) (by positivity)
        _ = 16 ^ m * (2 * m + 3) := by ring
    rw [← h16]
    exact Nat.lt_of_mul_lt_mul_right hstep
  by_contra hcon
  push_neg at hcon
  exact absurd (Nat.pow_le_pow_left hcon 2) (Nat.not_le.mpr h1)

/-- **Quantitative dimension bound (odd `n = 2m+1`).**  The degree-`(m+d)` coefficient count splits as the exact
lower half plus the `d` middle terms: `Σ_{i≤m+d} C(2m+1,i) ≤ 4^m + d·C(2m+1,m)`.  The lower half is exactly `4^m`
(`sum_range_choose_halfway`), and each of the `d` extra terms is at most the central binomial `C(2m+1,m)`
(`choose_le_middle`).  This reduces the parity budget's binomial *sum* to a single central term. -/
theorem sum_choose_mid_le (m d : ℕ) :
    ∑ i ∈ Finset.range (m + d + 1), (2 * m + 1).choose i ≤ 4 ^ m + d * (2 * m + 1).choose m := by
  rw [show m + d + 1 = (m + 1) + d by ring, Finset.sum_range_add, Nat.sum_range_choose_halfway]
  refine Nat.add_le_add_left ?_ _
  calc ∑ i ∈ Finset.range d, (2 * m + 1).choose (m + 1 + i)
      ≤ ∑ _i ∈ Finset.range d, (2 * m + 1).choose m := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have h := Nat.choose_le_middle (m + 1 + i) (2 * m + 1)
        rwa [show (2 * m + 1) / 2 = m by omega] at h
    _ = d * (2 * m + 1).choose m := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **Parity lower bound with the central-binomial budget (odd `n`).**  Reformulates `no_boolParity_circuit` for
`n = 2m+1` with the *sharper* budget `size·2^(n-t) + d·C(2m+1,m) < 4^m` (= `2^(n-1)`), obtained by bounding the
binomial sum via `sum_choose_mid_le`.  The central-binomial term `d·C(2m+1,m)` is now provably `< 4^m` whenever
`4d² ≤ 2m+2` (`choose_mid_lt`, from the `√`-free concentration `centralBinom_sq_le`) — so for `d` up to `~√m`
(polylog `d` at large `m`) the only remaining hypothesis is the size term `size·2^(n-t)`, a clean
`t ≈ log(size)` choice.  The Stirling gap is closed. -/
theorem no_boolParity_circuit_odd {p t m : ℕ} [Fact p.Prime] (ht : 1 ≤ t) (htn : t ≤ 2 * m + 1)
    (h2 : (2 : ZMod p) ≠ 0) (d : ℕ) :
    ¬ ∃ C : Circuit (2 * m + 1), WF p C ∧ (t * (p - 1)) ^ depth C ≤ d ∧
        size C * 2 ^ (2 * m + 1 - t) + d * (2 * m + 1).choose m < 4 ^ m ∧
        (∀ x, cf p C x = boolParity x) := by
  rintro ⟨C, hC, hdeg, hbudget, hCf⟩
  refine no_boolParity_circuit (n := 2 * m + 1) ht htn h2 d ⟨C, hC, hdeg, ?_, hCf⟩
  rw [show (2 * m + 1) / 2 = m by omega]
  have hsum := sum_choose_mid_le m d
  have h4 : (2 : ℕ) ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul]; norm_num [mul_comm]
  omega

/-- **The unconditional parity (`q=2`) lower bound.**  For odd `n = 2m+1`: no well-formed AC⁰[p] circuit of depth
`≤ Δ` and size `≤ s` computes the `{0,1}` parity, provided the two *clean arithmetic parameter conditions*
`16·((t(p−1))^Δ)² ≤ 2m+2` (degree small — `(t(p−1))^Δ = O(√m)`) and `2·s·2^(n-t) ≤ 4^m` (size small —
`s ≤ 2^{t-2}`) hold.  No binomial sum, no central-binomial term, no analytic content survives in the hypotheses:
`choose_mid_lt` (the central-binomial concentration) discharges the degree term and the size term splits off
cleanly.  For poly-size constant-depth circuits, `t ≈ log s` satisfies both conditions at large `n`, so this is a
genuine, non-vacuous parity separation — the full `q=2` Razborov–Smolensky lower bound. -/
theorem no_parity_circuit {p t m Δ s : ℕ} [Fact p.Prime] (ht : 1 ≤ t) (htn : t ≤ 2 * m + 1)
    (h2 : (2 : ZMod p) ≠ 0) (hdeg : 16 * ((t * (p - 1)) ^ Δ) ^ 2 ≤ 2 * m + 2)
    (hsize : 2 * (s * 2 ^ (2 * m + 1 - t)) ≤ 4 ^ m) :
    ¬ ∃ C : Circuit (2 * m + 1),
      WF p C ∧ depth C ≤ Δ ∧ size C ≤ s ∧ (∀ x, cf p C x = boolParity x) := by
  rintro ⟨C, hC, hΔ, hs, hCf⟩
  have hb1 : 1 ≤ t * (p - 1) := by
    have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
    calc 1 = 1 * 1 := by ring
      _ ≤ t * (p - 1) := Nat.mul_le_mul ht (by omega)
  refine no_boolParity_circuit_odd ht htn h2 ((t * (p - 1)) ^ Δ) ⟨C, hC, ?_, ?_, hCf⟩
  · exact Nat.pow_le_pow_right hb1 hΔ
  · have hdC : 2 * ((t * (p - 1)) ^ Δ * (2 * m + 1).choose m) < 4 ^ m := by
      have hkey := choose_mid_lt (m := m) (d := 2 * (t * (p - 1)) ^ Δ)
        (by rw [show 4 * (2 * (t * (p - 1)) ^ Δ) ^ 2 = 16 * ((t * (p - 1)) ^ Δ) ^ 2 by ring]; exact hdeg)
      calc 2 * ((t * (p - 1)) ^ Δ * (2 * m + 1).choose m)
          = (2 * (t * (p - 1)) ^ Δ) * (2 * m + 1).choose m := by ring
        _ < 4 ^ m := hkey
    have hsz : 2 * (size C * 2 ^ (2 * m + 1 - t)) ≤ 4 ^ m :=
      le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hs)) hsize
    omega

end PallLean.Paper93.DeepMath.PathB.ACC0.Circuit

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.no_parity_circuit
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.centralBinom_sq_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.choose_mid_lt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.sum_choose_mid_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.no_boolParity_circuit_odd
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.walshFn_univ_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.hard_of_boolParity
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.no_boolParity_circuit
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.no_computing_circuit
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.hard_of_walshFn_univ
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.hard_of_walshFn_univ_sharp
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.hard_of_affine
