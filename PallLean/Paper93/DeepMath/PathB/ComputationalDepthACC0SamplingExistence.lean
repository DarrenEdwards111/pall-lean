import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FiniteChernoff

/-!
# The union-bound sampling existence theorem (closing the sampling gate, abstract form)

The finite Chernoff bound (`…ACC0FiniteChernoff`) gives, per input, geometric decay of the minority-good sample
fraction.  This file does the **union bound + pigeonhole** on top of it: if every input's good set has density `≥ 3/4`
and the population of inputs is small enough that `|X|·(7/8)^r < 1`, then a *single* sample of size `r` is
majority-correct at **every** input simultaneously.  This is the probabilistic-method existence argument, finite and
self-contained — the last conceptual gate of the Beigel–Tarui front half.

The statement is **abstract** — input set `X`, predictor pool `P`, good sets `Good : X → Finset P` — deliberately not
yet tied to parity forms.  The intended instantiation (next step) is:

* `X = Fin m → Bool` (the inputs),
* `P = ` the boosted `t`-tuples of parity forms (`…ACC0ProbabilisticBoost`),
* `Good x = ` the boosted forms correct on `x` (density `≥ 3/4` for `t ≥ 2`, by `boost_majority_nonzero`),

with `|X| = 2^m`, so `|X|·(7/8)^r < 1` holds for `r = O(m)` — giving a quasipolynomial-size form family
majority-correct everywhere, which is exactly the open clause of the socket `ApproxToExactSymmetricDecode`.

## What is proved (clean axioms, no `sorry`)

* `exists_sample_majority_correct_all` — given `∀ x, 3·|P| ≤ 4·|Good x|`, `0 < |P|`, and `|X|·(7/8)^r < 1`, there is a
  sample `σ : Fin r → P` with `∀ x, r < 2·#{i | σ i ∈ Good x}` (a strict majority of the `r` coordinates land in
  `Good x`, for every input `x`).

## Honest scope

This is the abstract sampling-existence theorem — the union bound + pigeonhole, proved from the finite Chernoff.  It
is **not** yet applied: instantiating `P` as the boosted parity-form tuples and discharging the density hypothesis
from `…ACC0ProbabilisticBoost` is the next step, after which the **basis bridge** (parity forms are low *poly*-degree
but high *monomial-`AND`*-degree vs `IsLowDegreeGate`) is the final piece of the Beigel–Tarui front half, **Wall 1**.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md` and `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SamplingExistence

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0FiniteChernoff

/-- **Union-bound sampling existence (proved).**  If every input `x ∈ X` has a good set `Good x ⊆ P` of density
`≥ 3/4` (`3·|P| ≤ 4·|Good x|`), the pool is nonempty (`0 < |P|`), and the inputs are few enough that
`|X|·(7/8)^r < 1`, then there is a single sample `σ : Fin r → P` that is **majority-correct at every input**:
`∀ x, r < 2·#{i | σ i ∈ Good x}`.  Probabilistic method, finite form: union the per-input minority-good sample sets
(`card_biUnion_le`), bound each by `(7|P|/8)^r` (`finite_chernoff_majority`), and conclude the bad samples are fewer
than all `|P|^r` samples — so a good one exists (pigeonhole). -/
theorem exists_sample_majority_correct_all {X P : Type*} [Fintype X] [Fintype P] [DecidableEq P]
    (r : ℕ) (Good : X → Finset P)
    (hgood : ∀ x, 3 * Fintype.card P ≤ 4 * (Good x).card)
    (hP : 0 < Fintype.card P)
    (hbound : (Fintype.card X : ℝ) * (7 / 8) ^ r < 1) :
    ∃ σ : Fin r → P, ∀ x, r < 2 * (Finset.univ.filter (fun i => σ i ∈ Good x)).card := by
  classical
  set B : Finset (Fin r → P) :=
    Finset.univ.filter (fun σ => ∃ x, 2 * (Finset.univ.filter (fun i => σ i ∈ Good x)).card ≤ r)
      with hB
  -- union bound: B ⊆ ⋃_x {minority-good at x}, so |B| ≤ ∑_x |minority-good at x|
  have hBsub : B ⊆ Finset.univ.biUnion (fun x =>
      Finset.univ.filter (fun σ : Fin r → P =>
        2 * (Finset.univ.filter (fun i => σ i ∈ Good x)).card ≤ r)) := by
    intro σ hσ
    rw [hB, Finset.mem_filter] at hσ
    obtain ⟨x, hx⟩ := hσ.2
    rw [Finset.mem_biUnion]
    exact ⟨x, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  have hcard1 : B.card
      ≤ ∑ x : X, (Finset.univ.filter (fun σ : Fin r → P =>
          2 * (Finset.univ.filter (fun i => σ i ∈ Good x)).card ≤ r)).card :=
    le_trans (Finset.card_le_card hBsub) Finset.card_biUnion_le
  -- real bound: |B| ≤ |X| · (7|P|/8)^r
  have hreal : (B.card : ℝ) ≤ (Fintype.card X : ℝ) * (7 / 8 * (Fintype.card P : ℝ)) ^ r := by
    calc (B.card : ℝ)
        ≤ ((∑ x : X, (Finset.univ.filter (fun σ : Fin r → P =>
            2 * (Finset.univ.filter (fun i => σ i ∈ Good x)).card ≤ r)).card : ℕ) : ℝ) := by
          exact_mod_cast hcard1
      _ = ∑ x : X, ((Finset.univ.filter (fun σ : Fin r → P =>
            2 * (Finset.univ.filter (fun i => σ i ∈ Good x)).card ≤ r)).card : ℝ) := by
          rw [Nat.cast_sum]
      _ ≤ ∑ _x : X, (7 / 8 * (Fintype.card P : ℝ)) ^ r :=
          Finset.sum_le_sum (fun x _ => finite_chernoff_majority r (Good x) (hgood x))
      _ = (Fintype.card X : ℝ) * (7 / 8 * (Fintype.card P : ℝ)) ^ r := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- |X| · (7|P|/8)^r < |P|^r
  have hPr : (0 : ℝ) < (Fintype.card P : ℝ) ^ r := pow_pos (by exact_mod_cast hP) r
  have hlt : (B.card : ℝ) < (Fintype.card P : ℝ) ^ r :=
    calc (B.card : ℝ)
        ≤ (Fintype.card X : ℝ) * (7 / 8 * (Fintype.card P : ℝ)) ^ r := hreal
      _ = (Fintype.card X : ℝ) * (7 / 8) ^ r * (Fintype.card P : ℝ) ^ r := by rw [mul_pow]; ring
      _ < 1 * (Fintype.card P : ℝ) ^ r := mul_lt_mul_of_pos_right hbound hPr
      _ = (Fintype.card P : ℝ) ^ r := one_mul _
  -- so |B| < |all samples|, hence a non-bad sample exists
  have hBlt : B.card < (Finset.univ : Finset (Fin r → P)).card := by
    have huniv : (Finset.univ : Finset (Fin r → P)).card = Fintype.card P ^ r := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    rw [huniv]
    have hcast : (B.card : ℝ) < ((Fintype.card P ^ r : ℕ) : ℝ) := by push_cast; exact hlt
    exact_mod_cast hcast
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (Fin r → P)) ⊆ B := by
    intro σ _
    rw [hB, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨x, hx⟩ := hcon σ
    exact ⟨x, hx⟩
  exact absurd (Finset.card_le_card hsub) (not_le.mpr hBlt)

end PallLean.Paper93.DeepMath.PathB.ACC0SamplingExistence

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SamplingExistence.exists_sample_majority_correct_all
