import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNaturalProofsBarrier

/-!
# The worst-case → average-case mechanism (toward resolving MCSP)

Hirahara's programme aims to prove that `MCSP` being **worst-case hard** makes it **average-case
hard** — the seam where a P-vs-NP-relevant lower bound might register.  His actual reduction is
*non-black-box* and research-scale.  This file builds the **classical mechanism** such reductions
must realize: a **random self-reduction** turns an average-case solver into a worst-case one, by the
union bound.

The mechanism (Lipton's technique): if computing `f x` for *any* `x` reduces to evaluating `f` at `k`
points that are each **individually uniform** (a random self-reduction), then an average-case solver
`A` — correct on all but a `δ`-fraction — solves `f x` for **every** `x` with error `≤ k·δ` over its
coins.  Majority vote over coins then computes `f` in the worst case.

* **`RandSelfRed`** — a random self-reduction at a fixed input `x`: `k` bijective (uniform) query
  maps `R ≃ X` on the coins, and a recovery of `f x` from `f` at the queries;
* **`worstCase_from_avgCase` (proved)** — for **every** `x`, the reduction driven by `A` errs on at
  most `k·|Bad(A)|` coins.  So worst-case-solving `f` reduces to average-case-solving it — the
  worst→average reduction, mechanism-level.

**Honest scope.**  This is the *mechanism*, proved with real content (bijection counting + union
bound), for any function that **has** a random self-reduction (e.g. the permanent, low-degree
polynomials).  **`MCSP` is not known to be randomly self-reducible** in this simple way — that is
precisely why Hirahara's worst→average reduction for `MCSP` is *non-black-box* and hard, and it is
**not** built here.  So this delivers the engine such a reduction runs on, and names the missing
part (an MCSP-specific self-reduction / Hirahara's amplification) exactly.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.WorstToAverage

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The **bad set** of an average-case solver `A` for `f`: the inputs where it errs. -/
def badSet (f A : X → Bool) : Finset X := Finset.univ.filter (fun y => A y ≠ f y)

/-- A **random self-reduction** of `f` at a fixed input `x`, over coin space `R`: `k` query maps,
each a bijection `R ≃ X` (so each query is uniform in `X` as the coins range over `R`), together with
a recovery that reconstructs `f x` from the values of `f` at the queries — for every coin. -/
structure RandSelfRed (R : Type*) [Fintype R] (f : X → Bool) (x : X) (k : ℕ) where
  /-- The `k` query maps; each is a bijection of the coin space onto the inputs (uniform queries). -/
  q : Fin k → (R ≃ X)
  /-- Reconstruct `f x` from the `k` queried values of `f`. -/
  recover : (Fin k → Bool) → Bool
  /-- Correctness of the self-reduction: for every coin, recovery reproduces `f x`. -/
  correct : ∀ r : R, recover (fun i => f (q i r)) = f x

/-- **The worst-case → average-case reduction (proved).**  Driving the random self-reduction with an
average-case solver `A`, the number of coins on which it returns the *wrong* value of `f x` is at
most `k · |Bad(A)|` — **for every input `x`**.  Hence if `A` errs on a `δ`-fraction, the reduction
errs on `≤ k·δ` of coins on *every* `x`; majority vote over coins then solves `f` in the worst case.
This is the classical mechanism a worst→average reduction realizes. -/
theorem worstCase_from_avgCase {R : Type*} [Fintype R] [DecidableEq R]
    {f : X → Bool} {x : X} {k : ℕ} (S : RandSelfRed R f x k) (A : X → Bool) :
    (Finset.univ.filter (fun r : R => S.recover (fun i => A (S.q i r)) ≠ f x)).card
      ≤ k * (badSet f A).card := by
  have hsub : (Finset.univ.filter (fun r : R => S.recover (fun i => A (S.q i r)) ≠ f x))
      ⊆ Finset.univ.filter (fun r : R => ∃ i, S.q i r ∈ badSet f A) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    by_contra hno
    push_neg at hno
    apply hr
    have heq : (fun i => A (S.q i r)) = (fun i => f (S.q i r)) := by
      funext i
      have hi := hno i
      simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, not_not] at hi
      exact hi
    rw [heq]; exact S.correct r
  have hunion : (Finset.univ.filter (fun r : R => ∃ i, S.q i r ∈ badSet f A))
      ⊆ (Finset.univ : Finset (Fin k)).biUnion
          (fun i => Finset.univ.filter (fun r : R => S.q i r ∈ badSet f A)) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    obtain ⟨i, hi⟩ := hr
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      Finset.mem_filter.mpr ⟨Finset.mem_univ r, hi⟩⟩
  have hcard_i : ∀ i, (Finset.univ.filter (fun r : R => S.q i r ∈ badSet f A)).card
      = (badSet f A).card := by
    intro i
    have hset : (Finset.univ.filter (fun r : R => S.q i r ∈ badSet f A))
        = (badSet f A).map (S.q i).symm.toEmbedding := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Equiv.coe_toEmbedding]
      constructor
      · intro hr; exact ⟨S.q i r, hr, Equiv.symm_apply_apply _ _⟩
      · rintro ⟨y, hy, hyr⟩; rw [← hyr]; simpa using hy
    rw [hset, Finset.card_map]
  calc (Finset.univ.filter (fun r : R => S.recover (fun i => A (S.q i r)) ≠ f x)).card
      ≤ (Finset.univ.filter (fun r : R => ∃ i, S.q i r ∈ badSet f A)).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.univ : Finset (Fin k)).biUnion
          (fun i => Finset.univ.filter (fun r : R => S.q i r ∈ badSet f A))).card :=
        Finset.card_le_card hunion
    _ ≤ ∑ i : Fin k, (Finset.univ.filter (fun r : R => S.q i r ∈ badSet f A)).card :=
        Finset.card_biUnion_le
    _ = ∑ _i : Fin k, (badSet f A).card := by simp_rw [hcard_i]
    _ = k * (badSet f A).card := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end PallLean.Paper93.DeepMath.PathB.WorstToAverage

#print axioms PallLean.Paper93.DeepMath.PathB.WorstToAverage.worstCase_from_avgCase
