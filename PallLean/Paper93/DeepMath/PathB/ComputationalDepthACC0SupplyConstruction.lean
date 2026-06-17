import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ChernoffDecay

/-!
# The supply construction — a per-input `3/4` supply yields a tuple good at every input (proved)

Entries 209–211 proved the per-input concentration over a `3/4` supply (combinatorial Chernoff, fiber-count, decay).
The **last** residual of the BT depth-collapse is the *supply construction*: producing a finite family of approximants
that is `≥3/4`-correct **at every input**, then amplifying to a tuple correct-majority everywhere.

**Honest subtlety.**  The repo's RS approximation `acc0_approx_by_lowRankPredictor` gives only *global* `3/4` — one
function correct on `3/4` of inputs — which does **not** give a per-input `3/4` supply (a single function is wrong on a
fixed `1/4` of inputs, and copies of it share that error set).  The per-input property — that at *every* input a `3/4`
fraction of the family is correct — is the genuine probabilistic-polynomial-method content (per-point error `≤ 1/4` over
the random polynomial), *stronger* than the formalised global statement.  We take it as the named socket
`Uniform34` and prove the **full amplification assembly** on top of it.

## What is proved (clean axioms, no `sorry`)

* **`Uniform34 corr w`** — the per-input `3/4`-supply socket: at every input `x`, the family has `3w` approximants
  correct and `w` wrong (so `|α| = 4w`, `≥3/4` correct at every input).  This is the RS per-point guarantee.
* **`exists_good_tuple`** — the assembly (PROVED): a uniform `3/4` supply (with `w ≥ 1`), at `k = 2j` with `j ≥ 3n+1`,
  yields a tuple `g : Fin (2j) → α` whose **majority is correct at every input** (`¬ #correct ≤ j`, i.e. `j < #correct`)
  — via entry-210's `bad_tuple_count_le` (per-input bound), entry-211's `decay_full` (`2^n·M < #tuples`), a union
  bound over inputs, and the probabilistic-method pigeonhole.

## Honest scope

This proves the **amplification assembly** completely — that a per-input `3/4` supply yields a tuple correct-majority at
every input — in pure `Nat`/`Finset` counting, combining entries 209–211 with a union bound and pigeonhole.  This is the
amplified `MajorityGoodFamily` witness the NW reconstruction needs (entry 206 then makes its majority an *exact*
representation).  What remains the named socket is **`Uniform34`** itself: the *existence* of a per-input `3/4` supply —
the genuine RS per-point error bound (per-point `≤ 1/4` over the random polynomial), stronger than the repo's *global*
`3/4` `acc0_approx_by_lowRankPredictor`.  This proves everything downstream of the supply, not the supply's existence
(which is the irreducible RS analytic input).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SupplyConstruction

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0FiberCount (bad_tuple_count_le)
open PallLean.Paper93.DeepMath.PathB.ACC0ChernoffDecay (decay_full)

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

/-- **The per-input `3/4`-supply socket.**  At every input `x`, the approximant family `α` has `3w` correct and `w`
wrong (`corr x a` = "approximant `a` correct at input `x`"), so `≥3/4` correct at every input and `|α| = 4w`.  This is
the genuine RS per-point guarantee (per-point error `≤ 1/4` over the random polynomial) — stronger than the repo's
*global* `3/4`.  Stated, not proved. -/
def Uniform34 (corr : (Fin n → Bool) → α → Bool) (w : ℕ) : Prop :=
  ∀ x, (Finset.univ.filter (fun a => corr x a = true)).card = 3 * w
    ∧ (Finset.univ.filter (fun a => corr x a = false)).card = w

/-- **The supply amplification assembly (PROVED).**  A uniform `3/4` supply (`Uniform34 corr w`, `w ≥ 1`), at `k = 2j`
with `j ≥ 3n+1`, yields a tuple `g : Fin (2j) → α` whose majority is correct at *every* input (`j < #{i | corr x (g i)}`,
i.e. `¬ #correct ≤ j`).  Proof: the bad tuples (bad at some input) number `≤ ∑_x #{bad at x}` (union bound) `≤ 2^n · M`
(entry-210 `bad_tuple_count_le` per input, `M = 2^{2j}·(3w)^j·w^j` uniform) `< #tuples = (4w)^{2j}` (entry-211
`decay_full`); since fewer than all tuples are bad, a tuple good at every input exists (pigeonhole). -/
theorem exists_good_tuple (corr : (Fin n → Bool) → α → Bool) (j w : ℕ)
    (hu : Uniform34 corr w) (hw : 1 ≤ w) (hj : 3 * n + 1 ≤ j) :
    ∃ g : Fin (2 * j) → α, ∀ x,
      ¬ (Finset.univ.filter (fun i => corr x (g i) = true)).card ≤ j := by
  set S := Finset.univ.filter (fun g : Fin (2 * j) → α =>
      ∃ x, (Finset.univ.filter (fun i => corr x (g i) = true)).card ≤ j) with hS
  have hcard : Fintype.card α = 4 * w := by
    obtain ⟨ht, hf⟩ := hu (Classical.arbitrary _)
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α))
      (p := fun a => corr (Classical.arbitrary _) a = true)
    rw [Finset.card_univ, ht] at this
    rw [show (Finset.univ.filter (fun a => ¬ corr (Classical.arbitrary _) a = true))
          = (Finset.univ.filter (fun a => corr (Classical.arbitrary _) a = false)) from by
        apply Finset.filter_congr; intro a _; simp [Bool.not_eq_true], hf] at this
    omega
  have hunion : S.card ≤ ∑ x : Fin n → Bool,
      (Finset.univ.filter (fun g : Fin (2 * j) → α =>
        (Finset.univ.filter (fun i => corr x (g i) = true)).card ≤ j)).card := by
    refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
    intro g hg
    rw [hS, Finset.mem_filter] at hg
    obtain ⟨x, hx⟩ := hg.2
    exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, Finset.mem_filter.mpr ⟨Finset.mem_univ g, hx⟩⟩
  have hperinput : ∀ x, (Finset.univ.filter (fun g : Fin (2 * j) → α =>
        (Finset.univ.filter (fun i => corr x (g i) = true)).card ≤ j)).card
      ≤ 2 ^ (2 * j) * (3 * w) ^ j * w ^ (2 * j - j) := by
    intro x
    obtain ⟨ht, hf⟩ := hu x
    have := bad_tuple_count_le (k := 2 * j) (fun a => corr x a) (m := j)
      (by rw [ht, hf]; omega) (by omega)
    rw [ht, hf, ← mul_assoc] at this
    exact this
  have hsum : ∑ x : Fin n → Bool,
        (Finset.univ.filter (fun g : Fin (2 * j) → α =>
          (Finset.univ.filter (fun i => corr x (g i) = true)).card ≤ j)).card
      ≤ 2 ^ n * (2 ^ (2 * j) * (3 * w) ^ j * w ^ (2 * j - j)) := by
    calc ∑ x : Fin n → Bool, _
        ≤ ∑ _x : Fin n → Bool, (2 ^ (2 * j) * (3 * w) ^ j * w ^ (2 * j - j)) :=
          Finset.sum_le_sum (fun x _ => hperinput x)
      _ = 2 ^ n * (2 ^ (2 * j) * (3 * w) ^ j * w ^ (2 * j - j)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin, smul_eq_mul]
  have hlt : S.card < Fintype.card (Fin (2 * j) → α) := by
    have hdec := decay_full n j w hw hj
    have htuples : Fintype.card (Fin (2 * j) → α) = (3 * w + w) ^ (2 * j) := by
      rw [Fintype.card_fun, Fintype.card_fin, hcard]; congr 1; omega
    rw [htuples]
    exact lt_of_le_of_lt (le_trans hunion hsum) hdec
  by_contra hcon
  push_neg at hcon
  have hSall : S = Finset.univ := by
    rw [hS]; exact Finset.filter_true_of_mem (fun g _ => hcon g)
  rw [hSall, Finset.card_univ] at hlt
  exact lt_irrefl _ hlt

end PallLean.Paper93.DeepMath.PathB.ACC0SupplyConstruction

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SupplyConstruction.exists_good_tuple
