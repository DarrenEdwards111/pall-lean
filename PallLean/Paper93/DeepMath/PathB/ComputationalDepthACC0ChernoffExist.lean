import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Amplification

/-!
# Chernoff amplification existence — the probabilistic method + union bound (proved), concentration socketed

Entry 206 left **`MajorityGoodFamily`** (a pointwise-majority-correct family of approximants exists) as the residual
probabilistic socket of the `3/4`→exact amplification.  This file discharges it from a *single* concentration socket,
proving everything else: the **probabilistic method** (positive count ⇒ existence) and the **union bound**.

The argument.  Over the finite space of `k`-tuples of approximants `Fin k → ((Fin n → Bool) → Bool)`, call a tuple *bad*
if at *some* input `x` the majority errs (`errsAt`).  (i) **Probabilistic method** (`exists_good_of_bad_lt`): if fewer
than *all* tuples are bad, a tuple that is good *everywhere* exists — pure pigeonhole.  (ii) **Union bound**
(`union_bound`): the bad tuples number at most `∑_x #{tuples bad at x}`.  (iii) **Sum bound**: if each per-input bad
count is `≤ M`, the sum is `≤ #inputs · M`.  So if `#inputs · M < #tuples` (the per-input concentration), then
`#bad < #tuples` and a good family exists.

The single remaining socket, **`ChernoffPerInput`**, is exactly the per-input concentration: at each input the bad
tuples are a `< 2^{-n}` fraction (`#inputs · M < #tuples`, i.e. `M < #tuples / 2^n`).  This is the genuine **Chernoff
bound** — for `k` *independent* approximants each correct w.p. `≥ 3/4`, the chance the majority errs at a fixed `x` is
`exp(-Ω(k))`, below `2^{-n}` for `k = Ω(n)` — and it needs the independence/concentration machinery (a probability
framework) absent here.

## What is proved (clean axioms, no `sorry`)

* **`exists_good_of_bad_lt`** — the probabilistic method: `#{bad tuples} < #tuples → ∃` a tuple good at every input.
* **`union_bound`** — `#{bad tuples} ≤ ∑_x #{tuples bad at x}` (`Finset.card_biUnion_le`).
* **`ChernoffPerInput`** — the per-input concentration socket: `∃ M`, each `#{tuples bad at x} ≤ M` and
  `#inputs · M < #tuples`.
* **`majorityGoodFamily_of_chernoff`** — discharges the entry-206 `MajorityGoodFamily` socket from `ChernoffPerInput`,
  via the sum bound, the union bound, and the probabilistic method.

## Honest scope

This proves the **probabilistic-method logic** (positive count ⇒ existence — pigeonhole) and the **union bound** + sum
bound completely, discharging entry-206's `MajorityGoodFamily` from the single per-input concentration socket
`ChernoffPerInput`.  That socket *is* the genuine **Chernoff concentration** (bad tuples a `< 2^{-n}` fraction at each
input, from the independence of the `k` approximants), which needs a probability/independence framework absent from this
development.  This proves the existence *scaffolding* (everything except the concentration), not the concentration
inequality itself.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ChernoffExist

open Finset
open scoped Classical
open PallLean.Paper93.DeepMath.PathB.ACC0Amplification (MajorityGoodFamily)

variable {n : ℕ}

/-- Boolean functions on `n` bits. -/
abbrev Fn (n : ℕ) := (Fin n → Bool) → Bool

/-- **A tuple errs at `x`**: at input `x`, at most half of the `k` approximants are correct (the majority errs). -/
def errsAt {k : ℕ} (f : Fn n) (g : Fin k → Fn n) (x : Fin n → Bool) : Prop :=
  2 * (Finset.univ.filter (fun i => g i x = f x)).card ≤ k

/-- **The probabilistic method (PROVED).**  If fewer than *all* `k`-tuples are bad (bad at some input), then a tuple
that is good at *every* input exists — pure pigeonhole: if all tuples were bad, the bad filter would be all of `univ`,
contradicting the strict count inequality. -/
theorem exists_good_of_bad_lt {k : ℕ} (f : Fn n)
    (h : (Finset.univ.filter (fun g : Fin k → Fn n => ∃ x, errsAt f g x)).card
        < Fintype.card (Fin k → Fn n)) :
    ∃ g : Fin k → Fn n, ∀ x, ¬ errsAt f g x := by
  by_contra hcon
  push_neg at hcon
  have hall : (Finset.univ.filter (fun g : Fin k → Fn n => ∃ x, errsAt f g x)) = Finset.univ :=
    Finset.filter_true_of_mem (fun g _ => hcon g)
  rw [hall, Finset.card_univ] at h
  exact lt_irrefl _ h

/-- **The union bound (PROVED).**  The bad tuples (bad at *some* input) number at most the sum over inputs of the tuples
bad at that input — `Finset.card_biUnion_le`. -/
theorem union_bound {k : ℕ} (f : Fn n) :
    (Finset.univ.filter (fun g : Fin k → Fn n => ∃ x, errsAt f g x)).card
      ≤ ∑ x : Fin n → Bool, (Finset.univ.filter (fun g : Fin k → Fn n => errsAt f g x)).card := by
  refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
  intro g hg
  rw [Finset.mem_filter] at hg
  obtain ⟨x, hx⟩ := hg.2
  exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, Finset.mem_filter.mpr ⟨Finset.mem_univ g, hx⟩⟩

/-- **The per-input concentration socket.**  There is a bound `M` on the number of `k`-tuples that err at each fixed
input, with `#inputs · M < #tuples` — i.e. at each input the bad tuples are a `< 2^{-n}` fraction.  This is the genuine
Chernoff bound (independence of the `k` approximants drives per-input majority-error probability below `2^{-n}`).
Stated, not proved. -/
def ChernoffPerInput (f : Fn n) (k : ℕ) : Prop :=
  ∃ M, (∀ x, (Finset.univ.filter (fun g : Fin k → Fn n => errsAt f g x)).card ≤ M)
    ∧ Fintype.card (Fin n → Bool) * M < Fintype.card (Fin k → Fn n)

/-- **Discharging the entry-206 `MajorityGoodFamily` socket (PROVED).**  From the per-input concentration
`ChernoffPerInput`: the sum bound (`∑_x #{bad at x} ≤ #inputs · M`) and the union bound give `#{bad tuples} < #tuples`,
so the probabilistic method yields a tuple good at every input — exactly a pointwise-majority-correct family. -/
theorem majorityGoodFamily_of_chernoff (f : Fn n) (k : ℕ) (hc : ChernoffPerInput f k) :
    MajorityGoodFamily f := by
  obtain ⟨M, hM, hlt⟩ := hc
  have hsum : ∑ x : Fin n → Bool, (Finset.univ.filter (fun g : Fin k → Fn n => errsAt f g x)).card
      ≤ Fintype.card (Fin n → Bool) * M := by
    calc ∑ x : Fin n → Bool, (Finset.univ.filter (fun g : Fin k → Fn n => errsAt f g x)).card
        ≤ ∑ _x : Fin n → Bool, M := Finset.sum_le_sum (fun x _ => hM x)
      _ = Fintype.card (Fin n → Bool) * M := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hbad : (Finset.univ.filter (fun g : Fin k → Fn n => ∃ x, errsAt f g x)).card
      < Fintype.card (Fin k → Fn n) :=
    lt_of_le_of_lt (le_trans (union_bound f) hsum) hlt
  obtain ⟨g, hg⟩ := exists_good_of_bad_lt f hbad
  exact ⟨k, g, fun x => not_le.mp (hg x)⟩

end PallLean.Paper93.DeepMath.PathB.ACC0ChernoffExist

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ChernoffExist.exists_good_of_bad_lt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ChernoffExist.union_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ChernoffExist.majorityGoodFamily_of_chernoff
