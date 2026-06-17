import Mathlib

/-!
# The `3/4`→exact amplification — the majority-vote exactness skeleton (proved)

Entry 205 reduced the span→`SYM∘AND` bridge to the single residual `ExactCountModPRep` — that the circuit has an *exact*
count-mod-`p` representation — whose deep content is the **`3/4`→exact amplification**: combine several independent
`3/4`-approximants into something exact.  This file proves the genuinely-provable **deterministic skeleton** of that
amplification: **majority-vote exactness** — if at every input *more than half* of a family of approximants is correct,
their majority vote agrees with the target *everywhere* (is exact).

The probabilistic content (that such a pointwise-majority-correct family *exists* — independence + Chernoff driving the
per-input error below `2^{-n}` so a union bound over the `2^n` inputs leaves none bad) needs a probability framework and
remains the named socket.  What is *deterministic and provable* is the skeleton: given the family, majority is exact.

## What is proved (clean axioms, no `sorry`)

* **`majBool`** / **`count_compl`** / **`majBool_eq_of_count`** — Boolean majority and its pointwise correctness: if
  more than half of `v : Fin k → Bool` equal `b`, then `majBool v = b`.
* **`MajVote`** / **`maj_exact`** — the majority vote of a family `g : Fin k → (… → Bool)` and the exactness theorem: if
  at every input `x` more than half the `g i` are correct (`k < 2·#{i | g i x = f x}`), then `MajVote g = f` exactly.
* **`MajorityGoodFamily`** — the residual probabilistic socket: a pointwise-majority-correct family of approximants
  exists.
* **`exact_from_majorityGood`** — the amplification: a pointwise-majority-correct family yields an exact majority-vote
  representation of `f`.

## Honest scope

This proves the **deterministic majority-vote skeleton** of the `3/4`→exact amplification: that a pointwise-majority-
correct family of approximants has an *exact* majority — genuine Boolean/counting arithmetic (`count_compl` +
`majBool_eq_of_count`), complete.  What remains the named socket, **`MajorityGoodFamily`**, is the *probabilistic*
content: that such a family exists — the independence/Chernoff amplification driving per-input error below `2^{-n}`,
union-bounded over the `2^n` inputs — which needs a probability framework absent here.  A second residual (not addressed
here) is that the majority vote of `SYM∘AND`s is itself representable as a single `SYM∘AND` — the `MAJ∘SYM∘AND`
collapse.  This proves the amplification's logical skeleton, not the probabilistic existence or the `MAJ∘SYM∘AND`
closure.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0Amplification

open Finset

variable {n : ℕ}

/-- **Boolean majority vote.**  `majBool v = true` iff strictly more than half of the `k` votes are `true`. -/
def majBool {k : ℕ} (v : Fin k → Bool) : Bool :=
  decide (k < 2 * (Finset.univ.filter (fun i => v i = true)).card)

/-- **The vote counts partition (proved).**  `#{i | v i = true} + #{i | v i = false} = k`. -/
theorem count_compl {k : ℕ} (v : Fin k → Bool) :
    (Finset.univ.filter (fun i => v i = true)).card
      + (Finset.univ.filter (fun i => v i = false)).card = k := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
    (p := fun i => v i = true)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have he : (Finset.univ.filter (fun i => v i = false)).card
      = (Finset.univ.filter (fun i => ¬ v i = true)).card := by
    congr 1
    apply Finset.filter_congr
    intro i _
    simp [Bool.not_eq_true]
  rw [he]; exact h

/-- **Pointwise majority correctness (proved).**  If strictly more than half of the votes `v` equal `b`
(`k < 2·#{i | v i = b}`), then the majority vote is `b`. -/
theorem majBool_eq_of_count {k : ℕ} (v : Fin k → Bool) (b : Bool)
    (hb : k < 2 * (Finset.univ.filter (fun i => v i = b)).card) : majBool v = b := by
  have hc := count_compl v
  cases b with
  | true => unfold majBool; simp only [decide_eq_true_eq]; exact hb
  | false => unfold majBool; simp only [decide_eq_false_iff_not, not_lt]; omega

/-- **The majority vote of a family of approximants.**  `MajVote g x` is the Boolean majority of the votes
`g i x`. -/
def MajVote {k : ℕ} (g : Fin k → ((Fin n → Bool) → Bool)) : (Fin n → Bool) → Bool :=
  fun x => majBool (fun i => g i x)

/-- **Majority-vote exactness (PROVED) — the amplification skeleton.**  If at every input `x` strictly more than half of
the family `g` is correct (`k < 2·#{i | g i x = f x}`), then the majority vote agrees with `f` *everywhere*:
`MajVote g = f`. -/
theorem maj_exact {k : ℕ} (g : Fin k → ((Fin n → Bool) → Bool)) (f : (Fin n → Bool) → Bool)
    (hgood : ∀ x, k < 2 * (Finset.univ.filter (fun i => g i x = f x)).card) :
    MajVote g = f := by
  funext x
  exact majBool_eq_of_count (fun i => g i x) (f x) (hgood x)

/-- **The residual probabilistic socket.**  A pointwise-majority-correct family of approximants for `f` exists: some
finite family `g` with, at *every* input, more than half correct.  Producing this is the independence/Chernoff
amplification (per-input error below `2^{-n}`, union-bounded over the `2^n` inputs).  Stated, not proved. -/
def MajorityGoodFamily (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (k : ℕ) (g : Fin k → ((Fin n → Bool) → Bool)),
    ∀ x, k < 2 * (Finset.univ.filter (fun i => g i x = f x)).card

/-- **Amplification to exact (PROVED).**  A pointwise-majority-correct family yields an *exact* majority-vote
representation of `f`: `∃ k g, MajVote g = f`. -/
theorem exact_from_majorityGood (f : (Fin n → Bool) → Bool) (hf : MajorityGoodFamily f) :
    ∃ (k : ℕ) (g : Fin k → ((Fin n → Bool) → Bool)), MajVote g = f := by
  obtain ⟨k, g, hgood⟩ := hf
  exact ⟨k, g, maj_exact g f hgood⟩

end PallLean.Paper93.DeepMath.PathB.ACC0Amplification

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Amplification.majBool_eq_of_count
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Amplification.maj_exact
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Amplification.exact_from_majorityGood
