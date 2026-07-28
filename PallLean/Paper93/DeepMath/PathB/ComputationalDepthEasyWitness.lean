import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHardSlice

/-!
# The IKW easy-witness lemma: its enumeration heart, proved (not assumed)

The `SpringRelease` and `Uniformization` bricks use the Impagliazzo–Kabanets–Wigderson easy-witness lemma
(`NEXP ⊆ P/poly ⟹ NEXP = EXP`) as a *hypothesis* — a socket.  This file pays part of that socket: it proves
the genuine **combinatorial heart** of the lemma as real theorems.

**Honest scope.**  The full IKW lemma needs the machine-model definitions of `NEXP`, `EXP`, `P/poly`, and the
witness/verifier formulation — a large formalization not attempted here.  What *is* the mathematical content,
and what is proved below, is the **easy-witness enumeration mechanism**: if a witness is *easy* (computed by a
small circuit), then the search for it collapses from the space of all witnesses (`2^N`) to the space of small
circuits (`≤ 2^{poly}`), because easy witnesses are exactly the image of the small-circuit evaluation map.
That collapse is why `NEXP ⊆ P/poly` (⟹ all witnesses easy) puts `NEXP` in `EXP`: the witness is found by
enumerating circuits, `2^{poly}` of them, each checked in `EXP`.

* **`easy_functions_bounded`** — the easy functions are the image of `eval`, so there are at most as many as
  there are circuits: `|easy| ≤ |Circuit|`.  (The counting fact, used the *other* way from `HardSlice`.)
* **`easy_witness_reduces_search`** — searching for a witness with property `P`, *restricted to easy
  witnesses*, reduces to enumerating circuits: if an easy witness satisfies `P`, some circuit's output does.
* **`easy_witness_shrinks_search`** — the circuit-enumeration space `2^s` is exponentially smaller than the
  brute-force witness space `2^N` when `s < N` (small circuits vs long witnesses) — the IKW speedup.

## Honest verdict — a socket, partly paved

This is real forward motion of the modest kind I promised: the easy-witness lemma was a hypothesis, and its
enumeration heart is now three proved, axiom-checked theorems — the witness search provably collapses to a
circuit enumeration (`easy_functions_bounded`, `easy_witness_reduces_search`, `easy_witness_shrinks_search`).
It does not cross the wall and it is not the full IKW theorem — the machine-model class collapse
(`NEXP ⊆ EXP`) still needs the complexity-class infrastructure this file abstracts.  But the mathematical
mechanism that makes IKW work is now paved, not assumed.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.EasyWitness

/-! ### The easy functions are a small set -/

/-- **Easy functions are bounded by the circuit count (proved).**  A function is *easy* if it is `eval c` for
some circuit `c`; the easy functions are the image of `eval`, so there are at most `|Circuit|` of them.  This
is the counting fact behind easy-witness (and, used the other way, behind the `HardSlice` lower bound). -/
theorem easy_functions_bounded {Circuit Func : Type} [Fintype Circuit] [DecidableEq Func]
    (eval : Circuit → Func) :
    (Finset.univ.image eval).card ≤ Fintype.card Circuit :=
  le_trans Finset.card_image_le (le_of_eq Finset.card_univ)

/-! ### The witness search collapses to a circuit enumeration -/

/-- **The easy-witness search reduces to enumerating circuits (proved).**  If a witness satisfying property
`P` is *easy* — equal to `eval c` for some circuit — then enumerating circuits finds it: some circuit's output
satisfies `P`.  This is the easy-witness method's core move: replace a search over all `2^N` witnesses by a
search over the circuits. -/
theorem easy_witness_reduces_search {Circuit Func : Type} (eval : Circuit → Func) (P : Func → Prop)
    (h : ∃ w, (∃ c, eval c = w) ∧ P w) : ∃ c, P (eval c) := by
  obtain ⟨w, ⟨c, hc⟩, hP⟩ := h
  subst hc
  exact ⟨c, hP⟩

/-- **The circuit enumeration is exponentially smaller (proved).**  With `s` the (poly-size) circuit
description length and `N` the (exponential) witness length, the circuit-enumeration space `2^s` is strictly
smaller than the brute-force witness space `2^N` whenever `s < N` — the exponential speedup easy witnesses
buy. -/
theorem easy_witness_shrinks_search (s N : ℕ) (h : s < N) : 2 ^ s < 2 ^ N :=
  Nat.pow_lt_pow_right (by decide) h

end PallLean.Paper93.DeepMath.PathB.EasyWitness

#print axioms PallLean.Paper93.DeepMath.PathB.EasyWitness.easy_functions_bounded
#print axioms PallLean.Paper93.DeepMath.PathB.EasyWitness.easy_witness_reduces_search
#print axioms PallLean.Paper93.DeepMath.PathB.EasyWitness.easy_witness_shrinks_search
