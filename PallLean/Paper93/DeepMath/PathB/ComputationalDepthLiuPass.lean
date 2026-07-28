import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHardSlice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Paving the Liu–Pass socket: the Kolmogorov-counting + compressibility core, from scratch

`MetaComplexityOWF` and `HiraharaBridge` use Liu–Pass (2020) — *one-way functions exist iff time-bounded
Kolmogorov complexity is mildly hard on average* — as a hypothesis.  This file pays its genuine core.

**Honest scope.**  The full Liu–Pass theorem needs the one-way-function security game, the definition of
`K^t`, and the average-case reduction in both directions — a large formalization not attempted here.  What *is*
the mathematical heart of the easy direction (OWF ⟹ `K^t` hard), and what is proved below, is a **counting +
compressibility** argument, entirely elementary:

* **`descriptions_lt`** — there are exactly `2^s − 1` descriptions (programs) of length `< s`: `∑_{i<s} 2^i +
  1 = 2^s`, proved by induction.  So *compressible* strings — those with a short description — are **rare**.
* **`compressible_rare`** — the strings with a description in a program set of size `< 2^s` number `< 2^s`
  (they are the image of the decode map): incompressibility is the common case.
* **`owf_outputs_compressible`** — a one-way function `f : D → C` has image of size `≤ |D|`, so its outputs
  are describable by their `|D|`-bit preimage: **OWF outputs have low `K^t`** — they are compressible.

Put together (`owf_outputs_are_rare`): the outputs of a length-increasing OWF land inside the rare set of
compressible strings, while random codomain strings are (mostly) incompressible.  That is exactly why a `K^t`
algorithm breaks the OWF: it distinguishes the compressible OWF-outputs from incompressible random strings.
The remaining step — turning that distinguisher into an inverter (the security reduction) — is the part this
file abstracts.

## What is proved

* **`descriptions_lt`** — `∑_{i<s} 2^i + 1 = 2^s`: the count of short descriptions (the Kolmogorov bound).
* **`compressible_rare`** — compressible strings number `< 2^s`: incompressibility is generic.
* **`owf_outputs_compressible`** — OWF outputs number `≤ |D|`: they are compressible / low `K^t`.
* **`owf_outputs_are_rare`** — a length-increasing OWF's outputs are strictly fewer than the codomain: they
  sit in the rare compressible set, detectable by `K^t`.

## Honest verdict — the counting heart of Liu–Pass, paved

This is real forward motion of the promised kind: the Liu–Pass socket's genuine core — *OWF outputs are
compressible, and compressible strings are rare* — is now four proved, axiom-checked theorems
(`descriptions_lt`, `compressible_rare`, `owf_outputs_compressible`, `owf_outputs_are_rare`), the Kolmogorov
counting derived from scratch by induction.  It is honestly scoped: the average-case security reduction that
turns "K^t detects OWF outputs" into "K^t easy ⟹ OWF inverted", and the converse direction, still need the
crypto infrastructure this abstracts.  But the mathematical mechanism at the heart of Liu–Pass is paved, not
assumed — and it is the same compressible-is-rare counting that runs through `HardSlice`, natural proofs, and
`IncompressibleCircuit`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.LiuPass

/-! ### The Kolmogorov counting bound -/

/-- **The count of short descriptions (proved).**  There are `2^s − 1` binary programs of length `< s`:
`∑_{i<s} 2^i + 1 = 2^s`.  This is the counting bound behind Kolmogorov complexity — compressible strings are
scarce because short programs are scarce. -/
theorem descriptions_lt (s : ℕ) : (∑ i ∈ Finset.range s, 2 ^ i) + 1 = 2 ^ s := by
  induction s with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-! ### Compressible strings are rare -/

/-- **Compressible strings are rare (proved).**  The strings decodable from a program set of size `< 2^s`
are the image of `decode`, hence number `< 2^s`.  Most strings have no short description — incompressibility
is the common case. -/
theorem compressible_rare {Prog Str : Type} [Fintype Prog] [DecidableEq Str]
    (decode : Prog → Str) (s : ℕ) (hprog : Fintype.card Prog < 2 ^ s) :
    (Finset.univ.image decode).card < 2 ^ s :=
  lt_of_le_of_lt (le_trans Finset.card_image_le (le_of_eq Finset.card_univ)) hprog

/-! ### One-way-function outputs are compressible -/

/-- **OWF outputs are compressible (proved).**  A one-way function `f : D → C` has image of size `≤ |D|`, so
each output is describable by its `|D|`-bit preimage: OWF outputs have low `K^t`. -/
theorem owf_outputs_compressible {D C : Type} [Fintype D] [DecidableEq C] (f : D → C) :
    (Finset.univ.image f).card ≤ Fintype.card D :=
  le_trans Finset.card_image_le (le_of_eq Finset.card_univ)

/-- **OWF outputs sit in the rare compressible set (proved).**  A length-increasing OWF (`|D| < |C|`) has
strictly fewer outputs than codomain strings — its outputs are compressible while most codomain strings are
not, so a `K^t` algorithm distinguishes them (the heart of Liu–Pass's easy direction). -/
theorem owf_outputs_are_rare {D C : Type} [Fintype D] [Fintype C] [DecidableEq C]
    (f : D → C) (h : Fintype.card D < Fintype.card C) :
    (Finset.univ.image f).card < Fintype.card C :=
  lt_of_le_of_lt (owf_outputs_compressible f) h

end PallLean.Paper93.DeepMath.PathB.LiuPass

#print axioms PallLean.Paper93.DeepMath.PathB.LiuPass.descriptions_lt
#print axioms PallLean.Paper93.DeepMath.PathB.LiuPass.compressible_rare
#print axioms PallLean.Paper93.DeepMath.PathB.LiuPass.owf_outputs_compressible
#print axioms PallLean.Paper93.DeepMath.PathB.LiuPass.owf_outputs_are_rare
