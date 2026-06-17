import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CarryRealization

/-!
# Degree of exact count realisation — a formal obstruction (conservative)

Entries 239/240 eliminated two suspects: the carry observer's *state count* is quasipoly (239) and the *decode* is
realisable over a field (240).  The wall is now precisely **exact low-degree count computation for composite/carry
observers**.  This file proves the genuine **degree obstruction** that explains *why* the field route of entry 240 is
too expensive: a faithful field indicator over `N+1` count-points needs **degree ≥ N** — linear in the faithful range,
not low-degree.

⚠️ **This is a formal obstruction for the single-field route, not a separation.**  It shows the naive field decode
costs degree `Θ(N)`.  Whether *carry/digit layers* can realise the exact composite count at *low* degree while keeping
quasipoly size is the open crossing question (entry-238 `CarryRefinementCrossing`); this file does not resolve it.

## What is proved (clean axioms, no `sorry`)

* **`indicator_natDegree_ge`** (PROVED) — over a field, a nonzero polynomial vanishing at `N` distinct points has
  `natDegree ≥ N` (it has `≥ N` roots; `Polynomial.card_roots'`).  The degree lower bound.
* **`faithful_decode_degree_ge`** (PROVED) — the obstruction: a field decode that is nonzero at one point and `0` at
  `N` other distinct count-points needs `natDegree ≥ N`.  This is why entry-240's field decode on `{0,…,N}` is
  expensive.
* **`pointIndicator_natDegree_ge`** (PROVED) — the entry-240 prime point-indicator has `natDegree ≥ p-1` (it vanishes
  on the `p-1` other field elements); combined with the entry-240 upper bound `≤ p-1`, its degree is **exactly `p-1`**
  = (field size) − 1.
* **`prime_indicator_natDegree_eq`** (PROVED) — tightness: `(pointIndicator p b).natDegree = p - 1`.

## Degree vs faithful range (the finding)

A faithful field decode distinguishing counts `{0,…,N}` needs the field to have `≥ N+1` elements (entry 239), and a
single-count indicator among them has degree exactly `N` (lower bound here + upper bound entry 240).  So the field-route
degree is `Θ(N)` — **linear in the count range**, hence *not* low-degree (low-degree means `polylog`/`n^{o(1)}`).  This
formally confirms the field readout cannot be the crossing.

## The open question (named, not resolved)

**Can p-adic carry/digit layers realise the exact composite count at degree `≪ N` (low-degree) while keeping quasipoly
size?**  The lower bound here is *per single-field polynomial*; a layered (multi-polynomial, base-`p` digit) realisation
might evade it.  If yes → a possible `ACC⁰[m]` crossing; if no → a formal degree obstruction.  Either is the entry-238
`CarryRefinementCrossing` socket; this file does not settle it.

## Honest scope

The proved content is a **degree lower bound** (`indicator_natDegree_ge` / `faithful_decode_degree_ge`) and the
tightness of the prime field indicator (`prime_indicator_natDegree_eq`), establishing that the single-field exact-count
decode costs degree `Θ(N)` — too expensive to be low-degree.  This is a genuine formal obstruction *for the field route*.
It does **not** prove a lower bound against *layered* carry realisations (the open crossing), nor is it `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

open Polynomial Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0CompositeCountDegree

/-- **Degree lower bound (PROVED).**  Over a field, a nonzero polynomial vanishing at `N` distinct points has
`natDegree ≥ N`: the `N` points are distinct roots, and `#roots ≤ natDegree` (`Polynomial.card_roots'`). -/
theorem indicator_natDegree_ge {F : Type*} [Field F] [DecidableEq F] (P : F[X]) (S : Finset F)
    (hP : P ≠ 0) (hroots : ∀ a ∈ S, P.eval a = 0) : S.card ≤ P.natDegree := by
  have hsub : S ⊆ P.roots.toFinset := by
    intro a ha
    rw [Multiset.mem_toFinset, mem_roots hP]
    exact hroots a ha
  calc S.card ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card P.roots := P.roots.toFinset_card_le
    _ ≤ P.natDegree := P.card_roots'

/-- **The faithful-decode degree obstruction (PROVED).**  A field decode `P` that is nonzero at one point `b` and `0`
at `N` other distinct count-points `S` needs `natDegree ≥ N = S.card`.  This is why the entry-240 field decode on
`{0,…,N}` costs degree `Θ(N)`. -/
theorem faithful_decode_degree_ge {F : Type*} [Field F] [DecidableEq F] (P : F[X]) (b : F)
    (S : Finset F) (hb : P.eval b ≠ 0) (hzero : ∀ a ∈ S, P.eval a = 0) : S.card ≤ P.natDegree := by
  have hP : P ≠ 0 := by intro h; rw [h] at hb; simp at hb
  exact indicator_natDegree_ge P S hP hzero

variable (p : ℕ) [Fact p.Prime]

/-- **The prime point-indicator has degree `≥ p-1` (PROVED).**  `pointIndicator p b` vanishes on the `p-1` field
elements `≠ b`, so its degree is at least `p-1`. -/
theorem pointIndicator_natDegree_ge (b : ZMod p) :
    p - 1 ≤ (ACC0CarryRealization.pointIndicator p b).natDegree := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have hP : ACC0CarryRealization.pointIndicator p b ≠ 0 := by
    intro h
    have he := ACC0CarryRealization.pointIndicator_eval p b b
    rw [h] at he; simp at he
  have hcard : (Finset.univ \ {b} : Finset (ZMod p)).card = p - 1 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_singleton, Finset.card_univ, ZMod.card]
  rw [← hcard]
  refine indicator_natDegree_ge _ _ hP ?_
  intro a ha
  rw [Finset.mem_sdiff, Finset.mem_singleton] at ha
  rw [ACC0CarryRealization.pointIndicator_eval, if_neg ha.2]

/-- **Tightness (PROVED): the prime field indicator has degree exactly `p-1` = (field size) − 1.**  Lower bound here,
upper bound entry-240 `pointIndicator_natDegree_le`.  Since faithfulness needs field `≥ N+1` (entry 239), the field
decode degree is `Θ(N)` — *not* low-degree. -/
theorem prime_indicator_natDegree_eq (b : ZMod p) :
    (ACC0CarryRealization.pointIndicator p b).natDegree = p - 1 :=
  le_antisymm (ACC0CarryRealization.pointIndicator_natDegree_le p b) (pointIndicator_natDegree_ge p b)

end PallLean.Paper93.DeepMath.PathB.ACC0CompositeCountDegree

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeCountDegree.indicator_natDegree_ge
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeCountDegree.faithful_decode_degree_ge
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeCountDegree.prime_indicator_natDegree_eq
