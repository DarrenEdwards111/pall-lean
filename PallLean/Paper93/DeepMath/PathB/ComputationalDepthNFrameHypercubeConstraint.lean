import Mathlib

/-!
# The N‑Frame hypercube constraint / SPDP bridge — assumption vs derivation, made explicit

This formalizes, exactly, the bridge underlying N‑Frame book1's "SPDP event horizon": that a polynomial‑time
observer cannot realize a high‑SPDP‑rank (high‑dimensional) decision view, so SAT — which requires one — has no
polynomial‑time observer.  The point of this file is to **separate the proved part from the assumed part**, so
it is unambiguous whether the framework *derives* the bridge or *assumes* it.

The three ingredients, each an explicit hypothesis:

* **`bridge` (`PObserverLowSPDP`)** — *polynomial time ⇒ low SPDP rank of the decision view*.  This is the
  N‑Frame "P‑observer confined to low SPDP / low dimension" principle.
* **`correct_needs_rank`** — a correct SAT decider's view has SPDP rank `≥` what SAT requires (decision‑relevance
  of the rank).
* **`sat_high`** — SAT's required SPDP rank is super‑polynomial (the SPDP lower bound, book1 pillar 4).

## Proved (clean axioms, no `sorry`)

* `p_ne_np_from_bridge` — `bridge + correct_needs_rank + sat_high ⇒` no polynomial‑time observer decides SAT.
  A clean conditional: the separation *follows* from the three hypotheses.
* `restricted_bridge_gives_separation` — the same with the bridge restricted to a structural class `K`
  (`inK`): for observers in `K`, `restrictedBridge` is *provable*, giving "no polynomial‑time SAT decider in
  `K`."

## Honest status — which ingredient is which

* `restrictedBridge` (poly‑time `∧` in `K` ⇒ low SPDP) is **provable for concrete `K`** — bounded crossing
  sequences, low CEW, bounded holonomy, low‑raveling action, bounded‑locality.  That is the whole proved corpus
  (the calibrations and the non‑collapse ladder), and `restricted_bridge_gives_separation` is its shape.
* The **global `bridge`** — *every* polynomial‑time observer has low SPDP rank — is **`P ≠ NP`‑hard, and false
  in the naïve model**: a poly‑time decider may use poly *space*, hence a high‑dimensional (high‑boundary)
  view, so it is *not* confined to low SPDP rank by time alone (cf. the brute‑force escape / time→action
  obstruction).  N‑Frame book1 asserts this bridge as a *principle* (low SPDP rank "encodes" P‑reach); it does
  **not derive it** from computation mechanics.  So in the book the bridge is an **assumption equivalent in
  strength to the separation**.
* `sat_high` is the SPDP lower bound.  For the diagonal `χ_φ` family it is **disproved** (the rank can be far
  below `#SAT`); for the permanent it is a genuine *depth‑3/4 arithmetic‑circuit* bound that does **not** reach
  `P/poly`, and the SPDP method is barriered short of `VP` vs `VNP`.

So this file makes the split unambiguous: **the restricted bridge is a theorem (and the corpus proves
instances); the global bridge is an assumption equal in strength to `P ≠ NP`; and `sat_high` is the open (and,
for the diagonal route, false) SPDP lower bound.**  The N‑Frame hypercube constraint is real geometry and a
faithful reframing — but the load‑bearing implication is assumed, not derived.  No `P ≠ NP` claim.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameHypercube

variable {M : Type*}

/-- A `poly(n)` upper bound: dominated by some `C·n^k + C`. -/
def PolyBounded (f : ℕ → ℕ) : Prop := ∃ C k, ∀ n, f n ≤ C * n ^ k + C

/-- A super‑polynomial lower bound: exceeds every `C·n^k + C`. -/
def SuperPoly (g : ℕ → ℕ) : Prop := ∀ C k, ∃ n, C * n ^ k + C < g n

/-- **The `PObserverLowSPDP` bridge.**  Every polynomial‑time observer `M` has a decision view whose SPDP rank
is polynomially bounded in `n`.  This is the N‑Frame "P confined to low SPDP / low dimension" principle —
assumed, not derived, and `P ≠ NP`‑hard. -/
def PObserverLowSPDP (PolyTime : M → Prop) (spdp : M → ℕ → ℕ) : Prop :=
  ∀ m, PolyTime m → PolyBounded (spdp m)

/-- **Separation from the bridge (proved conditional).**  Given the bridge (`PObserverLowSPDP`: poly‑time ⇒
low SPDP), the decision‑relevance of rank (`correct_needs_rank`: a correct SAT decider's view has SPDP `≥` the
SAT requirement), and the SPDP lower bound (`sat_high`: SAT's required rank is super‑poly), no observer is both
polynomial‑time and a correct SAT decider — `P ≠ NP` in observer form. -/
theorem p_ne_np_from_bridge (PolyTime decidesSAT : M → Prop) (spdp : M → ℕ → ℕ) (satRank : ℕ → ℕ)
    (bridge : PObserverLowSPDP PolyTime spdp)
    (correct_needs_rank : ∀ m, decidesSAT m → ∀ n, satRank n ≤ spdp m n)
    (sat_high : SuperPoly satRank) :
    ∀ m, ¬ (PolyTime m ∧ decidesSAT m) := by
  rintro m ⟨hp, hd⟩
  obtain ⟨C, k, hbound⟩ := bridge m hp
  obtain ⟨n, hn⟩ := sat_high C k
  have h1 := correct_needs_rank m hd n
  have h2 := hbound n
  omega

/-- **Restricted bridge ⇒ restricted separation (proved).**  If the bridge is only assumed for observers in a
structural class `K` (`restrictedBridge`: poly‑time `∧ inK ⇒` low SPDP — *provable* for concrete `K`), the
conclusion is restricted to `K`: no polynomial‑time SAT decider lies in `K`.  This is the shape of every proved
lower bound in the corpus; the global statement drops `inK` and needs the `P ≠ NP`‑hard global bridge. -/
theorem restricted_bridge_gives_separation (PolyTime decidesSAT inK : M → Prop)
    (spdp : M → ℕ → ℕ) (satRank : ℕ → ℕ)
    (restrictedBridge : ∀ m, PolyTime m → inK m → PolyBounded (spdp m))
    (correct_needs_rank : ∀ m, decidesSAT m → ∀ n, satRank n ≤ spdp m n)
    (sat_high : SuperPoly satRank) :
    ∀ m, ¬ (PolyTime m ∧ inK m ∧ decidesSAT m) := by
  rintro m ⟨hp, hk, hd⟩
  obtain ⟨C, k, hbound⟩ := restrictedBridge m hp hk
  obtain ⟨n, hn⟩ := sat_high C k
  have h1 := correct_needs_rank m hd n
  have h2 := hbound n
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameHypercube

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameHypercube.p_ne_np_from_bridge
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameHypercube.restricted_bridge_gives_separation
