import Mathlib.Algebra.Polynomial.Roots

/-!
# Schwartz–Zippel (univariate base case) = randomized `PIT`, the side we *have*

The hardness↔randomness escape (`HardnessRandomness`) reduces a circuit lower bound to **derandomizing
`PIT`** (polynomial identity testing).  We *have* a randomized `PIT` — it is exactly Schwartz–Zippel.
This file builds its univariate base case unconditionally from Mathlib's root bound `card_roots'`
(a nonzero degree-`d` polynomial has `≤ d` roots), and states it as randomized-`PIT` correctness.

* **`sz_roots_le_natDegree` (proved)** — a nonzero polynomial `p` has at most `natDegree p` roots in
  *any* finite set `S`: `#{a ∈ S | p(a) = 0} ≤ deg p`.  (So a random `a ∈ S` is a root with
  probability `≤ deg p / |S|` — the Schwartz–Zippel bound.)
* **`sz_exists_nonroot` (proved)** — if `deg p < |S|`, a nonzero `p` has a witness `a ∈ S` with
  `p(a) ≠ 0`.  This is **randomized `PIT`**: evaluating at a random point of a large-enough set
  detects non-vanishing with high probability, so `p ≢ 0` is caught.

This is the *randomized* half of the hardness↔randomness picture — the algorithm we already possess.
**The open, hard half is *derandomizing* it** (making `PIT` deterministic), which by
`hardness_randomness_bridge` would force a circuit lower bound; that (and the full multivariate S–Z,
by induction on variables) is the next brick.  Nothing here is `P ≠ NP`; it is the foundation the
derandomization program stands on, proved unconditionally.
-/

namespace PallLean.Paper93.DeepMath.PathB.SchwartzZippel

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Schwartz–Zippel, univariate (proved).**  A nonzero polynomial `p` over a field has at most
`natDegree p` roots inside any finite set `S`.  Equivalently, a uniformly random point of `S` is a
root of `p` with probability at most `deg p / |S|`. -/
theorem sz_roots_le_natDegree (p : F[X]) (hp : p ≠ 0) (S : Finset F) :
    (S.filter (fun a => p.eval a = 0)).card ≤ p.natDegree := by
  have hsub : S.filter (fun a => p.eval a = 0) ⊆ p.roots.toFinset := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Multiset.mem_toFinset, mem_roots']
    exact ⟨hp, ha.2⟩
  calc (S.filter (fun a => p.eval a = 0)).card
      ≤ p.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := card_roots' p

/-- **Randomized `PIT` detects a nonzero polynomial (proved).**  If the evaluation set `S` is larger
than the degree, a nonzero `p` has an explicit witness `a ∈ S` with `p(a) ≠ 0`.  So testing `p` at a
random point of `S` catches its non-vanishing — the correctness of randomized identity testing. -/
theorem sz_exists_nonroot (p : F[X]) (hp : p ≠ 0) (S : Finset F)
    (hdeg : p.natDegree < S.card) : ∃ a ∈ S, p.eval a ≠ 0 := by
  by_contra hno
  push_neg at hno
  have hall : S.filter (fun a => p.eval a = 0) = S :=
    Finset.filter_true_of_mem (fun a ha => hno a ha)
  have hle := sz_roots_le_natDegree p hp S
  rw [hall] at hle
  omega

/-- **The identity-testing contrapositive (proved).**  If a nonzero-degree-bounded polynomial vanishes
on *every* point of a set larger than its degree, it is the zero polynomial — the soundness of the
random test at full strength (no false "identically zero"). -/
theorem sz_zero_of_vanishes (p : F[X]) (S : Finset F) (hdeg : p.natDegree < S.card)
    (hvanish : ∀ a ∈ S, p.eval a = 0) : p = 0 := by
  by_contra hp
  obtain ⟨a, ha, hne⟩ := sz_exists_nonroot p hp S hdeg
  exact hne (hvanish a ha)

end PallLean.Paper93.DeepMath.PathB.SchwartzZippel

#print axioms PallLean.Paper93.DeepMath.PathB.SchwartzZippel.sz_roots_le_natDegree
#print axioms PallLean.Paper93.DeepMath.PathB.SchwartzZippel.sz_exists_nonroot
#print axioms PallLean.Paper93.DeepMath.PathB.SchwartzZippel.sz_zero_of_vanishes
