import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverBlockDecompositionMin

/-!
# Structured-class `min` regimes, unified: forcing families, and address-block robustness for `hardF`

The observer method proves `min`-over-decompositions lower bounds exactly on **forcing families**: a
decomposition class in which *every* member is independently forced above a threshold, so the `min` is too.
The two proved regimes — resolution proof-space (Tseitin, §8) and address-block continuation (`hardF`, §11) —
are both instances.  This file extracts the pattern as an abstraction and uses it to **expand** the
address-block result: not just the full family, but *every nonempty subfamily* of address blocks still has
super-logarithmic `min` — the decomposition-chooser cannot escape within the structure.

## The abstraction

A `ForcingFamily` is a finite set of decompositions with a per-decomposition `boundary` and a `threshold`
that every member meets (`forced`).  Then `threshold ≤ minBoundary` (`threshold_le_min`), and — the robust
form — `threshold ≤` the `min` over *any* nonempty subfamily (`subfamily_min_ge`).

## Expanded `hardF` result

`hardFAddressFamily` packages the `m` address blocks of `hardF` as a forcing family with threshold `2^b−1`.
Then:

* `hardF_family_min_ge` — `min` over all address blocks `≥ 2^b−1`;
* `hardF_subfamily_min_ge` — `min` over **any nonempty subfamily** of address blocks `≥ 2^b−1` (the
  structure-preserving robustness the frontier note asked for: the chooser restricted to address-respecting
  decompositions cannot get below the threshold);
* `hardF_subfamily_min_superlog` — and `2^b−1` is super-logarithmic, so every such subfamily's `min` exceeds
  `c·log₂(input)` for the balanced family.

## Honest scope

"Structure-preserving" here means **address-respecting**: each decomposition reads (at least) the address bits
of a gadget.  Arbitrary *coarsening* is **not** covered — residual count is not monotone (reading *all*
variables leaves a single residual), so a decomposition that dissolves the block structure can be cheap.  So
this expands the `min` quantifier over a genuinely larger but still *structured* class; the all-decompositions
case stays open (`= CookLevinFrontierHyp`).  Proof-space (Tseitin) is the other instance of the same
abstraction (its forcing family is *all refutations*, threshold `c·t`).
-/

namespace PallLean.Paper93.DeepMath.PathB.ForcingFamily

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.NecHard
open PallLean.Paper93.DeepMath.PathB.ObserverNeciporuk
open PallLean.Paper93.DeepMath.PathB.BlockDecompositionMin
open scoped BigOperators

/-- A **forcing family**: a finite decomposition class in which every member's boundary meets a common
`threshold`.  The structured-class regimes where the observer method proves `min` lower bounds. -/
structure ForcingFamily (ι : Type*) where
  /-- The decompositions. -/
  decompositions : Finset ι
  /-- The family is nonempty. -/
  nonempty : decompositions.Nonempty
  /-- The per-decomposition observer boundary. -/
  boundary : ι → ℕ
  /-- The forced threshold. -/
  threshold : ℕ
  /-- Every decomposition is forced above the threshold. -/
  forced : ∀ i ∈ decompositions, threshold ≤ boundary i

variable {ι : Type*}

/-- The `min` boundary over the family. -/
noncomputable def ForcingFamily.minBoundary (F : ForcingFamily ι) : ℕ :=
  F.decompositions.inf' F.nonempty F.boundary

/-- **The threshold bounds the `min`** — the basic forcing-family theorem. -/
theorem ForcingFamily.threshold_le_min (F : ForcingFamily ι) : F.threshold ≤ F.minBoundary := by
  unfold ForcingFamily.minBoundary
  apply Finset.le_inf'
  exact F.forced

/-- **Robustness: every nonempty subfamily still meets the threshold.**  The decomposition-chooser cannot
escape the threshold by restricting to any sub-collection of the family. -/
theorem ForcingFamily.subfamily_min_ge (F : ForcingFamily ι) {D : Finset ι}
    (hsub : D ⊆ F.decompositions) (hD : D.Nonempty) :
    F.threshold ≤ D.inf' hD F.boundary := by
  apply Finset.le_inf'
  intro i hi
  exact F.forced i (hsub hi)

/-- **Super-logarithmic `min`**: if the threshold exceeds `c·log₂ N`, so does the `min`. -/
theorem ForcingFamily.min_superlog (F : ForcingFamily ι) {c N : ℕ}
    (h : c * Nat.log 2 N < F.threshold) : c * Nat.log 2 N < F.minBoundary :=
  lt_of_lt_of_le h F.threshold_le_min

/-! ## Instantiation: the `hardF` address-block forcing family -/

variable {b m : ℕ}

/-- The `m` address blocks of `hardF`, packaged as a forcing family with threshold `2^b − 1`. -/
noncomputable def hardFAddressFamily (hm : 0 < m) (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = hardF x) : ForcingFamily (Fin m) where
  decompositions := Finset.univ
  nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  boundary := fun k => formulaBlockBoundary (blockS k) F
  threshold := Dsize b - 1
  forced := fun k _ => hardF_blockBoundary_ge k F hF

/-- `min` over all address blocks is `≥ 2^b − 1`. -/
theorem hardF_family_min_ge (hm : 0 < m) (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = hardF x) :
    Dsize b - 1 ≤ (hardFAddressFamily hm F hF).minBoundary :=
  (hardFAddressFamily hm F hF).threshold_le_min

/-- **The expanded result.**  `min` over **any nonempty subfamily** of address blocks is `≥ 2^b − 1`: the
chooser, restricted to address-respecting decompositions, cannot get below the threshold. -/
theorem hardF_subfamily_min_ge (hm : 0 < m) (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = hardF x) {D : Finset (Fin m)} (hD : D.Nonempty) :
    Dsize b - 1 ≤ D.inf' hD (fun k => formulaBlockBoundary (blockS k) F) :=
  (hardFAddressFamily hm F hF).subfamily_min_ge (Finset.subset_univ D) hD

/-- **Super-logarithmic over every subfamily.**  For every constant `c`, some balanced family member has
every-subfamily `min` boundary exceeding `c·log₂(input size)`.  (Threshold `2^b−1` is super-log by
`minBlockBoundary_superlog`; the subfamily bound carries it.) -/
theorem hardF_subfamily_min_superlog (c : ℕ) :
    ∃ b : ℕ, 5 ≤ b ∧ ∀ (m : ℕ) (hm : 0 < m) (F : BFormula (nn b m))
      (_ : ∀ x, BFormula.eval F x = hardF x) {D : Finset (Fin m)} (hD : D.Nonempty),
      c * Nat.log 2 (nn b (2 ^ b)) < D.inf' hD (fun k => formulaBlockBoundary (blockS k) F) := by
  obtain ⟨b, hb5, hsl⟩ := minBlockBoundary_superlog c
  exact ⟨b, hb5, fun m hm F hF D hD => lt_of_lt_of_le hsl (hardF_subfamily_min_ge hm F hF hD)⟩

end PallLean.Paper93.DeepMath.PathB.ForcingFamily

#print axioms PallLean.Paper93.DeepMath.PathB.ForcingFamily.ForcingFamily.subfamily_min_ge
#print axioms PallLean.Paper93.DeepMath.PathB.ForcingFamily.hardF_subfamily_min_ge
#print axioms PallLean.Paper93.DeepMath.PathB.ForcingFamily.hardF_subfamily_min_superlog
