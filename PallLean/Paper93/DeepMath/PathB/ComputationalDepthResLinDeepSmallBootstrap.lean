import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResLinLiftedTseitinInterface

/-!
# Deep-small `Res(⊕)` refutations: unconditional bootstrap and the depth-reduction barrier

The bounded-depth lifting theorem does not by itself exclude arbitrarily deep small dags.  This file
extracts the strongest unconditional consequence available from the checked dag structure:

* every exact dependency level is at most its line index;
* hence every checked dag has `depth ≤ size`;
* a lower bound `sizeFloor` for depth at most `depthCap` therefore yields the unrestricted lower
  bound `min sizeFloor (depthCap + 1)`.

For the 2025 lifted-Tseitin regime, `sizeFloor` is exponential while `depthCap` is nearly quadratic,
so this cashes out only the nearly-quadratic floor.  Crossing that floor requires eliminating the
deep-small case with formula-specific mathematics.

A generic efficient depth reducer cannot be the missing theorem.  Supercritical tradeoffs now give
`Res(⊕)` families that have quasi-polynomial proofs but require exponential size at shallow depth;
see Itsykson--Knop, ITCS 2026, DOI 10.4230/LIPIcs.ITCS.2026.81.  The final theorem below formalizes
the exact contradiction any proposed reducer faces when such a witness is supplied.
-/

namespace PallLean.Paper93.DeepMath.PathB.ResLinParity

open Classical

namespace DAGRefutation

/-- Exact dependency levels cannot outrun line indices because every parent pointer is backward and
every inference level is one plus a parent level (or their maximum). -/
theorem level_le_index {n : ℕ} {Γ : Finset (Clause n)} (P : DAGRefutation n Γ) :
    ∀ i, i < P.steps.length → P.level i ≤ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hi
      let s := P.steps[i]
      have hs : P.steps[i]? = some s := by
        simp only [s, List.getElem?_eq_getElem hi]
      have hv := P.valid i hi
      unfold ValidAt at hv
      rw [hs] at hv
      cases hwhy : s.why with
      | premise =>
          simp only [hwhy] at hv
          omega
      | boolean v =>
          simp only [hwhy] at hv
          omega
      | weaken p e =>
          simp only [hwhy] at hv
          rcases hv with ⟨hp, C, hC, hline, hlevel⟩
          have hpLevel := ih p hp (by omega : p < P.steps.length)
          omega
      | simplify p b =>
          simp only [hwhy] at hv
          rcases hv with ⟨hp, hb, C, hC, hline, hlevel⟩
          have hpLevel := ih p hp (by omega : p < P.steps.length)
          omega
      | linearResolve p q e f =>
          simp only [hwhy] at hv
          rcases hv with ⟨hp, hq, C, D, hC, hD, hline, hlevel⟩
          have hpLevel := ih p hp (by omega : p < P.steps.length)
          have hqLevel := ih q hq (by omega : q < P.steps.length)
          have hmax : max (P.level p) (P.level q) ≤ max p q :=
            max_le_max hpLevel hqLevel
          have hmaxIndex : max p q < i := (max_lt_iff).2 ⟨hp, hq⟩
          omega

/-- **Structure-only depth reduction.**  A checked dag's dependency depth is at most its stored
line count.  This is tight for a chain and is the only universal reduction available without
changing the proof. -/
theorem depth_le_size {n : ℕ} {Γ : Finset (Clause n)} (P : DAGRefutation n Γ) :
    P.depth ≤ P.size := by
  have hpos : 0 < P.steps.length := by simpa [size] using P.size_pos
  let i := P.steps.length - 1
  have hi : i < P.steps.length := by
    simp only [i]
    omega
  have hlevel := P.level_le_index i hi
  unfold depth size
  simp only [i] at hlevel ⊢
  omega

/-! A concrete three-line chain shows that `depth ≤ size` is already exact at the checked proof
object level (the premise set intentionally contains the empty clause; this is a structural
calibration, not a hard formula). -/

def depthThreeSteps : List (DAGStep 0) :=
  [⟨∅, .premise⟩,
   ⟨{falseConstant 0 1}, .weaken 0 (falseConstant 0 1)⟩,
   ⟨∅, .simplify 1 1⟩]

def depthThreeRefutation : DAGRefutation 0 ({∅} : Finset (Clause 0)) where
  steps := depthThreeSteps
  level := fun i => i
  nonempty := by decide
  valid := by
    intro i hi
    have hiCases : i = 0 ∨ i = 1 ∨ i = 2 := by
      simp [depthThreeSteps] at hi
      omega
    rcases hiCases with rfl | rfl | rfl <;>
      simp [ValidAt, depthThreeSteps, lineAt, falseConstant]
  final_empty := rfl

theorem depth_le_size_tight_at_three :
    depthThreeRefutation.depth = depthThreeRefutation.size ∧
      depthThreeRefutation.size = 3 := by
  constructor <;> rfl

end DAGRefutation

/-- The unconditional size floor obtained by combining a shallow lower bound with `depth ≤ size`. -/
def BootstrapFloor (depthCap sizeFloor : ℕ → ℕ) (m : ℕ) : ℕ :=
  min (sizeFloor m) (depthCap m + 1)

/-- **Bounded-depth-to-unrestricted bootstrap.**  Every checked refutation has size at least the
minimum of the shallow size floor and one more than the shallow depth cap. -/
theorem unrestricted_bootstrap_of_depthSize
    {F : LiftedTseitinFamily} {depthCap sizeFloor : ℕ → ℕ}
    (hbound : HasDepthSizeLowerBound F depthCap sizeFloor) :
    HasUnrestrictedSizeLowerBound F (BootstrapFloor depthCap sizeFloor) := by
  intro m P
  rcases depth_size_dichotomy hbound m P with hlarge | hdeep
  · exact (Nat.min_le_left _ _).trans hlarge
  · exact (Nat.min_le_right _ _).trans (by
      have hdepthSize := P.depth_le_size
      omega)

/-- In the interesting regime where the shallow size floor exceeds the depth cap, the automatic
unrestricted consequence stops exactly at `depthCap + 1`. -/
theorem bootstrapFloor_eq_depthCap_succ
    {depthCap sizeFloor : ℕ → ℕ} {m : ℕ}
    (h : depthCap m + 1 ≤ sizeFloor m) :
    BootstrapFloor depthCap sizeFloor m = depthCap m + 1 := by
  exact Nat.min_eq_right h

/-- A proposed depth reducer maps every dag to a shallow dag for the same encoded instance, with
size controlled by `blowup`. -/
def HasDepthReducer (F : LiftedTseitinFamily) (depthCap : ℕ → ℕ)
    (blowup : ℕ → ℕ → ℕ) : Prop :=
  ∀ m (P : FamilyRefutation F m), ∃ Q : FamilyRefutation F m,
    Q.depth ≤ depthCap m ∧ Q.size ≤ blowup m P.size

/-- **Supercritical obstruction to generic depth reduction.**  If one instance has a proof whose
claimed reduced size is below the established shallow lower bound, then no reducer with that
blowup can exist.  The theorem is purely checked glue; the supercritical witness is the external
mathematical input supplied by results such as Itsykson--Knop 2026. -/
theorem no_depthReducer_of_supercritical_witness
    {F : LiftedTseitinFamily} {depthCap sizeFloor : ℕ → ℕ}
    {blowup : ℕ → ℕ → ℕ}
    (hbound : HasDepthSizeLowerBound F depthCap sizeFloor)
    (m : ℕ) (P : FamilyRefutation F m)
    (hgap : blowup m P.size < sizeFloor m) :
    ¬ HasDepthReducer F depthCap blowup := by
  intro hreduce
  rcases hreduce m P with ⟨Q, hQdepth, hQsize⟩
  have hQfloor := hbound m Q hQdepth
  omega

#print axioms DAGRefutation.level_le_index
#print axioms DAGRefutation.depth_le_size
#print axioms DAGRefutation.depth_le_size_tight_at_three
#print axioms unrestricted_bootstrap_of_depthSize
#print axioms no_depthReducer_of_supercritical_witness

end PallLean.Paper93.DeepMath.PathB.ResLinParity
