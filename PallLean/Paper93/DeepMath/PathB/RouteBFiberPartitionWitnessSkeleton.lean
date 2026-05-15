import PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiExtraction
import PallLean.Paper93.DeepMath.PathB.RouteBPlacedQuotientDescentKR

/-!
# Route B fiber-partition seam — gap-isolation skeleton

This file produces a kernel-clean inhabitant of
`Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData`
parameterised by the single §40/Lemma-31 membership field
`factorSlotContribution_mem_compiledBasis`.

The remaining explicit hypothesis is precisely the paper-faithful §40 / Lemma 31
statement: for every realizable interface-anonymous profile `ρ` and every
selected `(σ, j)` slot, the product of `iterDerivList (d i)
(restrictedFactors i)` over the corresponding factor-slot fiber lies in
the compiled-basis interface space `W_σ`. This is the actual algebraic
content the seam packages.

Fields 1–5 (block partition, canonical profile, single-bucket fiber
assignment, pairwise disjointness, covering identity) are discharged
constructively.

Once §40 Lemma 31 lands, its proof supplies the explicit parameter below.
Note that the canonical Route B closure
`P_ne_NP_canonical_routeB_bottomSeam_primary_from_fiberPartition_and_localAlgebra_conditional`
takes *both* a fiber-partition seam and a `…CompiledBasisLocalAlgebraData`
companion plus compatibility hypotheses. This file inhabits only the
fiber-partition half. An analogous skeleton for the local-algebra side
(plus the `sourcePartition`/profile compatibility lemmas) is still
needed before the closure fires end-to-end.

**CLAUDE.md note.** The global "DO NOT SIMPLIFY proofs" rule is
explicitly relaxed for this file by user request. The explicit Lemma-31 parameter isolates the open math gap to one named
obligation; the file is a gap-marker, not an unconditional closure.
-/

set_option maxHeartbeats 800000

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.Paper283
open TuringMachine
open WithinProfileBound
open Step4Compiler
open SymmetricPowerBound
open scoped BigOperators

/-- Canonical realizable profile concentrating all mass on
`ConstraintType.booleanity`. Used as the constant value of
`profileOfCanonicalWindow` in the fiber-partition skeleton below. -/
noncomputable def routeBFiberSkeleton_canonicalProfile (n : ℕ) :
    RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
      ConstraintType (Nat.log 2 n) := by
  classical
  refine ⟨fun σ => if σ = ConstraintType.booleanity then Nat.log 2 n else 0, ?_⟩
  unfold PallLean.Paper93.RealizableProfiles
  rw [Finset.mem_image]
  refine
    ⟨fun σ => if σ = ConstraintType.booleanity
              then ⟨Nat.log 2 n, Nat.lt_succ_self _⟩
              else 0,
     ?_, ?_⟩
  · rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have :
        (∑ σ : ConstraintType,
            ((if σ = ConstraintType.booleanity
                then (⟨Nat.log 2 n, Nat.lt_succ_self _⟩ : Fin (Nat.log 2 n + 1))
                else 0) : ℕ)) = Nat.log 2 n := by
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    exact this
  · funext σ
    by_cases h : σ = ConstraintType.booleanity
    · subst h; simp
    · simp [h]

/-- The exact §40/Lemma-31 membership obligation for the single-bucket
fiber skeleton below.

This is intentionally a `Prop`, not an axiom: callers must supply a proof of
the genuine compiled-basis membership payload before the skeleton can be
promoted to Route B data. -/
def RouteBFiberPartitionWitnessSkeletonLemma31Obligation
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (ρ : RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
          ConstraintType (Nat.log 2 n))
      (S' : List (Fin (n / 3)))
      (shift : MvPolynomial (Fin (n / 3)) ℚ)
      (α : Fin n →₀ ℕ)
      (hSlen : S'.length = Nat.log 2 n)
      (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
      (hshiftVars :
        (MvPolynomial.rename (_root_.Step4Compiler.Step252.cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (_root_.Step4Compiler.Step252.cookLevinStrictFOBFlatMap n)).toFinset)
      (hadm :
        SPDP.isBlockAdmissible
          (_root_.PaperFaithfulSeparation.cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (_root_.Step4Compiler.Step252.cookLevinStrictFOBFlatMap n)))
      (hrow :
        routeBPaperFaithfulTPhiStrictProfileCoverCanonicalRowFamily
          M n hn2 htb hns S' shift α)
      (hρ :
        routeBFiberSkeleton_canonicalProfile n = ρ)
      (d : Fin ((cookLevinFactorList M n hn2 htb hns).length) →
        List (Fin (n / 3)))
      (hd_elts : ∀ i, ∀ v ∈ d i, v ∈ S')
      (hlen : ∑ i : Fin ((cookLevinFactorList M n hn2 htb hns).length),
          (d i).length ≤ S'.length)
      (σ : ConstraintType) (j : Fin (ρ.val σ)),
        ((if σ = ConstraintType.booleanity ∧ j.val = 0
          then (Finset.univ :
            Finset (Fin ((cookLevinFactorList M n hn2 htb hns).length)))
          else ∅).prod (fun i =>
            SPDP.iterDerivList (d i)
              ((routeBPaperFaithfulTPhi_strictSourceRestrictedFactors
                M n hn2 htb hns) i))) ∈
          interfaceSpace_compiledBasis
            ({ numBlocks := 1
               assign := fun _ => ⟨0, by decide⟩ } : SPDP.BlockPartition (n / 3))
            (Nat.log 2 n) (Nat.log 2 n) σ

/-- The current single-bucket skeleton obligation exposes the genuinely hard
case explicitly: its booleanity/zero-slot instance is the full unshifted
Leibniz product of all restricted Cook--Levin factors, not a background or
empty-slot artifact.

This lemma is intentionally diagnostic. It prevents the skeleton obligation
from being mistaken for a harmless bookkeeping field: proving it requires the
non-degenerate §40/Lemma-31 compiled-basis membership payload for the actual
factor product. -/
theorem routeBFiberPartitionWitnessSkeletonLemma31Obligation_fullProduct_mem_booleanity
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (hLemma31 : RouteBFiberPartitionWitnessSkeletonLemma31Obligation
      M n hn2 htb hns)
    (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ)
    (α : Fin n →₀ ℕ)
    (hSlen : S'.length = Nat.log 2 n)
    (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
    (hshiftVars :
      (MvPolynomial.rename (_root_.Step4Compiler.Step252.cookLevinStrictFOBFlatMap n) shift).vars ⊆
        (S'.map (_root_.Step4Compiler.Step252.cookLevinStrictFOBFlatMap n)).toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (_root_.PaperFaithfulSeparation.cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (_root_.Step4Compiler.Step252.cookLevinStrictFOBFlatMap n)))
    (hrow :
      routeBPaperFaithfulTPhiStrictProfileCoverCanonicalRowFamily
        M n hn2 htb hns S' shift α)
    (d : Fin ((cookLevinFactorList M n hn2 htb hns).length) →
      List (Fin (n / 3)))
    (hd_elts : ∀ i, ∀ v ∈ d i, v ∈ S')
    (hlen : ∑ i : Fin ((cookLevinFactorList M n hn2 htb hns).length),
        (d i).length ≤ S'.length) :
      Finset.univ.prod (fun i : Fin ((cookLevinFactorList M n hn2 htb hns).length) =>
          SPDP.iterDerivList (d i)
            ((routeBPaperFaithfulTPhi_strictSourceRestrictedFactors
              M n hn2 htb hns) i)) ∈
        interfaceSpace_compiledBasis
          ({ numBlocks := 1
             assign := fun _ => ⟨0, by decide⟩ } : SPDP.BlockPartition (n / 3))
          (Nat.log 2 n) (Nat.log 2 n) ConstraintType.booleanity := by
  classical
  let ρ := routeBFiberSkeleton_canonicalProfile n
  have hmass : ρ.val ConstraintType.booleanity = Nat.log 2 n := by
    simp [ρ, routeBFiberSkeleton_canonicalProfile]
  have hlog_pos : 0 < Nat.log 2 n := Nat.log_pos (by decide) hn2
  have hbool_pos : 0 < ρ.val ConstraintType.booleanity := by
    rw [hmass]
    exact hlog_pos
  have hmem := hLemma31 ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    rfl d hd_elts hlen ConstraintType.booleanity ⟨0, hbool_pos⟩
  simpa using hmem

/-- The fiber-partition skeleton witness, parameterised by the exact
§40/Lemma-31 compiled-basis membership obligation.

All finite-combinatorial fields are discharged constructively.  The only
non-structural mathematical input is the explicit `hLemma31` parameter above;
there is no proof placeholder and no new axiom. -/
noncomputable def routeBFiberPartitionWitness_skeleton
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hLemma31 :
      RouteBFiberPartitionWitnessSkeletonLemma31Obligation
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictSourceSelectedShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData
      M n hn2 htb hns :=
{ sourcePartition :=
    { numBlocks := 1
      assign := fun _ => ⟨0, by decide⟩ }
  profileOfCanonicalWindow := fun _w _hw =>
    routeBFiberSkeleton_canonicalProfile n
  factorSlotFiber := fun _ρ _S' _shift _α _hSlen _hshiftDegree _hshiftVars
    _hadm _hrow _hρ _d _hd_elts _hlen σ j =>
    -- Single-bucket dump: every factor index goes into the unique
    -- `(σ = .booleanity, j.val = 0)` slot; all other slots are empty.
    if σ = ConstraintType.booleanity ∧ j.val = 0
      then (Finset.univ :
            Finset (Fin ((cookLevinFactorList M n hn2 htb hns).length)))
      else ∅
  factorSlotFiber_pairwiseDisjoint := by
    intro ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow hρ
      d hd_elts hlen p _hp q _hq hpq
    -- At most one of the two fibers can be non-empty (only the unique
    -- (booleanity, 0) slot ever yields a non-empty `Finset.univ`).
    simp only [Function.onFun]
    by_cases hp' : p.1 = ConstraintType.booleanity ∧ p.2.val = 0
    · by_cases hq' : q.1 = ConstraintType.booleanity ∧ q.2.val = 0
      · -- both pairs are (.booleanity, 0): forces p = q, contradicting hpq.
        exfalso
        apply hpq
        obtain ⟨hp1, hp2⟩ := hp'
        obtain ⟨hq1, hq2⟩ := hq'
        rcases p with ⟨a₁, b₁⟩
        rcases q with ⟨a₂, b₂⟩
        dsimp at hp1 hp2 hq1 hq2
        subst hp1
        subst hq1
        congr 1
        exact Fin.ext (hp2.trans hq2.symm)
      · -- q fiber is empty
        show Disjoint (if p.1 = ConstraintType.booleanity ∧ p.2.val = 0
                        then (Finset.univ :
                              Finset (Fin ((cookLevinFactorList M n hn2 htb hns).length)))
                        else ∅)
                      (if q.1 = ConstraintType.booleanity ∧ q.2.val = 0
                        then (Finset.univ :
                              Finset (Fin ((cookLevinFactorList M n hn2 htb hns).length)))
                        else ∅)
        rw [if_neg hq']
        exact Finset.disjoint_empty_right _
    · -- p fiber is empty
      show Disjoint (if p.1 = ConstraintType.booleanity ∧ p.2.val = 0
                      then (Finset.univ :
                            Finset (Fin ((cookLevinFactorList M n hn2 htb hns).length)))
                      else ∅)
                    (if q.1 = ConstraintType.booleanity ∧ q.2.val = 0
                      then (Finset.univ :
                            Finset (Fin ((cookLevinFactorList M n hn2 htb hns).length)))
                      else ∅)
      rw [if_neg hp']
      exact Finset.disjoint_empty_left _
  factorSlotFiber_biUnion_eq_univ := by
    intro ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow hρ
      d hd_elts hlen
    apply Finset.ext
    intro i
    refine ⟨fun _ => Finset.mem_univ _, fun _ => ?_⟩
    rw [Finset.mem_biUnion]
    -- ρ equals our canonical profile (forced by `hρ`), whose mass at
    -- `.booleanity` is `Nat.log 2 n ≥ 1` (since `n ≥ 2`).
    have hρ_eq : ρ = routeBFiberSkeleton_canonicalProfile n := hρ.symm
    have hmass : ρ.val ConstraintType.booleanity = Nat.log 2 n := by
      rw [hρ_eq]; simp [routeBFiberSkeleton_canonicalProfile]
    have hlog_pos : 0 < Nat.log 2 n := Nat.log_pos (by decide) hn2
    have hbool_pos : 0 < ρ.val ConstraintType.booleanity := by
      rw [hmass]; exact hlog_pos
    refine ⟨⟨ConstraintType.booleanity, ⟨0, hbool_pos⟩⟩, ?_, ?_⟩
    · exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
    · rw [if_pos (And.intro rfl rfl)]
      exact Finset.mem_univ _
  factorSlotContribution_mem_compiledBasis := by
    intro ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow hρ
      d hd_elts hlen σ j
    exact hLemma31 ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow
      hρ d hd_elts hlen σ j }

/-- Uniform §40/Lemma-31 obligation for the skeleton, matching the Step-247
quantifier shape. -/
def Step247UniformRouteBFiberPartitionWitnessSkeletonLemma31Obligation : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    RouteBFiberPartitionWitnessSkeletonLemma31Obligation M n hn2 htb hns

/-- **Uniform Step-247 wrapping from the real Lemma-31 payload.**

Promotes the per-instance skeleton above into the uniform `Prop` expected by
the Route B PathB closure aggregator once the non-degenerate §40/Lemma-31
membership obligation has been supplied. -/
noncomputable def step247UniformFiberPartitionData_skeleton
    (hLemma31 : Step247UniformRouteBFiberPartitionWitnessSkeletonLemma31Obligation) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData := by
  intro M n hn hn2 htb hns
  exact ⟨routeBFiberPartitionWitness_skeleton M n hn2 htb hns
    (hLemma31 M n hn hn2 htb hns)⟩

/-! ### Open obligation summary

The `#print axioms` directives below report the skeleton wrapper itself as
kernel-clean: the remaining §40/Lemma-31 content is an explicit hypothesis,
not a hidden placeholder axiom or bespoke axiom. -/

#print axioms routeBFiberPartitionWitness_skeleton
#print axioms step247UniformFiberPartitionData_skeleton

end PallLean.Paper93.DeepMath.PathB
