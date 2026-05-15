import PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiExtraction
import PallLean.Paper93.DeepMath.PathB.RouteBPlacedQuotientDescentKR

/-!
# Route B fiber-partition seam — gap-isolation skeleton

This file produces an unconditional inhabitant of
`Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData`
**modulo a single `sorry`** at the
`factorSlotContribution_mem_compiledBasis` field.

The remaining `sorry` is precisely the paper-faithful §40 / Lemma 31
statement: for every realizable interface-anonymous profile `ρ` and every
selected `(σ, j)` slot, the product of `iterDerivList (d i)
(restrictedFactors i)` over the corresponding factor-slot fiber lies in
the compiled-basis interface space `W_σ`. This is the actual algebraic
content the seam packages.

Fields 1–5 (block partition, canonical profile, single-bucket fiber
assignment, pairwise disjointness, covering identity) are discharged
constructively.

Once §40 Lemma 31 lands, this file's `sorry` becomes a real proof.
Note that the canonical Route B closure
`P_ne_NP_canonical_routeB_bottomSeam_primary_from_fiberPartition_and_localAlgebra_conditional`
takes *both* a fiber-partition seam and a `…CompiledBasisLocalAlgebraData`
companion plus compatibility hypotheses. This file inhabits only the
fiber-partition half. An analogous skeleton for the local-algebra side
(plus the `sourcePartition`/profile compatibility lemmas) is still
needed before the closure fires end-to-end.

**CLAUDE.md note.** The global "DO NOT SIMPLIFY proofs" rule is
explicitly relaxed for this file by user request. The sole `sorry`
isolates the open math gap to one named obligation; the file is a
gap-marker, not a closure.
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

/-- The fiber-partition skeleton witness.

Discharges every structural field of
`RouteBPaperFaithfulTPhiStrictSourceSelectedShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData`
except `factorSlotContribution_mem_compiledBasis`, which is left as
`sorry` and labelled as the §40 / Lemma 31 open obligation. -/
noncomputable def routeBFiberPartitionWitness_skeleton
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
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
    -- **§40 Lemma 31 — the actual paper-faithful open obligation.**
    --
    -- For each selected (σ, j) and the fiber `factorSlotFiber σ j`
    -- defined above (`Finset.univ` at (.booleanity, 0) or `∅`
    -- otherwise), the product
    --   `∏ i ∈ fiber, iterDerivList (d i) (restrictedFactors i)`
    -- must lie in
    --   `interfaceSpace_compiledBasis sourcePartition (log₂ n) (log₂ n) σ`.
    --
    -- Two sub-cases:
    --   (a) empty fiber → product = 1, need `1 ∈ W_σ`;
    --   (b) universal fiber at (booleanity, 0) → product = full unshifted
    --       bounded-Leibniz product, need it ∈ W_{booleanity} (literal
    --       Lemma 31).
    --
    -- Both require the paper's §40 disjoint-fiber-product +
    -- compiled-basis-containment argument and are not derivable from
    -- existing in-repo primitives. Hence the single `sorry`.
    sorry }

/-- **Uniform Step-247 wrapping.**

Promotes the per-instance skeleton above into the uniform `Prop`
expected by the Route B PathB closure aggregator. -/
noncomputable def step247UniformFiberPartitionData_skeleton :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData := by
  intro M n _hn hn2 htb hns
  exact ⟨routeBFiberPartitionWitness_skeleton M n hn2 htb hns⟩

/-! ### Sole open obligation summary

The `#print axioms` directive below reports the transitive axiom set of
the skeleton. While field 6 is unproved it will include `sorryAx`.
Once §40 Lemma 31 lands, replace the `sorry` and this print will
reduce to `[propext, Classical.choice, Quot.sound]`. -/

#print axioms step247UniformFiberPartitionData_skeleton

end PallLean.Paper93.DeepMath.PathB
