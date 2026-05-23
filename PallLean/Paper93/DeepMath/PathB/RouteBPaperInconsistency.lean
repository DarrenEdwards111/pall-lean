import PallLean.Paper93.DeepMath.PathB.ProjectedIdentityMinorConcrete

/-!
# Route B paper-internal inconsistency

This file records the honest paper-faithful closeout: if the paper's Route-B
P-side collapse statement (Theorem 228/225, applied to the concrete Cook--Levin
`q_n`) is stated on the same Step247 output for which the already-formalized
identity-minor lower bound (Theorem 230) holds, the two statements imply
`False` at the paper scale.

No new bridge or gauge is constructed here.  The point is exactly that the
collapse theorem, as a theorem about this `q_n`, cannot coexist with the proved
NP-side identity-minor theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine
open MultilinearSPDP
open PaperFaithfulCompilation

/-- The paper's concrete Route-B `q_n`: the full Step247 Cook--Levin compiler
output.  This is the polynomial to which the Route-B P-side collapse would be
applied. -/
noncomputable abbrev routeB_q_n
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    PMnPoly (Step4Compiler.Step247.partitioned_output_cookLevin
      M n hn2 htb hns).σ :=
  (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).full_output

/-- Paper-faithful statement of the Route-B Theorem 228/225 collapse conclusion
on the concrete `q_n`: the SPDP rank of the compiler output is polynomially
bounded. -/
def RouteBTheorem228225CollapseOn_q_n
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  PaperFaithfulCompilerPSideBound n
    (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
    (extendedCookLevinPartition M n hn2)
    (Nat.log 2 n) (Nat.log 2 n)
    (routeB_q_n M n hn2 htb hns)

/-- The named collapse statement is exactly the existing concrete projected
P-side bound frontier, just phrased as the paper's `q_n` collapse. -/
theorem routeBTheorem228225CollapseOn_q_n_iff_cookLevinProjectedPSideBound
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBTheorem228225CollapseOn_q_n M n hn2 htb hns ↔
      ProjectedIdentityMinorConcrete.CookLevinProjectedPSideBound
        M n hn2 htb hns := by
  rfl

/-- Theorem 230, in the same concrete Route-B setting: the Step247 verifier
sheet carries the identity-minor lower bound. -/
theorem routeBTheorem230_identityMinorLower_on_q_n
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2) :
    SourceIdentityMinorLowerBound n
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
      (extendedCookLevinPartition M n hn2)
      (Nat.log 2 n) (Nat.log 2 n)
      (Step4Compiler.Step247.partitioned_output_cookLevin
        M n hn2 htb hns).Q_verifier :=
  ProjectedIdentityMinorConcrete.sourceIdentityMinorLowerBound_cookLevin_partitionedOutput
    M n hn htb hns hn2

/-- The paper-faithful contradiction: Route-B's claimed P-side collapse on
`q_n` cannot coexist with the already proved Theorem-230 identity-minor lower
bound on the same Step247 Cook--Levin output. -/
theorem routeBTheorem228225CollapseOn_q_n_false_by_theorem230
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2)
    (hcollapse : RouteBTheorem228225CollapseOn_q_n M n hn2 htb hns) :
    False := by
  exact ProjectedIdentityMinorConcrete.false_of_cookLevinProjectedPSideBound
    M n hn htb hns hn2
    ((routeBTheorem228225CollapseOn_q_n_iff_cookLevinProjectedPSideBound
      M n hn2 htb hns).mp hcollapse)

/-- Equivalently, the Route-B Theorem 228/225 collapse theorem for `q_n` is
refuted at the paper scale. -/
theorem not_routeBTheorem228225CollapseOn_q_n
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2) :
    ¬ RouteBTheorem228225CollapseOn_q_n M n hn2 htb hns := by
  intro hcollapse
  exact routeBTheorem228225CollapseOn_q_n_false_by_theorem230
    M n hn htb hns hn2 hcollapse

/-! ## Axiom audit anchors -/

#print axioms routeBTheorem228225CollapseOn_q_n_iff_cookLevinProjectedPSideBound
#print axioms routeBTheorem230_identityMinorLower_on_q_n
#print axioms routeBTheorem228225CollapseOn_q_n_false_by_theorem230
#print axioms not_routeBTheorem228225CollapseOn_q_n

end PallLean.Paper93.DeepMath.PathB
