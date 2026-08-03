import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementNoChannel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTseitinEntanglement
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTensorEntanglementLowerBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTensorNetworkMERA
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverInvariantBridge

/-!
# Entanglement route closure: depth, restricted rank, and the intrinsic frontier

The entanglement programme produced several genuine theorems, but they live at
different complexity levels.  This file puts those levels in one audit.

* Logical/tree entanglement correlates two observer clashes, but supplies no
  channel carrying the missing separating projection.
* Seam monogamy exactly characterizes when entanglement destroys reusable
  template sharing.
* Tseitin self-encoding supplies sequential dependence.  It increases depth,
  but it need not fork the reusable template and therefore need not satisfy the
  size socket.
* Tensor rank gives an exponential lower bound for equality at a fixed cut in
  the charged factorization model.  Tensor-network size, however, is only an
  upper bound on general computational cost in the abstract compression model;
  a large representation is not by itself a machine lower bound.
* The surviving unrestricted proposal must therefore be an intrinsic,
  representation-independent entanglement invariant: polynomially bounded by
  every polynomial-time correct decider, yet superpolynomial for every correct
  SAT decider.  With Cook--Levin, those two fields imply `P != NP` immediately.

Thus entanglement is not discarded.  It gives real restricted and depth lower
bounds and a coherent non-natural target.  What remains is precisely the
uniform forking/invariant lower bound; no theorem below manufactures it from
Tseitin gating, a single tensor cut, or observer correlation.
-/

namespace PallLean.Paper93.DeepMath.PathB.EntanglementRouteClosure

open PallLean.Paper93.DeepMath.PathB.SharingMonogamy
open PallLean.Paper93.DeepMath.PathB.TseitinEntanglement
open PallLean.Paper93.DeepMath.PathB.DimensionFullRank
open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge

/-! ## Seam monogamy: the exact size-relevant condition -/

/-- For an entangled seam, the mass-production socket holds exactly when
entanglement covers the template excess.  The previously proved sufficient
condition is also necessary in this arithmetic model. -/
theorem seam_socket_iff_entangledEnough (S : EntangledSeam) :
    2 * S.shared_ <= S.C <-> SATEntangledEnough S := by
  simp only [EntangledSeam.shared_, SATEntangledEnough]
  have hle := S.ent_le
  omega

/-- Consequently, proving the SAT seam socket through this model and proving
`SATEntangledEnough` are not two independent steps: they are the same
inequality. -/
theorem satEntangledEnough_iff_seam_socket (S : EntangledSeam) :
    SATEntangledEnough S <-> 2 * S.shared_ <= S.C :=
  (seam_socket_iff_entangledEnough S).symm

/-! ## Tseitin: genuine depth dependence, no forced size dependence -/

/-- Sequential entanglement alone cannot imply the size socket.  There is a
seam with positive Tseitin-style dependence and no forking whose reusable
template still mass-produces. -/
theorem sequential_entanglement_does_not_force_size_socket :
    exists S : TseitinSeam,
      0 < S.seqDep /\ S.forkDep = 0 /\
      (forall d1 d2 : Nat, max d1 d2 <= d1 + d2) /\
      ¬ (2 * S.shared_ <= S.C) :=
  tseitin_gives_depth_not_size

/-- Forking, rather than sequential gating, is exactly the size-relevant
entanglement quantity. -/
theorem forking_is_exact_size_condition (S : TseitinSeam) :
    2 * S.shared_ <= S.C <->
      2 * S.template <= S.C + 2 * S.forkDep :=
  size_socket_iff_forking S

/-! ## Tensor entanglement: a real restricted lower bound -/

/-- Re-export the fixed-cut charged-tensor lower bound at the closure point:
equality on `k` paired bits requires bond dimension at least `2^k`. -/
theorem equality_fixedCut_requires_exponential_bond
    {K : Type*} [Field K] {k chi : Nat}
    (T : TensorEntanglement.TensorFactorization
      (blockS k) (eqFun K k) chi) :
    2 ^ k <= chi :=
  TensorEntanglement.eqFun_tensor_bond_ge T

/-- A large tensor-network representation is not, without a converse
simulation theorem, a lower bound on unrestricted computation. -/
theorem representation_size_not_general_cost_lower_bound
    (k : Nat) (hk : 0 < k) :
    exists cb tn : Nat, cb <= tn /\ cb < k /\ k <= tn :=
  TensorNetworkMERA.tn_size_is_not_a_lower_bound k hk

/-! ## The sole surviving unrestricted bridge -/

/-- The exact data an unrestricted entanglement proof must provide.  `flow`
must be calibrated against the running time of every correct implementation,
not merely one tensor layout, and must remain superpolynomial after minimizing
over every correct SAT decider. -/
structure IntrinsicEntanglementPackage (SATV : NPObs) where
  flow : Invariant
  timeBounded : InvTimeBounded SATV flow
  hard : InvHard SATV flow

/-- An intrinsic entanglement package rules out a polynomial SAT collapse. -/
theorem no_polyCollapse_of_intrinsicEntanglement
    {SATV : NPObs} (E : IntrinsicEntanglementPackage SATV) :
    ¬ PolyCollapse SATV :=
  invariant_bridge SATV E.flow
    (invSound_of_timeBounded SATV E.flow E.timeBounded) E.hard

/-- With Cook--Levin, the intrinsic package is already a `P != NP` proof.
This is the exact unrestricted frontier, not an additional entanglement lemma
waiting downstream. -/
theorem PneqNP_of_intrinsicEntanglement
    {SATV : NPObs} (E : IntrinsicEntanglementPackage SATV)
    (hCL : CookLevin SATV) :
    ¬ PeqNP :=
  PneqNP_from_timeBounded SATV E.flow E.timeBounded E.hard hCL

/-! ## Consolidated closure statement -/

/-- The route in one theorem: Tseitin depth without a size socket and a
fixed-cut exponential tensor lower bound coexist with the fact that only an
intrinsic machine-calibrated package closes the unrestricted class
separation. -/
theorem entanglement_route_frontier
    {K : Type*} [Field K] {k chi : Nat}
    (T : TensorEntanglement.TensorFactorization
      (blockS k) (eqFun K k) chi)
    {SATV : NPObs} (E : IntrinsicEntanglementPackage SATV)
    (hCL : CookLevin SATV) :
    (2 ^ k <= chi) /\ (¬ PeqNP) :=
  ⟨equality_fixedCut_requires_exponential_bond T,
    PneqNP_of_intrinsicEntanglement E hCL⟩

end PallLean.Paper93.DeepMath.PathB.EntanglementRouteClosure

#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementRouteClosure.seam_socket_iff_entangledEnough
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementRouteClosure.sequential_entanglement_does_not_force_size_socket
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementRouteClosure.equality_fixedCut_requires_exponential_bond
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementRouteClosure.no_polyCollapse_of_intrinsicEntanglement
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementRouteClosure.PneqNP_of_intrinsicEntanglement
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementRouteClosure.entanglement_route_frontier
