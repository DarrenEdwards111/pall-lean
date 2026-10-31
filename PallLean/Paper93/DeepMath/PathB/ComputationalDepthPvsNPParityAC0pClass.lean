import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPParityInterfaceDischarge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPRestrictedCapstoneTransfer

/-!
# The `AC⁰[p]` parity-family solver class — brick 5 / model bridge (gap iii)

This file closes the **uniform↔non-uniform** gap by instantiating the repo's `RestrictedCapstoneTransfer`
adapter with a concrete solver class inside an abstract `MachineModel U`:

> `SmallAC0pParityClass` = decision machines `M` whose decision on the parity-CNF family,
> `x ↦ U.decisionRun M.code (parityCNF (ofFn x))`, is **realised by a small `AC⁰[p]` circuit** (`IsAC0pSyntax p`,
> depth `≤ d`, size `+ 1 < lower`).

The forbidden object (`ParityObstruction`) is such a small `AC⁰[p]` circuit deciding the family; it is
**empty** by the unconditional discharge (brick 4 + Razborov–Smolensky), and it is **extracted** from any
class member that decides SAT (via `DecidesSAT` + brick 1).  So `RestrictedCapstoneTransfer` yields
`¬ SATDecisionInClass SmallAC0pParityClass`: **no SAT decider has a small `AC⁰[p]` realisation on the
parity-CNF family.**

This is the honest content of the model bridge: it does **not** claim `P`-time ⊆ `AC⁰[p]` (which is false).
The class is explicitly the restricted "small `AC⁰[p]` realisation" class, and the lower bound is backed by the
real capstone — not by any pigeonhole socket.

## Honest scope

Gap (iii): a genuine `RestrictedCapstoneTransfer` instance for the `AC⁰[p]` parity-family class, giving a
machine-model restricted lower bound backed by the Razborov–Smolensky capstone.  `sorry`-free.  It is a
restricted-class result (`SAT` decider `∉` small-`AC⁰[p]`-on-the-family), not general `SAT ∉ AC⁰[p]` and
certainly not `P ≠ NP`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPParityAC0pClass

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.PvsNPParityToSAT (parityCNF)
open PallLean.Paper93.DeepMath.PathB.PvsNPParityInterfaceDischarge
open PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedDynamicTraceInvariant (SolverClass SATDecisionInClass)
open PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedCapstoneTransfer

variable (U : MachineModel) (p m t d lower : ℕ)

/-- The class of decision machines whose decision on the parity-CNF family is realised by a **small**
`AC⁰[p]` circuit of depth `≤ d`. -/
def SmallAC0pParityClass : SolverClass U :=
  fun M => ∃ Dec : BoolCircuitSyntax (2 * m + 1),
    Dec.IsAC0pSyntax p ∧ Dec.depth ≤ d ∧ Dec.size + 1 < lower ∧
    ∀ x : Fin (2 * m + 1) → Bool,
      Dec.eval x = U.decisionRun M.code (parityCNF (List.ofFn x))

/-- The forbidden object: a small `AC⁰[p]` circuit deciding satisfiability of the parity-CNF family. -/
structure ParityObstruction where
  Dec : BoolCircuitSyntax (2 * m + 1)
  ac0p : Dec.IsAC0pSyntax p
  depth_le : Dec.depth ≤ d
  small : Dec.size + 1 < lower
  decides : ∀ x : Fin (2 * m + 1) → Bool,
    Dec.eval x = true ↔ Satisfiable (parityCNF (List.ofFn x))

open Classical in
/-- **The `RestrictedCapstoneTransfer` instance** for the `AC⁰[p]` parity-family class.  `no_obstruction` is
the unconditional discharge (brick 4 + capstone); `obstruction_of_decides` extracts the circuit from any
class member deciding SAT (using `DecidesSAT` + brick 1). -/
noncomputable def parityAC0pTransfer [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (ht1 : 1 ≤ t) (hpt : 1 ≤ (p - 1) * t) (hlow : 4 * lower ≤ p ^ t)
    (hm : 8 * (((p - 1) * t) ^ (d + 1)) ^ 2 ≤ m) :
    RestrictedCapstoneTransfer U (SmallAC0pParityClass U p m d lower) where
  Obstruction := ParityObstruction p m d lower
  no_obstruction := by
    constructor
    intro obs
    have hwin : 8 * (((p - 1) * t) ^ (obs.Dec.depth + 1)) ^ 2 ≤ m := by
      refine le_trans ?_ hm
      have hmono : ((p - 1) * t) ^ (obs.Dec.depth + 1) ≤ ((p - 1) * t) ^ (d + 1) :=
        Nat.pow_le_pow_right hpt (Nat.succ_le_succ obs.depth_le)
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmono 2)
    have hle := no_small_ac0p_parityCNF_decider_unconditional p hp2 m t ht1 obs.Dec hwin
      obs.ac0p obs.decides lower hlow
    have := obs.small
    omega
  obstruction_of_decides := fun M hM hDec => by
    simp only [SmallAC0pParityClass] at hM
    refine ⟨hM.choose, hM.choose_spec.1, hM.choose_spec.2.1, hM.choose_spec.2.2.1, ?_⟩
    intro x
    rw [hM.choose_spec.2.2.2 x]
    exact hDec (parityCNF (List.ofFn x))

/-- **Cash-out (gap iii closed).**  No SAT decider has a small `AC⁰[p]` realisation on the parity-CNF family. -/
theorem no_SATDecisionInClass_smallAC0pParity [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (ht1 : 1 ≤ t) (hpt : 1 ≤ (p - 1) * t) (hlow : 4 * lower ≤ p ^ t)
    (hm : 8 * (((p - 1) * t) ^ (d + 1)) ^ 2 ≤ m) :
    ¬ SATDecisionInClass (SmallAC0pParityClass U p m d lower) :=
  no_SATDecisionInClass_of_restrictedCapstone
    (parityAC0pTransfer U p m t d lower hp2 ht1 hpt hlow hm)

end PallLean.Paper93.DeepMath.PathB.PvsNPParityAC0pClass

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPParityAC0pClass.no_SATDecisionInClass_smallAC0pParity
