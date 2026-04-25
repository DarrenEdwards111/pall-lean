import PallLean.Paper93.DeepMath.CookLevin.BridgeA
import PallLean.Paper93.DeepMath.CookLevin.BridgeB
import PallLean.Paper93.Paper283.BridgeAActiveBudget

/-!
# Paper §28.3 Bridge A concrete Cook-Levin gadget connection

This file connects the abstract Paper283 `LocalGadget` interface to the
checked Cook-Levin rank theorem currently available in the repository.

The repository does not yet expose a per-vertex Cook-Levin compiler object
`Q_v` for every vertex of a Paper283 graph.  Consequently, the concrete bridge
below is intentionally uniform: every vertex is assigned the same checked
Cook-Levin gadget rank `(cookLevinGadget alpha n).rank`.  Under `alpha > 0`
and `n >= 2`, the existing theorem `CookLevin.bridge_A_pocket` supplies rank
at least `1`, which is exactly the `hGadgetRank` hypothesis needed by
`bridgeA_activeSet_rank_budget` for `kappa = 1`.

What remains for a fully per-vertex concrete Bridge A is an actual compiler
mapping each active vertex `v` to its local compiled SPDP gadget `Q_v`, plus a
proof that `Q_v.rank` is represented by the Cook-Levin rank used here.
-/

namespace PallLean.Paper93.Paper283

/-- The uniform concrete Paper283 local gadget obtained by reading the rank
from the checked Cook-Levin gadget `cookLevinGadget alpha n`. -/
noncomputable def cookLevinLocalGadget (N : Nat) (alpha : Real) (n : Nat) (v : Fin N) :
    LocalGadget N v where
  rank :=
    (PallLean.Paper93.DeepMath.CookLevin.cookLevinGadget alpha n).rank

/-- The uniform Cook-Levin-backed local gadget family over all vertices. -/
noncomputable def cookLevinLocalGadgetFamily (N : Nat) (alpha : Real) (n : Nat) :
    ∀ v : Fin N, LocalGadget N v :=
  fun v => cookLevinLocalGadget N alpha n v

/-- The checked Cook-Levin Bridge A rank theorem, transported to the
Paper283 `LocalGadget` wrapper. -/
theorem cookLevinLocalGadget_rank_one {N : Nat}
    (alpha : Real) (n : Nat) (v : Fin N)
    (halpha : 0 < alpha) (hn : 2 ≤ n) :
    1 ≤ ((cookLevinLocalGadgetFamily N alpha n) v).rank := by
  simpa [cookLevinLocalGadgetFamily, cookLevinLocalGadget] using
    PallLean.Paper93.DeepMath.CookLevin.bridge_A_pocket alpha n halpha hn

/-- The `hGadgetRank` hypothesis required by `bridgeA_activeSet_rank_budget`,
specialised to the uniform Cook-Levin-backed gadget family and `kappa = 1`.

The local-energy hypothesis is retained because it is part of the Bridge A
interface, but the present uniform Cook-Levin rank proof does not depend on it:
the missing future ingredient is the per-vertex compiler identifying each
active vertex's local gadget with the concrete Cook-Levin gadget. -/
theorem cookLevin_hGadgetRank_one {N d : Nat}
    (alpha beta alpha0 : Real) (n : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N → Real)
    (halpha : 0 < alpha) (hn : 2 ≤ n) :
    ∀ v : Fin N,
      alpha0 ≤ localEnergy alpha beta G chi Phi v →
        1 ≤ ((cookLevinLocalGadgetFamily N alpha n) v).rank := by
  intro v _hv
  exact cookLevinLocalGadget_rank_one alpha n v halpha hn

/-- Bridge A active-set rank budget discharged by the checked Cook-Levin
rank theorem for the uniform concrete gadget family, at rank threshold `1`. -/
theorem bridgeA_activeSet_rank_budget_cookLevin_one {N d : Nat}
    (alpha beta alpha0 : Real) (n : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N → Real)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0) (hn : 2 ≤ n) :
    (activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card * 1 ≤
      ∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
        ((cookLevinLocalGadgetFamily N alpha n) v).rank := by
  exact bridgeA_activeSet_rank_budget
    alpha beta alpha0 1 G chi Phi (cookLevinLocalGadgetFamily N alpha n)
    halpha0
    (cookLevin_hGadgetRank_one alpha beta alpha0 n G chi Phi halpha hn)

/-! ## κ-pocket Bridge A interface -/

/-- The uniform concrete Paper283 local gadget obtained from the checked
`κ`-pocket Cook-Levin family.  This is the matrix-side rank object used by the
Route B analytic core when the active-set threshold is `κ`, not just `1`. -/
noncomputable def cookLevinPocketLocalGadget
    (N : Nat) (alpha : Real) (kappa n : Nat) (v : Fin N) :
    LocalGadget N v where
  rank :=
    (PallLean.Paper93.DeepMath.BridgeB.pocketFamily alpha kappa n).rank

/-- Uniform `κ`-pocket gadget family over all vertices. -/
noncomputable def cookLevinPocketLocalGadgetFamily
    (N : Nat) (alpha : Real) (kappa n : Nat) :
    ∀ v : Fin N, LocalGadget N v :=
  fun v => cookLevinPocketLocalGadget N alpha kappa n v

/-- The checked Cook-Levin/Pocket Bridge B theorem supplies the rank lower
bound needed by Bridge A for arbitrary `κ`. -/
theorem cookLevinPocketLocalGadget_rank_kappa {N : Nat}
    (alpha : Real) (kappa n : Nat) (v : Fin N)
    (halpha : 0 < alpha) (hn : 2 ≤ n) :
    kappa ≤ ((cookLevinPocketLocalGadgetFamily N alpha kappa n) v).rank := by
  simpa [cookLevinPocketLocalGadgetFamily, cookLevinPocketLocalGadget] using
    PallLean.Paper93.DeepMath.CookLevin.bridge_B_kappa_pocket
      alpha kappa n halpha hn

/-- The `hGadgetRank` hypothesis required by `bridgeA_activeSet_rank_budget`,
specialised to the uniform `κ`-pocket Cook-Levin-backed gadget family. -/
theorem cookLevin_hGadgetRank_kappa {N d : Nat}
    (alpha beta alpha0 : Real) (kappa n : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N → Real)
    (halpha : 0 < alpha) (hn : 2 ≤ n) :
    ∀ v : Fin N,
      alpha0 ≤ localEnergy alpha beta G chi Phi v →
        kappa ≤ ((cookLevinPocketLocalGadgetFamily N alpha kappa n) v).rank := by
  intro v _hv
  exact cookLevinPocketLocalGadget_rank_kappa alpha kappa n v halpha hn

/-- Bridge A active-set rank budget discharged by the checked `κ`-pocket
Cook-Levin rank theorem. -/
theorem bridgeA_activeSet_rank_budget_cookLevin_kappa {N d : Nat}
    (alpha beta alpha0 : Real) (kappa n : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N → Real)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0) (hn : 2 ≤ n) :
    (activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card * kappa ≤
      ∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
        ((cookLevinPocketLocalGadgetFamily N alpha kappa n) v).rank := by
  exact bridgeA_activeSet_rank_budget
    alpha beta alpha0 kappa G chi Phi
    (cookLevinPocketLocalGadgetFamily N alpha kappa n)
    halpha0
    (cookLevin_hGadgetRank_kappa
      alpha beta alpha0 kappa n G chi Phi halpha hn)

/-! ## Axiom audit anchors -/

#print axioms cookLevinLocalGadget_rank_one
#print axioms cookLevin_hGadgetRank_one
#print axioms bridgeA_activeSet_rank_budget_cookLevin_one
#print axioms cookLevinPocketLocalGadget_rank_kappa
#print axioms cookLevin_hGadgetRank_kappa
#print axioms bridgeA_activeSet_rank_budget_cookLevin_kappa

end PallLean.Paper93.Paper283
