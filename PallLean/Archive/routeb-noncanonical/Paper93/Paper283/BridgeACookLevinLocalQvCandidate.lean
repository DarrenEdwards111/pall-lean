import PallLean.Paper93.Paper283.BridgeAPolynomialLocalGadget

/-!
# Cook-Levin local `Q_v` candidate for Bridge A

The matrix-side `pocketFamily` is not a compiler polynomial.  This file
therefore defines the honest polynomial candidate directly from the active
Cook-Levin compiler:

`Q_b = product of (1 - C.poly) over constraints touching locality block b`.

The file does not assert that this candidate has the required rank.  Instead it
names the exact energy-to-SPDP-rank theorem needed to turn these real compiler
polynomials into polynomial-bearing Bridge A gadgets.
-/

namespace PallLean.Paper93.Paper283

open MultilinearSPDP
open PaperFaithfulSeparation

attribute [local instance] Classical.dec

/-- A compiler constraint touches a locality block when one of its support
variables is assigned to that block by the compiler partition. -/
def cookLevinConstraintTouchesBlock {M : TuringMachine.DTM} {n : Nat}
    (T : CompiledTableau M n)
    (b : Fin T.partition.numBlocks)
    (c : PaperFaithfulSeparation.LocalConstraint T.numVars) : Prop :=
  ∃ i : Fin T.numVars, i ∈ c.support ∧ T.partition.assign i = b

/-- The actual constraints of a compiled tableau that touch locality block
`b`. -/
noncomputable def cookLevinConstraintsTouchingBlock {M : TuringMachine.DTM} {n : Nat}
    (T : CompiledTableau M n)
    (b : Fin T.partition.numBlocks) :
    List (PaperFaithfulSeparation.LocalConstraint T.numVars) :=
  T.constraints.filter (fun c => cookLevinConstraintTouchesBlock T b c)

/-- The paper-faithful local polynomial candidate for a compiler locality
block: the product of the real Cook-Levin factors whose constraints touch that
block. -/
noncomputable def cookLevinLocalBlockQ
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks) :
    MvPolynomial (Fin (cook_levin_compilation M n hn htb hns).numVars) Rat :=
  let T := cook_levin_compilation M n hn htb hns
  ((cookLevinConstraintsTouchingBlock T b).map
    (fun c => (1 : MvPolynomial (Fin T.numVars) Rat) - c.poly)).prod

/-- The exact rank target for the real local-block polynomial candidate.  This
is the theorem that would replace the current matrix-rank shortcut. -/
def CookLevinLocalBlockQRankTarget
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (kappa gadgetN : Nat)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks) :
    Prop :=
  mlBlockedSpdpRank
      (cook_levin_compilation M n hn htb hns).partition
      kappa kappa
      (cookLevinLocalBlockQ M n hn htb hns b) =
    kappa * gadgetN

/-- Energy-to-rank target for a chosen map from Route B vertices to actual
Cook-Levin locality blocks. -/
def CookLevinLocalBlockQEnergyToRankTarget {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (blockOfVertex :
      Fin N -> Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks) :
    Prop :=
  ∀ v : Fin N,
    alpha0 <= localEnergy alpha beta G chi Phi v ->
      kappa <=
        mlBlockedSpdpRank
          (cook_levin_compilation M n hn htb hns).partition
          kappa kappa
          (cookLevinLocalBlockQ M n hn htb hns (blockOfVertex v))

/-- The named missing package for a paper-faithful Bridge A: pick the compiler
locality block corresponding to every Route B vertex and prove the local
energy-to-SPDP-rank implication for the real block polynomial. -/
structure CookLevinLocalBlockQBridgeAData {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) : Type where
  blockOfVertex :
    Fin N -> Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks
  energy_to_spdpRank :
    CookLevinLocalBlockQEnergyToRankTarget
      M n hn htb hns alpha beta alpha0 kappa G chi Phi blockOfVertex

/-- A proved `CookLevinLocalBlockQBridgeAData` package upgrades the real
compiler-local block polynomial to the polynomial-bearing Bridge A interface. -/
noncomputable def cookLevinLocalBlockQ_polynomialLocalGadget
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (data :
      CookLevinLocalBlockQBridgeAData
        M n hn htb hns alpha beta alpha0 kappa G chi Phi)
    (v : Fin N) :
    BridgeAPolynomialLocalGadget
      alpha beta alpha0 kappa G chi Phi v where
  spdpVars := (cook_levin_compilation M n hn htb hns).numVars
  partition := (cook_levin_compilation M n hn htb hns).partition
  Qv := cookLevinLocalBlockQ M n hn htb hns (data.blockOfVertex v)
  energy_to_spdpRank := data.energy_to_spdpRank v

/-- Family form of the real compiler-local polynomial candidate. -/
noncomputable def cookLevinLocalBlockQ_polynomialLocalGadgetFamily
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (data :
      CookLevinLocalBlockQBridgeAData
        M n hn htb hns alpha beta alpha0 kappa G chi Phi) :
    ∀ v : Fin N,
      BridgeAPolynomialLocalGadget
        alpha beta alpha0 kappa G chi Phi v :=
  fun v =>
    cookLevinLocalBlockQ_polynomialLocalGadget
      M n hn htb hns alpha beta alpha0 kappa G chi Phi data v

/-! ## Axiom audit anchors -/

#print axioms cookLevinConstraintTouchesBlock
#print axioms cookLevinConstraintsTouchingBlock
#print axioms cookLevinLocalBlockQ
#print axioms CookLevinLocalBlockQRankTarget
#print axioms CookLevinLocalBlockQEnergyToRankTarget
#print axioms CookLevinLocalBlockQBridgeAData
#print axioms cookLevinLocalBlockQ_polynomialLocalGadget
#print axioms cookLevinLocalBlockQ_polynomialLocalGadgetFamily

end PallLean.Paper93.Paper283
