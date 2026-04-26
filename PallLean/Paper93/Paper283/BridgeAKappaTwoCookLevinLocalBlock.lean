import PallLean.Paper93.Paper283.BridgeAKappaOneCookLevinLocalBlock
import PallLean.Paper93.Paper283.BridgeAKappaGeneralBoolRows
import PallLean.Paper93.Paper283.BridgeAKappaLocalSupportObstruction

/-!
# Bridge A at `kappa = 2` for the real Cook-Levin local block product

This file pushes Route C ⇒ Route A from `kappa = 1` (closed in
`BridgeAKappaOneCookLevinLocalBlock`) toward `kappa = 2` on the actual
compiler-local product `cookLevinLocalBlockQ`.

The very first step is identifying the genuine structural obstruction to a
naive within-block formulation.  Cook-Levin's locality partition assigns
three consecutive variables to each block.  A would-be `kappa = 2` row
with both coordinates inside one such block (e.g. `{a, b}`, `{a, c}`,
`{b, c}` for the three vertices of a single block) is automatically
**not block-admissible**: the strict admissibility predicate
`SPDP.isBlockAdmissible` requires at most one coordinate per block.

We therefore split the file into two halves:

1. **The within-block obstruction is sharp.**
   We prove that any block-admissible derivative list whose every
   coordinate lies in the same locality block has length at most one.
   This is the precise structural reason the prompt's proposed three
   rows `∂_{a,b}`, `∂_{a,c}`, `∂_{b,c}` cannot live in the locality-partition
   SPDP subspace at all.

2. **A cross-block formulation is the honest `kappa = 2` target.**
   We name and package the cross-block coefficient-diagonal hypothesis
   that closes `kappa = 2` Bridge A through the existing
   `cookLevinLocalBlockQ_rank_ge_of_coeff_diagonal` machinery, and we
   prove the conditional rank lower bound.  The package compiles into
   the same `CookLevinLocalBlockQBridgeAData` interface used at
   `kappa = 1`.

No new axioms are introduced; the kernel-only `[propext, Classical.choice,
Quot.sound]` set is preserved.  No `sorry`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP

attribute [local instance] Classical.dec

/-! ## Section A: structural obstruction for within-block `kappa = 2` rows -/

/-- A length-2 block-admissible row over the actual Cook-Levin locality
partition cannot have both coordinates in the same locality block.

Cook-Levin places three consecutive variables in each locality block, so
the prompt's proposed rows `[a, b]`, `[a, c]`, `[b, c]` (all three
coordinates inside one block of size 3) are simultaneously ruled out by
this lemma. -/
theorem cookLevinLocalBlockQ_kappaTwo_within_block_obstruction
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {S : List (Fin n)}
    (hlen : S.length = 2)
    (hadm :
      isBlockAdmissible
        (cook_levin_compilation M n hn htb hns).partition S)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (hall :
      forall v : Fin n, v ∈ S ->
        (cook_levin_compilation M n hn htb hns).partition.assign v = b) :
    False := by
  have hle :
      (2 : Nat) <= 1 := by
    have :=
      kappa_le_one_of_blockAdmissible_row_supported_in_single_block
        (B := (cook_levin_compilation M n hn htb hns).partition)
        (S := S) (b := b) hlen hadm hall
    simpa using this
  omega

/-- Equivalent set-form statement of the obstruction.  No three distinct
within-block vertices `{a, b, c}` of a single Cook-Levin locality block
yield even one block-admissible length-2 derivative row, let alone three
independent ones. -/
theorem cookLevinLocalBlockQ_within_block_pair_not_admissible
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (a b : Fin n)
    (hab : a ≠ b)
    (hsame :
      (cook_levin_compilation M n hn htb hns).partition.assign a =
      (cook_levin_compilation M n hn htb hns).partition.assign b) :
    ¬ isBlockAdmissible
        (cook_levin_compilation M n hn htb hns).partition [a, b] := by
  intro hadm
  have hlen : ([a, b] : List (Fin n)).length = 2 := by simp
  refine
    cookLevinLocalBlockQ_kappaTwo_within_block_obstruction
      M n hn htb hns hlen hadm
      ((cook_levin_compilation M n hn htb hns).partition.assign a)
      (fun v hv => ?_)
  rcases List.mem_cons.mp hv with rfl | hv'
  · rfl
  · rcases List.mem_singleton.mp hv' with rfl
    exact hsame.symm

/-! ## Section B: cross-block coefficient-diagonal `kappa = 2` package

With the within-block obstruction in hand, the honest `kappa = 2` target
is constructed from two **cross-block** length-2 derivative rows.  Each
row picks one coordinate inside the block of interest and one coordinate
outside it.  Two distinct outside coordinates (in different blocks from
each other and from the inside coordinate's block) give two distinct
cross-block rows, whose linear independence after `mlProj` is the only
remaining mathematical input. -/

/-- The honest cross-block coefficient-diagonal hypothesis at `kappa = 2`
for the real local block product `cookLevinLocalBlockQ`.

We require **two** strict length-2 block-admissible derivative rows
together with monomial probes that diagonalize the projected derivative
rows on those probes.  Once provided, the linear independence criterion
of `BridgeAKappaGeneralBoolRows` plus the generic rank-from-independence
lemma close `kappa = 2` Bridge A on the locality partition. -/
structure CookLevinLocalBlockQKappaTwoCrossBlockDiagonal
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    : Type where
  rows    : Fin 2 -> List (Fin n)
  probe   : Fin 2 -> Fin n →₀ Nat
  diag    : Fin 2 -> Rat
  hlen    : forall r : Fin 2, (rows r).length = 2
  hadm    :
    forall r : Fin 2,
      isBlockAdmissible
        (cook_levin_compilation M n hn htb hns).partition (rows r)
  hdiag_ne : forall r : Fin 2, diag r ≠ 0
  hcoeff  :
    forall r s : Fin 2,
      MvPolynomial.coeff (probe r)
          (mlProj (iterDerivList (rows s)
            (cookLevinLocalBlockQ M n hn htb hns b))) =
        if r = s then diag r else 0

/-- Conditional `kappa = 2` rank lower bound for the real Cook-Levin
local block product, packaged from a cross-block diagonal certificate. -/
theorem cookLevinLocalBlockQ_rank_two_le_of_crossBlockDiagonal
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (data :
      CookLevinLocalBlockQKappaTwoCrossBlockDiagonal
        M n hn htb hns b) :
    (2 : Nat) <=
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        2 2
        (cookLevinLocalBlockQ M n hn htb hns b) := by
  exact
    cookLevinLocalBlockQ_rank_ge_of_coeff_diagonal
      M n hn htb hns 2 2 b
      data.rows data.hlen data.hadm
      data.probe data.diag data.hdiag_ne data.hcoeff

/-! ## Section C: energy-to-rank `kappa = 2` package -/

/-- Energy-to-rank form of the `kappa = 2` Bridge A target for the real
Cook-Levin local block product, conditional on a cross-block diagonal
certificate at every selected compiler block. -/
theorem cookLevinLocalBlockQEnergyToRankTarget_two_of_crossBlockDiagonal
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (blockOfVertex :
      Fin N -> Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (data :
      forall v : Fin N,
        CookLevinLocalBlockQKappaTwoCrossBlockDiagonal
          M n hn htb hns (blockOfVertex v)) :
    CookLevinLocalBlockQEnergyToRankTarget
      M n hn htb hns alpha beta alpha0 2 G chi Phi blockOfVertex := by
  intro v _henergy
  exact
    cookLevinLocalBlockQ_rank_two_le_of_crossBlockDiagonal
      M n hn htb hns (blockOfVertex v) (data v)

/-- Packaged `kappa = 2` Bridge A data for the real Cook-Levin local
block product, conditional on a per-vertex cross-block diagonal
certificate. -/
noncomputable def cookLevinLocalBlockQBridgeAData_two_of_crossBlockDiagonal
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (blockOfVertex :
      Fin N -> Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (data :
      forall v : Fin N,
        CookLevinLocalBlockQKappaTwoCrossBlockDiagonal
          M n hn htb hns (blockOfVertex v)) :
    CookLevinLocalBlockQBridgeAData
      M n hn htb hns alpha beta alpha0 2 G chi Phi where
  blockOfVertex := blockOfVertex
  energy_to_spdpRank :=
    cookLevinLocalBlockQEnergyToRankTarget_two_of_crossBlockDiagonal
      M n hn htb hns alpha beta alpha0 G chi Phi blockOfVertex data

/-! ## Section D: the support obstruction at `kappa = 2`

Beyond block admissibility, a second necessary condition for `kappa = 2`
is that the local block polynomial actually exposes at least two distinct
variables.  This is automatic on the real compiler product when the
locality block sits inside the variable range, but we record the sharp
obstruction here. -/

/-- If the real local block product exposes fewer than two variables, the
strict `kappa = 2` rank vanishes — independent of any diagonal data. -/
theorem cookLevinLocalBlockQ_rank_two_eq_zero_of_vars_card_lt_two
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (hvars :
      (cookLevinLocalBlockQ M n hn htb hns b).vars.card < 2) :
    mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        2 2
        (cookLevinLocalBlockQ M n hn htb hns b) = 0 :=
  cookLevinLocalBlockQ_rank_eq_zero_of_vars_card_lt_kappa
    M n hn htb hns 2 2 b hvars

/-- Therefore the `kappa = 2` lower bound is impossible whenever the real
local block exposes fewer than two variables — this is the
support-cardinality companion to the within-block obstruction. -/
theorem not_cookLevinLocalBlockQ_rank_two_le_of_vars_card_lt_two
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (hvars :
      (cookLevinLocalBlockQ M n hn htb hns b).vars.card < 2) :
    ¬ (2 : Nat) <=
        mlBlockedSpdpRank
          (cook_levin_compilation M n hn htb hns).partition
          2 2
          (cookLevinLocalBlockQ M n hn htb hns b) := by
  intro hge
  rw [cookLevinLocalBlockQ_rank_two_eq_zero_of_vars_card_lt_two
        M n hn htb hns b hvars] at hge
  omega

/-! ## Axiom audit anchors -/

#print axioms cookLevinLocalBlockQ_kappaTwo_within_block_obstruction
#print axioms cookLevinLocalBlockQ_within_block_pair_not_admissible
#print axioms cookLevinLocalBlockQ_rank_two_le_of_crossBlockDiagonal
#print axioms cookLevinLocalBlockQEnergyToRankTarget_two_of_crossBlockDiagonal
#print axioms cookLevinLocalBlockQBridgeAData_two_of_crossBlockDiagonal
#print axioms cookLevinLocalBlockQ_rank_two_eq_zero_of_vars_card_lt_two
#print axioms not_cookLevinLocalBlockQ_rank_two_le_of_vars_card_lt_two

end PallLean.Paper93.Paper283
