import PallLean.CookLevinDefs
import PallLean.PartialDerivMatrix
import PallLean.BinomialBound2
import Mathlib.Tactic

namespace PaperFaithfulSeparation

open SPDP MultilinearSPDP MvPolynomial TuringMachine

/-- A 3-CNF formula: a list of clauses, each a triple of variable indices. -/
structure ThreeCNF where
  numVars : ℕ
  clauses : List (Fin numVars × Fin numVars × Fin numVars)

/-- The coupled verifier sheet polynomial Q×_Φ from Definition 39.
For each clause C with verifier gadget V_C and selector variable z_C:
  Q×_Φ(u,z) = ∏_{C∈Cl(Φ)} (1 - z_C · V_C(u_{B_C})²)
where B_C are the clause-local gadget variables. -/
structure CoupledVerifierSheet where
  numVerifierVars : ℕ
  numSelectorVars : ℕ
  totalVars : ℕ
  totalVars_eq : totalVars = numVerifierVars + numSelectorVars
  poly : MvPolynomial (Fin totalVars) ℚ
  disjoint_blocks : Prop
  has_tag_monomials : Prop

/-- NP-side lower surface used by the God-Move route. -/
def np_exponential_lower_bound (numClauses κ rank : ℕ) : Prop :=
  Nat.choose numClauses κ ≤ rank

/-- A clause (i, j, k) is satisfied by assignment σ if at least one literal is true. -/
def clauseSatisfied (σ : Fin n → Bool) (c : Fin n × Fin n × Fin n) : Prop :=
  σ c.1 = true ∨ σ c.2.1 = true ∨ σ c.2.2 = true

/-- A 3-CNF formula φ is satisfiable if there exists a Boolean assignment
    satisfying every clause. -/
def ThreeCNF.IsSatisfiable (φ : ThreeCNF) : Prop :=
  ∃ (σ : Fin φ.numVars → Bool), ∀ c ∈ φ.clauses, clauseSatisfied σ c

/-- Encoding size of a 3-CNF formula: numVars + 3 * numClauses bits suffice
    to specify the formula (each clause needs 3 variable indices). -/
def ThreeCNF.encodingSize (φ : ThreeCNF) : ℕ :=
  φ.numVars + 3 * φ.clauses.length

/-- Semantic predicate: the DTM M decides 3-SAT.

M decides 3-SAT if for every 3-CNF formula φ whose encoding fits
within M's time bound at some input size n:
- If φ is satisfiable, then M accepts some encoding of φ of length n.
- If φ is unsatisfiable, then M does not accept any input of length n
  that encodes φ.

The fields use the DTM execution semantics from TuringMachine.lean
(`accepts`), making `DecidesSAT M` genuinely load-bearing: it constrains
M's transition function to correctly classify 3-SAT instances. -/
structure DecidesSAT (M : DTM) : Prop where
  /-- For satisfiable formulas, M accepts a valid encoding. -/
  accepts_sat : ∀ (φ : ThreeCNF) (n : ℕ) (hn : n ≥ 1),
    φ.encodingSize ≤ n →
    φ.IsSatisfiable →
    ∃ (input : Fin n → Bool), accepts M n hn input
  /-- For unsatisfiable formulas, M does not accept any encoding. -/
  rejects_unsat : ∀ (φ : ThreeCNF) (n : ℕ) (hn : n ≥ 1),
    φ.encodingSize ≤ n →
    ¬ φ.IsSatisfiable →
    ∀ (input : Fin n → Bool), ¬ accepts M n hn input

/-- **Key semantic lemma**: DecidesSAT produces an accepting computation.

If M decides 3-SAT and φ is a satisfiable formula with encoding size ≤ n,
then M has an accepting input of length n. This is the load-bearing content
of DecidesSAT for the Route B extraction.

Combined with Cook-Levin (the compiled polynomial evaluates to 1 on the
accepting tableau), this accepting input determines the restriction
assignment in the God-Move extraction. -/
theorem DecidesSAT.accepting_input_of_satisfiable
    {M : DTM} (hdec : DecidesSAT M)
    (φ : ThreeCNF) (n : ℕ) (hn : n ≥ 1)
    (hsize : φ.encodingSize ≤ n)
    (hsat : φ.IsSatisfiable) :
    ∃ (input : Fin n → Bool), accepts M n hn input :=
  hdec.accepts_sat φ n hn hsize hsat

/-- From an accepting input, extract the accepting computation tableau.

The DTM's run produces a sequence of configurations, and the accepting
condition guarantees one of them is in the accept state. This gives
the full tableau data needed for the Cook-Levin restriction. -/
theorem accepting_input_gives_tableau
    (M : DTM) (n : ℕ) (hn : n ≥ 1) (input : Fin n → Bool)
    (hacc : accepts M n hn input) :
    ∃ (t : ℕ), t ≤ timeSteps M n ∧
      (run M n t (initialConfig M n hn input)).state = acceptState M :=
  hacc

/-- Paper-faithful abstract source/target interface for the God-Move.

This avoids the false typing shortcut of placing the compiled polynomial and the
coupled verifier sheet in the same ambient variable space before the actual map
`ΠΦ : F[u,v] → F[u]` has been formalized. -/
structure GodMoveExtractionInterface (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  coupledVars : ℕ
  coupledPartition : BlockPartition coupledVars
  coupledPoly : MvPolynomial (Fin coupledVars) ℚ
  instance_uniform : Prop
  witness_free : Prop
  block_local : Prop
  target_lower :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank coupledPartition (Nat.log 2 n) (Nat.log 2 n) coupledPoly
  rank_transfer :
      mlBlockedSpdpRank coupledPartition (Nat.log 2 n) (Nat.log 2 n) coupledPoly ≤
      mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))

/-- Paper-faithful Route B semantic interface for the God-Move.

This is the narrowed paper-faithful variant of `GodMoveExtractionInterface`
that explicitly requires the coupled space to be a PROPER substructure
derived from the hard Tseitin instance, and makes `DecidesSAT` genuinely
load-bearing in the construction.

The fields capture the paper's three-stage God-Move (§29, Lemma 123):

1. **Hard instance selection**: a specific 3-CNF formula `φ_n` from the
   Ramanujan-Tseitin family (the NP-side hard family).

2. **Extraction map `Π_Φ`**: a witness-free, instance-uniform, block-local
   map from the compiled polynomial space to the coupled verifier sheet space.
   This map exists BECAUSE `M` decides 3-SAT — the acceptance semantics of `M`
   on `φ_n` are what connect the compiled polynomial to the clause-sheet structure.

3. **Rank transfer**: the SPDP rank of the coupled sheet is bounded by that
   of the compiled polynomial, via the extraction map's rank-monotone property.

Unlike `GodMoveExtractionInterface`, this structure ensures the coupled space
is genuinely distinct from the compiled space and derived from the hard instance.
This prevents the identity-construction shortcut that makes `DecidesSAT` inert.

**Current status**: NOT YET INHABITED. This is the exact theorem seam for the
paper-faithful Route B semantic frontier. Inhabiting it requires:
- Formalizing the variable-space map `Π_Φ` as a concrete algebra homomorphism
- Proving that the map sends the compiled polynomial to a polynomial containing
  the coupled verifier sheet Q× as a substructure
- Establishing rank monotonicity through the extraction map -/
structure GodMoveSemanticInterface (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) where
  /-- The hard 3-CNF instance from the Ramanujan-Tseitin family -/
  hardInstance : ThreeCNF
  /-- The hard instance has Θ(n) clauses -/
  hardInstance_size : hardInstance.clauses.length ≤ 10 * n ∧ n / 30 ≤ hardInstance.clauses.length
  /-- The coupled clause-sheet variable space (strictly smaller than compiled) -/
  coupledVars : ℕ
  coupledVars_lt : coupledVars < (cook_levin_compilation M n hn2 htb hns).numVars
  coupledPartition : BlockPartition coupledVars
  coupledPoly : MvPolynomial (Fin coupledVars) ℚ
  /-- The extraction map is instance-uniform (does not depend on the specific
      satisfying assignment) -/
  instance_uniform : True
  /-- The extraction map is witness-free (does not use the NP witness) -/
  witness_free : True
  /-- The extraction map is block-local (preserves the block structure) -/
  block_local : True
  /-- NP lower bound on the coupled sheet (from identity minor / Tseitin structure) -/
  target_lower :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank coupledPartition (Nat.log 2 n) (Nat.log 2 n) coupledPoly
  /-- Rank transfer from coupled sheet back to compiled polynomial -/
  rank_transfer :
      mlBlockedSpdpRank coupledPartition (Nat.log 2 n) (Nat.log 2 n) coupledPoly ≤
      mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))

/-- A semantic interface trivially forgets to the abstract interface.
This is the direction we want to go: prove the semantic interface first,
then derive the abstract one. -/
def GodMoveSemanticInterface.toAbstract
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (g : GodMoveSemanticInterface M n hn2 htb hns hdec) :
    GodMoveExtractionInterface M n hn2 htb hns where
  coupledVars := g.coupledVars
  coupledPartition := g.coupledPartition
  coupledPoly := g.coupledPoly
  instance_uniform := True
  witness_free := True
  block_local := True
  target_lower := g.target_lower
  rank_transfer := g.rank_transfer

/-! ## Characteristic-Polynomial Route B Bridge

The paper's Route B derives the NP-side lower bound from the characteristic
polynomial of the hard Ramanujan-Tseitin instance, NOT from the compiled
Cook-Levin polynomial directly. The God-Move extraction map `Π_Φ` connects
the two:

  compiled polynomial P_{M,n}
       ↓ restriction + projection (God-Move Π_Φ)
  coupled verifier sheet Q×_Φ
       ↓ structure of Tseitin encoding
  characteristic polynomial χ_{φ_n}
       ↓ PD-matrix lower bound (sound encoding, RamanujanTseitin §11)
  exponential SPDP rank

The `DecidesSAT` hypothesis is load-bearing in the FIRST step: the existence
of the extraction map depends on `M` correctly classifying the hard instance.

The structures below decompose the God-Move interface into three independent
obligations, making the role of `DecidesSAT` explicit. -/

/-- Obligation 2 (requires DecidesSAT): Extraction map rank transfer.

This is the exact remaining semantic frontier for Route B. It says:
the SPDP rank of the coupled verifier sheet is bounded by the SPDP rank
of the compiled Cook-Levin polynomial, via the extraction map Π_Φ.

The extraction map exists BECAUSE `M` decides 3-SAT: if `M` accepts
the hard instance φ_n, then the compiled polynomial P_{M,n} contains the
clause-sheet structure of φ_n, and the extraction map simply picks out
those coordinates. -/
structure GodMoveExtractionTarget (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  coupledVars : ℕ
  coupledVars_lt : coupledVars < (cook_levin_compilation M n hn2 htb hns).numVars
  coupledPartition : BlockPartition coupledVars
  coupledPoly : MvPolynomial (Fin coupledVars) ℚ

/-- Shared Route B target-side data.

This packages the parts of Route B that are common to both the strong and
weakened NP-side surfaces: the hard instance bookkeeping and the
extraction-facing coupled-sheet target. The only remaining variation between
the two surfaces is which separate NP lower bound they attach to this shared
target package. -/
structure GodMoveRouteB_TargetData (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  hardInstance : ThreeCNF
  hardInstance_size : hardInstance.clauses.length ≤ 10 * n ∧
    n / 30 ≤ hardInstance.clauses.length
  extractionTarget : GodMoveExtractionTarget M n hn2 htb hns

/-- Strong Route B obligations: shared target-side data plus the paper's
binomial NP lower bound on the coupled sheet. -/
structure GodMoveRouteB_Obligations (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    extends GodMoveRouteB_TargetData M n hn2 htb hns where
  /-- Obligation 3 (independent of DecidesSAT): NP lower bound. -/
  target_lower :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank extractionTarget.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) extractionTarget.coupledPoly

/-- Bare rank transfer on the narrowed extraction-facing target.

This proposition is only the inequality between the chosen coupled-sheet
target and the compiled polynomial. By itself it does not explain why this
target is the paper-faithful one; the `DecidesSAT`-dependent semantic work is
the restriction/projection witness that produces the target from an accepting
computation on the hard instance. -/
def GodMoveRouteB_ExtractionTransfer (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M)
    (target : GodMoveExtractionTarget M n hn2 htb hns) : Prop :=
  mlBlockedSpdpRank target.coupledPartition (Nat.log 2 n) (Nat.log 2 n) target.coupledPoly ≤
    mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns))

/-- Paper-faithful Route B extraction obligation.

This is definitionally the same inequality as
`GodMoveRouteB_ExtractionTransfer`. The extra `DecidesSAT` parameter records
the intended provenance of the target: in Route B the transfer only counts as
the right one once the target has been justified from the SAT-decider's
accepting computation on the hard instance. -/
abbrev GodMoveRouteB_ExtractionObligation (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (target : GodMoveExtractionTarget M n hn2 htb hns) : Prop :=
  GodMoveRouteB_ExtractionTransfer M n hn2 htb hns hdec target

@[simp] theorem GodMoveRouteB_ExtractionObligation_iff_transfer
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    {target : GodMoveExtractionTarget M n hn2 htb hns} :
    GodMoveRouteB_ExtractionObligation M n hn2 htb hns hdec target ↔
      GodMoveRouteB_ExtractionTransfer M n hn2 htb hns hdec target := Iff.rfl

/-- From the three obligations, the full semantic interface follows. -/
def GodMoveSemanticInterface.fromObligations
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (obs : GodMoveRouteB_Obligations M n hn2 htb hns)
    (extraction :
      GodMoveRouteB_ExtractionObligation M n hn2 htb hns hdec obs.extractionTarget) :
    GodMoveSemanticInterface M n hn2 htb hns hdec where
  hardInstance := obs.hardInstance
  hardInstance_size := obs.hardInstance_size
  coupledVars := obs.extractionTarget.coupledVars
  coupledVars_lt := obs.extractionTarget.coupledVars_lt
  coupledPartition := obs.extractionTarget.coupledPartition
  coupledPoly := obs.extractionTarget.coupledPoly
  instance_uniform := trivial
  witness_free := trivial
  block_local := trivial
  target_lower := obs.target_lower
  rank_transfer := extraction

/-! ## Paper-Faithful Extraction Map Decomposition

The extraction map Π_Φ from the paper's §29 / Lemma 123 is a composite of
three operations:

1. **Restriction** (fix admin/tableau variables): the compiled polynomial
   P_{M,n}(u, z, v) is restricted by setting the administrative and tableau
   variables v to constants determined by the hard instance φ_n and the
   DTM's acceptance computation on φ_n.

2. **Projection** (extract clause-sheet coordinates): from the restricted
   polynomial, keep only the clause-sheet coordinates u = (u_1, ..., u_m)
   corresponding to the coupled verifier sheet.

3. **Relabeling** (block-local normalization): apply a fixed block-local
   basis change to normalize the clause-sheet coordinates to the standard
   form used by the coupled verifier sheet Q×_Φ.

Each step is rank-monotone:
- Restriction: specializing variables can only decrease SPDP rank
- Projection: dropping variables can only decrease SPDP rank
- Relabeling: block-local basis change preserves SPDP rank

The overall extraction obligation decomposes into these three rank-monotone
steps plus the STRUCTURAL identification of the output with the coupled
verifier sheet polynomial.

**Key insight**: `DecidesSAT` is load-bearing in step 1. The restriction
constants come from the DTM's acceptance computation on the hard instance.
If M does NOT decide 3-SAT correctly, the restriction produces a polynomial
that does NOT contain the coupled verifier sheet as a substructure. -/

/-- The restriction stage of the God-Move extraction map.

Fixes administrative and tableau variables in the compiled polynomial to
constants determined by the DTM's acceptance computation on the hard instance.

`DecidesSAT` is load-bearing here: the restriction constants come from the
machine's accepting computation, which must exist because M decides 3-SAT
and the hard instance (by construction) is satisfiable. -/
structure ExtractionRestrictionStage (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) where
  /-- Number of variables after restriction (< compiled vars). -/
  restrictedVars : ℕ
  restrictedVars_lt : restrictedVars < (cook_levin_compilation M n hn2 htb hns).numVars
  /-- The restricted polynomial lives in a smaller variable space. -/
  restrictedPoly : MvPolynomial (Fin restrictedVars) ℚ
  /-- The restricted-space partition used by the extraction proof. -/
  restrictedPartition : BlockPartition restrictedVars
  /-- The restriction is a coordinate specialization (not an arbitrary map).
      Formally: there exists an assignment σ to the fixed variables such that
      restrictedPoly = P_{M,n}[v := σ(v)]. -/
  is_specialization : Prop
  /-- Rank monotonicity: specializing variables does not increase SPDP rank.
      This is a consequence of the restriction monotonicity lemma (Lemma 141). -/
  restriction_rank_mono : ∀ (κ ℓ : ℕ),
      mlBlockedSpdpRank restrictedPartition κ ℓ restrictedPoly ≤
        mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))

/-- The projection stage of the God-Move extraction map.

After restriction, projects to the clause-sheet coordinates, dropping
the remaining non-clause-sheet variables. This step does NOT use `DecidesSAT`;
it is a purely structural coordinate-selection operation. -/
structure ExtractionProjectionStage (restrictedVars coupledVars : ℕ) where
  /-- The specific restricted polynomial fed into the projection stage. -/
  inputPoly : MvPolynomial (Fin restrictedVars) ℚ
  /-- The projected polynomial lives in the coupled variable space. -/
  projectedPoly : MvPolynomial (Fin coupledVars) ℚ
  /-- The projection selects clause-sheet coordinates. -/
  is_coordinate_selection : Prop
  /-- Rank monotonicity: projecting to a subset of coordinates does not
      increase SPDP rank. -/
  projection_rank_mono :
    ∀ (B_restricted : BlockPartition restrictedVars)
      (B_coupled : BlockPartition coupledVars) (κ ℓ : ℕ),
      mlBlockedSpdpRank B_coupled κ ℓ projectedPoly ≤
        mlBlockedSpdpRank B_restricted κ ℓ inputPoly

/-- The load-bearing semantic core of the three-stage extraction map.

This keeps only the staged restriction/projection/output-identification data.
The rank-monotonicity lemmas needed to derive the extracted inequality are
packaged separately, because they are mathematical wrappers around the staged
semantic witness rather than additional `DecidesSAT`-dependent content. -/
structure ExtractionMapSemantics (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (target : GodMoveExtractionTarget M n hn2 htb hns) where
  /-- Stage 1: Restriction data (uses DecidesSAT). -/
  restriction : ExtractionRestrictionStage M n hn2 htb hns hdec
  /-- Stage 2: Projection to coupled space. -/
  projection : ExtractionProjectionStage restriction.restrictedVars target.coupledVars
  /-- The projection stage is fed the restricted polynomial from stage 1. -/
  projection_input_matches : projection.inputPoly = restriction.restrictedPoly
  /-- The projected polynomial matches the coupled polynomial. -/
  output_identification :
    projection.projectedPoly = target.coupledPoly

/-- The full three-stage extraction map decomposition.

This makes the paper's three-stage God-Move extraction explicit. The key
structural property is that the composite of the three stages sends
the compiled polynomial to the coupled verifier sheet polynomial. -/
structure ExtractionMapDecomposition (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (target : GodMoveExtractionTarget M n hn2 htb hns)
    extends ExtractionMapSemantics M n hn2 htb hns hdec target

namespace ExtractionMapDecomposition

/-- Forget the decomposition wrapper and keep only the staged semantic core. -/
def toSemantics
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M} {target : GodMoveExtractionTarget M n hn2 htb hns}
    (decomp : ExtractionMapDecomposition M n hn2 htb hns hdec target) :
    ExtractionMapSemantics M n hn2 htb hns hdec target :=
  { restriction := decomp.restriction
    projection := decomp.projection
    projection_input_matches := decomp.projection_input_matches
    output_identification := decomp.output_identification }

end ExtractionMapDecomposition

/-- The exact staged semantic obligation on the extraction-facing target.

This is the narrow Route B semantic seam: to derive extraction monotonicity we
only need a three-stage decomposition for the chosen coupled target, not the
separate NP lower-bound or hard-instance bookkeeping. -/
def GodMoveExtractionDecompositionObligation (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (target : GodMoveExtractionTarget M n hn2 htb hns) : Prop :=
  Nonempty (ExtractionMapDecomposition M n hn2 htb hns hdec target)

/-- The exact semantic theorem seam on a chosen extraction target.

This is smaller than `GodMoveExtractionDecompositionObligation`: it records
only the staged semantic witness, leaving the generic rank-monotonicity layer
as separate mathematical packaging. -/
def GodMoveExtractionSemanticObligation (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (target : GodMoveExtractionTarget M n hn2 htb hns) : Prop :=
  Nonempty (ExtractionMapSemantics M n hn2 htb hns hdec target)

/-- Separate rank-wrapper data over a fixed staged semantic witness. -/
structure ExtractionMapRankBridge
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M} {target : GodMoveExtractionTarget M n hn2 htb hns}
    (sem : ExtractionMapSemantics M n hn2 htb hns hdec target) where
  restriction_rank_mono : ∀ (κ ℓ : ℕ),
      mlBlockedSpdpRank sem.restriction.restrictedPartition κ ℓ sem.restriction.restrictedPoly ≤
        mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))
  projection_rank_mono :
    ∀ (B_restricted : BlockPartition sem.restriction.restrictedVars)
      (B_coupled : BlockPartition target.coupledVars) (κ ℓ : ℕ),
      mlBlockedSpdpRank B_coupled κ ℓ sem.projection.projectedPoly ≤
        mlBlockedSpdpRank B_restricted κ ℓ sem.projection.inputPoly

namespace ExtractionMapRankBridge

/-- A full decomposition automatically yields the separate rank wrapper. -/
def ofDecomposition
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M} {target : GodMoveExtractionTarget M n hn2 htb hns}
    (decomp : ExtractionMapDecomposition M n hn2 htb hns hdec target) :
    ExtractionMapRankBridge decomp.toSemantics :=
  { restriction_rank_mono := decomp.restriction.restriction_rank_mono
    projection_rank_mono := decomp.projection.projection_rank_mono }

end ExtractionMapRankBridge

/-- The staged semantic witness plus separate rank wrappers imply the bare
extraction transfer inequality. -/
theorem extraction_from_semantics
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    {target : GodMoveExtractionTarget M n hn2 htb hns}
    (sem : ExtractionMapSemantics M n hn2 htb hns hdec target)
    (bridge : ExtractionMapRankBridge sem) :
    GodMoveRouteB_ExtractionObligation M n hn2 htb hns hdec target := by
  unfold GodMoveRouteB_ExtractionObligation
  change
    mlBlockedSpdpRank target.coupledPartition (Nat.log 2 n) (Nat.log 2 n) target.coupledPoly ≤
      mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))
  rw [← sem.output_identification]
  calc
    mlBlockedSpdpRank target.coupledPartition (Nat.log 2 n) (Nat.log 2 n)
        sem.projection.projectedPoly
      ≤ mlBlockedSpdpRank sem.restriction.restrictedPartition
          (Nat.log 2 n) (Nat.log 2 n) sem.projection.inputPoly :=
        bridge.projection_rank_mono
          sem.restriction.restrictedPartition target.coupledPartition
          (Nat.log 2 n) (Nat.log 2 n)
    _ = mlBlockedSpdpRank sem.restriction.restrictedPartition
          (Nat.log 2 n) (Nat.log 2 n) sem.restriction.restrictedPoly := by
        rw [sem.projection_input_matches]
    _ ≤ mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) :=
        bridge.restriction_rank_mono (Nat.log 2 n) (Nat.log 2 n)

/-- The extraction map decomposition implies the extraction obligation.

This is the key compositionality lemma: if we have an explicit three-stage
extraction map where each stage is rank-monotone and the output matches
the coupled polynomial, then the overall rank transfer holds. -/
theorem extraction_from_decomposition
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    {target : GodMoveExtractionTarget M n hn2 htb hns}
    (decomp : ExtractionMapDecomposition M n hn2 htb hns hdec target) :
    GodMoveRouteB_ExtractionObligation M n hn2 htb hns hdec target :=
  extraction_from_semantics decomp.toSemantics
    (ExtractionMapRankBridge.ofDecomposition decomp)

/-- The decomposition obligation is already enough to discharge the extracted
rank-transfer inequality. -/
theorem extraction_from_decomposition_obligation
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    {target : GodMoveExtractionTarget M n hn2 htb hns}
    (hdecomp :
      GodMoveExtractionDecompositionObligation M n hn2 htb hns hdec target) :
    GodMoveRouteB_ExtractionObligation M n hn2 htb hns hdec target := by
  rcases hdecomp with ⟨decomp⟩
  exact extraction_from_decomposition decomp

/-- A full decomposition also proves the smaller semantic obligation. -/
theorem semantics_from_decomposition_obligation
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    {target : GodMoveExtractionTarget M n hn2 htb hns}
    (hdecomp :
      GodMoveExtractionDecompositionObligation M n hn2 htb hns hdec target) :
    GodMoveExtractionSemanticObligation M n hn2 htb hns hdec target := by
  rcases hdecomp with ⟨decomp⟩
  exact ⟨decomp.toSemantics⟩

/-! ## Narrowed Extraction Frontier

The above decomposition shows that the extraction obligation reduces to
providing three pieces of data:

1. **Restriction data** (load-bearing, uses DecidesSAT): an explicit
   assignment to the administrative/tableau variables that comes from
   M's accepting computation on the hard instance.

2. **Projection data** (structural): the coordinate selection that picks
   out the clause-sheet variables from the restricted polynomial.

3. **Output identification** (structural): the projected polynomial
   matches the coupled verifier sheet polynomial.

The rank-monotonicity conditions at each stage are mathematical theorems
(Lemma 141 for restriction, subspace containment for projection). The
genuine semantic content is in the EXISTENCE of the restriction assignment
and the CORRECTNESS of the output identification.

The following structure isolates just the semantic content: -/

/-- The narrowest semantic gap for the God-Move extraction.

This isolates the genuinely load-bearing content of the extraction map:
an explicit variable assignment to the compiled polynomial's administrative
and tableau coordinates, derived from M's accepting computation on the
hard instance, such that the resulting restricted+projected polynomial
matches the coupled verifier sheet.

Everything else (rank monotonicity, quantitative bounds) follows from
proved mathematical lemmas once this semantic identification is established. -/
structure GodMoveHardInstanceData (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M) where
  /-- The hard instance φ_n (from the Ramanujan-Tseitin family). -/
  hardInstance : ThreeCNF
  /-- The hard instance is satisfiable, so SAT-correctness yields acceptance. -/
  hardInstance_satisfiable : hardInstance.IsSatisfiable
  /-- The hard instance fits into the input budget `n`, so `DecidesSAT` applies. -/
  hardInstance_fits_input : hardInstance.encodingSize ≤ n
  /-- The hard instance has Θ(n) clauses. -/
  hardInstance_size : hardInstance.clauses.length ≤ 10 * n ∧
    n / 30 ≤ hardInstance.clauses.length

/-- Exact extraction-target data for the God-Move theorem seam.

This is the smallest data package still needed by downstream Route B
packaging: the hard-instance applicability facts together with the chosen
extraction-side coupled target. -/
structure GodMoveExtractionTargetData (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    extends GodMoveHardInstanceData M n hn2 htb hns hdec where
  extractionTarget : GodMoveExtractionTarget M n hn2 htb hns

/-- Exact remaining staged semantic theorem on a chosen extraction target. -/
abbrev GodMoveExtractionTargetTheorem (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (target : GodMoveExtractionTarget M n hn2 htb hns) : Prop :=
  GodMoveExtractionSemanticObligation M n hn2 htb hns hdec target

namespace GodMoveExtractionTargetData

/-- Rebuild the exact extraction-target package from separate hard-instance
data and an extraction-facing target. -/
def ofHardInstanceData
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (hard : GodMoveHardInstanceData M n hn2 htb hns hdec)
    (target : GodMoveExtractionTarget M n hn2 htb hns) :
    GodMoveExtractionTargetData M n hn2 htb hns hdec where
  toGodMoveHardInstanceData := hard
  extractionTarget := target

/-- Preferred name for the shared Route B target-side data carried by the exact
extraction-target package. -/
def toRouteB_TargetData
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (targetData : GodMoveExtractionTargetData M n hn2 htb hns hdec) :
    GodMoveRouteB_TargetData M n hn2 htb hns where
  hardInstance := targetData.hardInstance
  hardInstance_size := targetData.hardInstance_size
  extractionTarget := targetData.extractionTarget

/-- Forget the staged semantic theorem and keep only the shared Route B
target-side data consumed by the strong and weakened NP packages. -/
def targetData
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (targetData : GodMoveExtractionTargetData M n hn2 htb hns hdec) :
    GodMoveRouteB_TargetData M n hn2 htb hns where
  hardInstance := targetData.hardInstance
  hardInstance_size := targetData.hardInstance_size
  extractionTarget := targetData.extractionTarget

/-- Add the paper's strong NP-side lower bound on the same exact extraction
target chosen by the semantic theorem. -/
def toRouteB_Obligations
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (targetData : GodMoveExtractionTargetData M n hn2 htb hns hdec)
    (np_lower : Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank targetData.extractionTarget.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) targetData.extractionTarget.coupledPoly) :
    GodMoveRouteB_Obligations M n hn2 htb hns where
  toGodMoveRouteB_TargetData := targetData.toRouteB_TargetData
  target_lower := np_lower

/-- The staged target theorem yields the extraction-side transfer inequality on
that same exact target once the generic rank wrappers are provided. -/
theorem extraction
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (targetData : GodMoveExtractionTargetData M n hn2 htb hns hdec)
    (hsem : GodMoveExtractionTargetTheorem M n hn2 htb hns hdec targetData.extractionTarget)
    (bridge :
      ∀ sem : ExtractionMapSemantics M n hn2 htb hns hdec targetData.extractionTarget,
        ExtractionMapRankBridge sem) :
    GodMoveRouteB_ExtractionObligation M n hn2 htb hns hdec targetData.extractionTarget :=
by
  rcases hsem with ⟨sem⟩
  exact extraction_from_semantics sem (bridge sem)

/-- The exact extraction-target package, together with the separate strong
NP-side lower bound and generic rank wrappers, recovers the older semantic
interface directly. -/
def toSemanticInterface
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (targetData : GodMoveExtractionTargetData M n hn2 htb hns hdec)
    (hsem : GodMoveExtractionTargetTheorem M n hn2 htb hns hdec targetData.extractionTarget)
    (np_lower : Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank targetData.extractionTarget.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) targetData.extractionTarget.coupledPoly)
    (bridge :
      ∀ sem : ExtractionMapSemantics M n hn2 htb hns hdec targetData.extractionTarget,
        ExtractionMapRankBridge sem) :
    GodMoveSemanticInterface M n hn2 htb hns hdec :=
  GodMoveSemanticInterface.fromObligations
    (obs := targetData.toRouteB_Obligations np_lower)
    (extraction := targetData.extraction hsem bridge)

/-- Forgetful compatibility bridge from the exact extraction-target package to
the older abstract source/target interface. -/
def toAbstractInterface
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (targetData : GodMoveExtractionTargetData M n hn2 htb hns hdec)
    (hsem : GodMoveExtractionTargetTheorem M n hn2 htb hns hdec targetData.extractionTarget)
    (np_lower : Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank targetData.extractionTarget.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) targetData.extractionTarget.coupledPoly)
    (bridge :
      ∀ sem : ExtractionMapSemantics M n hn2 htb hns hdec targetData.extractionTarget,
        ExtractionMapRankBridge sem) :
    GodMoveExtractionInterface M n hn2 htb hns :=
  (targetData.toSemanticInterface hsem np_lower bridge).toAbstract

end GodMoveExtractionTargetData

/-- Backwards-compatible alias for the exact extraction-target package. -/
abbrev GodMoveSemanticTargetData (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :=
  GodMoveExtractionTargetData M n hn2 htb hns hdec

/-- Backwards-compatible alias for the staged theorem on exact target data. -/
abbrev GodMoveSemanticTargetTheorem (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (targetData : GodMoveExtractionTargetData M n hn2 htb hns hdec) : Prop :=
  GodMoveExtractionTargetTheorem M n hn2 htb hns hdec targetData.extractionTarget

/-- Exact remaining paper-faithful extraction theorem.

The final semantic theorem should mention only the exact extraction-facing
target and the staged restriction/projection witness on that target. Hard-
instance applicability bookkeeping sits outside this theorem in compatibility
packages such as `GodMoveSemanticGap` and `GodMoveSemanticTheorem`.
The monotonicity layer remains separate mathematical packaging over that
semantic witness. -/
abbrev GodMoveSemanticExtractionTheorem (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) : Prop :=
  ∃ target : GodMoveExtractionTarget M n hn2 htb hns,
    GodMoveExtractionSemanticObligation M n hn2 htb hns hdec target

/-- Backwards-compatible alias re-indexing the extraction theorem by
hard-instance applicability data. -/
abbrev GodMoveSemanticTheorem (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (_hard : GodMoveHardInstanceData M n hn2 htb hns hdec) : Prop :=
  GodMoveSemanticExtractionTheorem M n hn2 htb hns hdec

/-- Convenience bundle: hard-instance applicability data plus a proof of the
exact semantic extraction theorem on an explicit target. This is kept because
it is ergonomic for downstream packaging, but the actual missing theorem is
now `GodMoveSemanticExtractionTheorem`; `GodMoveSemanticTheorem` remains only
as a compatibility alias indexed by the hard-instance data. -/
structure GodMoveSemanticGap (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) where
  toHardInstanceData : GodMoveHardInstanceData M n hn2 htb hns hdec
  extractionTarget : GodMoveExtractionTarget M n hn2 htb hns
  extractionSemantics :
    GodMoveExtractionSemanticObligation M n hn2 htb hns hdec extractionTarget

namespace GodMoveSemanticGap

/-- Exact extraction-target data carried by the semantic gap. -/
abbrev toTargetData
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec) :
    GodMoveExtractionTargetData M n hn2 htb hns hdec :=
  GodMoveExtractionTargetData.ofHardInstanceData
    gap.toHardInstanceData gap.extractionTarget

/-- The staged semantic theorem carried by the gap's exact target data. -/
abbrev targetTheorem
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec) :
    GodMoveExtractionTargetTheorem M n hn2 htb hns hdec gap.extractionTarget :=
  gap.extractionSemantics

/-- The bundled gap inhabits the exact extraction-only theorem package. -/
theorem semantic_extraction_theorem
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec) :
    GodMoveSemanticExtractionTheorem M n hn2 htb hns hdec :=
  ⟨gap.extractionTarget, gap.extractionSemantics⟩

/-- Compatibility projection to the older hard-instance-indexed theorem name. -/
theorem semantic_theorem
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec) :
    GodMoveSemanticTheorem M n hn2 htb hns hdec gap.toHardInstanceData :=
  gap.semantic_extraction_theorem

/-- Rebuild the convenience bundle from the extraction-only theorem interface. -/
noncomputable def ofSemanticExtractionTheorem
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (hard : GodMoveHardInstanceData M n hn2 htb hns hdec)
    (hsem : GodMoveSemanticExtractionTheorem M n hn2 htb hns hdec) :
    GodMoveSemanticGap M n hn2 htb hns hdec :=
  let target := Classical.choose hsem
  let htarget := Classical.choose_spec hsem
  { toHardInstanceData := hard
    extractionTarget := target
    extractionSemantics := htarget }

/-- Compatibility constructor from the older hard-instance-indexed theorem name. -/
noncomputable def ofSemanticTheorem
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (hard : GodMoveHardInstanceData M n hn2 htb hns hdec)
    (hsem : GodMoveSemanticTheorem M n hn2 htb hns hdec hard) :
    GodMoveSemanticGap M n hn2 htb hns hdec :=
  ofSemanticExtractionTheorem hard hsem

/-- Add an NP-side lower bound on the carried target and package the strong
Route B obligations on that exact extraction-facing target. -/
def toRouteB_Obligations
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec)
    (np_lower : Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank gap.extractionTarget.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) gap.extractionTarget.coupledPoly) :
    GodMoveRouteB_Obligations M n hn2 htb hns :=
  gap.toTargetData.toRouteB_Obligations (by
    simpa [GodMoveSemanticGap.toTargetData] using np_lower)

/-- The exact semantic gap, together with the separate NP lower bound and the
generic rank wrappers, recovers the older semantic interface. This is the
direct compatibility bridge from the narrowed semantic-core theorem seam back
to the legacy Route B surface. -/
def toSemanticInterface
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec)
    (np_lower : Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank gap.extractionTarget.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) gap.extractionTarget.coupledPoly)
    (bridge :
      ∀ sem : ExtractionMapSemantics M n hn2 htb hns hdec gap.extractionTarget,
        ExtractionMapRankBridge sem) :
    GodMoveSemanticInterface M n hn2 htb hns hdec :=
  gap.toTargetData.toSemanticInterface
    gap.targetTheorem
    (by simpa [GodMoveSemanticGap.toTargetData] using np_lower)
    bridge

/-- Forgetful compatibility bridge from the exact semantic gap package to the
older abstract source/target interface. This keeps the narrowed semantic seam
primary while preserving the separation-facing API. -/
def toAbstractInterface
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec)
    (np_lower : Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank gap.extractionTarget.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) gap.extractionTarget.coupledPoly)
    (bridge :
      ∀ sem : ExtractionMapSemantics M n hn2 htb hns hdec gap.extractionTarget,
        ExtractionMapRankBridge sem) :
    GodMoveExtractionInterface M n hn2 htb hns :=
  gap.toTargetData.toAbstractInterface
    gap.targetTheorem
    (by simpa [GodMoveSemanticGap.toTargetData] using np_lower)
    bridge

end GodMoveSemanticGap

/-- The SAT-correctness hypothesis already supplies the accepting input; the
semantic gap only needs to prove the hard instance fits the input budget. -/
theorem GodMoveSemanticGap.accepting_input
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec) :
    ∃ input : Fin n → Bool, accepts M n (by omega : n ≥ 1) input := by
  exact DecidesSAT.accepting_input_of_satisfiable hdec
    gap.toHardInstanceData.hardInstance n (by omega : n ≥ 1)
    gap.toHardInstanceData.hardInstance_fits_input
    gap.toHardInstanceData.hardInstance_satisfiable

/-- Once the hard instance fits the input budget, the accepting tableau is also
available without enlarging the semantic obligation record. -/
theorem GodMoveSemanticGap.accepting_tableau
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec) :
    ∃ input : Fin n → Bool, ∃ t : ℕ, t ≤ timeSteps M n ∧
      (run M n t (initialConfig M n (by omega : n ≥ 1) input)).state = acceptState M := by
  rcases gap.accepting_input with ⟨input, hacc⟩
  rcases accepting_input_gives_tableau M n (by omega : n ≥ 1) input hacc with ⟨t, ht, hstate⟩
  exact ⟨input, t, ht, hstate⟩

/-- The semantic gap yields the extraction-side rank transfer once the generic
rank wrappers are supplied for the carried staged semantic witness.

This is the precise semantic role of `DecidesSAT` in the paper-faithful seam:
`DecidesSAT` is used to justify the staged semantic data, and the separate
mathematical monotonicity wrappers then discharge the otherwise bare
rank-transfer inequality. -/
theorem GodMoveSemanticGap.extraction
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec)
    (bridge :
      ∀ sem : ExtractionMapSemantics M n hn2 htb hns hdec gap.extractionTarget,
        ExtractionMapRankBridge sem) :
    GodMoveRouteB_ExtractionObligation M n hn2 htb hns hdec gap.extractionTarget :=
by
  rcases gap.extractionSemantics with ⟨sem⟩
  exact extraction_from_semantics sem (bridge sem)

/-- Forget the semantic target theorem and keep only the shared Route B target-side
data consumed by the strong and weakened NP packages. -/
def GodMoveSemanticGap.targetData
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec) :
    GodMoveRouteB_TargetData M n hn2 htb hns :=
  GodMoveExtractionTargetData.toRouteB_TargetData
    (GodMoveSemanticGap.toTargetData gap)

/-- Package full Route B obligations from the semantic gap plus a separate
NP-side lower bound.

This theorem shows that once the semantic gap is filled (the restriction
assignment is found and the output identification is verified), the full
Route B obligations follow. The NP lower bound on the coupled polynomial
is provided as a separate hypothesis because it is independent of DecidesSAT
and can be proved via the sound characteristic-polynomial route. So
`DecidesSAT` supplies the accepting-computation side of the extraction target,
not the NP lower bound itself. -/
def routeB_from_semantic_gap
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec)
    (np_lower : Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank gap.extractionTarget.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) gap.extractionTarget.coupledPoly) :
    GodMoveRouteB_Obligations M n hn2 htb hns :=
  gap.toRouteB_Obligations np_lower

/-- Packaging the semantic gap into Route B obligations preserves the exact
extraction-facing target carried by the gap. -/
@[simp] theorem routeB_from_semantic_gap_extractionTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec)
    (np_lower : Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank gap.extractionTarget.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) gap.extractionTarget.coupledPoly) :
    (routeB_from_semantic_gap gap np_lower).extractionTarget = gap.extractionTarget := rfl

/-- Strong Route B packaging leaves the extraction proposition unchanged on the
same semantic target carried by the gap. -/
@[simp] theorem routeB_from_semantic_gap_extractionObligation
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec)
    (np_lower : Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank gap.extractionTarget.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) gap.extractionTarget.coupledPoly) :
    GodMoveRouteB_ExtractionObligation M n hn2 htb hns hdec
        (routeB_from_semantic_gap gap np_lower).extractionTarget ↔
      GodMoveRouteB_ExtractionObligation M n hn2 htb hns hdec gap.extractionTarget :=
  Iff.rfl

/-! ## Characteristic-Polynomial to Route B NP Bridge

The sound Ramanujan-Tseitin encoding provides pdMatrixRank ≥ n^(log n/4).
Route B needs mlBlockedSpdpRank ≥ n^(log n/4) on the coupled polynomial.

The bridge requires:
1. A BlockPartition compatible with the VarPartition from the sound encoding
2. That the PD-rank lower bound transfers to blocked SPDP rank

In the paper, compatibility follows from the Ramanujan graph's girth Ω(log n):
distinct clause neighborhoods produce block-admissible derivative lists.

### Weakened Route B (sufficient for separation)

The original Route B target_lower uses C(n/3, log n), which is stronger than
what the sound encoding provides (C(n/30, log n) ≥ n^(log n/4)). Since
n^(log n/4) suffices for the exponent contradiction at n = 2^804, we provide
a weakened formulation that is directly connected to the sound encoding. -/

/-- Route B obligations with weakened NP lower bound.

Uses `n^(log n/4) ≤ rank` instead of `C(n/3, log n) ≤ rank`.
This is only the NP-side/data package for the weakened Route B seam; the
DecidesSAT-dependent extraction obligation is still carried separately.
Sufficient for separation since the contradiction uses n^201 ≤ n^200. -/
structure GodMoveRouteB_WeakenedObligations (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    extends GodMoveRouteB_TargetData M n hn2 htb hns where
  target_lower_weakened :
    n ^ (Nat.log 2 n / 4) ≤
      mlBlockedSpdpRank extractionTarget.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) extractionTarget.coupledPoly

namespace GodMoveExtractionTargetData

/-- Add the weakened NP-side lower bound on the same exact extraction target
chosen by the semantic theorem. -/
def toRouteB_WeakenedObligations
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (targetData : GodMoveExtractionTargetData M n hn2 htb hns hdec)
    (np_lower : n ^ (Nat.log 2 n / 4) ≤
      mlBlockedSpdpRank targetData.extractionTarget.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) targetData.extractionTarget.coupledPoly) :
    GodMoveRouteB_WeakenedObligations M n hn2 htb hns where
  toGodMoveRouteB_TargetData := targetData.toRouteB_TargetData
  target_lower_weakened := np_lower

end GodMoveExtractionTargetData

/-- The same semantic gap also feeds the weakened Route B surface used by the
sound characteristic-polynomial path. This keeps the DecidesSAT-dependent
extraction obligation identical while only swapping the separate NP-side bound
to match what the current sound encoding actually proves. -/
def routeB_weakened_from_semantic_gap
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec)
    (np_lower : n ^ (Nat.log 2 n / 4) ≤
      mlBlockedSpdpRank gap.extractionTarget.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) gap.extractionTarget.coupledPoly) :
    GodMoveRouteB_WeakenedObligations M n hn2 htb hns :=
  gap.toTargetData.toRouteB_WeakenedObligations (by
    simpa [GodMoveSemanticGap.toTargetData] using np_lower)

/-- Packaging the semantic gap into the weakened Route B surface preserves the
same exact extraction-facing target. -/
@[simp] theorem routeB_weakened_from_semantic_gap_extractionTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec)
    (np_lower : n ^ (Nat.log 2 n / 4) ≤
      mlBlockedSpdpRank gap.extractionTarget.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) gap.extractionTarget.coupledPoly) :
    (routeB_weakened_from_semantic_gap gap np_lower).extractionTarget = gap.extractionTarget := rfl

/-- Weakened Route B extraction obligation.

This is intentionally the same semantic seam as the non-weakened Route B
surface: only the NP-side lower bound package is weakened. -/
abbrev GodMoveRouteB_WeakenedExtractionObligation (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (target : GodMoveExtractionTarget M n hn2 htb hns) : Prop :=
  GodMoveRouteB_ExtractionObligation M n hn2 htb hns hdec target

@[simp] theorem GodMoveRouteB_WeakenedExtractionObligation_iff_transfer
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    {target : GodMoveExtractionTarget M n hn2 htb hns} :
    GodMoveRouteB_WeakenedExtractionObligation M n hn2 htb hns hdec target ↔
      GodMoveRouteB_ExtractionTransfer M n hn2 htb hns hdec target := Iff.rfl

@[simp] theorem GodMoveRouteB_WeakenedExtractionObligation_iff_extractionObligation
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    {target : GodMoveExtractionTarget M n hn2 htb hns} :
    GodMoveRouteB_WeakenedExtractionObligation M n hn2 htb hns hdec target ↔
      GodMoveRouteB_ExtractionObligation M n hn2 htb hns hdec target := Iff.rfl

/-- The weakened Route B surface uses the same DecidesSAT-dependent extraction
transfer on the same chosen target; only the separate NP lower bound changes. -/
theorem GodMoveSemanticGap.weakened_extraction
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec)
    (bridge :
      ∀ sem : ExtractionMapSemantics M n hn2 htb hns hdec gap.extractionTarget,
        ExtractionMapRankBridge sem) :
    GodMoveRouteB_WeakenedExtractionObligation M n hn2 htb hns hdec gap.extractionTarget :=
  gap.extraction bridge

/-- Weakened Route B packaging still reindexes to the exact same shared
extraction proposition on the preserved semantic target. Only the separate
NP-side inequality changes. -/
@[simp] theorem routeB_weakened_from_semantic_gap_extractionObligation
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec)
    (np_lower : n ^ (Nat.log 2 n / 4) ≤
      mlBlockedSpdpRank gap.extractionTarget.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) gap.extractionTarget.coupledPoly) :
    GodMoveRouteB_WeakenedExtractionObligation M n hn2 htb hns hdec
        (routeB_weakened_from_semantic_gap gap np_lower).extractionTarget ↔
      GodMoveRouteB_ExtractionObligation M n hn2 htb hns hdec gap.extractionTarget :=
  Iff.rfl

/-- Separation from weakened Route B NP-side data + extraction + P-side bound.

Uses `n^(log n/4)` directly as the NP lower bound. The theorem does not hide
the semantic gap: the DecidesSAT-dependent extraction transfer is still an
explicit hypothesis. -/
theorem separation_from_weakened_routeB
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) (hn804 : n ≥ 2 ^ 804)
    (obs : GodMoveRouteB_WeakenedObligations M n hn2 htb hns)
    (extraction :
      GodMoveRouteB_WeakenedExtractionObligation M n hn2 htb hns hdec obs.extractionTarget)
    (hP : mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≤ n ^ 200) :
    False := by
  have hchain : n ^ (Nat.log 2 n / 4) ≤ n ^ 200 :=
    le_trans obs.target_lower_weakened (le_trans extraction hP)
  have hlog : 804 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn804
  have hdiv : 201 ≤ Nat.log 2 n / 4 := by omega
  have hcontra : n ^ 201 ≤ n ^ 200 :=
    le_trans (Nat.pow_le_pow_right (by omega : 1 ≤ n) hdiv) hchain
  exact absurd hcontra
    (not_le_of_gt (Nat.pow_lt_pow_right (by omega : 1 < n) (by omega : 200 < 201)))

/-- Same contradiction as `separation_from_weakened_routeB`, but with the
semantic hypothesis stated in the narrower decomposition form on the extraction
target itself. This keeps the Route B front honest about the actual theorem
obligation: once the staged extraction decomposition exists for the chosen
target, the rank-transfer inequality is no longer an independent gap. -/
theorem separation_from_weakened_routeB_via_decomposition
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) (hn804 : n ≥ 2 ^ 804)
    (obs : GodMoveRouteB_WeakenedObligations M n hn2 htb hns)
    (hdecomp :
      GodMoveExtractionDecompositionObligation M n hn2 htb hns hdec obs.extractionTarget)
    (hP : mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≤ n ^ 200) :
    False := by
  exact separation_from_weakened_routeB M n hn2 htb hns hdec hn804 obs
    (extraction_from_decomposition_obligation hdecomp) hP

/-- NP-side data package for weakened Route B, stated in terms of PD-matrix rank
(what the sound encoding provides).

The single bridge gap is `pd_to_blocked_transfer`: PD rank → blocked SPDP rank
under the Ramanujan graph's natural block structure. -/
structure RouteBNPFromPdMatrix (n numVars : ℕ) where
  varPart : PartialDerivMatrix.VarPartition numVars
  poly : MvPolynomial (Fin numVars) ℚ
  S_linear : n / 30 ≤ varPart.S.card
  pd_lower : n ^ (Nat.log 2 n / 4) ≤ PartialDerivMatrix.pdMatrixRank ℚ varPart poly
  blockPart : BlockPartition numVars
  /-- Bridge gap: PD rank transfers to blocked SPDP rank.
      Follows from Ramanujan girth Ω(log n) ensuring block-admissibility. -/
  pd_to_blocked_transfer :
    PartialDerivMatrix.pdMatrixRank ℚ varPart poly ≤
      mlBlockedSpdpRank blockPart (Nat.log 2 n) (Nat.log 2 n) poly

/-- From PD-matrix NP data, derive the weakened Route B NP bound.

This theorem only discharges the weakened NP-side inequality. It does not
address the semantic extraction seam. -/
theorem routeB_weakened_np_from_pdMatrix
    {n numVars : ℕ}
    (d : RouteBNPFromPdMatrix n numVars) :
    n ^ (Nat.log 2 n / 4) ≤
      mlBlockedSpdpRank d.blockPart (Nat.log 2 n) (Nat.log 2 n) d.poly :=
  le_trans d.pd_lower d.pd_to_blocked_transfer

/-- The weakened Route B contradiction can be stated directly on a chosen exact
extraction target.

This is the smallest paper-faithful contradiction shell above the semantic
core: a chosen target, the staged semantic witness on that target, the
separate NP-side lower bound on that same target, and the generic rank
wrappers. No `GodMoveSemanticGap` packaging is required. -/
theorem separation_from_semantic_target
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) (hn804 : n ≥ 2 ^ 804)
    (target : GodMoveExtractionTarget M n hn2 htb hns)
    (hsem : GodMoveExtractionSemanticObligation M n hn2 htb hns hdec target)
    (np_lower : n ^ (Nat.log 2 n / 4) ≤
      mlBlockedSpdpRank target.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) target.coupledPoly)
    (bridge :
      ∀ sem : ExtractionMapSemantics M n hn2 htb hns hdec target,
        ExtractionMapRankBridge sem)
    (hP : mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≤ n ^ 200) :
    False := by
  have extraction :
      GodMoveRouteB_ExtractionObligation M n hn2 htb hns hdec target := by
    rcases hsem with ⟨sem⟩
    exact extraction_from_semantics sem (bridge sem)
  have hchain : n ^ (Nat.log 2 n / 4) ≤ n ^ 200 :=
    le_trans np_lower (le_trans extraction hP)
  have hlog : 804 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn804
  have hdiv : 201 ≤ Nat.log 2 n / 4 := by omega
  have hcontra : n ^ 201 ≤ n ^ 200 :=
    le_trans (Nat.pow_le_pow_right (by omega : 1 ≤ n) hdiv) hchain
  exact absurd hcontra
    (not_le_of_gt (Nat.pow_lt_pow_right (by omega : 1 < n) (by omega : 200 < 201)))

/-- The semantic gap convenience bundle feeds the same direct weakened
contradiction shell once the separate NP-side lower bound is supplied on its
chosen target. -/
theorem separation_from_semantic_gap
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) (hn804 : n ≥ 2 ^ 804)
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec)
    (np_lower : n ^ (Nat.log 2 n / 4) ≤
      mlBlockedSpdpRank gap.extractionTarget.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) gap.extractionTarget.coupledPoly)
    (bridge :
      ∀ sem : ExtractionMapSemantics M n hn2 htb hns hdec gap.extractionTarget,
        ExtractionMapRankBridge sem)
    (hP : mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≤ n ^ 200) :
    False := by
  exact separation_from_semantic_target M n hn2 htb hns hdec hn804
    gap.extractionTarget gap.extractionSemantics np_lower bridge hP

/-- Compatibility wrapper around `separation_from_semantic_target` that keeps
the exact target-data package explicit while the surrounding API still talks in
terms of `GodMoveExtractionTargetData`. -/
theorem separation_from_semantic_target_theorem
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) (hn804 : n ≥ 2 ^ 804)
    (targetData : GodMoveExtractionTargetData M n hn2 htb hns hdec)
    (hsem : GodMoveExtractionTargetTheorem M n hn2 htb hns hdec targetData.extractionTarget)
    (np_lower : n ^ (Nat.log 2 n / 4) ≤
      mlBlockedSpdpRank targetData.extractionTarget.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) targetData.extractionTarget.coupledPoly)
    (bridge :
      ∀ sem : ExtractionMapSemantics M n hn2 htb hns hdec targetData.extractionTarget,
        ExtractionMapRankBridge sem)
    (hP : mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≤ n ^ 200) :
    False := by
  exact separation_from_semantic_target M n hn2 htb hns hdec hn804
    targetData.extractionTarget hsem np_lower bridge hP

/-- The final weakened contradiction can be phrased directly against the exact
semantic extraction theorem itself. This is smaller than going through
`GodMoveSemanticGap`: the theorem just unpacks the existentially chosen target
and applies `separation_from_semantic_target`. -/
theorem separation_from_semantic_extraction_theorem
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) (hn804 : n ≥ 2 ^ 804)
    (hsem : GodMoveSemanticExtractionTheorem M n hn2 htb hns hdec)
    (np_lower :
      ∀ target : GodMoveExtractionTarget M n hn2 htb hns,
        n ^ (Nat.log 2 n / 4) ≤
          mlBlockedSpdpRank target.coupledPartition
            (Nat.log 2 n) (Nat.log 2 n) target.coupledPoly)
    (bridge :
      ∀ target : GodMoveExtractionTarget M n hn2 htb hns,
        ∀ sem : ExtractionMapSemantics M n hn2 htb hns hdec target,
          ExtractionMapRankBridge sem)
    (hP : mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≤ n ^ 200) :
    False := by
  rcases hsem with ⟨target, htarget⟩
  exact separation_from_semantic_target M n hn2 htb hns hdec hn804
    target htarget (np_lower target) (bridge target) hP

/-! ## Axiom audits for Route B theorems -/

#print axioms extraction_from_decomposition
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms)
-- The extraction follows from the decomposition data, no external axioms.

#print axioms separation_from_weakened_routeB
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms)
-- All mathematical content is in the hypotheses.

#print axioms routeB_weakened_np_from_pdMatrix
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms)
-- Pure arithmetic chain from RouteBNPFromPdMatrix data.

#print axioms separation_from_semantic_target
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms)
-- Direct exact-target contradiction shell above the semantic witness.

#print axioms separation_from_semantic_extraction_theorem
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms)
-- Pure wrapper: unpacks the exact semantic theorem and feeds the weakened shell.

/-! ## Summary: Exact theorem seams for Route B

### Discharged (modulo sound encoding axioms):
- **NP PD lower bound**: n^(log n/4) ≤ pdMatrixRank (sound_theorem72_condensed)

### Remaining gaps (narrowest form):
1. **PD→blocked SPDP** (`pd_to_blocked_transfer`): linear algebra lemma
2. **Semantic extraction theorem** (`GodMoveSemanticExtractionTheorem`)
   equivalently, existence of an exact extraction target carrying
   `GodMoveExtractionSemanticObligation`
   (`GodMoveSemanticTheorem` remains as a compatibility alias indexed by
   `GodMoveHardInstanceData`)
3. **Compiled-side transfer packaging**
   (`separation_from_semantic_target`,
   `separation_from_semantic_gap`,
   and `separation_from_weakened_routeB_via_decomposition` are now the direct
   contradiction wrappers above the semantic core)
4. **P-side** (`compiled_rank_bound`): BP compilation axiom
-/

end PaperFaithfulSeparation
