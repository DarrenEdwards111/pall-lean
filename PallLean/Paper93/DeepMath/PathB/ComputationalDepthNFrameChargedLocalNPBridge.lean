import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalSATFrontier
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATVerifierSpec

/-!
# A verifier-based NP bridge for the charged local machine model

`ComposableMachine` supplies a faithful deterministic polynomial-time class,
but previously had no matching verifier-based NP class.  This file adds one
using a self-delimiting pairing of an instance and a certificate.

For the concrete encoded SAT language, the semantic witness theorem is proved
for every input bitstring, including malformed encodings.  The unary formula
decoder cannot manufacture a variable index larger than the input length, so
an assignment of length `|x| + 1` always suffices.

The only remaining SAT NP-membership obligation is operational and explicit:
the paired SAT verifier language must belong to `ComposableMachine.InP`.
Assuming precisely that machine theorem, encoded SAT belongs to the new local
NP class, and the charged superpolynomial SAT clock lower bound proves that
local NP is not contained in local P.  (The routine opposite inclusion also
needs a concrete local pairing/parser machine and is not silently assumed.)
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalNPBridge

open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit
open PallLean.Paper93.DeepMath.PathB.SATVerifierSpec (evalFormula_congr getD_range_map)
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalSATFrontier

/-! ## A faithful instance/certificate pairing -/

/-- Self-delimiting pairing: unary instance length, then instance, then witness. -/
def packWitness (x w : List Bool) : List Bool := encodeNat x.length ++ x ++ w

/-- Decode the instance and witness from a paired verifier input. -/
def unpackWitness (z : List Bool) : List Bool × List Bool :=
  let p := decodeNat z
  (p.2.take p.1, p.2.drop p.1)

@[simp] theorem unpackWitness_packWitness (x w : List Bool) :
    unpackWitness (packWitness x w) = (x, w) := by
  simp [unpackWitness, packWitness, List.append_assoc, decodeNat_encodeNat]

/-- Turn a two-input verifier into its ordinary paired Boolean language. -/
def verifierLanguage (V : List Bool → List Bool → Bool) : List Bool → Bool :=
  fun z => V (unpackWitness z).1 (unpackWitness z).2

@[simp] theorem verifierLanguage_packWitness
    (V : List Bool → List Bool → Bool) (x w : List Bool) :
    verifierLanguage V (packWitness x w) = V x w := by
  simp [verifierLanguage]

/-! ## The local verifier class NP -/

/-- Languages with a polynomial-length certificate checked by a paired
`ComposableMachine.InP` verifier language. -/
def LocalInNP (L : List Bool → Bool) : Prop :=
  ∃ (V : List Bool → List Bool → Bool) (q : Nat → Nat),
    PolyBounded q ∧ InP (verifierLanguage V) ∧
      ∀ x, L x = true ↔ ∃ w, w.length ≤ q x.length ∧ V x w = true

/-- The repaired local-model collapse proposition `NP ⊆ P`. -/
def LocalNPCollapse : Prop := ∀ L : List Bool → Bool, LocalInNP L → InP L

/-! ## Decoder bounds for the unary formula codec -/

theorem decodeNat_value_le_length (bs : List Bool) :
    (decodeNat bs).1 ≤ bs.length := by
  induction bs with
  | nil => simp [decodeNat]
  | cons b bs ih => cases b <;> simp [decodeNat, ih]

theorem decodeNat_rest_length_le (bs : List Bool) :
    (decodeNat bs).2.length ≤ bs.length := by
  induction bs with
  | nil => simp [decodeNat]
  | cons b bs ih =>
      cases b
      · simp [decodeNat]
      · exact le_trans ih (Nat.le_succ _)

theorem decodeLit_var_le_length (bs : List Bool) :
    (decodeLit bs).1.1 ≤ bs.length := by
  simp only [decodeLit]
  exact decodeNat_value_le_length bs

theorem decodeLit_rest_length_le (bs : List Bool) :
    (decodeLit bs).2.length ≤ bs.length := by
  simp only [decodeLit]
  have ht : (decodeNat bs).2.tail.length ≤ (decodeNat bs).2.length := by
    cases (decodeNat bs).2 <;> simp
  exact le_trans ht (decodeNat_rest_length_le bs)

theorem decodeLits_rest_length_le (k : Nat) (bs : List Bool) :
    (decodeLits k bs).2.length ≤ bs.length := by
  induction k generalizing bs with
  | zero => simp [decodeLits]
  | succ k ih =>
      exact le_trans (ih (decodeLit bs).2) (decodeLit_rest_length_le bs)

theorem decodeLits_var_le_length (k : Nat) (bs : List Bool)
    {l : Lit} (hl : l ∈ (decodeLits k bs).1) :
    l.1 ≤ bs.length := by
  induction k generalizing bs with
  | zero => simp [decodeLits] at hl
  | succ k ih =>
      simp only [decodeLits, List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact decodeLit_var_le_length bs
      · exact le_trans (ih (decodeLit bs).2 hl) (decodeLit_rest_length_le bs)

theorem decodeClause_rest_length_le (bs : List Bool) :
    (decodeClause bs).2.length ≤ bs.length := by
  simp only [decodeClause]
  exact le_trans (decodeLits_rest_length_le _ (decodeNat bs).2)
    (decodeNat_rest_length_le bs)

theorem decodeClause_var_le_length (bs : List Bool)
    {l : Lit} (hl : l ∈ (decodeClause bs).1) :
    l.1 ≤ bs.length := by
  simp only [decodeClause] at hl
  exact le_trans (decodeLits_var_le_length _ (decodeNat bs).2 hl)
    (decodeNat_rest_length_le bs)

theorem decodeClauses_rest_length_le (k : Nat) (bs : List Bool) :
    (decodeClauses k bs).2.length ≤ bs.length := by
  induction k generalizing bs with
  | zero => simp [decodeClauses]
  | succ k ih =>
      exact le_trans (ih (decodeClause bs).2) (decodeClause_rest_length_le bs)

theorem decodeClauses_var_le_length (k : Nat) (bs : List Bool)
    {c : Clause} (hc : c ∈ (decodeClauses k bs).1)
    {l : Lit} (hl : l ∈ c) :
    l.1 ≤ bs.length := by
  induction k generalizing bs with
  | zero => simp [decodeClauses] at hc
  | succ k ih =>
      simp only [decodeClauses, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact decodeClause_var_le_length bs hl
      · exact le_trans (ih (decodeClause bs).2 hc)
          (decodeClause_rest_length_le bs)

/-- Every variable occurring in a decoded formula is bounded by the length of
the original bitstring. -/
theorem decodeFormula_var_le_length (bs : List Bool)
    {c : Clause} (hc : c ∈ decodeFormula bs)
    {l : Lit} (hl : l ∈ c) :
    l.1 ≤ bs.length := by
  simp only [decodeFormula] at hc
  exact le_trans
    (decodeClauses_var_le_length _ (decodeNat bs).2 hc hl)
    (decodeNat_rest_length_le bs)

/-! ## Encoded SAT has polynomial semantic witnesses -/

/-- The direct SAT certificate checker. -/
def satWitnessVerifier (x w : List Bool) : Bool :=
  evalFormula (fun v => w.getD v false) (decodeFormula x)

/-- One bit for every possible decoded variable index. -/
def satWitnessBound (n : Nat) : Nat := n + 1

theorem satWitnessBound_poly : PolyBounded satWitnessBound := by
  refine ⟨1, 1, ?_⟩
  intro n
  simp [satWitnessBound]

/-- Complete semantic witness characterization, including malformed formula
encodings. -/
theorem encodedSATLanguage_witness_iff (x : List Bool) :
    encodedSATLanguage x = true ↔
      ∃ w, w.length ≤ satWitnessBound x.length ∧
        satWitnessVerifier x w = true := by
  rw [encodedSATLanguage_eq_true_iff]
  constructor
  · rintro ⟨a, ha⟩
    let w := (List.range (x.length + 1)).map a
    refine ⟨w, ?_, ?_⟩
    · simp [w, satWitnessBound]
    · unfold satWitnessVerifier
      rw [show evalFormula (fun v => w.getD v false) (decodeFormula x) =
          evalFormula a (decodeFormula x) from
        evalFormula_congr _ fun c hc l hl => by
          rw [getD_range_map]
          exact Nat.lt_succ_of_le (decodeFormula_var_le_length x hc hl)]
      exact ha
  · rintro ⟨w, -, hw⟩
    exact ⟨fun v => w.getD v false, hw⟩

/-! ## Operational verifier seam and separation cashout -/

/-- The one concrete operational theorem still needed for SAT membership in
the repaired local NP class. -/
def LocalSATVerifierInP : Prop :=
  InP (verifierLanguage satWitnessVerifier)

theorem encodedSATLanguage_in_localNP
    (hverify : LocalSATVerifierInP) :
    LocalInNP encodedSATLanguage := by
  exact ⟨satWitnessVerifier, satWitnessBound, satWitnessBound_poly,
    hverify, encodedSATLanguage_witness_iff⟩

/-- Once the verifier machine is supplied, the charged SAT clock lower bound
proves that repaired local NP is not contained in repaired local P. -/
theorem local_NP_not_subset_P_of_SAT_clock_lower_bound
    (hverify : LocalSATVerifierInP)
    (hlower : LocalSATSuperpolynomialClockLowerBound) :
    ¬ LocalNPCollapse := by
  intro heq
  exact (localSAT_superpolyClock_iff_not_inP.mp hlower)
    (heq encodedSATLanguage (encodedSATLanguage_in_localNP hverify))

/-- Conversely, local `NP ⊆ P` plus the verifier theorem refutes the universal
SAT clock lower bound. -/
theorem no_SAT_clock_lower_bound_of_local_NP_collapse
    (hverify : LocalSATVerifierInP)
    (heq : LocalNPCollapse) :
    ¬ LocalSATSuperpolynomialClockLowerBound := by
  rw [not_superpolyClock_iff_localSAT_inP]
  exact heq encodedSATLanguage (encodedSATLanguage_in_localNP hverify)

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalNPBridge

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalNPBridge.unpackWitness_packWitness
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalNPBridge.decodeFormula_var_le_length
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalNPBridge.encodedSATLanguage_witness_iff
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalNPBridge.encodedSATLanguage_in_localNP
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalNPBridge.local_NP_not_subset_P_of_SAT_clock_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalNPBridge.no_SAT_clock_lower_bound_of_local_NP_collapse
