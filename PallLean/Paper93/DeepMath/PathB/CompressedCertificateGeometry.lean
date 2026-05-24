import PallLean.Paper93.DeepMath.PathB.OperationalZeroBoundaryObstruction

/-!
# Compressed certificate geometry

This file tests the remaining paper-faithful positive door after the dynamic
rank-as-width route fails.

The proposed escape is to split two quantities:

* `descriptionSize`: the size of a compressed canonical N-frame certificate;
* `obstructionRank`: the large SAT obstruction exposed by the geometry.

This avoids the immediate SPDP-style rank sandwich only if the obstruction rank
is **not** bounded by the description size and is **not** simply the observer
width.  The file records both sides:

1. A disconnected compressed geometry can have polynomial description and
   superpolynomial obstruction, but by itself proves no lower bound.
2. If a load-bearing bridge says the obstruction rank must fit inside every
   SAT observer's live width, then the theorem is again exactly the SAT lower
   bound: any SAT-deciding DTM is ruled out by the zero-boundary operational
   presentation.

So this layer is structurally the only remaining door, but the missing theorem
is now explicit: a non-monotone, non-same-object bridge from compressed
certificate geometry to SAT observer failure.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-! ## Split compressed geometry -/

/-- A compressed N-frame geometry separates certificate description size from
obstruction rank. -/
structure CompressedCanonicalNFrameGeometry
    (enc : ThreeCNFEncoding) where
  descriptionSize : Nat -> Nat
  obstructionRank : Nat -> Nat

/-- Polynomial description-size bound. -/
def DescriptionPolynomialBound
    {enc : ThreeCNFEncoding}
    (G : CompressedCanonicalNFrameGeometry enc) (k : Nat) : Prop :=
  forall n : Nat, G.descriptionSize n <= n ^ k

/-- SAT-side obstruction lower bound at the paper's binomial scale. -/
def SATObstructionLowerBound
    {enc : ThreeCNFEncoding}
    (G : CompressedCanonicalNFrameGeometry enc) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
    4 * (c + 1) <= Nat.log 2 n /\
    Nat.choose (n / 3) (Nat.log 2 n) <= G.obstructionRank n

/-- The monotone/same-object bridge that the compressed route must avoid. -/
def ObstructionRankBoundedByDescription
    {enc : ThreeCNFEncoding}
    (G : CompressedCanonicalNFrameGeometry enc) : Prop :=
  forall n : Nat, G.obstructionRank n <= G.descriptionSize n

/-! ## A disconnected split is easy but non-load-bearing -/

/-- A deliberately disconnected compressed geometry: tiny descriptions and
binomial obstruction rank by definition.

This shows that merely splitting the quantities is not a proof.  Without a
soundness bridge connecting the obstruction to SAT observers, the data can be
written down independently of computation. -/
noncomputable def disconnectedCompressedGeometry
    (enc : ThreeCNFEncoding) :
    CompressedCanonicalNFrameGeometry enc where
  descriptionSize := fun _ => 0
  obstructionRank := fun n => Nat.choose (n / 3) (Nat.log 2 n)

/-- The disconnected geometry has polynomial description size. -/
theorem disconnectedCompressedGeometry_description_poly
    (enc : ThreeCNFEncoding) :
    DescriptionPolynomialBound (disconnectedCompressedGeometry enc) 0 := by
  intro n
  exact Nat.zero_le _

/-- The disconnected geometry has the SAT obstruction lower bound, because the
obstruction rank was defined to be the binomial boundary. -/
theorem disconnectedCompressedGeometry_sat_obstruction
    (enc : ThreeCNFEncoding) :
    SATObstructionLowerBound (disconnectedCompressedGeometry enc) := by
  intro c
  let k : Nat := Nat.max 20 (4 * (c + 1))
  let n : Nat := 2 ^ k
  refine ⟨n, ?_, ?_, ?_⟩
  · dsimp [n, k]
    exact Nat.pow_le_pow_right
      (by norm_num : 1 <= 2)
      (Nat.le_max_left 20 (4 * (c + 1)))
  · dsimp [n, k]
    have hpow :
        2 ^ (4 * (c + 1)) <= 2 ^ Nat.max 20 (4 * (c + 1)) :=
      Nat.pow_le_pow_right
        (by norm_num : 1 <= 2)
        (Nat.le_max_right 20 (4 * (c + 1)))
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow
  · rfl

/-- Even under a SAT-decider hypothesis, the disconnected split geometry still
exists.  Thus split data alone cannot imply P vs NP. -/
theorem disconnectedCompressedGeometry_exists_under_decider
    {enc : ThreeCNFEncoding}
    (_hdec : exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) :
    exists G : CompressedCanonicalNFrameGeometry enc,
      DescriptionPolynomialBound G 0 /\ SATObstructionLowerBound G := by
  exact ⟨disconnectedCompressedGeometry enc,
    disconnectedCompressedGeometry_description_poly enc,
    disconnectedCompressedGeometry_sat_obstruction enc⟩

/-! ## The old sandwich returns if obstruction rank is bounded by description -/

/-- Polynomial description, SAT obstruction, and a monotone
`obstructionRank <= descriptionSize` bridge are mutually inconsistent.

This is the compressed-certificate version of the rank sandwich. -/
theorem not_rank_le_description_of_poly_description_and_sat_lower
    {enc : ThreeCNFEncoding}
    {G : CompressedCanonicalNFrameGeometry enc} {k : Nat}
    (hdesc : DescriptionPolynomialBound G k)
    (hsat : SATObstructionLowerBound G)
    (hmono : ObstructionRankBoundedByDescription G) :
    False := by
  rcases hsat k with ⟨n, hn20, hlog, hlower⟩
  have hupper :
      Nat.choose (n / 3) (Nat.log 2 n) <= n ^ k :=
    le_trans hlower (le_trans (hmono n) (hdesc n))
  exact (not_le_of_gt
    (arithmetic_gap_for_exponent k n hn20 hlog)) hupper

/-! ## Load-bearing bridge back to observer width -/

/-- A compressed obstruction is load-bearing for an observer class only if the
obstruction rank must fit inside every SAT observer's live width. -/
def ObstructionRankLoadsIntoObserverWidth
    {enc : ThreeCNFEncoding}
    (G : CompressedCanonicalNFrameGeometry enc)
    (Decides : TrajectoryObserverMachine -> Prop) : Prop :=
  forall T : TrajectoryObserverMachine, Decides T ->
    forall n : Nat, G.obstructionRank n <= T.width n

/-- A load-bearing compressed obstruction lower bound rules out polynomial-width
SAT observers in the target class.

This is a valid lower-bound theorem, but it shows exactly where the hard
content lives: proving the load bridge for SAT observers. -/
theorem no_polyWidthSATObserver_of_compressed_load
    {enc : ThreeCNFEncoding}
    {G : CompressedCanonicalNFrameGeometry enc}
    {Decides : TrajectoryObserverMachine -> Prop}
    (hsat : SATObstructionLowerBound G)
    (hload : ObstructionRankLoadsIntoObserverWidth G Decides)
    (c : Nat) :
    Not (TrajectoryObserverSATPolyWidthAtMost Decides c) := by
  intro hpolySat
  rcases hpolySat with ⟨T, hdecides, hpoly⟩
  rcases hsat c with ⟨n, hn20, hlog, hlower⟩
  have hupper :
      Nat.choose (n / 3) (Nat.log 2 n) <= n ^ c :=
    le_trans hlower (le_trans (hload T hdecides n) (hpoly n))
  exact (not_le_of_gt
    (arithmetic_gap_for_exponent c n hn20 hlog)) hupper

/-- If the compressed obstruction loads into raw operational SAT observer
width, then it already proves that no DTM decides SAT under the encoding.

The proof uses the existing zero-boundary operational presentation of any
SAT-deciding DTM.  Therefore this bridge is not a small lemma: it is the SAT
lower bound in operational form. -/
theorem no_DTMDecidesSATWithEncoding_of_operational_compressed_load
    {enc : ThreeCNFEncoding}
    {G : CompressedCanonicalNFrameGeometry enc}
    (hsat : SATObstructionLowerBound G)
    (hload :
      ObstructionRankLoadsIntoObserverWidth G
        (OperationalTrajectoryObserverDecidesSAT enc)) :
    Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) := by
  intro hM
  rcases hM with ⟨M, hdec⟩
  have hpolySat :
      TrajectoryObserverSATPolyWidthAtMost
        (OperationalTrajectoryObserverDecidesSAT enc) 0 := by
    refine ⟨zeroBoundaryOperationalTrajectoryObserver M,
      zeroBoundaryOperationalTrajectoryObserver_decidesSAT hdec, ?_⟩
    intro n
    simp [zeroBoundaryOperationalTrajectoryObserver]
  exact
    (no_polyWidthSATObserver_of_compressed_load
      (G := G)
      (Decides := OperationalTrajectoryObserverDecidesSAT enc)
      hsat hload 0)
      hpolySat

/-! ## Positive-program socket -/

/-- The load-bearing compressed-certificate program.

This is the structurally alive shape, but its final field is exactly the hard
bridge: the SAT obstruction rank must load into every operational SAT
observer's live width without collapsing to `obstructionRank <= descriptionSize`.
-/
structure LoadBearingCompressedCertificateProgram
    (enc : ThreeCNFEncoding) where
  geometry : CompressedCanonicalNFrameGeometry enc
  description_exponent : Nat
  description_poly :
    DescriptionPolynomialBound geometry description_exponent
  sat_obstruction : SATObstructionLowerBound geometry
  loads_into_operational_width :
    ObstructionRankLoadsIntoObserverWidth geometry
      (OperationalTrajectoryObserverDecidesSAT enc)

/-- A completed load-bearing compressed-certificate program proves the SAT
lower bound.  The theorem is correct, but the load-bearing bridge is precisely
the missing positive breakthrough. -/
theorem no_DTMDecidesSATWithEncoding_of_loadBearingCompressedCertificateProgram
    (enc : ThreeCNFEncoding)
    (program : LoadBearingCompressedCertificateProgram enc) :
    Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) :=
  no_DTMDecidesSATWithEncoding_of_operational_compressed_load
    program.sat_obstruction
    program.loads_into_operational_width

/-! ## Kernel-only axiom trace -/

#print axioms disconnectedCompressedGeometry_exists_under_decider
#print axioms not_rank_le_description_of_poly_description_and_sat_lower
#print axioms no_polyWidthSATObserver_of_compressed_load
#print axioms no_DTMDecidesSATWithEncoding_of_operational_compressed_load
#print axioms no_DTMDecidesSATWithEncoding_of_loadBearingCompressedCertificateProgram

end PallLean.Paper93.DeepMath.PathB
