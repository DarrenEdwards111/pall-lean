import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameRadiusOneLocalityThreshold

/-!
# Radius-one four-Helly endpoint

For Boolean Hamming balls of radius one, four-local compatibility is sufficient
to construct one coherent centre for an arbitrary finite semantic fibre.

The key dimension-free fact is that two distinct anchor words have at most two
common radius-one centres.  If one candidate fails on a fibre word and the other
fails on another, fourwise compatibility of the two anchors and those two
witnesses gives an impossible third choice.  Singleton fibres are immediate.

Thus radius-one received-word projection has an exact finite local certificate:
fourwise compatibility implies the global projection, while the previous
parity-triple example proves that arity three does not suffice.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneFourHellyEndpoint

open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordListDecodingBridge
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalityThreshold

/-! ## Radius-one metric rigidity -/

/-- Once one disagreement has consumed a radius-one budget, all other
coordinates agree. -/
theorem agree_elsewhere_of_distance_le_one
    {N : Nat} {x y : Assignment N} {i : Fin N}
    (hnear : hammingDistance x y <= 1) (hi : x i ≠ y i) :
    forall j : Fin N, j ≠ i -> x j = y j := by
  intro j hji
  by_contra hj
  classical
  let disagreements :=
    (Finset.univ : Finset (Fin N)).filter (fun k => x k ≠ y k)
  have hsub : ({i, j} : Finset (Fin N)) ⊆ disagreements := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have htwo : 2 <= disagreements.card := by
    calc
      2 = ({i, j} : Finset (Fin N)).card :=
        (Finset.card_pair (Ne.symm hji)).symm
      _ <= disagreements.card := Finset.card_le_card hsub
  have hone : disagreements.card <= 1 := by
    simpa [disagreements, hammingDistance] using hnear
  omega

/-- Received words simultaneously within radius one of two encoded anchors. -/
def CommonRadiusOneCenters
    {N : Nat} (x y : Assignment N) :=
  {received : Assignment N //
    hammingDistance received x <= 1 ∧
      hammingDistance received y <= 1}

noncomputable instance commonRadiusOneCentersFintype
    {N : Nat} (x y : Assignment N) :
    Fintype (CommonRadiusOneCenters x y) := by
  classical
  unfold CommonRadiusOneCenters
  infer_instance

/-- Two distinct Boolean words have at most two common radius-one centres.  A
differing coordinate injectively labels every possible centre by one Boolean
bit. -/
theorem commonRadiusOneCenters_card_le_two
    {N : Nat} {x y : Assignment N} (hxy : x ≠ y) :
    Fintype.card (CommonRadiusOneCenters x y) <= 2 := by
  classical
  have hcoord : ∃ i : Fin N, x i ≠ y i := by
    by_contra h
    push_neg at h
    exact hxy (funext h)
  obtain ⟨i, hi⟩ := hcoord
  let bit : CommonRadiusOneCenters x y -> Bool := fun r => r.1 i
  have hbit : Function.Injective bit := by
    intro r s hrs
    have hrs' : r.1 i = s.1 i := by simpa [bit] using hrs
    apply Subtype.ext
    funext j
    by_cases hji : j = i
    · subst j
      exact hrs'
    · by_cases hrx : r.1 i = x i
      · have hsx : s.1 i = x i := hrs'.symm.trans hrx
        have hry : r.1 i ≠ y i := fun h => hi (hrx.symm.trans h)
        have hsy : s.1 i ≠ y i := fun h => hi (hsx.symm.trans h)
        rw [agree_elsewhere_of_distance_le_one r.property.2 hry j hji,
          agree_elsewhere_of_distance_le_one s.property.2 hsy j hji]
      · have hry : r.1 i = y i := by
          cases hx : x i <;> cases hy : y i <;> cases hr : r.1 i <;>
            simp_all
        have hsy : s.1 i = y i := hrs'.symm.trans hry
        have hrx' : r.1 i ≠ x i := hrx
        have hsx' : s.1 i ≠ x i := fun h => hi (h.symm.trans hsy)
        rw [agree_elsewhere_of_distance_le_one r.property.1 hrx' j hji,
          agree_elsewhere_of_distance_le_one s.property.1 hsx' j hji]
  have := Fintype.card_le_of_injective bit hbit
  simpa using this

/-- In a finite type of cardinality at most two, once two distinct elements are
known, every element different from the first is the second. -/
theorem eq_second_of_card_le_two
    {α : Type} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α <= 2) {x y z : α}
    (hxy : x ≠ y) (hzx : z ≠ x) : z = y := by
  by_contra hzy
  have hthree : 3 <= Fintype.card α := by
    classical
    calc
      3 = ({x, y, z} : Finset α).card := by
        have hxnot : x ∉ ({y, z} : Finset α) := by
          simp [hxy, Ne.symm hzx]
        rw [Finset.card_insert_of_notMem hxnot,
          Finset.card_pair (Ne.symm hzy)]
      _ <= (Finset.univ : Finset α).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card α := Finset.card_univ
  omega

/-! ## Fourwise gluing inside one fibre -/

/-- Fourwise radius-one compatibility supplies a common centre for every
inhabited exact cell fibre. -/
theorem common_center_for_fiber_of_fourwise
    {m N : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (hfour : CellFourwiseRadiusCompatible C cellOf (R := 1))
    {c : Cell} {a : Assignment m} (ha : cellOf a = c) :
    ∃ received : Assignment N,
      forall z : Assignment m, cellOf z = c ->
        hammingDistance received (C.encode z) <= 1 := by
  classical
  by_cases hsecond : ∃ b : Assignment m, cellOf b = c ∧ b ≠ a
  · obtain ⟨b, hb, hba⟩ := hsecond
    have habCell : cellOf a = cellOf b := ha.trans hb.symm
    have habCode : C.encode a ≠ C.encode b := by
      intro h
      exact hba (C.injective h).symm
    obtain ⟨r0, hr0a, hr0b, _, _⟩ :=
      hfour a b a b habCell habCell.symm habCell
    let center0 : CommonRadiusOneCenters (C.encode a) (C.encode b) :=
      ⟨r0, hr0a, hr0b⟩
    by_cases hglobal0 : forall z : Assignment m, cellOf z = c ->
        hammingDistance center0.1 (C.encode z) <= 1
    · exact ⟨center0.1, hglobal0⟩
    · push_neg at hglobal0
      obtain ⟨z0, hz0, hfail0⟩ := hglobal0
      have hbz : cellOf b = cellOf z0 := hb.trans hz0.symm
      obtain ⟨r1, hr1a, hr1b, hr1z, _⟩ :=
        hfour a b z0 z0 habCell hbz rfl
      let center1 : CommonRadiusOneCenters (C.encode a) (C.encode b) :=
        ⟨r1, hr1a, hr1b⟩
      have hcenters : center0 ≠ center1 := by
        intro heq
        have hnear : hammingDistance center0.1 (C.encode z0) <= 1 := by
          rw [heq]
          exact hr1z
        omega
      refine ⟨center1.1, ?_⟩
      intro w hw
      have hzw : cellOf z0 = cellOf w := hz0.trans hw.symm
      obtain ⟨r2, hr2a, hr2b, hr2z, hr2w⟩ :=
        hfour a b z0 w habCell hbz hzw
      let center2 : CommonRadiusOneCenters (C.encode a) (C.encode b) :=
        ⟨r2, hr2a, hr2b⟩
      have hc2ne0 : center2 ≠ center0 := by
        intro heq
        have hnear : hammingDistance center0.1 (C.encode z0) <= 1 := by
          rw [← heq]
          exact hr2z
        omega
      have hc2eq1 : center2 = center1 :=
        eq_second_of_card_le_two
          (commonRadiusOneCenters_card_le_two habCode)
          hcenters hc2ne0
      have hval : center2.1 = center1.1 := congrArg Subtype.val hc2eq1
      rw [← hval]
      exact hr2w
  · refine ⟨C.encode a, ?_⟩
    intro z hz
    have hza : z = a := by
      by_contra hne
      exact hsecond ⟨z, hz, hne⟩
    subst z
    have hzero : hammingDistance (C.encode a) (C.encode a) = 0 :=
      hammingDistance_eq_zero_iff.mpr rfl
    omega

/-! ## Four-Helly projection theorem -/

/-- Fourwise radius-one compatibility glues into a genuine received-word
projection on every cell. -/
noncomputable def radiusOneProjectionOfFourwise
    {m N : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (hfour : CellFourwiseRadiusCompatible C cellOf (R := 1)) :
    CellReceivedWordProjection C cellOf 1 := by
  classical
  have hexists : forall c : Cell, ∃ received : Assignment N,
      forall a : Assignment m, cellOf a = c ->
        hammingDistance received (C.encode a) <= 1 := by
    intro c
    by_cases hinh : ∃ a : Assignment m, cellOf a = c
    · obtain ⟨a, ha⟩ := hinh
      exact common_center_for_fiber_of_fourwise C cellOf hfour ha
    · exact ⟨fun _ => false, fun a ha => False.elim (hinh ⟨a, ha⟩)⟩
  exact
    { received := fun c => Classical.choose (hexists c)
      trueCodewordNear := fun a =>
        Classical.choose_spec (hexists (cellOf a)) a rfl }

/-- Exact radius-one local-to-global threshold: fourwise compatibility is
equivalent to existence of a coherent cell received-word projection. -/
theorem fourwise_iff_radiusOneProjection
    {m N : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell) :
    CellFourwiseRadiusCompatible C cellOf (R := 1) ↔
      Nonempty (CellReceivedWordProjection C cellOf 1) := by
  constructor
  · intro hfour
    exact ⟨radiusOneProjectionOfFourwise C cellOf hfour⟩
  · rintro ⟨P⟩
    exact projection_to_fourwise C cellOf P

end PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneFourHellyEndpoint

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneFourHellyEndpoint.agree_elsewhere_of_distance_le_one
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneFourHellyEndpoint.commonRadiusOneCenters_card_le_two
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneFourHellyEndpoint.eq_second_of_card_le_two
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneFourHellyEndpoint.common_center_for_fiber_of_fourwise
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneFourHellyEndpoint.fourwise_iff_radiusOneProjection
