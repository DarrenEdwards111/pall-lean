import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultiSwitchingLayeredBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTwoSATSimpleWalkCutoff

/-!
# Width-two outside signatures as implication-graph clauses

The multi-switching bridge stores the semantic outside part of a competitor as a finset of
`Rung4Literal`s.  The verified 2-SAT development instead uses pairs `(variable, demanded value)`.
This file closes that representation boundary.  A width-two nonempty signature is represented by
one pair clause; a singleton is represented by repeating its literal.  The resulting list formula
has exactly the hitting semantics of the original competitor core and uses the existing
`TwoSATFastSAT.Edge` relation without introducing a second implication graph.

The nonempty premise is material: an empty outside signature is an empty CNF clause, which cannot
be represented by a pair clause.  The Hall-obstruction application already records nonempty
incidence explicitly.
-/

namespace PallLean.Paper93.DeepMath.PathB.MultiSwitching

open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting
open PallLean.Paper93.DeepMath.PathB.TwoSATFastSAT
open PallLean.Paper93.DeepMath.PathB.TwoSATSCCLinearBudget
open PallLean.Paper93.DeepMath.PathB.TwoSATSimpleWalkCutoff
open PallLean.Paper93.DeepMath.PathB.TwoSATBoundedReachability

variable {n G pad : ℕ}

/-- The 2-SAT literal demanded by an outside competitor occurrence.  Hitting a competitor means
assigning the variable its falsifying value, so that value is exactly the 2-SAT polarity. -/
def outsideLiteralToTwoSAT (ell : Rung4Literal n) : Lit n :=
  (litVar ell, falValue ell)

/-- Variable together with falsifying polarity remembers the original outside literal. -/
theorem outsideLiteralToTwoSAT_injective :
    Function.Injective (@outsideLiteralToTwoSAT n) := by
  intro a b hab
  cases a with
  | pos i =>
      cases b with
      | pos j =>
          have hij : i = j := congrArg Prod.fst hab
          exact congrArg Rung4Literal.pos hij
      | neg j => simp [outsideLiteralToTwoSAT, litVar, falValue] at hab
  | neg i =>
      cases b with
      | pos j => simp [outsideLiteralToTwoSAT, litVar, falValue] at hab
      | neg j =>
          have hij : i = j := congrArg Prod.fst hab
          exact congrArg Rung4Literal.neg hij

/-- A nonempty outside-variable support contains a polarity-sensitive outside literal. -/
theorem competitorOutsideTargetLiteralSet_nonempty_of_vars_nonempty
    {target : Fin G → Depth3.Clause n} {U : Depth3.Clause n}
    (hvars : (competitorOutsideTargetVars target U).Nonempty) :
    (competitorOutsideTargetLiteralSet target U).Nonempty := by
  obtain ⟨i, hi⟩ := hvars
  rw [mem_competitorOutsideTargetVars] at hi
  obtain ⟨⟨ell, hell, rfl⟩, hout⟩ := hi
  exact ⟨ell, (mem_competitorOutsideTargetLiteralSet target U ell).2 ⟨hell, hout⟩⟩

@[simp] theorem litVal_outsideLiteralToTwoSAT
    (assignment : Fin n → Bool) (ell : Rung4Literal n) :
    litVal assignment (outsideLiteralToTwoSAT ell) ↔
      assignment (litVar ell) = falValue ell := by
  rfl

/-- Satisfaction of one semantic outside-literal signature. -/
def OutsideSignatureSat (assignment : Fin n → Bool)
    (signature : Finset (Rung4Literal n)) : Prop :=
  ∃ ell ∈ signature, assignment (litVar ell) = falValue ell

/-- The pair clause associated with two outside literals.  Equal arguments encode a unit clause. -/
def outsidePairClause (a b : Rung4Literal n) :
    PallLean.Paper93.DeepMath.PathB.TwoSATFastSAT.Clause n :=
  (outsideLiteralToTwoSAT a, outsideLiteralToTwoSAT b)

theorem clauseSat_outsidePairClause_iff
    (assignment : Fin n → Bool) (a b : Rung4Literal n) :
    clauseSat assignment (outsidePairClause a b) ↔
      assignment (litVar a) = falValue a ∨
        assignment (litVar b) = falValue b := by
  rfl

/-- A nonempty finset of cardinality at most two is a pair, allowing the two entries to coincide.
This is the exact syntactic normalization needed for unit clauses. -/
theorem exists_pair_eq_of_nonempty_of_card_le_two
    {S : Finset (Rung4Literal n)} (hne : S.Nonempty) (hcard : S.card ≤ 2) :
    ∃ a b, S = {a, b} := by
  have hpos : 0 < S.card := Finset.card_pos.mpr hne
  have hcases : S.card = 1 ∨ S.card = 2 := by omega
  rcases hcases with hone | htwo
  · obtain ⟨a, ha⟩ := hne
    refine ⟨a, a, ?_⟩
    simp only [Finset.pair_eq_singleton]
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨ha, ?_⟩
    intro x hx
    have hleOne : S.card ≤ 1 := by omega
    exact (Finset.card_le_one.mp hleOne) x hx a ha
  · obtain ⟨a, b, _, hab⟩ := Finset.card_eq_two.mp htwo
    exact ⟨a, b, hab⟩

/-- Every nonempty width-two signature has a pair-clause presentation with exactly the same
satisfying assignments. -/
theorem exists_outsidePairClause_semantics
    {S : Finset (Rung4Literal n)} (hne : S.Nonempty) (hcard : S.card ≤ 2) :
    ∃ a b, S = {a, b} ∧
      ∀ assignment, OutsideSignatureSat assignment S ↔
        clauseSat assignment (outsidePairClause a b) := by
  obtain ⟨a, b, rfl⟩ := exists_pair_eq_of_nonempty_of_card_le_two hne hcard
  refine ⟨a, b, rfl, fun assignment => ?_⟩
  simp [OutsideSignatureSat, clauseSat_outsidePairClause_iff]

/-- The generated pair contributes exactly the two standard skew implication edges.  This
states the representation bridge directly in the existing semantic `Edge` API. -/
theorem edge_singleton_outsidePairClause_iff
    (a b : Rung4Literal n) (x y : Lit n) :
    Edge [outsidePairClause a b] x y ↔
      (x = neg (outsideLiteralToTwoSAT a) ∧ y = outsideLiteralToTwoSAT b) ∨
      (x = neg (outsideLiteralToTwoSAT b) ∧ y = outsideLiteralToTwoSAT a) := by
  simp [Edge, outsidePairClause]

/-- Choose the pair presentation of one core member's semantic outside signature. -/
noncomputable def coreOutsidePair
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    (p : ↑core) : Rung4Literal n × Rung4Literal n :=
  Classical.choose <| show ∃ ab : Rung4Literal n × Rung4Literal n,
      competitorOutsideTargetLiteralSet target p.1.2 = {ab.1, ab.2} by
    obtain ⟨a, b, hab⟩ := exists_pair_eq_of_nonempty_of_card_le_two
      (hnonempty p.1 p.2)
      ((competitorOutsideTargetLiteralSet_card_le_length target p.1.2).trans
        (hwidth p.1 p.2))
    exact ⟨(a, b), hab⟩

theorem coreOutsidePair_spec
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    (p : ↑core) :
    competitorOutsideTargetLiteralSet target p.1.2 =
      {(coreOutsidePair hnonempty hwidth p).1,
        (coreOutsidePair hnonempty hwidth p).2} := by
  exact Classical.choose_spec <| show ∃ ab : Rung4Literal n × Rung4Literal n,
      competitorOutsideTargetLiteralSet target p.1.2 = {ab.1, ab.2} by
    obtain ⟨a, b, hab⟩ := exists_pair_eq_of_nonempty_of_card_le_two
      (hnonempty p.1 p.2)
      ((competitorOutsideTargetLiteralSet_card_le_length target p.1.2).trans
        (hwidth p.1 p.2))
    exact ⟨(a, b), hab⟩

/-- The concrete 2-CNF list associated with a nonempty width-two competitor core.  It retains one
pair clause per indexed core member; duplicate pair clauses are harmless and remain visible to
later edge charging. -/
noncomputable def outsideCoreTwoSATClauses
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2) :
    List (PallLean.Paper93.DeepMath.PathB.TwoSATFastSAT.Clause n) :=
  core.attach.toList.map fun p =>
    outsidePairClause (coreOutsidePair hnonempty hwidth p).1
      (coreOutsidePair hnonempty hwidth p).2

/-- The chosen ordered pair clause attached to one retained core member. -/
noncomputable def coreOutsideClause
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    (p : ↑core) : PallLean.Paper93.DeepMath.PathB.TwoSATFastSAT.Clause n :=
  outsidePairClause (coreOutsidePair hnonempty hwidth p).1
    (coreOutsidePair hnonempty hwidth p).2

theorem outsideCoreTwoSATClauses_eq_map_coreOutsideClause
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2) :
    outsideCoreTwoSATClauses hnonempty hwidth =
      core.attach.toList.map (coreOutsideClause hnonempty hwidth) := by
  rfl

/-- Minimality makes the concrete translated pair clause identify its attached core member.
The order chosen for a two-element signature is irrelevant: equality of ordered clauses implies
equality of the underlying unordered signatures. -/
theorem InclusionMinimalUnsatisfiableCore.coreOutsideClause_injective
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2) :
    Function.Injective (coreOutsideClause hnonempty hwidth) := by
  intro p q hpq
  apply Subtype.ext
  apply hminimal.outsideLiteralSet_injectiveOn p.2 q.2
  have hpairs : coreOutsidePair hnonempty hwidth p =
      coreOutsidePair hnonempty hwidth q := by
    apply Prod.ext
    · exact outsideLiteralToTwoSAT_injective (congrArg Prod.fst hpq)
    · exact outsideLiteralToTwoSAT_injective (congrArg Prod.snd hpq)
  change competitorOutsideTargetLiteralSet target p.1.2 =
    competitorOutsideTargetLiteralSet target q.1.2
  rw [coreOutsidePair_spec hnonempty hwidth p,
    coreOutsidePair_spec hnonempty hwidth q, hpairs]

/-- Equality of an implication edge remembers the underlying pair clause up to swapping its two
literals.  This is the orientation-forgetting fact needed when a path charge may select either
of a clause's directed edges. -/
theorem unorderedClause_eq_of_shared_implicationEdge
    (c d : PallLean.Paper93.DeepMath.PathB.TwoSATFastSAT.Clause n)
    (e : Lit n × Lit n)
    (hc : e = (neg c.1, c.2) ∨ e = (neg c.2, c.1))
    (hd : e = (neg d.1, d.2) ∨ e = (neg d.2, d.1)) :
    ({c.1, c.2} : Finset (Lit n)) = {d.1, d.2} := by
  rcases hc with hc | hc <;> rcases hd with hd | hd
  · have h := hc.symm.trans hd
    have h1 : c.1 = d.1 := by
      simpa using congrArg (fun z => neg z.1) h
    have h2 : c.2 = d.2 := (Prod.mk.inj h).2
    simp [h1, h2]
  · have h := hc.symm.trans hd
    have h1 : c.1 = d.2 := by
      simpa using congrArg (fun z => neg z.1) h
    have h2 : c.2 = d.1 := (Prod.mk.inj h).2
    simp [h1, h2, Finset.pair_comm]
  · have h := hc.symm.trans hd
    have h1 : c.2 = d.1 := by
      simpa using congrArg (fun z => neg z.1) h
    have h2 : c.1 = d.2 := (Prod.mk.inj h).2
    simp [h1, h2, Finset.pair_comm]
  · have h := hc.symm.trans hd
    have h1 : c.2 = d.2 := by
      simpa using congrArg (fun z => neg z.1) h
    have h2 : c.1 = d.1 := (Prod.mk.inj h).2
    simp [h1, h2]

/-- Even after forgetting which of the two directed orientations was charged, a used edge still
identifies its member of the semantic minimal core.  Hence choosing an orientation cannot create
a collision in the eventual occurrence-counting map. -/
theorem InclusionMinimalUnsatisfiableCore.eq_of_shared_coreOutsideClause_edge
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    (p q : ↑core) (e : Lit n × Lit n)
    (hp : let c := coreOutsideClause hnonempty hwidth p
      e = (neg c.1, c.2) ∨ e = (neg c.2, c.1))
    (hq : let c := coreOutsideClause hnonempty hwidth q
      e = (neg c.1, c.2) ∨ e = (neg c.2, c.1)) :
    p = q := by
  apply Subtype.ext
  apply hminimal.outsideLiteralSet_injectiveOn p.2 q.2
  apply Finset.image_injective outsideLiteralToTwoSAT_injective
  change Finset.image outsideLiteralToTwoSAT
      (competitorOutsideTargetLiteralSet target p.1.2) =
    Finset.image outsideLiteralToTwoSAT
      (competitorOutsideTargetLiteralSet target q.1.2)
  rw [coreOutsidePair_spec hnonempty hwidth p,
    coreOutsidePair_spec hnonempty hwidth q]
  simpa [coreOutsideClause, outsidePairClause] using
    unorderedClause_eq_of_shared_implicationEdge
      (coreOutsideClause hnonempty hwidth p)
      (coreOutsideClause hnonempty hwidth q) e hp hq

/-- The translated formula has one distinct clause for every member of a minimal core. -/
theorem InclusionMinimalUnsatisfiableCore.outsideCoreTwoSATClauses_nodup
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2) :
    (outsideCoreTwoSATClauses hnonempty hwidth).Nodup := by
  rw [outsideCoreTwoSATClauses_eq_map_coreOutsideClause]
  exact (Finset.nodup_toList core.attach).map
    (hminimal.coreOutsideClause_injective hnonempty hwidth)

/-- The semantic deletion witness for an attached core member satisfies the concrete translated
list after erasing that member's pair clause.  Injectivity above is the essential interface: it
ensures that membership in the erased list can only come from a different core member. -/
theorem InclusionMinimalUnsatisfiableCore.twoSat_erase_coreOutsideClause
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    (p : ↑core) :
    TwoSat ((outsideCoreTwoSATClauses hnonempty hwidth).erase
      (coreOutsideClause hnonempty hwidth p)) := by
  obtain ⟨assignment, hhit⟩ := hminimal.2 p.1 p.2
  refine ⟨assignment, ?_⟩
  intro c hc
  have hcFull : c ∈ outsideCoreTwoSATClauses hnonempty hwidth :=
    List.mem_of_mem_erase hc
  rw [outsideCoreTwoSATClauses_eq_map_coreOutsideClause] at hcFull
  obtain ⟨q, hqList, rfl⟩ := List.mem_map.mp hcFull
  have hqne : q ≠ p := by
    intro hqp
    subst q
    exact ((hminimal.outsideCoreTwoSATClauses_nodup hnonempty hwidth).mem_erase_iff.mp hc).1 rfl
  have hqvalne : q.1 ≠ p.1 := by
    intro hqp
    exact hqne (Subtype.ext hqp)
  obtain ⟨ell, hell, hout, hvalue⟩ :=
    hhit q.1 (Finset.mem_erase.mpr ⟨hqvalne, q.2⟩)
  have hellSignature : ell ∈ competitorOutsideTargetLiteralSet target q.1.2 :=
    (mem_competitorOutsideTargetLiteralSet target q.1.2 ell).2 ⟨hell, hout⟩
  rw [coreOutsidePair_spec hnonempty hwidth q] at hellSignature
  simp only [Finset.mem_insert, Finset.mem_singleton] at hellSignature
  rw [show coreOutsideClause hnonempty hwidth q =
      outsidePairClause (coreOutsidePair hnonempty hwidth q).1
        (coreOutsidePair hnonempty hwidth q).2 from rfl,
    clauseSat_outsidePairClause_iff]
  rcases hellSignature with hellSignature | hellSignature
  · subst ell
    exact Or.inl hvalue
  · subst ell
    exact Or.inr hvalue

/-- Core hitting is exactly satisfaction of the translated 2-CNF. -/
theorem hitsOutsideCompetitorCore_iff_twoSATClauses
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    (assignment : Fin n → Bool) :
    HitsOutsideCompetitorCore target core assignment ↔
      ∀ c ∈ outsideCoreTwoSATClauses hnonempty hwidth,
        clauseSat assignment c := by
  constructor
  · intro hhit c hc
    simp only [outsideCoreTwoSATClauses, List.mem_map, Finset.mem_toList] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    have hpCore : p.1 ∈ core := p.2
    obtain ⟨ell, hell, hout, hvalue⟩ := hhit p.1 hpCore
    have hellSignature : ell ∈ competitorOutsideTargetLiteralSet target p.1.2 :=
      (mem_competitorOutsideTargetLiteralSet target p.1.2 ell).2 ⟨hell, hout⟩
    rw [coreOutsidePair_spec hnonempty hwidth p] at hellSignature
    simp only [Finset.mem_insert, Finset.mem_singleton] at hellSignature
    rw [clauseSat_outsidePairClause_iff]
    rcases hellSignature with hellSignature | hellSignature
    · subst ell
      exact Or.inl hvalue
    · subst ell
      exact Or.inr hvalue
  · intro hsat p hp
    let q : ↑core := ⟨p, hp⟩
    have hmem : outsidePairClause (coreOutsidePair hnonempty hwidth q).1
        (coreOutsidePair hnonempty hwidth q).2 ∈
        outsideCoreTwoSATClauses hnonempty hwidth := by
      apply List.mem_map.mpr
      refine ⟨q, ?_, rfl⟩
      simp
    have hclause := hsat _ hmem
    rw [clauseSat_outsidePairClause_iff] at hclause
    rcases hclause with hleft | hright
    · let ell := (coreOutsidePair hnonempty hwidth q).1
      have hellSignature : ell ∈ competitorOutsideTargetLiteralSet target p.2 := by
        rw [coreOutsidePair_spec hnonempty hwidth q]
        simp [ell]
      obtain ⟨hell, hout⟩ :=
        (mem_competitorOutsideTargetLiteralSet target p.2 ell).1 hellSignature
      exact ⟨ell, hell, hout, hleft⟩
    · let ell := (coreOutsidePair hnonempty hwidth q).2
      have hellSignature : ell ∈ competitorOutsideTargetLiteralSet target p.2 := by
        rw [coreOutsidePair_spec hnonempty hwidth q]
        simp [ell]
      obtain ⟨hell, hout⟩ :=
        (mem_competitorOutsideTargetLiteralSet target p.2 ell).1 hellSignature
      exact ⟨ell, hell, hout, hright⟩

/-- Formula-level bridge: the verified 2-SAT predicate is precisely satisfiability of the
original nonempty width-two competitor core. -/
theorem twoSat_outsideCore_iff
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2) :
    TwoSat (outsideCoreTwoSATClauses hnonempty hwidth) ↔
      ∃ assignment, HitsOutsideCompetitorCore target core assignment := by
  simp only [TwoSat]
  constructor
  · rintro ⟨assignment, hassignment⟩
    exact ⟨assignment,
      (hitsOutsideCompetitorCore_iff_twoSATClauses hnonempty hwidth assignment).2 hassignment⟩
  · rintro ⟨assignment, hassignment⟩
    exact ⟨assignment,
      (hitsOutsideCompetitorCore_iff_twoSATClauses hnonempty hwidth assignment).1 hassignment⟩

/-- A minimally unsatisfiable nonempty width-two outside core produces the standard pair of
oppositely directed implication reaches in the translated formula. -/
theorem InclusionMinimalUnsatisfiableCore.exists_twoSAT_contradiction_reaches
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2) :
    ∃ ell : Lit n,
      Reach (outsideCoreTwoSATClauses hnonempty hwidth) ell (neg ell) ∧
      Reach (outsideCoreTwoSATClauses hnonempty hwidth) (neg ell) ell := by
  let cls := outsideCoreTwoSATClauses hnonempty hwidth
  have hnotTwoSat : ¬ TwoSat cls := by
    intro hsat
    apply hminimal.1
    exact (twoSat_outsideCore_iff hnonempty hwidth).mp hsat
  have hnotNoContra : ¬ NoContra cls := by
    intro hno
    exact hnotTwoSat (twosat_complete cls hno)
  simpa only [NoContra, not_forall, not_not] using hnotNoContra

/-- Cycle erasure turns the two contradiction reaches into simple walks.  Each has at most
`2n-1` edges, so together they use at most `4n-2` edge occurrences.  This is the graph-theoretic
count required by the classical minimal-2-CNF argument; localizing which clauses can be charged
to these walks remains a separate obligation. -/
theorem InclusionMinimalUnsatisfiableCore.exists_twoSAT_simple_contradiction_walks
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2) :
    ∃ (ell : Lit n)
      (forward : EdgeWalk (implicationEdges
        (outsideCoreTwoSATClauses hnonempty hwidth)) ell (neg ell))
      (backward : EdgeWalk (implicationEdges
        (outsideCoreTwoSATClauses hnonempty hwidth)) (neg ell) ell),
      (EdgeWalk.vertices forward).Nodup ∧
      (EdgeWalk.vertices backward).Nodup ∧
      EdgeWalk.length forward ≤ 2 * n - 1 ∧
      EdgeWalk.length backward ≤ 2 * n - 1 ∧
      EdgeWalk.length forward + EdgeWalk.length backward ≤ 4 * n - 2 := by
  obtain ⟨ell, hforward, hbackward⟩ :=
    hminimal.exists_twoSAT_contradiction_reaches hnonempty hwidth
  obtain ⟨forward₀⟩ := EdgeWalk.nonempty_of_reach
    (outsideCoreTwoSATClauses hnonempty hwidth) hforward
  obtain ⟨backward₀⟩ := EdgeWalk.nonempty_of_reach
    (outsideCoreTwoSATClauses hnonempty hwidth) hbackward
  obtain ⟨forward, hforwardSimple⟩ := EdgeWalk.exists_simple forward₀
  obtain ⟨backward, hbackwardSimple⟩ := EdgeWalk.exists_simple backward₀
  have hforwardLt := EdgeWalk.length_lt_card_of_nodup forward hforwardSimple
  have hbackwardLt := EdgeWalk.length_lt_card_of_nodup backward hbackwardSimple
  rw [card_literals] at hforwardLt hbackwardLt
  refine ⟨ell, forward, backward, hforwardSimple, hbackwardSimple, ?_, ?_, ?_⟩ <;> omega

/-! ## The deletion-witness path charge

The classical `4n-2` proof needs more than short contradiction paths: every indispensable
clause must contribute an edge to one of those fixed paths.  The following list-level lemmas
isolate that argument without depending on the competitor-core representation.
-/

namespace TwoSATPathCharge

/-- The directed edge occurrences traversed by an explicit walk, in traversal order. -/
def EdgeWalk.usedEdges {edges : List (Lit n × Lit n)} :
    {a b : Lit n} → EdgeWalk edges a b → List (Lit n × Lit n)
  | _, _, .nil _ => []
  | _, _, .snoc (b := b) (c := c) walk _ =>
      EdgeWalk.usedEdges walk ++ [(b, c)]

@[simp] theorem EdgeWalk.usedEdges_nil
    {edges : List (Lit n × Lit n)} (a : Lit n) :
    EdgeWalk.usedEdges (EdgeWalk.nil (edges := edges) a) = [] := by
  simp [EdgeWalk.usedEdges]

@[simp] theorem EdgeWalk.usedEdges_snoc
    {edges : List (Lit n × Lit n)} {a b c : Lit n}
    (walk : EdgeWalk edges a b) (edge : (b, c) ∈ edges) :
    EdgeWalk.usedEdges (walk.snoc edge) = EdgeWalk.usedEdges walk ++ [(b, c)] := by
  simp [EdgeWalk.usedEdges]

theorem EdgeWalk.usedEdges_subset
    {edges : List (Lit n × Lit n)} {a b : Lit n}
    (walk : EdgeWalk edges a b) :
    ∀ e ∈ EdgeWalk.usedEdges walk, e ∈ edges := by
  induction walk with
  | nil => simp
  | @snoc b c walk edge ih =>
      intro e he
      simp only [EdgeWalk.usedEdges_snoc, List.mem_append, List.mem_singleton] at he
      exact he.elim (fun he' => ih e he') (fun he' => he' ▸ edge)

@[simp] theorem EdgeWalk.usedEdges_length
    {edges : List (Lit n × Lit n)} {a b : Lit n}
    (walk : EdgeWalk edges a b) :
    (EdgeWalk.usedEdges walk).length = EdgeWalk.length walk := by
  induction walk with
  | nil => simp [EdgeWalk.length]
  | snoc walk edge ih => simp [EdgeWalk.length, ih]

/-- The destination of every traversed edge occurs in the walk's vertex list. -/
theorem EdgeWalk.usedEdges_snd_mem_vertices
    {edges : List (Lit n × Lit n)} {a b : Lit n}
    (walk : EdgeWalk edges a b) {e : Lit n × Lit n}
    (he : e ∈ EdgeWalk.usedEdges walk) : e.2 ∈ EdgeWalk.vertices walk := by
  induction walk with
  | nil => simp at he
  | @snoc b c walk edge ih =>
      simp only [EdgeWalk.usedEdges_snoc, List.mem_append, List.mem_singleton] at he
      rw [EdgeWalk.vertices_snoc, List.mem_append]
      exact he.elim (fun he' => Or.inl (ih he')) (fun he' => Or.inr (by simp [he']))

/-- On a vertex-simple walk, a destination literal identifies the traversed directed edge.
This is the local injection used to count only those edges internal to a chosen support. -/
theorem EdgeWalk.usedEdges_snd_injective_of_vertices_nodup
    {edges : List (Lit n × Lit n)} {a b : Lit n}
    (walk : EdgeWalk edges a b) (hsimple : (EdgeWalk.vertices walk).Nodup) :
    ∀ {e f : Lit n × Lit n}, e ∈ EdgeWalk.usedEdges walk →
      f ∈ EdgeWalk.usedEdges walk → e.2 = f.2 → e = f := by
  induction walk with
  | nil => simp
  | @snoc b c walk edge ih =>
      rw [EdgeWalk.vertices_snoc] at hsimple
      have hprev : (EdgeWalk.vertices walk).Nodup := hsimple.of_append_left
      have hc : c ∉ EdgeWalk.vertices walk := by
        intro hmem
        exact (List.disjoint_of_nodup_append hsimple hmem (by simp)).elim
      intro e f he hf hef
      simp only [EdgeWalk.usedEdges_snoc, List.mem_append, List.mem_singleton] at he hf
      rcases he with he | rfl <;> rcases hf with hf | rfl
      · exact ih hprev he hf hef
      · change e.2 = c at hef
        exact (hc (hef ▸ EdgeWalk.usedEdges_snd_mem_vertices walk he)).elim
      · change c = f.2 at hef
        exact (hc (hef.symm ▸ EdgeWalk.usedEdges_snd_mem_vertices walk hf)).elim
      · rfl

/-- Directed edge values of a walk whose two endpoint variables lie in `support`. -/
def EdgeWalk.internalUsedEdges
    {edges : List (Lit n × Lit n)} {a b : Lit n}
    (walk : EdgeWalk edges a b) (support : Finset (Fin n)) : Finset (Lit n × Lit n) :=
  (EdgeWalk.usedEdges walk).toFinset.filter fun e =>
    e.1.1 ∈ support ∧ e.2.1 ∈ support

/-- A vertex-simple walk uses at most two internal directed edge values per supported variable.
The destination map is injective, and its image lies among the two polarities over `support`. -/
theorem EdgeWalk.internalUsedEdges_card_le_two_mul
    {edges : List (Lit n × Lit n)} {a b : Lit n}
    (walk : EdgeWalk edges a b) (hsimple : (EdgeWalk.vertices walk).Nodup)
    (support : Finset (Fin n)) :
    (EdgeWalk.internalUsedEdges walk support).card ≤ 2 * support.card := by
  let target : Finset (Lit n) := support ×ˢ (Finset.univ : Finset Bool)
  let destination : ↑(EdgeWalk.internalUsedEdges walk support) → ↑target := fun e =>
    ⟨e.1.2, by
      have he := e.2
      simp only [EdgeWalk.internalUsedEdges, Finset.mem_filter] at he
      simpa [target] using he.2.2⟩
  have hinjective : Function.Injective destination := by
    intro e f hef
    apply Subtype.ext
    apply EdgeWalk.usedEdges_snd_injective_of_vertices_nodup walk hsimple
    · exact List.mem_toFinset.mp ((Finset.mem_filter.mp e.2).1)
    · exact List.mem_toFinset.mp ((Finset.mem_filter.mp f.2).1)
    · exact congrArg Subtype.val hef
  have hcard : Fintype.card ↑(EdgeWalk.internalUsedEdges walk support) ≤
      Fintype.card ↑target := Fintype.card_le_of_injective destination hinjective
  simp only [Fintype.card_coe] at hcard
  simpa [target, Nat.mul_comm] using hcard

/-- A walk can be transported to a second edge list once every edge occurrence that it actually
uses belongs to the second list. -/
theorem EdgeWalk.exists_of_usedEdges_subset
    {edges edges' : List (Lit n × Lit n)} {a b : Lit n}
    (walk : EdgeWalk edges a b)
    (hsubset : ∀ e ∈ EdgeWalk.usedEdges walk, e ∈ edges') :
    Nonempty (EdgeWalk edges' a b) := by
  induction walk with
  | nil => exact ⟨.nil _⟩
  | @snoc b c walk edge ih =>
      obtain ⟨walk'⟩ := ih fun e he => hsubset e (by simp [he])
      exact ⟨walk'.snoc (hsubset (b, c) (by simp))⟩

theorem mem_implicationEdges_erase_of_ne
    (cls : List (PallLean.Paper93.DeepMath.PathB.TwoSATFastSAT.Clause n))
    (c : PallLean.Paper93.DeepMath.PathB.TwoSATFastSAT.Clause n)
    (e : Lit n × Lit n)
    (he : e ∈ implicationEdges cls)
    (hleft : e ≠ (neg c.1, c.2))
    (hright : e ≠ (neg c.2, c.1)) :
    e ∈ implicationEdges (cls.erase c) := by
  simp only [implicationEdges, List.mem_flatMap] at he ⊢
  obtain ⟨d, hd, hed⟩ := he
  by_cases hdc : d = c
  · subst d
    simp at hed
    rcases hed with hed | hed
    · exact (hleft hed).elim
    · exact (hright hed).elim
  · refine ⟨d, ?_, hed⟩
    simp [hd, hdc]

/-- If deleting `c` is satisfiable, then every fixed pair of contradiction walks for the full
formula uses at least one of the two implication edges contributed by `c`.  This is the exact
minimality charge in the standard linear upper bound for minimally unsatisfiable 2-CNF. -/
theorem clause_edge_used_of_twoSat_erase
    (cls : List (PallLean.Paper93.DeepMath.PathB.TwoSATFastSAT.Clause n))
    (c : PallLean.Paper93.DeepMath.PathB.TwoSATFastSAT.Clause n)
    (ell : Lit n)
    (forward : EdgeWalk (implicationEdges cls) ell (neg ell))
    (backward : EdgeWalk (implicationEdges cls) (neg ell) ell)
    (herase : TwoSat (cls.erase c)) :
    (neg c.1, c.2) ∈ EdgeWalk.usedEdges forward ∨
      (neg c.2, c.1) ∈ EdgeWalk.usedEdges forward ∨
      (neg c.1, c.2) ∈ EdgeWalk.usedEdges backward ∨
      (neg c.2, c.1) ∈ EdgeWalk.usedEdges backward := by
  by_contra hused
  simp only [not_or] at hused
  obtain ⟨forward'⟩ := EdgeWalk.exists_of_usedEdges_subset forward fun e he =>
      mem_implicationEdges_erase_of_ne cls c e
        (EdgeWalk.usedEdges_subset forward e he)
        (fun heq => hused.1 (heq ▸ he))
        (fun heq => hused.2.1 (heq ▸ he))
  obtain ⟨backward'⟩ := EdgeWalk.exists_of_usedEdges_subset backward fun e he =>
      mem_implicationEdges_erase_of_ne cls c e
        (EdgeWalk.usedEdges_subset backward e he)
        (fun heq => hused.2.2.1 (heq ▸ he))
        (fun heq => hused.2.2.2 (heq ▸ he))
  have hforward : Reach (cls.erase c) ell (neg ell) :=
    reachWithin_sound (cls.erase c) forward'.to_reachWithin
  have hbackward : Reach (cls.erase c) (neg ell) ell :=
    reachWithin_sound (cls.erase c) backward'.to_reachWithin
  exact (twosat_sound (cls.erase c) herase ell) ⟨hforward, hbackward⟩

end TwoSATPathCharge

/-- Every retained member of a minimal nonempty width-two outside core contributes one of its two
directed implication edges to any fixed pair of contradiction walks.  This is the core-level
path-coverage theorem obtained by composing semantic deletion witnesses with concrete list
erasure; no special choice of contradiction paths is required. -/
theorem InclusionMinimalUnsatisfiableCore.coreOutsideClause_edge_used
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    (ell : Lit n)
    (forward : EdgeWalk (implicationEdges
      (outsideCoreTwoSATClauses hnonempty hwidth)) ell (neg ell))
    (backward : EdgeWalk (implicationEdges
      (outsideCoreTwoSATClauses hnonempty hwidth)) (neg ell) ell)
    (p : ↑core) :
    let c := coreOutsideClause hnonempty hwidth p
    (neg c.1, c.2) ∈ TwoSATPathCharge.EdgeWalk.usedEdges forward ∨
      (neg c.2, c.1) ∈ TwoSATPathCharge.EdgeWalk.usedEdges forward ∨
      (neg c.1, c.2) ∈ TwoSATPathCharge.EdgeWalk.usedEdges backward ∨
      (neg c.2, c.1) ∈ TwoSATPathCharge.EdgeWalk.usedEdges backward := by
  exact TwoSATPathCharge.clause_edge_used_of_twoSat_erase
    (outsideCoreTwoSATClauses hnonempty hwidth)
    (coreOutsideClause hnonempty hwidth p) ell forward backward
    (hminimal.twoSat_erase_coreOutsideClause hnonempty hwidth p)

/-! ## Injective charging into the two used-edge lists -/

/-- The finite disjoint union of directed edge values used by the forward and backward walks.
The sum tag distinguishes the two walks, but deliberately does not record which clause orientation
was selected. -/
abbrev TwoWalkUsedEdgeSlot
    {edges : List (Lit n × Lit n)} {a b : Lit n}
    (forward : EdgeWalk edges a b) (backward : EdgeWalk edges b a) :=
  Sum {e // e ∈ (TwoSATPathCharge.EdgeWalk.usedEdges forward).toFinset}
    {e // e ∈ (TwoSATPathCharge.EdgeWalk.usedEdges backward).toFinset}

/-- The two-walk slot type restricted to directed edges internal to `support`. -/
abbrev TwoWalkInternalEdgeSlot
    {edges : List (Lit n × Lit n)} {a b : Lit n}
    (forward : EdgeWalk edges a b) (backward : EdgeWalk edges b a)
    (support : Finset (Fin n)) :=
  Sum {e // e ∈ TwoSATPathCharge.EdgeWalk.internalUsedEdges forward support}
    {e // e ∈ TwoSATPathCharge.EdgeWalk.internalUsedEdges backward support}

/-- A slot validly charges `p` when its directed edge is one of the two orientations contributed
by `p`'s translated pair clause. -/
def CoreOutsideEdgeChargeValid
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    {edges : List (Lit n × Lit n)} {a b : Lit n}
    (forward : EdgeWalk edges a b) (backward : EdgeWalk edges b a)
    (p : ↑core) (slot : TwoWalkUsedEdgeSlot forward backward) : Prop :=
  let c := coreOutsideClause hnonempty hwidth p
  match slot with
  | Sum.inl e => e.1 = (neg c.1, c.2) ∨ e.1 = (neg c.2, c.1)
  | Sum.inr e => e.1 = (neg c.1, c.2) ∨ e.1 = (neg c.2, c.1)

/-- Forget the walk tag and subtype proof of a used-edge slot. -/
def TwoWalkUsedEdgeSlot.edge
    {edges : List (Lit n × Lit n)} {a b : Lit n}
    {forward : EdgeWalk edges a b} {backward : EdgeWalk edges b a} :
    TwoWalkUsedEdgeSlot forward backward → Lit n × Lit n
  | Sum.inl e => e.1
  | Sum.inr e => e.1

/-- A valid charge from one core member has both endpoint variables in that member's queried
incidence, provided all of its outside variables are queried.  The negation on the source of an
implication edge changes only polarity, so both endpoints recover the two variables in the
member's semantic outside signature. -/
theorem CoreOutsideEdgeChargeValid.endpoints_mem_incidentQueriedVars
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    {queried : Finset (Fin n)} (p : ↑core)
    (hsupport : competitorOutsideTargetVars target p.1.2 ⊆ queried)
    {edges : List (Lit n × Lit n)} {a b : Lit n}
    {forward : EdgeWalk edges a b} {backward : EdgeWalk edges b a}
    (slot : TwoWalkUsedEdgeSlot forward backward)
    (hvalid : CoreOutsideEdgeChargeValid hnonempty hwidth forward backward p slot) :
    (TwoWalkUsedEdgeSlot.edge slot).1.1 ∈ incidentQueriedVars target queried p.1 ∧
      (TwoWalkUsedEdgeSlot.edge slot).2.1 ∈ incidentQueriedVars target queried p.1 := by
  let x := (coreOutsidePair hnonempty hwidth p).1
  let y := (coreOutsidePair hnonempty hwidth p).2
  have hxSignature : x ∈ competitorOutsideTargetLiteralSet target p.1.2 := by
    rw [coreOutsidePair_spec hnonempty hwidth p]
    simp [x]
  have hySignature : y ∈ competitorOutsideTargetLiteralSet target p.1.2 := by
    rw [coreOutsidePair_spec hnonempty hwidth p]
    simp [y]
  have hxOutside := (mem_competitorOutsideTargetLiteralSet target p.1.2 x).1 hxSignature
  have hyOutside := (mem_competitorOutsideTargetLiteralSet target p.1.2 y).1 hySignature
  have hxVars : litVar x ∈ competitorOutsideTargetVars target p.1.2 :=
    (mem_competitorOutsideTargetVars target p.1.2 (litVar x)).2
      ⟨⟨x, hxOutside.1, rfl⟩, hxOutside.2⟩
  have hyVars : litVar y ∈ competitorOutsideTargetVars target p.1.2 :=
    (mem_competitorOutsideTargetVars target p.1.2 (litVar y)).2
      ⟨⟨y, hyOutside.1, rfl⟩, hyOutside.2⟩
  have hxIncident : litVar x ∈ incidentQueriedVars target queried p.1 :=
    Finset.mem_inter.mpr ⟨hxVars, hsupport hxVars⟩
  have hyIncident : litVar y ∈ incidentQueriedVars target queried p.1 :=
    Finset.mem_inter.mpr ⟨hyVars, hsupport hyVars⟩
  cases slot with
  | inl e =>
      simp only [TwoWalkUsedEdgeSlot.edge]
      change e.1 =
        (neg (outsideLiteralToTwoSAT x), outsideLiteralToTwoSAT y) ∨
        e.1 = (neg (outsideLiteralToTwoSAT y), outsideLiteralToTwoSAT x) at hvalid
      rcases hvalid with hvalid | hvalid
      · rw [show e.1 = _ from hvalid]
        simpa [TwoWalkUsedEdgeSlot.edge, outsideLiteralToTwoSAT] using
          And.intro hxIncident hyIncident
      · rw [show e.1 = _ from hvalid]
        simpa [TwoWalkUsedEdgeSlot.edge, outsideLiteralToTwoSAT] using
          And.intro hyIncident hxIncident
  | inr e =>
      simp only [TwoWalkUsedEdgeSlot.edge]
      change e.1 =
        (neg (outsideLiteralToTwoSAT x), outsideLiteralToTwoSAT y) ∨
        e.1 = (neg (outsideLiteralToTwoSAT y), outsideLiteralToTwoSAT x) at hvalid
      rcases hvalid with hvalid | hvalid
      · rw [show e.1 = _ from hvalid]
        simpa [TwoWalkUsedEdgeSlot.edge, outsideLiteralToTwoSAT] using
          And.intro hxIncident hyIncident
      · rw [show e.1 = _ from hvalid]
        simpa [TwoWalkUsedEdgeSlot.edge, outsideLiteralToTwoSAT] using
          And.intro hyIncident hxIncident

/-- Path coverage supplies at least one valid slot for every retained core member. -/
theorem InclusionMinimalUnsatisfiableCore.exists_coreOutsideEdgeCharge
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    (ell : Lit n)
    (forward : EdgeWalk (implicationEdges
      (outsideCoreTwoSATClauses hnonempty hwidth)) ell (neg ell))
    (backward : EdgeWalk (implicationEdges
      (outsideCoreTwoSATClauses hnonempty hwidth)) (neg ell) ell)
    (p : ↑core) :
    ∃ slot : TwoWalkUsedEdgeSlot forward backward,
      CoreOutsideEdgeChargeValid hnonempty hwidth forward backward p slot := by
  let c := coreOutsideClause hnonempty hwidth p
  rcases hminimal.coreOutsideClause_edge_used hnonempty hwidth ell forward backward p with
    h | h | h | h
  · exact ⟨Sum.inl ⟨(neg c.1, c.2), by simpa using h⟩, Or.inl rfl⟩
  · exact ⟨Sum.inl ⟨(neg c.2, c.1), by simpa using h⟩, Or.inr rfl⟩
  · exact ⟨Sum.inr ⟨(neg c.1, c.2), by simpa using h⟩, Or.inl rfl⟩
  · exact ⟨Sum.inr ⟨(neg c.2, c.1), by simpa using h⟩, Or.inr rfl⟩

/-- Choose one of the covered used-edge slots for each member. -/
noncomputable def InclusionMinimalUnsatisfiableCore.coreOutsideEdgeCharge
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    (ell : Lit n)
    (forward : EdgeWalk (implicationEdges
      (outsideCoreTwoSATClauses hnonempty hwidth)) ell (neg ell))
    (backward : EdgeWalk (implicationEdges
      (outsideCoreTwoSATClauses hnonempty hwidth)) (neg ell) ell)
    (p : ↑core) : TwoWalkUsedEdgeSlot forward backward :=
  Classical.choose <|
    hminimal.exists_coreOutsideEdgeCharge hnonempty hwidth ell forward backward p

theorem InclusionMinimalUnsatisfiableCore.coreOutsideEdgeCharge_spec
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    (ell : Lit n)
    (forward : EdgeWalk (implicationEdges
      (outsideCoreTwoSATClauses hnonempty hwidth)) ell (neg ell))
    (backward : EdgeWalk (implicationEdges
      (outsideCoreTwoSATClauses hnonempty hwidth)) (neg ell) ell)
    (p : ↑core) :
    CoreOutsideEdgeChargeValid hnonempty hwidth forward backward p
      (hminimal.coreOutsideEdgeCharge hnonempty hwidth ell forward backward p) :=
  Classical.choose_spec <|
    hminimal.exists_coreOutsideEdgeCharge hnonempty hwidth ell forward backward p

/-- The chosen charges of a Hall subfamily are internal edges over the union of that
subfamily's incident queried variables. -/
theorem InclusionMinimalUnsatisfiableCore.coreOutsideEdgeCharge_endpoints_mem_incidentUnion
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    {queried : Finset (Fin n)}
    (hsupport : ∀ p ∈ core, competitorOutsideTargetVars target p.2 ⊆ queried)
    (s : Finset ↑core)
    (ell : Lit n)
    (forward : EdgeWalk (implicationEdges
      (outsideCoreTwoSATClauses hnonempty hwidth)) ell (neg ell))
    (backward : EdgeWalk (implicationEdges
      (outsideCoreTwoSATClauses hnonempty hwidth)) (neg ell) ell)
    (p : ↑s) :
    let slot := hminimal.coreOutsideEdgeCharge hnonempty hwidth ell forward backward p.1
    (TwoWalkUsedEdgeSlot.edge slot).1.1 ∈
        s.biUnion (fun q => incidentQueriedVars target queried q.1) ∧
      (TwoWalkUsedEdgeSlot.edge slot).2.1 ∈
        s.biUnion (fun q => incidentQueriedVars target queried q.1) := by
  dsimp only
  have hendpoints := CoreOutsideEdgeChargeValid.endpoints_mem_incidentQueriedVars
    hnonempty hwidth p.1 (hsupport p.1 p.1.2)
    (hminimal.coreOutsideEdgeCharge hnonempty hwidth ell forward backward p.1)
    (hminimal.coreOutsideEdgeCharge_spec hnonempty hwidth ell forward backward p.1)
  constructor
  · exact Finset.mem_biUnion.mpr ⟨p.1, p.2, hendpoints.1⟩
  · exact Finset.mem_biUnion.mpr ⟨p.1, p.2, hendpoints.2⟩

/-- The chosen charge is injective.  Equality of sum slots fixes the walk and directed edge;
`eq_of_shared_coreOutsideClause_edge` then recovers the semantic core member even when the two
members were charged through different clause orientations. -/
theorem InclusionMinimalUnsatisfiableCore.coreOutsideEdgeCharge_injective
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    (ell : Lit n)
    (forward : EdgeWalk (implicationEdges
      (outsideCoreTwoSATClauses hnonempty hwidth)) ell (neg ell))
    (backward : EdgeWalk (implicationEdges
      (outsideCoreTwoSATClauses hnonempty hwidth)) (neg ell) ell) :
    Function.Injective
      (hminimal.coreOutsideEdgeCharge hnonempty hwidth ell forward backward) := by
  intro p q hpq
  have hp := hminimal.coreOutsideEdgeCharge_spec hnonempty hwidth ell forward backward p
  have hq := hminimal.coreOutsideEdgeCharge_spec hnonempty hwidth ell forward backward q
  rw [hpq] at hp
  generalize hslot : hminimal.coreOutsideEdgeCharge hnonempty hwidth ell forward backward q =
    slot at hp hq
  cases slot with
  | inl e =>
      exact hminimal.eq_of_shared_coreOutsideClause_edge hnonempty hwidth p q e.1 hp hq
  | inr e =>
      exact hminimal.eq_of_shared_coreOutsideClause_edge hnonempty hwidth p q e.1 hp hq

/-- Forget that a two-walk edge slot was certified internal to a fixed support. -/
def TwoWalkInternalEdgeSlot.toUsedEdgeSlot
    {edges : List (Lit n × Lit n)} {a b : Lit n}
    {forward : EdgeWalk edges a b} {backward : EdgeWalk edges b a}
    {support : Finset (Fin n)} :
    TwoWalkInternalEdgeSlot forward backward support →
      TwoWalkUsedEdgeSlot forward backward
  | Sum.inl e => Sum.inl ⟨e.1, (Finset.mem_filter.mp e.2).1⟩
  | Sum.inr e => Sum.inr ⟨e.1, (Finset.mem_filter.mp e.2).1⟩

theorem TwoWalkInternalEdgeSlot.toUsedEdgeSlot_injective
    {edges : List (Lit n × Lit n)} {a b : Lit n}
    {forward : EdgeWalk edges a b} {backward : EdgeWalk edges b a}
    {support : Finset (Fin n)} :
    Function.Injective
      (@TwoWalkInternalEdgeSlot.toUsedEdgeSlot n edges a b forward backward support) := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          injection hxy with hsub
          have hval : x.1 = y.1 := congrArg (fun z => z.1) hsub
          exact congrArg Sum.inl (Subtype.ext hval)
      | inr y => cases hxy
  | inr x =>
      cases y with
      | inl y => cases hxy
      | inr y =>
          injection hxy with hsub
          have hval : x.1 = y.1 := congrArg (fun z => z.1) hsub
          exact congrArg Sum.inr (Subtype.ext hval)

/-- Equip a used-edge slot with internal-support membership from its two localized endpoints. -/
def TwoWalkUsedEdgeSlot.toInternalEdgeSlot
    {edges : List (Lit n × Lit n)} {a b : Lit n}
    {forward : EdgeWalk edges a b} {backward : EdgeWalk edges b a}
    {support : Finset (Fin n)}
    (slot : TwoWalkUsedEdgeSlot forward backward)
    (hendpoints : (TwoWalkUsedEdgeSlot.edge slot).1.1 ∈ support ∧
      (TwoWalkUsedEdgeSlot.edge slot).2.1 ∈ support) :
    TwoWalkInternalEdgeSlot forward backward support :=
  match slot with
  | Sum.inl e => Sum.inl ⟨e.1, Finset.mem_filter.mpr ⟨e.2, hendpoints⟩⟩
  | Sum.inr e => Sum.inr ⟨e.1, Finset.mem_filter.mpr ⟨e.2, hendpoints⟩⟩

@[simp] theorem TwoWalkUsedEdgeSlot.toUsedEdgeSlot_toInternalEdgeSlot
    {edges : List (Lit n × Lit n)} {a b : Lit n}
    {forward : EdgeWalk edges a b} {backward : EdgeWalk edges b a}
    {support : Finset (Fin n)}
    (slot : TwoWalkUsedEdgeSlot forward backward)
    (hendpoints : (TwoWalkUsedEdgeSlot.edge slot).1.1 ∈ support ∧
      (TwoWalkUsedEdgeSlot.edge slot).2.1 ∈ support) :
    TwoWalkInternalEdgeSlot.toUsedEdgeSlot
        (slot.toInternalEdgeSlot hendpoints) = slot := by
  cases slot with
  | inl e => exact congrArg Sum.inl (Subtype.ext rfl)
  | inr e => exact congrArg Sum.inr (Subtype.ext rfl)

/-- Restrict the chosen charge of a Hall subfamily to edges internal to its incident union. -/
noncomputable def InclusionMinimalUnsatisfiableCore.coreOutsideInternalEdgeCharge
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    {queried : Finset (Fin n)}
    (hsupport : ∀ p ∈ core, competitorOutsideTargetVars target p.2 ⊆ queried)
    (s : Finset ↑core)
    (ell : Lit n)
    (forward : EdgeWalk (implicationEdges
      (outsideCoreTwoSATClauses hnonempty hwidth)) ell (neg ell))
    (backward : EdgeWalk (implicationEdges
      (outsideCoreTwoSATClauses hnonempty hwidth)) (neg ell) ell) :
    ↑s → TwoWalkInternalEdgeSlot forward backward
      (s.biUnion (fun q => incidentQueriedVars target queried q.1)) := fun p =>
  (hminimal.coreOutsideEdgeCharge hnonempty hwidth ell forward backward p.1).toInternalEdgeSlot
    (hminimal.coreOutsideEdgeCharge_endpoints_mem_incidentUnion
      hnonempty hwidth hsupport s ell forward backward p)

theorem InclusionMinimalUnsatisfiableCore.coreOutsideInternalEdgeCharge_toUsedEdgeSlot
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    {queried : Finset (Fin n)}
    (hsupport : ∀ p ∈ core, competitorOutsideTargetVars target p.2 ⊆ queried)
    (s : Finset ↑core)
    (ell : Lit n)
    (forward : EdgeWalk (implicationEdges
      (outsideCoreTwoSATClauses hnonempty hwidth)) ell (neg ell))
    (backward : EdgeWalk (implicationEdges
      (outsideCoreTwoSATClauses hnonempty hwidth)) (neg ell) ell)
    (p : ↑s) :
    TwoWalkInternalEdgeSlot.toUsedEdgeSlot
        (hminimal.coreOutsideInternalEdgeCharge hnonempty hwidth hsupport s ell forward backward p) =
      hminimal.coreOutsideEdgeCharge hnonempty hwidth ell forward backward p.1 := by
  exact TwoWalkUsedEdgeSlot.toUsedEdgeSlot_toInternalEdgeSlot _ _

/-- The localized charge remains injective after restricting its codomain. -/
theorem InclusionMinimalUnsatisfiableCore.coreOutsideInternalEdgeCharge_injective
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    {queried : Finset (Fin n)}
    (hsupport : ∀ p ∈ core, competitorOutsideTargetVars target p.2 ⊆ queried)
    (s : Finset ↑core)
    (ell : Lit n)
    (forward : EdgeWalk (implicationEdges
      (outsideCoreTwoSATClauses hnonempty hwidth)) ell (neg ell))
    (backward : EdgeWalk (implicationEdges
      (outsideCoreTwoSATClauses hnonempty hwidth)) (neg ell) ell) :
    Function.Injective
      (hminimal.coreOutsideInternalEdgeCharge hnonempty hwidth hsupport s ell forward backward) := by
  intro p q hpq
  apply Subtype.ext
  apply hminimal.coreOutsideEdgeCharge_injective hnonempty hwidth ell forward backward
  rw [← hminimal.coreOutsideInternalEdgeCharge_toUsedEdgeSlot hnonempty hwidth hsupport
      s ell forward backward p,
    ← hminimal.coreOutsideInternalEdgeCharge_toUsedEdgeSlot hnonempty hwidth hsupport
      s ell forward backward q,
    hpq]

/-- Every Hall subfamily obeys the required load-four bound.  Each of the two simple
contradiction walks supplies at most two internal edge slots per incident variable. -/
theorem InclusionMinimalUnsatisfiableCore.subfamily_card_le_four_mul_incidentUnion_twoSAT
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    {queried : Finset (Fin n)}
    (hsupport : ∀ p ∈ core, competitorOutsideTargetVars target p.2 ⊆ queried)
    (s : Finset ↑core) :
    s.card ≤ 4 * (s.biUnion (fun q => incidentQueriedVars target queried q.1)).card := by
  obtain ⟨ell, forward, backward, hforwardSimple, hbackwardSimple, _, _, _⟩ :=
    hminimal.exists_twoSAT_simple_contradiction_walks hnonempty hwidth
  let support := s.biUnion (fun q => incidentQueriedVars target queried q.1)
  have hcharge : Fintype.card ↑s ≤
      Fintype.card (TwoWalkInternalEdgeSlot forward backward support) :=
    Fintype.card_le_of_injective
      (hminimal.coreOutsideInternalEdgeCharge hnonempty hwidth hsupport
        s ell forward backward)
      (hminimal.coreOutsideInternalEdgeCharge_injective hnonempty hwidth hsupport
        s ell forward backward)
  rw [Fintype.card_coe, Fintype.card_sum] at hcharge
  simp only [Fintype.card_coe] at hcharge
  have hforward := TwoSATPathCharge.EdgeWalk.internalUsedEdges_card_le_two_mul
    forward hforwardSimple support
  have hbackward := TwoSATPathCharge.EdgeWalk.internalUsedEdges_card_le_two_mul
    backward hbackwardSimple support
  dsimp only [support] at hcharge hforward hbackward ⊢
  omega

/-- The existing nonempty-incidence interface implies the load-four density needed by
capacitated Hall, with no separate literal-signature premise. -/
theorem InclusionMinimalUnsatisfiableCore.subfamily_card_le_four_mul_incidentUnion_of_incident
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    {queried : Finset (Fin n)}
    (hsupport : ∀ p ∈ core, competitorOutsideTargetVars target p.2 ⊆ queried)
    (hincident : ∀ p ∈ core, (incidentQueriedVars target queried p).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    (s : Finset ↑core) :
    s.card ≤ 4 * (s.biUnion (fun q => incidentQueriedVars target queried q.1)).card := by
  apply hminimal.subfamily_card_le_four_mul_incidentUnion_twoSAT
    (fun p hp => competitorOutsideTargetLiteralSet_nonempty_of_vars_nonempty
      ⟨(hincident p hp).choose, (Finset.mem_inter.mp (hincident p hp).choose_spec).1⟩)
    hwidth hsupport s

/-- Width-two inclusion-minimal cores have an incident-coordinate owner of load four.
This discharges the local-density premise of the existing capacitated Hall reduction. -/
theorem InclusionMinimalUnsatisfiableCore.exists_incidentCoordinateOwner_load_le_four
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hcore : core.Nonempty)
    {queried : Finset (Fin n)}
    (hsupport : ∀ p ∈ core, competitorOutsideTargetVars target p.2 ⊆ queried)
    (hincident : ∀ p ∈ core, (incidentQueriedVars target queried p).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2) :
    ∃ owner : (Fin G × Depth3.Clause n) → Fin n,
      IncidentCoordinateOwner target core queried owner ∧
        ∀ v, (core.filter fun p => owner p = v).card ≤ 4 := by
  apply exists_incidentCoordinateOwner_load_le_of_localDensity hcore hincident
  exact hminimal.subfamily_card_le_four_mul_incidentUnion_of_incident
    hsupport hincident hwidth

/-! ### Extensional load-four key alphabet

The owner theorem above is enough for fiber bounds, but the canonical prefix encoder eventually
needs a decodable finite key.  The Hall matching already contains the stronger extensional datum:
each core member can be injected into an incident queried coordinate together with one of four
slots.  Exposing that injection here avoids choosing a separate enumeration of every owner fiber
and makes clear that no executable use of the noncomputable Hall choice is needed for counting.
-/

/-- The finite load-four alphabet over the actually queried coordinates. -/
abbrev WidthTwoOwnedKey {n : ℕ} (queried : Finset (Fin n)) :=
  ↑queried × Fin 4

theorem card_widthTwoOwnedKey {n : ℕ} (queried : Finset (Fin n)) :
    Fintype.card (WidthTwoOwnedKey queried) = 4 * queried.card := by
  simp [WidthTwoOwnedKey, Fintype.card_prod, Nat.mul_comm]

/-- The exact fixed-length multiset alphabet obtained from load-four owned keys. -/
abbrev WidthTwoOwnedPrefixCode {n : ℕ} (queried : Finset (Fin n)) (d : ℕ) :=
  Sym (WidthTwoOwnedKey queried) d

theorem card_widthTwoOwnedPrefixCode {n : ℕ} (queried : Finset (Fin n)) (d : ℕ) :
    Fintype.card (WidthTwoOwnedPrefixCode queried d) =
      ((4 * queried.card + d - 1).choose d) := by
  simp [WidthTwoOwnedPrefixCode, Sym.card_sym_eq_choose, Nat.mul_comm]

/-- Conditional survivor-shell balance for the exact load-four alphabet.  This theorem is the
arithmetic that a coherent owned-prefix decoder would consume; it does not assert that the
current `(gate,term-position)` prefix has already been re-encoded by the Hall matching. -/
theorem widthTwoOwnedPrefix_balance
    {n w q K d savingNum savingDen : ℕ}
    (hdpos : 0 < d) (hdK : d ≤ K) (hKn : K ≤ n)
    (hsave : (savingNum * K) / savingDen ≤ d)
    (hdensity : (4 * ((w + 1) * (4 * q + 1))) * K + K ≤ n + 1) :
    Nat.choose n (K - d) * 2 ^ (n - (K - d)) *
          ((w + 1) ^ d * ((4 * q + d - 1).choose d + 1)) *
          2 ^ ((savingNum * K) / savingDen) ≤
        Nat.choose n K * 2 ^ (n - K) := by
  exact realizedPrefix_balance_of_actual_density
    (A := 4 * q) hdpos hdK hKn hsave hdensity

/-! ### Canonicalizing the two existential choices

The local compression uses two finite choices: an inclusion-minimal subcore of the full
competitor pool and a capacitated Hall embedding of that core.  Neither choice has to remain an
extra root-dependent parameter.  Classical choice turns each into a function of its semantic
inputs, and proof irrelevance makes the resulting functions independent of the proofs used to
justify those inputs.  Thus exact equality of target, full pool, and queried set is enough for
coherent reuse of the same choices; the remaining encoder obligation is to derive those data
equalities from its endpoint/label comparison.
-/

/-- A fixed inclusion-minimal unsatisfiable subcore, chosen solely from the target and full
competitor pool. -/
noncomputable def canonicalMinimalUnsatisfiableCore
    {n G : ℕ} (target : Fin G → Depth3.Clause n)
    (full : Finset (Fin G × Depth3.Clause n))
    (hunsat : ¬ ∃ assignment, HitsOutsideCompetitorCore target full assignment) :
    Finset (Fin G × Depth3.Clause n) :=
  Classical.choose (exists_inclusionMinimalUnsatisfiableCore_subset target full hunsat)

theorem canonicalMinimalUnsatisfiableCore_subset
    {n G : ℕ} (target : Fin G → Depth3.Clause n)
    (full : Finset (Fin G × Depth3.Clause n))
    (hunsat : ¬ ∃ assignment, HitsOutsideCompetitorCore target full assignment) :
    canonicalMinimalUnsatisfiableCore target full hunsat ⊆ full :=
  (Classical.choose_spec
    (exists_inclusionMinimalUnsatisfiableCore_subset target full hunsat)).1

theorem canonicalMinimalUnsatisfiableCore_minimal
    {n G : ℕ} (target : Fin G → Depth3.Clause n)
    (full : Finset (Fin G × Depth3.Clause n))
    (hunsat : ¬ ∃ assignment, HitsOutsideCompetitorCore target full assignment) :
    InclusionMinimalUnsatisfiableCore target
      (canonicalMinimalUnsatisfiableCore target full hunsat) :=
  (Classical.choose_spec
    (exists_inclusionMinimalUnsatisfiableCore_subset target full hunsat)).2

/-- The canonical core does not depend on which proof established unsatisfiability. -/
theorem canonicalMinimalUnsatisfiableCore_proof_irrel
    {n G : ℕ} (target : Fin G → Depth3.Clause n)
    (full : Finset (Fin G × Depth3.Clause n))
    (h₁ h₂ : ¬ ∃ assignment, HitsOutsideCompetitorCore target full assignment) :
    canonicalMinimalUnsatisfiableCore target full h₁ =
      canonicalMinimalUnsatisfiableCore target full h₂ := by
  congr

/-- Width-two Hall matching supplies an injective, incident load-four code for every member of
the concrete minimal core.  This is deliberately existential: subsequent cardinality arguments
may use the code extensionally, while a canonical decoder would additionally have to choose the
same code coherently across the two roots being compared. -/
theorem InclusionMinimalUnsatisfiableCore.exists_incidentWidthTwoOwnedKeyEmbedding
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    {queried : Finset (Fin n)}
    (hsupport : ∀ p ∈ core, competitorOutsideTargetVars target p.2 ⊆ queried)
    (hincident : ∀ p ∈ core, (incidentQueriedVars target queried p).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2) :
    ∃ code : ↑core → WidthTwoOwnedKey queried,
      Function.Injective code ∧
        ∀ p : ↑core, (code p).1.1 ∈ competitorOutsideTargetVars target p.1.2 := by
  classical
  let slots : ↑core → Finset (Fin n × Fin 4) := fun p =>
    incidentOwnerSlots target queried p.1
  have hslotsUnion (s : Finset ↑core) :
      s.biUnion slots =
        (s.biUnion fun p => incidentQueriedVars target queried p.1) ×ˢ Finset.univ := by
    ext z
    simp [slots, incidentOwnerSlots]
  have hhall : ∀ s : Finset ↑core, s.card ≤ (s.biUnion slots).card := by
    intro s
    rw [hslotsUnion, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    simpa [Nat.mul_comm] using
      hminimal.subfamily_card_le_four_mul_incidentUnion_of_incident
        hsupport hincident hwidth s
  obtain ⟨slot, hslotInjective, hslotMem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' slots).mp hhall
  have hslotQueried (p : ↑core) : (slot p).1 ∈ queried := by
    exact (Finset.mem_inter.mp (Finset.mem_product.mp (hslotMem p)).1).2
  let code : ↑core → WidthTwoOwnedKey queried := fun p =>
    (⟨(slot p).1, hslotQueried p⟩, (slot p).2)
  refine ⟨code, ?_, ?_⟩
  · intro p q hpq
    apply hslotInjective
    exact Prod.ext (congrArg (fun z => z.1.1) hpq)
      (congrArg (fun z : WidthTwoOwnedKey queried => z.2) hpq)
  · intro p
    exact (Finset.mem_inter.mp (Finset.mem_product.mp (hslotMem p)).1).1

/-- A fixed Hall embedding for a fixed semantic core.  Its value is noncomputable but extensional:
all decoding/counting statements below use only the returned finite function. -/
noncomputable def incidentWidthTwoOwnedKeyEmbedding
    {n G : ℕ} {target : Fin G → Depth3.Clause n}
    {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    {queried : Finset (Fin n)}
    (hsupport : ∀ p ∈ core, competitorOutsideTargetVars target p.2 ⊆ queried)
    (hincident : ∀ p ∈ core, (incidentQueriedVars target queried p).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2) :
    ↑core → WidthTwoOwnedKey queried :=
  Classical.choose
    (hminimal.exists_incidentWidthTwoOwnedKeyEmbedding hsupport hincident hwidth)

theorem incidentWidthTwoOwnedKeyEmbedding_injective
    {n G : ℕ} {target : Fin G → Depth3.Clause n}
    {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    {queried : Finset (Fin n)}
    (hsupport : ∀ p ∈ core, competitorOutsideTargetVars target p.2 ⊆ queried)
    (hincident : ∀ p ∈ core, (incidentQueriedVars target queried p).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2) :
    Function.Injective
      (incidentWidthTwoOwnedKeyEmbedding hminimal hsupport hincident hwidth) :=
  (Classical.choose_spec
    (hminimal.exists_incidentWidthTwoOwnedKeyEmbedding hsupport hincident hwidth)).1

theorem incidentWidthTwoOwnedKeyEmbedding_incident
    {n G : ℕ} {target : Fin G → Depth3.Clause n}
    {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    {queried : Finset (Fin n)}
    (hsupport : ∀ p ∈ core, competitorOutsideTargetVars target p.2 ⊆ queried)
    (hincident : ∀ p ∈ core, (incidentQueriedVars target queried p).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    (p : ↑core) :
    (incidentWidthTwoOwnedKeyEmbedding hminimal hsupport hincident hwidth p).1.1 ∈
      competitorOutsideTargetVars target p.1.2 :=
  (Classical.choose_spec
    (hminimal.exists_incidentWidthTwoOwnedKeyEmbedding hsupport hincident hwidth)).2 p

/-- For fixed semantic inputs, neither the minimality proof nor the support/width proofs can alter
the chosen Hall code.  This is the exact coherence fact needed after transporting the core. -/
theorem incidentWidthTwoOwnedKeyEmbedding_proof_irrel
    {n G : ℕ} {target : Fin G → Depth3.Clause n}
    {core : Finset (Fin G × Depth3.Clause n)} {queried : Finset (Fin n)}
    (hm₁ hm₂ : InclusionMinimalUnsatisfiableCore target core)
    (hs₁ hs₂ : ∀ p ∈ core, competitorOutsideTargetVars target p.2 ⊆ queried)
    (hi₁ hi₂ : ∀ p ∈ core, (incidentQueriedVars target queried p).Nonempty)
    (hw₁ hw₂ : ∀ p ∈ core, p.2.lits.length ≤ 2) :
    incidentWidthTwoOwnedKeyEmbedding hm₁ hs₁ hi₁ hw₁ =
      incidentWidthTwoOwnedKeyEmbedding hm₂ hs₂ hi₂ hw₂ := by
  congr

/-! ### Endpoint/position transport obstruction

The canonical Hall choices above are coherent once their semantic inputs agree.  The remaining
question is whether the current decoder's endpoint and literal-position word force those inputs
to agree.  The following definition records the target clause and its source gate at every
realized prefix position, before any Hall compression.
-/

/-- Source-gate/target-clause data selected by the first `d` fresh canonical witnesses. -/
def realizedPrefixTargetData {n G d : ℕ}
    (gates : Fin G → List (Depth3.Clause n)) (fuel : ℕ)
    (sigma : Restriction n) (x : Fin n → Bool) : List (Fin G × Depth3.Clause n) :=
  ((freshTaggedWitSeq gates fuel sigma x).take d).filterMap fun entry =>
    ((gates entry.1)[entry.2.2]?).map fun target => (entry.1, target)

/-- The independent two-singleton family has width one, so its position word lives in the
smallest nontrivial position alphabet. -/
theorem independentTwoLiteralGates_width_one :
    ∀ g T, T ∈ independentTwoLiteralGates g → T.lits.length ≤ 1 := by
  decide +revert

/-- Equal endpoint and equal literal-position word do not transport even the selected target
data.  The two one-query roots use position zero of term zero, but one query originates in gate
zero and the other in gate one.  Thus source-gate identity (and consequently target identity and
the source-gate-dependent full competitor pool) is unavailable before the global key component
has been decoded. -/
theorem endpoint_position_do_not_transport_realizedPrefixTargetData :
    freshTaggedPrefixEndpoint independentTwoLiteralGates 1 independentTwoRoot0
        independentTwoAssignment 1 =
      freshTaggedPrefixEndpoint independentTwoLiteralGates 1 independentTwoRoot1
        independentTwoAssignment 1 ∧
    freshPositionOptionCode (w := 1) (d := 1) independentTwoLiteralGates
        independentTwoLiteralGates_width_one 1 independentTwoRoot0 independentTwoAssignment =
      freshPositionOptionCode (w := 1) (d := 1) independentTwoLiteralGates
        independentTwoLiteralGates_width_one 1 independentTwoRoot1 independentTwoAssignment ∧
    realizedPrefixTargetData (d := 1) independentTwoLiteralGates 1 independentTwoRoot0
        independentTwoAssignment ≠
      realizedPrefixTargetData (d := 1) independentTwoLiteralGates 1 independentTwoRoot1
        independentTwoAssignment := by
  decide

/-- In the same counterexample the stable `(gate,term-position)` keys differ.  This pinpoints the
information discarded by a label retaining only endpoint and literal positions. -/
theorem endpoint_position_do_not_transport_realizedPrefixKeys :
    ((freshTaggedWitSeq independentTwoLiteralGates 1 independentTwoRoot0
        independentTwoAssignment).take 1).map taggedWitKey ≠
      ((freshTaggedWitSeq independentTwoLiteralGates 1 independentTwoRoot1
        independentTwoAssignment).take 1).map taggedWitKey := by
  decide

/-! ### Stable-source hybrid obstruction

Retaining the source gate repairs the preceding two-gate example, but it still does not select
the semantic target when one gate has several terms.  The following one-gate example isolates
that remaining ambiguity.
-/

/-- One source gate containing two distinct singleton targets. -/
def sameGateTwoTargetGates : Fin 1 → List (Depth3.Clause 2) :=
  fun _ => [⟨[Rung4Literal.pos 0]⟩, ⟨[Rung4Literal.pos 1]⟩]

/-- The two roots free different targets of the same source gate and otherwise agree with the
common all-false endpoint. -/
def sameGateTwoTargetRoot0 : Restriction 2 :=
  fun i => if i = 0 then none else some false

def sameGateTwoTargetRoot1 : Restriction 2 :=
  fun i => if i = 1 then none else some false

def sameGateTwoTargetAssignment : Fin 2 → Bool := fun _ => false

theorem sameGateTwoTargetGates_width_one :
    ∀ g T, T ∈ sameGateTwoTargetGates g → T.lits.length ≤ 1 := by
  decide

/-- Gate identity plus the literal-position word and endpoint still do not transport target
identity.  Both prefixes originate in the unique gate and query literal position zero, but they
select different term positions and hence different target clauses. -/
theorem endpoint_sourceGate_position_do_not_transport_realizedPrefixTargetData :
    freshTaggedPrefixEndpoint sameGateTwoTargetGates 1 sameGateTwoTargetRoot0
        sameGateTwoTargetAssignment 1 =
      freshTaggedPrefixEndpoint sameGateTwoTargetGates 1 sameGateTwoTargetRoot1
        sameGateTwoTargetAssignment 1 ∧
    ((freshTaggedWitSeq sameGateTwoTargetGates 1 sameGateTwoTargetRoot0
        sameGateTwoTargetAssignment).take 1).map Prod.fst =
      ((freshTaggedWitSeq sameGateTwoTargetGates 1 sameGateTwoTargetRoot1
        sameGateTwoTargetAssignment).take 1).map Prod.fst ∧
    freshPositionOptionCode (w := 1) (d := 1) sameGateTwoTargetGates
        sameGateTwoTargetGates_width_one 1 sameGateTwoTargetRoot0 sameGateTwoTargetAssignment =
      freshPositionOptionCode (w := 1) (d := 1) sameGateTwoTargetGates
        sameGateTwoTargetGates_width_one 1 sameGateTwoTargetRoot1 sameGateTwoTargetAssignment ∧
    realizedPrefixTargetData (d := 1) sameGateTwoTargetGates 1 sameGateTwoTargetRoot0
        sameGateTwoTargetAssignment ≠
      realizedPrefixTargetData (d := 1) sameGateTwoTargetGates 1 sameGateTwoTargetRoot1
        sameGateTwoTargetAssignment := by
  decide

/-- The missing stable datum in the same-gate example is exactly the term-position component of
the existing key. -/
theorem endpoint_sourceGate_position_do_not_transport_realizedPrefixKeys :
    ((freshTaggedWitSeq sameGateTwoTargetGates 1 sameGateTwoTargetRoot0
        sameGateTwoTargetAssignment).take 1).map taggedWitKey ≠
      ((freshTaggedWitSeq sameGateTwoTargetGates 1 sameGateTwoTargetRoot1
        sameGateTwoTargetAssignment).take 1).map taggedWitKey := by
  decide

/-! ### Whole-prefix decoder lower bound

The preceding examples rule out several underspecified decoder inputs position by position.  A
different possibility is to decode the selected variables of the entire realized prefix from one
shared code.  The independent-singleton common-endpoint fiber gives an exact information test for
that proposal: all `d`-subsets occur over the same endpoint, and the whole selected prefix is
exactly that subset.
-/

/-- Any finite code that recovers the *whole* selected-variable set on every realized
independent-singleton `d`-prefix has at least `choose n d` values.  The decoder is otherwise
arbitrary and receives one shared code per root; in particular, this theorem does not assume a
product of independently decoded per-witness meanings.

All tested roots have the common endpoint `independentAllFalse n` by
`independentLiteral_realized_endpoint_fiber_card`, so supplying that endpoint to the decoder would
not weaken the lower bound. -/
theorem independentRealizedPrefix_sharedDecoder_card_lower_bound
    {n d : ℕ} {L : Type} [Fintype L]
    (encode : Restriction n → L) (decode : L → Finset (Fin n))
    (hdecode : ∀ ρ ∈ independentRealizedRoots n d,
      decode (encode ρ) =
        freshTaggedPrefixVars (independentLiteralGates n) 1 ρ
          (independentAssignment n) d) :
    Nat.choose n d ≤ Fintype.card L := by
  classical
  have hinj : Set.InjOn encode (independentRealizedRoots n d) := by
    intro ρ hρ σ hσ hcode
    have hdρ := hdecode ρ hρ
    have hdσ := hdecode σ hσ
    have hρ' : ρ ∈ independentRealizedRoots n d := hρ
    have hσ' : σ ∈ independentRealizedRoots n d := hσ
    rw [independentRealizedRoots] at hρ' hσ'
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hρ'
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hσ'
    have hScard := (Finset.mem_powersetCard.mp hS).2
    have hTcard := (Finset.mem_powersetCard.mp hT).2
    apply congrArg independentRoot
    rw [← independentLiteral_freshTaggedPrefixVars S,
      ← independentLiteral_freshTaggedPrefixVars T,
      hScard, hTcard, ← hdρ, ← hdσ, hcode]
  calc
    Nat.choose n d = (independentRealizedRoots n d).card :=
      (independentLiteral_realized_endpoint_fiber_card n d).1.symm
    _ = ((independentRealizedRoots n d).image encode).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.univ : Finset L).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card L := Finset.card_univ

/-! ### Bad-event-sensitive whole-prefix decoder lower bound

Restricting the decoder to the semantic bad event could in principle remove most of the
independent-subset fiber.  At residual depth zero it does not: when `d > 0`, every root with
exactly `d` live independent singleton gates is bad for a trunk of depth `d - 1`.  The following
intersection and decoder theorems make that regression test explicit.
-/

/-- Every realized independent `d`-prefix root is in the matching depth-`d-1`, residual-zero bad
event.  Thus this particular bad-event restriction discards none of the common-endpoint fiber. -/
theorem independentRealizedRoots_subset_commonShallowBad
    {n d : ℕ} (hd : 0 < d) :
    independentRealizedRoots n d ⊆
      commonShallowBad (independentLiteralGates n) 1 d (d - 1) 0 := by
  intro ρ hρ
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hρ
  have hcard := (Finset.mem_powersetCard.mp hS).2
  exact independentRoot_mem_commonShallowBad_zero S hcard (by omega)

/-- The bad-event slice of the realized common-endpoint fiber is exactly the whole fiber. -/
theorem independentRealizedRoots_inter_commonShallowBad
    {n d : ℕ} (hd : 0 < d) :
    independentRealizedRoots n d ∩
        commonShallowBad (independentLiteralGates n) 1 d (d - 1) 0 =
      independentRealizedRoots n d := by
  apply Finset.inter_eq_left.mpr
  exact independentRealizedRoots_subset_commonShallowBad hd

/-- Even an arbitrary shared decoder defined only on the actual bad-event slice needs at least
`choose n d` code values on the independent-singleton family.  This does not assume a product
code or independently decoded per-witness meanings; it shows that bad-event sensitivity alone,
without an additional structural restriction on the circuit family or endpoint fiber, gives no
worst-case reduction. -/
theorem independentBadRealizedPrefix_sharedDecoder_card_lower_bound
    {n d : ℕ} (hd : 0 < d) {L : Type} [Fintype L]
    (encode : Restriction n → L) (decode : L → Finset (Fin n))
    (hdecode : ∀ ρ ∈ independentRealizedRoots n d ∩
        commonShallowBad (independentLiteralGates n) 1 d (d - 1) 0,
      decode (encode ρ) =
        freshTaggedPrefixVars (independentLiteralGates n) 1 ρ
          (independentAssignment n) d) :
    Nat.choose n d ≤ Fintype.card L := by
  apply independentRealizedPrefix_sharedDecoder_card_lower_bound encode decode
  intro ρ hρ
  apply hdecode ρ
  exact Finset.mem_inter.mpr
    ⟨hρ, independentRealizedRoots_subset_commonShallowBad hd hρ⟩

/-! ### Density boundary for the independent-subset obstruction

The preceding lower bound is deliberately worst-case.  The independent-singleton family uses one
genuine clause occurrence for every ambient coordinate, so it lies exactly on the
alphabet-equals-live boundary that the verified actual-density shell estimate excludes.  This
does not supply the missing density-aware decoder, but it proves that the regression family is not
itself a counterexample to such a decoder. -/

/-- The exact ragged clause-occurrence alphabet of the independent-singleton family has one entry
per ambient coordinate. -/
theorem independentLiteralGates_actualAlphabet_eq (n : ℕ) :
    (∑ g, (independentLiteralGates n g).length) = n := by
  simp [independentLiteralGates]

/-- On every positive shell, the independent-singleton family violates the actual-alphabet
density premise consumed by `commonShallowBad_scaled_le_of_actual_density`, irrespective of the
declared width bound.  Hence the full `choose n d` bad endpoint fiber above does not refute a
decoder whose smallness is proved only inside that verified density regime. -/
theorem independentLiteralGates_not_actualDensity
    {n w K : ℕ} (hK : 0 < K) :
    ¬((4 * ((w + 1) * ((∑ g, (independentLiteralGates n g).length) + 1))) * K + K ≤
        n + 1) := by
  rw [independentLiteralGates_actualAlphabet_eq]
  intro hdensity
  have hbase : n + 1 ≤ 4 * ((w + 1) * (n + 1)) := by
    calc
      n + 1 ≤ (4 * (w + 1)) * (n + 1) :=
        Nat.le_mul_of_pos_left _ (by positivity)
      _ = 4 * ((w + 1) * (n + 1)) := by ring
  have hmul : 4 * ((w + 1) * (n + 1)) ≤
      4 * ((w + 1) * (n + 1)) * K :=
    Nat.le_mul_of_pos_right _ hK
  have hstrict : n + 1 < 4 * ((w + 1) * (n + 1)) * K + K :=
    (hbase.trans hmul).trans_lt (Nat.lt_add_of_pos_right hK)
  exact (Nat.not_lt_of_ge hdensity) hstrict

/-! ### Density-aware support code for realized prefixes

The exact ragged alphabet counts clause occurrences, while the variables queried by a canonical
prefix must occur inside those clauses.  The following support code makes that relationship
explicit.  It bounds the number of distinct realized `d`-variable prefix sets, not the number of
roots in an endpoint fiber; reconstructing roots still requires the endpoint injection already
proved in the witness-label development. -/

/-- Variables occurring in one clause. -/
def clauseVariableSupport {n : ℕ} (T : Depth3.Clause n) : Finset (Fin n) :=
  (T.lits.map litVar).toFinset

/-- Variables occurring in one DNF gate. -/
def gateVariableSupport {n : ℕ} (cs : List (Depth3.Clause n)) : Finset (Fin n) :=
  cs.toFinset.biUnion clauseVariableSupport

/-- Variables occurring anywhere in the exact indexed gate family. -/
def familyVariableSupport {n G : ℕ} (gates : Fin G → List (Depth3.Clause n)) :
    Finset (Fin n) :=
  Finset.univ.biUnion fun g => gateVariableSupport (gates g)

/-- Every coordinate queried anywhere in a canonical gate tree occurs syntactically in that
gate.  Unlike the existing freshness theorem, this records the static support restriction and is
therefore useful when many ambient live variables are irrelevant to the family. -/
theorem canonicalDT_queriedVars_subset_gateVariableSupport {n : ℕ}
    (cs : List (Depth3.Clause n)) :
    ∀ fuel σ, queriedVars (canonicalDT cs fuel σ) ⊆ gateVariableSupport cs := by
  intro fuel
  induction fuel with
  | zero =>
      intro σ
      rw [canonicalDT]
      split <;> simp [queriedVars]
  | succ fuel ih =>
      intro σ
      rw [canonicalDT]
      split
      · simp [queriedVars]
      · split
        · simp [queriedVars]
        · rename_i T hactive
          obtain ⟨ell, hhead, _hfree⟩ := activeTerm_first_free hactive
          simp only [hhead, queriedVars]
          intro v hv
          rw [Finset.mem_insert, Finset.mem_union] at hv
          rcases hv with rfl | hv | hv
          · apply Finset.mem_biUnion.mpr
            refine ⟨T, List.mem_toFinset.mpr
              (SwitchingCounting.activeTerm_mem hactive), ?_⟩
            apply List.mem_toFinset.mpr
            apply List.mem_map.mpr
            refine ⟨ell, ?_, rfl⟩
            have hellFree : ell ∈ freeLits σ T := List.mem_of_mem_head? hhead
            exact (List.mem_filter.mp hellFree).1
          · exact ih _ hv
          · exact ih _ hv

/-- A read-once common-family path pays only for coordinates that are both live and actually
owned by the gate family.  This sharpens the ambient `stars` bound when padding coordinates are
live but irrelevant to every gate. -/
theorem canonicalFamily_trace_length_le_live_support {n G : ℕ}
    (gates : Fin G → List (Depth3.Clause n)) (fuel : ℕ) (σ : Restriction n)
    (x : Fin n → Bool) (hext : Rung4Restriction.Extends σ x) :
    (CommonTree.trace
      (CommonTree.readOnce σ (canonicalFamilyTree gates fuel σ)) x).length ≤
      ((familyVariableSupport gates).filter fun i ↦ σ i = none).card := by
  rw [CommonTree.trace_length_eq_queryVars_length]
  have hnd := CommonTree.queryVars_readOnce_nodup σ
    (canonicalFamilyTree gates fuel σ) x hext
  rw [← List.toFinset_card_of_nodup hnd]
  apply Finset.card_le_card
  intro v hv
  rw [Finset.mem_filter]
  have hvList : v ∈ CommonTree.queryVars
      (CommonTree.readOnce σ (canonicalFamilyTree gates fuel σ)) x :=
    List.mem_toFinset.mp hv
  constructor
  · have hvRaw := CommonTree.mem_queryVars_of_mem_readOnce σ
      (canonicalFamilyTree gates fuel σ) x hext hvList
    rw [canonicalFamilyTree, CommonTree.queryVars_commonRefineFin] at hvRaw
    obtain ⟨segment, hsegment, hvSegment⟩ := List.mem_flatten.mp hvRaw
    obtain ⟨tree, htree, rfl⟩ := List.mem_map.mp hsegment
    obtain ⟨g, rfl⟩ := List.mem_ofFn.mp htree
    apply Finset.mem_biUnion.mpr
    refine ⟨g, Finset.mem_univ g, ?_⟩
    apply canonicalDT_queriedVars_subset_gateVariableSupport (gates g) fuel σ
    exact CommonTree.queryVars_ofBool_toFinset_subset_queriedVars
      (canonicalDT (gates g) fuel σ) x (List.mem_toFinset.mpr hvSegment)
  · exact mem_freeVars.mp
      (CommonTree.mem_queryVars_readOnce_freeVars σ
        (canonicalFamilyTree gates fuel σ) x hext hvList)

/-- If the trunk budget covers the live part of the actual family support, irrelevant ambient
survivors need not be charged.  Ample fuel is still stated using the full live count because it
is what makes each completed canonical member path semantically terminal. -/
theorem commonShallowAt_zero_of_live_support_le {n G : ℕ}
    (gates : Fin G → List (Depth3.Clause n)) (fuel : ℕ) (σ : Restriction n)
    (trunkDepth : ℕ) (hstarsFuel : stars σ ≤ fuel)
    (hsupport : ((familyVariableSupport gates).filter fun i ↦ σ i = none).card ≤
      trunkDepth) :
    CommonShallowAt gates fuel σ trunkDepth 0 := by
  apply commonShallowAt_of_prefix_residual gates fuel σ trunkDepth 0
  intro x hext g
  have htrace : (CommonTree.trace
      (CommonTree.readOnce σ (canonicalFamilyTree gates fuel σ)) x).length ≤
      trunkDepth :=
    (canonicalFamily_trace_length_le_live_support gates fuel σ x hext).trans hsupport
  have hend := CommonTree.prefixEndpoint_eq_pathEndpoint_of_trace_length_le
    σ (canonicalFamilyTree gates fuel σ) trunkDepth x htrace
  rw [CommonTree.prefixEndpoint] at hend
  rw [hend]
  exact Nat.le_of_eq (canonicalDT_depth_eq_zero_of_terminal (gates g)
    (CommonTree.pathEndpoint σ (canonicalFamilyTree gates fuel σ) x)
    (canonicalFamily_pathEndpoint_terminal gates fuel σ x hext hstarsFuel g) fuel)

theorem clauseVariableSupport_card_le_width {n w : ℕ} {T : Depth3.Clause n}
    (hw : T.lits.length ≤ w) : (clauseVariableSupport T).card ≤ w := by
  exact (List.toFinset_card_le _).trans (by simpa using hw)

theorem gateVariableSupport_card_le {n w : ℕ} {cs : List (Depth3.Clause n)}
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) :
    (gateVariableSupport cs).card ≤ w * cs.length := by
  calc
    (gateVariableSupport cs).card ≤
        ∑ T ∈ cs.toFinset, (clauseVariableSupport T).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _T ∈ cs.toFinset, w := by
      apply Finset.sum_le_sum
      intro T hT
      exact clauseVariableSupport_card_le_width (hw T (List.mem_toFinset.mp hT))
    _ = cs.toFinset.card * w := by simp
    _ ≤ cs.length * w := Nat.mul_le_mul_right w (List.toFinset_card_le cs)
    _ = w * cs.length := Nat.mul_comm _ _

/-- Width times the exact ragged alphabet bounds the family's complete coordinate support. -/
theorem familyVariableSupport_card_le {n G w : ℕ}
    {gates : Fin G → List (Depth3.Clause n)}
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w) :
    (familyVariableSupport gates).card ≤ w * ∑ g, (gates g).length := by
  calc
    (familyVariableSupport gates).card ≤
        ∑ g, (gateVariableSupport (gates g)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ g, w * (gates g).length := by
      apply Finset.sum_le_sum
      intro g _
      exact gateVariableSupport_card_le (hw g)
    _ = w * ∑ g, (gates g).length := by rw [Finset.mul_sum]

/-- Every variable decoded by a fresh canonical prefix is in the family's actual literal
support.  This needs no path-length or bad-event premise: successful witness decoding itself
identifies the containing gate, clause, and literal occurrence. -/
theorem freshTaggedPrefixVars_subset_familyVariableSupport
    {n G : ℕ} (gates : Fin G → List (Depth3.Clause n)) (fuel : ℕ)
    (σ : Restriction n) (x : Fin n → Bool) (budget : ℕ) :
    freshTaggedPrefixVars gates fuel σ x budget ⊆ familyVariableSupport gates := by
  intro v hv
  have hv' : v ∈ ((freshTaggedWitSeq gates fuel σ x).take budget).filterMap
      (taggedWitVar? gates) := List.mem_toFinset.mp hv
  obtain ⟨e, _he, hdec⟩ := List.mem_filterMap.mp hv'
  rw [taggedWitVar?] at hdec
  obtain ⟨T, hTget, hellmap⟩ := Option.bind_eq_some_iff.mp hdec
  obtain ⟨ell, hellget, rfl⟩ := Option.map_eq_some_iff.mp hellmap
  apply Finset.mem_biUnion.mpr
  refine ⟨e.1, Finset.mem_univ _, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨T, List.mem_toFinset.mpr (List.mem_of_getElem? hTget), ?_⟩
  exact List.mem_toFinset.mpr (List.mem_map.mpr
    ⟨ell, List.mem_of_getElem? hellget, rfl⟩)

/-- The distinct selected-variable sets realized by a collection of roots. -/
def realizedPrefixVariableSets {n G : ℕ} (gates : Fin G → List (Depth3.Clause n))
    (fuel : ℕ) (roots : Finset (Restriction n))
    (assignment : Restriction n → (Fin n → Bool)) (d : ℕ) :
    Finset (Finset (Fin n)) :=
  roots.image fun ρ => freshTaggedPrefixVars gates fuel ρ (assignment ρ) d

/-- If all selected prefixes have length `d`, their distinct variable sets fit inside the exact
`d`th level of the family support's powerset. -/
theorem realizedPrefixVariableSets_card_le_choose_support
    {n G d fuel : ℕ} {gates : Fin G → List (Depth3.Clause n)}
    {roots : Finset (Restriction n)}
    {assignment : Restriction n → (Fin n → Bool)}
    (hcard : ∀ ρ ∈ roots,
      (freshTaggedPrefixVars gates fuel ρ (assignment ρ) d).card = d) :
    (realizedPrefixVariableSets gates fuel roots assignment d).card ≤
      Nat.choose (familyVariableSupport gates).card d := by
  rw [← Finset.card_powersetCard d (familyVariableSupport gates)]
  apply Finset.card_le_card
  intro S hS
  obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hS
  exact Finset.mem_powersetCard.mpr
    ⟨freshTaggedPrefixVars_subset_familyVariableSupport
        gates fuel ρ (assignment ρ) d,
      hcard ρ hρ⟩

/-- Density-aware capstone: the variable-set alphabet of any genuinely length-`d` realized
prefix family has size at most `choose (w * actualAlphabet) d`. -/
theorem realizedPrefixVariableSets_card_le_choose_actualAlphabet
    {n G w d fuel : ℕ} {gates : Fin G → List (Depth3.Clause n)}
    {roots : Finset (Restriction n)}
    {assignment : Restriction n → (Fin n → Bool)}
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hcard : ∀ ρ ∈ roots,
      (freshTaggedPrefixVars gates fuel ρ (assignment ρ) d).card = d) :
    (realizedPrefixVariableSets gates fuel roots assignment d).card ≤
      Nat.choose (w * ∑ g, (gates g).length) d := by
  exact (realizedPrefixVariableSets_card_le_choose_support hcard).trans
    (Nat.choose_le_choose d (familyVariableSupport_card_le hw))

/-- The semantic bad event itself realizes at most `choose (w * actualAlphabet) d` distinct
selected-variable sets, provided its canonical failure witnesses genuinely traverse `d` fresh
queries.  This is the density-aware structural statistic missing from the earlier arbitrary-code
lower bound. -/
theorem commonShallowBad_realizedPrefixVariableSets_card_le
    {n G w d fuel K residualDepth : ℕ}
    {gates : Fin G → List (Depth3.Clause n)}
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hlong : ∀ ρ ∈ commonShallowBad gates fuel K d residualDepth,
      d ≤ (CommonTree.trace
        (CommonTree.readOnce ρ (canonicalFamilyTree gates fuel ρ))
          (commonShallowBadAssignment gates fuel K d residualDepth ρ)).length) :
    (realizedPrefixVariableSets gates fuel
        (commonShallowBad gates fuel K d residualDepth)
        (commonShallowBadAssignment gates fuel K d residualDepth) d).card ≤
      Nat.choose (w * ∑ g, (gates g).length) d := by
  apply realizedPrefixVariableSets_card_le_choose_actualAlphabet hw
  intro ρ hρ
  exact freshTaggedPrefixVars_card_eq_of_le_trace gates fuel ρ
    (commonShallowBadAssignment gates fuel K d residualDepth ρ) d
    (commonShallowBadAssignment_spec hρ).1 (hlong ρ hρ)

/-! ### Complete bad-root count from the support alphabet

The support estimate above counts selected-variable sets.  On one fixed endpoint fiber this is
already enough to count roots: equality of the endpoint and equality of the selected set recover
the root restriction.  Summing the resulting uniform fiber bound over the exact residual shell
turns the support statistic into a complete bad-event estimate. -/

/-- A fixed endpoint fiber injects into the global image of realized prefix-variable sets. -/
theorem commonShallowBadEndpointFiber_card_le_realizedPrefixVariableSets
    {n G fuel K d residualDepth : ℕ} {gates : Fin G → List (Depth3.Clause n)}
    (assignment : Restriction n → (Fin n → Bool))
    (hext : ∀ ρ ∈ commonShallowBad gates fuel K d residualDepth,
      Rung4Restriction.Extends ρ (assignment ρ))
    (τ : Restriction n) :
    (commonShallowBadEndpointFiber gates fuel K d residualDepth assignment τ).card ≤
      (realizedPrefixVariableSets gates fuel
        (commonShallowBad gates fuel K d residualDepth) assignment d).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun ρ => freshTaggedPrefixVars gates fuel ρ (assignment ρ) d) ?_ ?_
  · intro ρ hρ
    have hρ' : ρ ∈ commonShallowBadEndpointFiber gates fuel K d residualDepth
        assignment τ := hρ
    rw [commonShallowBadEndpointFiber, Finset.mem_filter] at hρ'
    change freshTaggedPrefixVars gates fuel ρ (assignment ρ) d ∈
      realizedPrefixVariableSets gates fuel
        (commonShallowBad gates fuel K d residualDepth) assignment d
    exact Finset.mem_image.mpr ⟨ρ, hρ'.1, rfl⟩
  · intro ρ hρ σ hσ hvars
    have hρ' : ρ ∈ commonShallowBadEndpointFiber gates fuel K d residualDepth
        assignment τ := hρ
    have hσ' : σ ∈ commonShallowBadEndpointFiber gates fuel K d residualDepth
        assignment τ := hσ
    rw [commonShallowBadEndpointFiber, Finset.mem_filter] at hρ' hσ'
    apply freshTaggedPrefixEndpoint_inj_of_vars_eq gates fuel
      (hext ρ hρ'.1) (hext σ hσ'.1)
      (hρ'.2.trans hσ'.2.symm) hvars

/-- Complete density-aware bad-root count.  Every endpoint lies in the exact residual shell, and
each endpoint fiber has at most `choose (w * actualAlphabet) d` roots. -/
theorem commonShallowBad_card_le_shell_mul_choose_actualAlphabet
    {n G w fuel K d residualDepth : ℕ}
    {gates : Fin G → List (Depth3.Clause n)}
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (assignment : Restriction n → (Fin n → Bool))
    (hext : ∀ ρ ∈ commonShallowBad gates fuel K d residualDepth,
      Rung4Restriction.Extends ρ (assignment ρ))
    (hlong : ∀ ρ ∈ commonShallowBad gates fuel K d residualDepth,
      d ≤ (CommonTree.trace
        (CommonTree.readOnce ρ (canonicalFamilyTree gates fuel ρ))
          (assignment ρ)).length) :
    (commonShallowBad gates fuel K d residualDepth).card ≤
      ((Finset.univ : Finset (Restriction n)).filter fun τ => stars τ = K - d).card *
        Nat.choose (w * ∑ g, (gates g).length) d := by
  classical
  rw [← commonShallowBadEndpointFiber_aggregate_exact assignment hext hlong]
  calc
    (∑ τ ∈ (Finset.univ : Finset (Restriction n)).filter fun τ => stars τ = K - d,
        (commonShallowBadEndpointFiber gates fuel K d residualDepth assignment τ).card) ≤
        ∑ _τ ∈ (Finset.univ : Finset (Restriction n)).filter fun τ => stars τ = K - d,
          Nat.choose (w * ∑ g, (gates g).length) d := by
      apply Finset.sum_le_sum
      intro τ _hτ
      exact (commonShallowBadEndpointFiber_card_le_realizedPrefixVariableSets
        assignment hext τ).trans
        (realizedPrefixVariableSets_card_le_choose_actualAlphabet hw fun ρ hρ =>
          freshTaggedPrefixVars_card_eq_of_le_trace gates fuel ρ (assignment ρ) d
            (hext ρ hρ) (hlong ρ hρ))
    _ = ((Finset.univ : Finset (Restriction n)).filter fun τ => stars τ = K - d).card *
        Nat.choose (w * ∑ g, (gates g).length) d := by simp

/-- Ample fuel discharges both semantic side conditions of the support-shell count. -/
theorem commonShallowBad_card_le_shell_mul_choose_actualAlphabet_of_le_fuel
    {n G w fuel K d residualDepth : ℕ}
    {gates : Fin G → List (Depth3.Clause n)}
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hKfuel : K ≤ fuel) :
    (commonShallowBad gates fuel K d residualDepth).card ≤
      ((Finset.univ : Finset (Restriction n)).filter fun τ => stars τ = K - d).card *
        Nat.choose (w * ∑ g, (gates g).length) d := by
  apply commonShallowBad_card_le_shell_mul_choose_actualAlphabet hw
    (commonShallowBadAssignment gates fuel K d residualDepth)
  · intro ρ hρ
    exact (commonShallowBadAssignment_spec hρ).1
  · intro ρ hρ
    exact commonShallowBadAssignment_long_of_le_fuel hKfuel hρ

/-- Circuit-level normalized support contraction.  This inserts the smaller factor into the
exact two-polarity family without requiring duplicate-clause cleanliness. -/
theorem normalizedLayered_commonShallowBad_card_le_shell_mul_choose_actualAlphabet
    {n w fuel K d residualDepth : ℕ} {C : Layered n}
    (hw : BottomWidth w C) (hKfuel : K ≤ fuel) :
    (commonShallowBad (normalizedLayeredBottomFamily C) fuel K d residualDepth).card ≤
      ((Finset.univ : Finset (Restriction n)).filter fun τ => stars τ = K - d).card *
        Nat.choose
          (w * ∑ g, (normalizedLayeredBottomFamily C g).length) d := by
  exact commonShallowBad_card_le_shell_mul_choose_actualAlphabet_of_le_fuel
    (normalizedLayeredBottomFamily_width_le hw) hKfuel

/-- Exact circuit-level contraction interface for the support factor.  Schedule arithmetic can
now consume the smaller binomial directly, without routing back through the older density base. -/
theorem normalizedLayered_commonShallowBad_scaled_le_of_support_balance
    {n w fuel K d residualDepth saving : ℕ} {C : Layered n}
    (hw : BottomWidth w C) (hKfuel : K ≤ fuel)
    (hbalance :
      ((Finset.univ : Finset (Restriction n)).filter fun τ => stars τ = K - d).card *
          Nat.choose (w * ∑ g, (normalizedLayeredBottomFamily C g).length) d *
          2 ^ saving ≤
        ((Finset.univ : Finset (Restriction n)).filter fun τ => stars τ = K).card) :
    (commonShallowBad (normalizedLayeredBottomFamily C) fuel K d residualDepth).card *
        2 ^ saving ≤
      ((Finset.univ : Finset (Restriction n)).filter fun τ => stars τ = K).card := by
  have hcount := normalizedLayered_commonShallowBad_card_le_shell_mul_choose_actualAlphabet
    (C := C) (d := d) (residualDepth := residualDepth) hw hKfuel
  exact (Nat.mul_le_mul_right (2 ^ saving) hcount).trans hbalance

/-- At prefix depth one the support alphabet is strictly smaller than the existing
occurrence-multiset-plus-position factor, for every width and actual alphabet size.  Thus the new
count is not merely a renaming of the previous encoder in all parameter regimes. -/
theorem support_factor_strict_lt_realizedPrefix_factor_depth_one (w A : ℕ) :
    Nat.choose (w * A) 1 <
      (w + 1) ^ 1 * (Nat.choose (A + 1 - 1) 1 + 1) := by
  simp
  nlinarith

/-- The support-subset factor is bounded by the sharper non-optional realized-prefix factor.
Multiplying by `d!` exposes the comparison directly: a falling factorial is at most the
corresponding power, while that power is at most the rising factorial counted by multisets. -/
theorem choose_mul_le_pow_mul_multichoose (w A d : ℕ) :
    Nat.choose (w * A) d ≤
      w ^ d * Nat.choose (A + d - 1) d := by
  have hasc : A ^ d ≤ A.ascFactorial d := Nat.pow_succ_le_ascFactorial A d
  have h : d.factorial * Nat.choose (w * A) d ≤
      d.factorial * (w ^ d * Nat.choose (A + d - 1) d) := by
    calc
      d.factorial * Nat.choose (w * A) d = (w * A).descFactorial d :=
        (Nat.descFactorial_eq_factorial_mul_choose _ _).symm
      _ ≤ (w * A) ^ d := Nat.descFactorial_le_pow _ _
      _ = w ^ d * A ^ d := by rw [Nat.mul_pow]
      _ ≤ w ^ d * A.ascFactorial d := Nat.mul_le_mul_left _ hasc
      _ = d.factorial * (w ^ d * Nat.choose (A + d - 1) d) := by
        rw [Nat.ascFactorial_eq_factorial_mul_choose']
        ring
  exact Nat.le_of_mul_le_mul_left h (Nat.factorial_pos d)

/-- General comparison requested by the support-shell audit.  In fact the preceding theorem
shows that neither the optional-code `+1` nor the extra position symbol is needed. -/
theorem support_factor_le_realizedPrefix_factor (w A d : ℕ) :
    Nat.choose (w * A) d ≤
      (w + 1) ^ d * (Nat.choose (A + d - 1) d + 1) := by
  calc
    Nat.choose (w * A) d ≤ w ^ d * Nat.choose (A + d - 1) d :=
      choose_mul_le_pow_mul_multichoose w A d
    _ ≤ (w + 1) ^ d * (Nat.choose (A + d - 1) d + 1) := by gcongr <;> omega

/-! ### Support-specific shell balance

The support code removes both successor enlargements from the density base.  The two powers of
two below are intrinsic: one pays for moving down by `d` live coordinates, and one is the
requested saving. -/

/-- The complete support-shell factor has base `4*w*A`, with no `+1` enlargement of either
width or alphabet. -/
theorem supportSubset_factor_le_pow {w A d e : ℕ} (he : e ≤ d) :
    2 ^ d * Nat.choose (w * A) d * 2 ^ e ≤ (4 * (w * A)) ^ d := by
  have hchoose : Nat.choose (w * A) d ≤ (w * A) ^ d := Nat.choose_le_pow _ _
  have hsave : 2 ^ e ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) he
  calc
    2 ^ d * Nat.choose (w * A) d * 2 ^ e ≤
        2 ^ d * (w * A) ^ d * 2 ^ d := by gcongr
    _ = (4 * (w * A)) ^ d := by
      rw [show 4 * (w * A) = 2 * (w * A) * 2 by ring]
      simp only [mul_pow]

/-- Exact support-specific binomial shell balance.  Compared with the realized-prefix balance,
the density coefficient drops from `4*(w+1)*(A+1)` to `4*w*A`. -/
theorem supportSubset_balance_of_density
    {n w A K d savingNum savingDen : ℕ}
    (hdK : d ≤ K) (hKn : K ≤ n)
    (hsave : (savingNum * K) / savingDen ≤ d)
    (hdensity : (4 * (w * A)) * K + K ≤ n + 1) :
    Nat.choose n (K - d) * 2 ^ (n - (K - d)) *
          Nat.choose (w * A) d * 2 ^ ((savingNum * K) / savingDen) ≤
        Nat.choose n K * 2 ^ (n - K) := by
  have hfactor := supportSubset_factor_le_pow
    (w := w) (A := A) (d := d) (e := (savingNum * K) / savingDen) hsave
  have hbin := binomial_ratio_regime (w := w * A) hdK hdensity
  have hexp : n - (K - d) = n - K + d := by omega
  rw [hexp, pow_add]
  calc
    n.choose (K - d) * (2 ^ (n - K) * 2 ^ d) *
          (w * A).choose d * 2 ^ (savingNum * K / savingDen) =
        2 ^ (n - K) * n.choose (K - d) *
          (2 ^ d * (w * A).choose d * 2 ^ (savingNum * K / savingDen)) := by ring
    _ ≤ 2 ^ (n - K) * n.choose (K - d) * (4 * (w * A)) ^ d := by gcongr
    _ = 2 ^ (n - K) * ((4 * (w * A)) ^ d * n.choose (K - d)) := by ring
    _ ≤ 2 ^ (n - K) * n.choose K := Nat.mul_le_mul_left _ hbin
    _ = n.choose K * 2 ^ (n - K) := by ring

/-- Circuit-level support contraction under the sharper density premise. -/
theorem normalizedLayered_commonShallowBad_scaled_le_of_support_density
    {n w fuel K d residualDepth savingNum savingDen : ℕ} {C : Layered n}
    (hw : BottomWidth w C) (hKfuel : K ≤ fuel) (hdK : d ≤ K) (hKn : K ≤ n)
    (hsave : (savingNum * K) / savingDen ≤ d)
    (hdensity :
      (4 * (w * (∑ g, (normalizedLayeredBottomFamily C g).length))) * K + K ≤ n + 1) :
    (commonShallowBad (normalizedLayeredBottomFamily C) fuel K d residualDepth).card *
        2 ^ ((savingNum * K) / savingDen) ≤
      (Finset.univ.filter fun σ : Restriction n => stars σ = K).card := by
  apply normalizedLayered_commonShallowBad_scaled_le_of_support_balance hw hKfuel
  rw [card_stars_eq (N := n) (K := K - d), card_stars_eq (N := n) (K := K)]
  exact supportSubset_balance_of_density hdK hKn hsave hdensity

/-- Backward scale required by the support-specific half-shell schedule. -/
def layeredRoundSupportScale (M s : ℕ) : ℕ :=
  5 * ((s + 1) * layeredRoundActualKeyCap M s + 1)

def layeredRoundSupportLive (M s r j : ℕ) : ℕ :=
  100 * ((s + 1) * layeredRoundActualKeyCap M s + 1) *
    (r * layeredRoundSupportScale M s ^ j)

def layeredRoundSupportShell (M s r j : ℕ) : ℕ :=
  20 * (r * layeredRoundSupportScale M s ^ j)

theorem layeredRoundSupportShell_succ_eq_live (M s r j : ℕ) :
    layeredRoundSupportShell M s r (j + 1) = layeredRoundSupportLive M s r j := by
  simp only [layeredRoundSupportShell, layeredRoundSupportLive, layeredRoundSupportScale, pow_succ]
  ring

/-- The old stars-and-bars backward scale is at least twenty times the support scale. -/
theorem twenty_mul_layeredRoundSupportScale_le_actualScale (M s : ℕ) :
    20 * layeredRoundSupportScale M s ≤ layeredRoundActualScale M s := by
  simp only [layeredRoundSupportScale, layeredRoundActualScale]
  have h : (s + 1) * layeredRoundActualKeyCap M s + 1 ≤
      (s + 2) * (layeredRoundActualKeyCap M s + 1) := by nlinarith
  nlinarith

/-- Every actual alphabet below the recurrence cap satisfies the sharper support density premise
at a live scale twenty times smaller than `layeredRoundActualScale`. -/
theorem layeredRoundSupport_density {A M s r j : ℕ}
    (hA : A ≤ layeredRoundActualKeyCap M s) :
    (4 * ((s + 1) * A)) * layeredRoundSupportShell M s r j +
        layeredRoundSupportShell M s r j ≤ layeredRoundSupportLive M s r j + 1 := by
  let R := r * layeredRoundSupportScale M s ^ j
  simp only [layeredRoundSupportShell, layeredRoundSupportLive]
  change (4 * ((s + 1) * A)) * (20 * R) + 20 * R ≤
    100 * ((s + 1) * layeredRoundActualKeyCap M s + 1) * R + 1
  have hbase : (s + 1) * A ≤ (s + 1) * layeredRoundActualKeyCap M s :=
    Nat.mul_le_mul_left (s + 1) hA
  calc
    (4 * ((s + 1) * A)) * (20 * R) + 20 * R ≤
        (4 * ((s + 1) * layeredRoundActualKeyCap M s)) * (20 * R) + 20 * R := by
          gcongr
    _ = 80 * ((s + 1) * layeredRoundActualKeyCap M s) * R + 20 * R := by ring
    _ ≤ 100 * ((s + 1) * layeredRoundActualKeyCap M s) * R + 100 * R := by
      gcongr <;> omega
    _ = 100 * ((s + 1) * layeredRoundActualKeyCap M s + 1) * R := by ring
    _ ≤ 100 * ((s + 1) * layeredRoundActualKeyCap M s + 1) * R + 1 := by omega

/-- Despite the constant improvement, the support density premise still fails whenever the
external gate cap already dominates the ambient live dimension. -/
theorem not_layeredRoundSupport_worstCase_density_of_live_le_gateBound
    {N M s K : ℕ} (hN : 0 < N) (hNM : N ≤ M) (hK : 0 < K) :
    ¬((4 * ((s + 1) * layeredRoundActualKeyCap M s)) * K + K ≤ N + 1) := by
  intro hdensity
  have hM : 1 ≤ M := hN.trans_le hNM
  have hpow : 1 ≤ 2 ^ (s + 1) := one_le_pow₀ (by omega)
  have hcap : 2 * M ≤ layeredRoundActualKeyCap M s := by
    rw [layeredRoundActualKeyCap]
    exact Nat.le_mul_of_pos_right (2 * M) hpow
  have hbaseLower : 8 * M ≤ 4 * ((s + 1) * layeredRoundActualKeyCap M s) := by
    calc
      8 * M = 4 * (1 * (2 * M)) := by ring
      _ ≤ 4 * ((s + 1) * layeredRoundActualKeyCap M s) := by gcongr <;> omega
  have hbase : N + 1 < 4 * ((s + 1) * layeredRoundActualKeyCap M s) := by omega
  have hmul : 4 * ((s + 1) * layeredRoundActualKeyCap M s) ≤
      4 * ((s + 1) * layeredRoundActualKeyCap M s) * K :=
    Nat.le_mul_of_pos_right _ hK
  omega

theorem layeredRoundSupport_gateBound_lt_live_of_density
    {N M s K : ℕ} (hN : 0 < N) (hK : 0 < K)
    (hdensity : (4 * ((s + 1) * layeredRoundActualKeyCap M s)) * K + K ≤ N + 1) :
    M < N := by
  apply Nat.lt_of_not_ge
  intro hNM
  exact not_layeredRoundSupport_worstCase_density_of_live_le_gateBound hN hNM hK hdensity

/-- Half-shell contraction at every level of the support-specific schedule. -/
theorem normalizedLayered_commonShallowBad_scaled_le_support_schedule
    {M s r j fuel : ℕ}
    {C : Layered (layeredRoundSupportLive M s r j)}
    (hr : 0 < r) (hw : BottomWidth (s + 1) C)
    (hactual : (∑ g, (normalizedLayeredBottomFamily C g).length) ≤
      layeredRoundActualKeyCap M s)
    (hKfuel : layeredRoundSupportShell M s r j ≤ fuel) :
    (commonShallowBad (normalizedLayeredBottomFamily C) fuel
        (layeredRoundSupportShell M s r j)
        (10 * (r * layeredRoundSupportScale M s ^ j)) s).card *
        2 ^ (10 * (r * layeredRoundSupportScale M s ^ j)) ≤
      (Finset.univ.filter fun σ : Restriction (layeredRoundSupportLive M s r j) =>
        stars σ = layeredRoundSupportShell M s r j).card := by
  let R := r * layeredRoundSupportScale M s ^ j
  have hscale : 0 < layeredRoundSupportScale M s := by
    simp [layeredRoundSupportScale]
  have hR : 0 < R := Nat.mul_pos hr (pow_pos hscale _)
  have hdK : 10 * R ≤ layeredRoundSupportShell M s r j := by
    simp only [layeredRoundSupportShell]
    change 10 * R ≤ 20 * R
    omega
  have hKn : layeredRoundSupportShell M s r j ≤ layeredRoundSupportLive M s r j := by
    simp only [layeredRoundSupportShell, layeredRoundSupportLive]
    change 20 * R ≤ 100 * ((s + 1) * layeredRoundActualKeyCap M s + 1) * R
    exact Nat.mul_le_mul_right R (by omega)
  have hsave : 1 * layeredRoundSupportShell M s r j / 2 ≤ 10 * R := by
    simp only [layeredRoundSupportShell]
    change 1 * (20 * R) / 2 ≤ 10 * R
    omega
  have hbound := normalizedLayered_commonShallowBad_scaled_le_of_support_density
    (residualDepth := s) (d := 10 * R) (savingNum := 1) (savingDen := 2)
    hw hKfuel hdK hKn hsave (layeredRoundSupport_density hactual)
  have hhalf : 1 * layeredRoundSupportShell M s r j / 2 = 10 * R := by
    simp only [layeredRoundSupportShell]
    change 1 * (20 * R) / 2 = 10 * R
    omega
  rw [hhalf] at hbound
  simpa [R] using hbound

/-- Any finite label that losslessly retains every stable `(gate, term-position)` key has at
least the original rectangular `G*m` cardinality.  Adding an owned Hall slot after this datum
therefore cannot reduce the key alphabet used by the current decoder. -/
theorem stableTermKey_card_le_of_leftInverse {G m : ℕ} {L : Type}
    [Fintype L] (encode : Fin G × Fin m → L) (decode : L → Fin G × Fin m)
    (hleft : Function.LeftInverse decode encode) :
    G * m ≤ Fintype.card L := by
  simpa [Fintype.card_prod] using
    Fintype.card_le_of_injective encode hleft.injective

/-- Recovering only a root-independent target meaning cannot compress a family whose meanings
are already pairwise distinct.  Unlike `stableTermKey_card_le_of_leftInverse`, the decoder here
does not recover the syntactic `(gate, term-position)` key: it may land in an arbitrary semantic
type `S`.  Injectivity of the realized meaning alone still forces the complete `G*m` alphabet.

Thus a semantic quotient can save labels only by proving genuine semantic collisions in the
particular family; it gives no worst-case improvement for families with distinct targets. -/
theorem stableTargetMeaning_card_le_of_decoder {G m : ℕ} {L S : Type}
    [Fintype L] (meaning : Fin G × Fin m → S) (hmeaning : Function.Injective meaning)
    (encode : Fin G × Fin m → L) (decode : L → S)
    (hdecode : ∀ key, decode (encode key) = meaning key) :
    G * m ≤ Fintype.card L := by
  have hencode : Function.Injective encode := by
    intro a b hab
    apply hmeaning
    rw [← hdecode a, ← hdecode b, hab]
  simpa [Fintype.card_prod] using
    Fintype.card_le_of_injective encode hencode

/-! ### The distinct-meaning obstruction is realized at width one

The preceding lower bound is not merely conditional on an abstract semantic family.  A
rectangular `G`-by-`m` family of positive singleton clauses over `G*m` coordinates realizes all
of its targets as distinct Boolean functions.  Thus bounded width, duplicate elimination, and
semantic quotienting alone cannot force collisions below the full occurrence count.
-/

/-- The singleton clause assigned to one rectangular stable key. -/
def rectangularDistinctSingletonMeaning (key : Fin G × Fin m) :
    Depth3.Clause (G * m) :=
  ⟨[Rung4Literal.pos (finProdFinEquiv key)]⟩

/-- The actual Boolean meaning of the rectangular singleton target. -/
def rectangularDistinctSingletonSemantics (key : Fin G × Fin m) :
    (Fin (G * m) → Bool) → Bool :=
  (rectangularDistinctSingletonMeaning key).eval

/-- Distinct rectangular keys compute distinct Boolean functions. -/
theorem rectangularDistinctSingletonSemantics_injective :
    Function.Injective (@rectangularDistinctSingletonSemantics G m) := by
  intro a b hab
  apply finProdFinEquiv.injective
  by_contra hne
  have happ := congrFun hab (fun i => decide (i = finProdFinEquiv a))
  simp [rectangularDistinctSingletonSemantics, rectangularDistinctSingletonMeaning,
    Depth3.Clause.eval, Rung4Literal.eval, Ne.symm hne] at happ

/-- The corresponding canonical gate family: gate `g` contains the `m` singleton meanings in
its row. -/
def rectangularDistinctSingletonGates (G m : ℕ) :
    Fin G → List (Depth3.Clause (G * m)) :=
  fun g => List.ofFn fun j : Fin m => rectangularDistinctSingletonMeaning (g, j)

theorem rectangularDistinctSingletonGates_get (g : Fin G) (j : Fin m) :
    (rectangularDistinctSingletonGates G m g).get
        (Fin.cast (by simp [rectangularDistinctSingletonGates]) j) =
      rectangularDistinctSingletonMeaning (g, j) := by
  simp [rectangularDistinctSingletonGates]

/-- Every target in the concrete obstruction has bottom width exactly one. -/
theorem rectangularDistinctSingletonGates_width_one :
    ∀ g T, T ∈ rectangularDistinctSingletonGates G m g → T.lits.length ≤ 1 := by
  intro g T hT
  simp [rectangularDistinctSingletonGates] at hT
  obtain ⟨j, rfl⟩ := hT
  simp [rectangularDistinctSingletonMeaning]

/-- Any label decoder recovering only the Boolean functions of the concrete width-one targets
still needs at least `G*m` labels. -/
theorem rectangularDistinctSingleton_card_le_of_semanticDecoder
    {L : Type} [Fintype L]
    (encode : Fin G × Fin m → L)
    (decode : L → ((Fin (G * m) → Bool) → Bool))
    (hdecode : ∀ key,
      decode (encode key) = rectangularDistinctSingletonSemantics key) :
    G * m ≤ Fintype.card L :=
  stableTargetMeaning_card_le_of_decoder rectangularDistinctSingletonSemantics
    rectangularDistinctSingletonSemantics_injective encode decode hdecode

/-! ### The width-one obstruction is an actual collapse-round output

The independent singleton family is not excluded merely by requiring the current circuit to be
the result of `collapseRound`.  Put one singleton DNF below each inner `gAnd`, group `m` of those
children per row, and put the `G` rows below an outer `gOr`.  At fuel one under the all-live
restriction, each singleton DNF switches to the corresponding singleton CNF; the inner `gAnd`
merges each row, while the outer `gOr` preserves the `G` separate CNF gates.
-/

/-- One positive singleton DNF switches exactly to its singleton CNF at fuel one. -/
theorem collapseRound_positiveSingletonDnf (i : Fin n) :
    collapseRound 1 (fun _ : Fin n => none)
      (Layered.dnf [⟨[Rung4Literal.pos i]⟩]) =
      Layered.cnf [⟨[Rung4Literal.pos i]⟩] := by
  simp [collapseRound, leafCollapse, mergePass, canonicalDT, toDTree, dtreeToCNF,
    SwitchingCounting.anyTermSat, SwitchingCounting.termSat,
    SwitchingCounting.activeTerm, SwitchingCounting.freeLits, Depth3.litFree,
    Depth3.litTrue, Depth3.litFixedVal, SwitchingCounting.litFalse,
    SwitchingCounting.termFalsified, SwitchingCounting.litVar, fixVar, Function.update]

/-- A positive singleton switches in exactly the same way below an arbitrary restriction, provided
its coordinate is still live.  This form is needed to test recurrence states away from the root
shell. -/
theorem collapseRound_positiveSingletonDnf_of_free
    (σ : Restriction n) (i : Fin n) (hi : σ i = none) :
    collapseRound 1 σ (Layered.dnf [⟨[Rung4Literal.pos i]⟩]) =
      Layered.cnf [⟨[Rung4Literal.pos i]⟩] := by
  simp [collapseRound, leafCollapse, mergePass, canonicalDT, toDTree, dtreeToCNF,
    SwitchingCounting.anyTermSat, SwitchingCounting.termSat,
    SwitchingCounting.activeTerm, SwitchingCounting.freeLits, Depth3.litFree,
    Depth3.litTrue, Depth3.litFixedVal, SwitchingCounting.litFalse,
    SwitchingCounting.termFalsified, SwitchingCounting.litVar, fixVar, Function.update, hi]

/-- A depth-four predecessor whose next collapsed bottom gates will be the rectangular singleton
rows. -/
def rectangularDistinctSingletonPredecessor (G m : ℕ) : Layered (G * m) :=
  Layered.gOr (List.ofFn fun g : Fin G =>
    Layered.gAnd (List.ofFn fun j : Fin m =>
      Layered.dnf [rectangularDistinctSingletonMeaning (g, j)]))

/-- The claimed one-round output, retaining one CNF bottom gate per rectangular row. -/
def rectangularDistinctSingletonRoundOutput (G m : ℕ) : Layered (G * m) :=
  Layered.gOr (List.ofFn fun g : Fin G =>
    Layered.cnf (rectangularDistinctSingletonGates G m g))

/-- With nonempty row and column sets, the predecessor is a genuine depth-four alternating
top-OR circuit, not merely an arbitrary `Layered` syntax tree. -/
theorem rectangularDistinctSingletonPredecessor_altO
    (hG : 0 < G) (hm : 0 < m) :
    AltO 4 (rectangularDistinctSingletonPredecessor G m) := by
  unfold rectangularDistinctSingletonPredecessor
  refine AltO.gOr 1 _ ?_ ?_
  · intro hnil
    have hlen := congrArg List.length hnil
    simp at hlen
    omega
  · intro gate hgate
    simp at hgate
    obtain ⟨g, rfl⟩ := hgate
    refine AltA.gAnd 0 _ ?_ ?_
    · intro hnil
      have hlen := congrArg List.length hnil
      simp at hlen
      omega
    · intro gate hgate
      simp at hgate
      obtain ⟨j, rfl⟩ := hgate
      exact AltO.dnf _

private theorem rectangular_allCnf_map_cnf (css : List (List (Depth3.Clause n))) :
    allCnf (css.map Layered.cnf) = some css := by
  induction css with
  | nil => rfl
  | cons cs css ih => simp [allCnf, ih]

private theorem rectangular_mergePass_gAnd_map_cnf
    (css : List (List (Depth3.Clause n))) :
    mergePass (Layered.gAnd (css.map Layered.cnf)) = Layered.cnf css.flatten := by
  simp [mergePass, rectangular_allCnf_map_cnf]

private theorem rectangular_flatten_map_singleton (xs : List α) :
    (xs.map singleton).flatten = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.map_cons, List.flatten_cons, ih]
      rfl

private theorem rectangular_mergePass_row (g : Fin G) :
    mergePass (Layered.gAnd (List.ofFn fun j : Fin m =>
      Layered.cnf [rectangularDistinctSingletonMeaning (g, j)])) =
      Layered.cnf (rectangularDistinctSingletonGates G m g) := by
  have hlist : (List.ofFn fun j : Fin m =>
      Layered.cnf [rectangularDistinctSingletonMeaning (g, j)]) =
      (List.ofFn fun j : Fin m =>
        [rectangularDistinctSingletonMeaning (g, j)]).map Layered.cnf := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    rfl
  rw [hlist, rectangular_mergePass_gAnd_map_cnf]
  have hsingle : (List.ofFn fun j : Fin m =>
      [rectangularDistinctSingletonMeaning (g, j)]) =
      (List.ofFn fun j : Fin m =>
        rectangularDistinctSingletonMeaning (g, j)).map singleton := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    rfl
  rw [hsingle, rectangular_flatten_map_singleton]
  rfl

/-- For every nonempty row index, the concrete predecessor produces the independent singleton
family after one actual collapse round. -/
theorem collapseRound_rectangularDistinctSingletonPredecessor
    (hG : 0 < G) :
    collapseRound 1 (fun _ : Fin (G * m) => none)
      (rectangularDistinctSingletonPredecessor G m) =
      rectangularDistinctSingletonRoundOutput G m := by
  unfold collapseRound rectangularDistinctSingletonPredecessor
    rectangularDistinctSingletonRoundOutput
  rw [show leafCollapse 1 (fun _ : Fin (G * m) => none)
      (Layered.gOr (List.ofFn fun g : Fin G =>
        Layered.gAnd (List.ofFn fun j : Fin m =>
          Layered.dnf [rectangularDistinctSingletonMeaning (g, j)]))) =
      Layered.gOr (List.ofFn fun g : Fin G =>
        Layered.gAnd (List.ofFn fun j : Fin m =>
          Layered.cnf [rectangularDistinctSingletonMeaning (g, j)])) by
    rw [leafCollapse, leafCollapseList_eq]
    congr 1
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext g
    change Layered.gAnd (leafCollapseList 1 (fun _ : Fin (G * m) => none)
      (List.ofFn fun j : Fin m =>
        Layered.dnf [rectangularDistinctSingletonMeaning (g, j)])) = _
    rw [leafCollapseList_eq, List.map_ofFn]
    congr 1
    apply congrArg List.ofFn
    funext j
    exact collapseRound_positiveSingletonDnf (finProdFinEquiv (g, j))]
  cases G with
  | zero => simp at hG
  | succ G =>
      have hnone : allDnf (List.ofFn fun g : Fin (G + 1) =>
          Layered.gAnd (List.ofFn fun j : Fin m =>
            Layered.cnf [rectangularDistinctSingletonMeaning (g, j)])) = none := by
        rw [List.ofFn_succ]
        rfl
      rw [mergePass, hnone, mergePassList_eq, List.map_ofFn]
      simp only
      congr 1
      apply congrArg List.ofFn
      funext g
      exact rectangular_mergePass_row g

/-- The syntactic bottom-gate extractor sees exactly the `G` rectangular singleton rows in the
one-round output. -/
theorem bottomGates_rectangularDistinctSingletonRoundOutput :
    bottomGates (rectangularDistinctSingletonRoundOutput G m) =
      List.ofFn (rectangularDistinctSingletonGates G m) := by
  rw [rectangularDistinctSingletonRoundOutput, bottomGates, bottomGatesList_eq,
    List.map_ofFn]
  change (List.ofFn fun g : Fin G => [rectangularDistinctSingletonGates G m g]).flatten = _
  have hsingle : (List.ofFn fun g : Fin G =>
      [rectangularDistinctSingletonGates G m g]) =
      (List.ofFn (rectangularDistinctSingletonGates G m)).map singleton := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext g
    rfl
  rw [hsingle, rectangular_flatten_map_singleton]

/-- The positive bottom-gate family of the exact round output owns every ambient coordinate.
Thus even width-one support need not become sublinear merely because the circuit is the result of
a genuine collapse round. -/
theorem familyVariableSupport_rectangularDistinctSingletonGates :
    familyVariableSupport (rectangularDistinctSingletonGates G m) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  obtain ⟨key, rfl⟩ := finProdFinEquiv.surjective i
  rcases key with ⟨g, j⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨g, Finset.mem_univ g, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨rectangularDistinctSingletonMeaning (g, j), ?_, ?_⟩
  · simp [rectangularDistinctSingletonGates]
  · simp [clauseVariableSupport, rectangularDistinctSingletonMeaning, litVar]

/-- Duplicate normalization and adjoining the negative polarity do not shrink the support of the
exact circuit-indexed family: its positive half already contains every singleton coordinate. -/
theorem normalizedLayeredBottomFamily_rectangularRoundOutput_support :
    familyVariableSupport
        (normalizedLayeredBottomFamily (rectangularDistinctSingletonRoundOutput G m)) =
      Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  obtain ⟨key, rfl⟩ := finProdFinEquiv.surjective i
  rcases key with ⟨g, j⟩
  have hrow : rectangularDistinctSingletonGates G m g ∈
      bottomGates (rectangularDistinctSingletonRoundOutput G m) := by
    rw [bottomGates_rectangularDistinctSingletonRoundOutput]
    simp
  have hfamily : rectangularDistinctSingletonGates G m g ∈
      layeredBottomFamilyList (rectangularDistinctSingletonRoundOutput G m) :=
    List.mem_append_left _ hrow
  obtain ⟨idx, hidx⟩ := List.get_of_mem hfamily
  apply Finset.mem_biUnion.mpr
  refine ⟨idx, Finset.mem_univ idx, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨rectangularDistinctSingletonMeaning (g, j), ?_, ?_⟩
  · rw [List.mem_toFinset]
    change rectangularDistinctSingletonMeaning (g, j) ∈
      ((layeredBottomFamilyList
        (rectangularDistinctSingletonRoundOutput G m)).get idx).eraseDups
    rw [hidx,
      PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.mem_eraseDups_iff]
    simp [rectangularDistinctSingletonGates]
  · simp [clauseVariableSupport, rectangularDistinctSingletonMeaning, litVar]

/-- The normalized circuit-owned variable support of this actual one-round output saturates the
live dimension exactly.  This refutes any sublinear support conclusion derived only from the
current width, normalization, alternation, collapse-range, and scalar conservation invariants. -/
theorem rectangularDistinctSingletonRoundOutput_support_saturates_live :
    (familyVariableSupport
      (normalizedLayeredBottomFamily (rectangularDistinctSingletonRoundOutput G m))).card =
      stars (fun _ : Fin (G * m) => none) := by
  rw [normalizedLayeredBottomFamily_rectangularRoundOutput_support,
    Finset.card_univ, Fintype.card_fin, stars, freeVars]
  simp

/-! ### The exact round also saturates the natural global budgets

The range witness above is not ruled out by remembering the original bottom-clause occurrence
budget or the current survivor count.  Both the predecessor and its round output have exactly
`G*m` bottom-clause occurrences, and the all-live restriction has exactly `G*m` survivors.
Thus bare occurrence conservation and a non-strict occurrence-versus-live invariant are sharp on
this example; any useful global recurrence invariant must impose a genuine quantitative gap or
use more history than these scalar totals.
-/

/-- The depth-four predecessor already has exactly one bottom-clause occurrence per rectangular
key. -/
private theorem rectangular_bottomClauseCountList_eq_map_sum
    (gs : List (Layered n)) :
    bottomClauseCountList gs = (gs.map bottomClauseCount).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [ih]

private theorem rectangularSingletonPredecessor_row_bottomClauseCount
    (g : Fin G) :
    bottomClauseCount (Layered.gAnd (List.ofFn fun j : Fin m =>
      Layered.dnf [rectangularDistinctSingletonMeaning (g, j)])) = m := by
  rw [bottomClauseCount_gAnd, rectangular_bottomClauseCountList_eq_map_sum,
    List.map_ofFn, List.sum_ofFn]
  simp [Finset.sum_const]

theorem bottomClauseCount_rectangularDistinctSingletonPredecessor :
    bottomClauseCount (rectangularDistinctSingletonPredecessor G m) = G * m := by
  rw [rectangularDistinctSingletonPredecessor, bottomClauseCount_gOr,
    rectangular_bottomClauseCountList_eq_map_sum, List.map_ofFn, List.sum_ofFn]
  have hrow (g : Fin G) :
      bottomClauseCountList (List.ofFn fun j : Fin m =>
        Layered.dnf [rectangularDistinctSingletonMeaning (g, j)]) = m :=
    rectangularSingletonPredecessor_row_bottomClauseCount g
  calc
    (∑ g : Fin G, bottomClauseCountList (List.ofFn fun j : Fin m =>
        Layered.dnf [rectangularDistinctSingletonMeaning (g, j)])) =
        ∑ _ : Fin G, m := Finset.sum_congr rfl (fun g _ => hrow g)
    _ = G * m := by simp [Finset.sum_const]

/-- The collapse output preserves that occurrence budget exactly. -/
theorem bottomClauseCount_rectangularDistinctSingletonRoundOutput :
    bottomClauseCount (rectangularDistinctSingletonRoundOutput G m) = G * m := by
  rw [bottomClauseCount, bottomGates_rectangularDistinctSingletonRoundOutput]
  rw [List.map_ofFn, List.sum_ofFn]
  simp [rectangularDistinctSingletonGates, Finset.sum_const]

/-- The output has exactly one syntactic bottom gate per row. -/
theorem bottomGates_length_rectangularDistinctSingletonRoundOutput :
    (bottomGates (rectangularDistinctSingletonRoundOutput G m)).length = G := by
  rw [bottomGates_rectangularDistinctSingletonRoundOutput]
  simp

/-- At the root used by the exact collapse computation, every ambient coordinate survives. -/
theorem stars_rectangularDistinctSingleton_allLive :
    stars (fun _ : Fin (G * m) => none) = G * m := by
  rw [stars, freeVars]
  simp

/-- Consequently the exact round output simultaneously saturates original-occurrence
conservation and the live-dimension bound. -/
theorem rectangularDistinctSingletonRoundOutput_saturates_global_budgets :
    bottomClauseCount (rectangularDistinctSingletonRoundOutput G m) =
        bottomClauseCount (rectangularDistinctSingletonPredecessor G m) ∧
      bottomClauseCount (rectangularDistinctSingletonRoundOutput G m) =
        stars (fun _ : Fin (G * m) => none) := by
  rw [bottomClauseCount_rectangularDistinctSingletonRoundOutput,
    bottomClauseCount_rectangularDistinctSingletonPredecessor,
    stars_rectangularDistinctSingleton_allLive]
  exact ⟨rfl, rfl⟩

/-! ### Saturation persists below a non-root padded restriction

Adding `pad` ambient coordinates and fixing all of them does not create slack in either scalar
budget.  The independent singleton coordinates occupy the right summand of `Fin (pad + G*m)`.
The padded restriction is a proper extension of the all-live root when `pad > 0`, but it leaves
exactly the `G*m` coordinates used by the circuit live.
-/

/-- Fix the padding coordinates to false and leave the rectangular coordinates live. -/
def paddedRectangularRestriction (pad G m : ℕ) : Restriction (pad + G * m) :=
  Fin.append (fun _ : Fin pad => some false) (fun _ : Fin (G * m) => none)

/-- The padded singleton belonging to one stable rectangular key. -/
def paddedRectangularSingletonMeaning (pad : ℕ) (key : Fin G × Fin m) :
    Depth3.Clause (pad + G * m) :=
  ⟨[Rung4Literal.pos (Fin.natAdd pad (finProdFinEquiv key))]⟩

def paddedRectangularSingletonGates (pad G m : ℕ) :
    Fin G → List (Depth3.Clause (pad + G * m)) :=
  fun g => List.ofFn fun j : Fin m => paddedRectangularSingletonMeaning pad (g, j)

def paddedRectangularSingletonPredecessor (pad G m : ℕ) : Layered (pad + G * m) :=
  Layered.gOr (List.ofFn fun g : Fin G =>
    Layered.gAnd (List.ofFn fun j : Fin m =>
      Layered.dnf [paddedRectangularSingletonMeaning pad (g, j)]))

def paddedRectangularSingletonRoundOutput (pad G m : ℕ) : Layered (pad + G * m) :=
  Layered.gOr (List.ofFn fun g : Fin G =>
    Layered.cnf (paddedRectangularSingletonGates pad G m g))

/-- Padding variables does not change the predecessor's genuine depth-four alternation shape. -/
theorem paddedRectangularSingletonPredecessor_altO (hG : 0 < G) (hm : 0 < m) :
    AltO 4 (paddedRectangularSingletonPredecessor pad G m) := by
  unfold paddedRectangularSingletonPredecessor
  refine AltO.gOr 1 _ ?_ ?_
  · intro hnil
    have hlen := congrArg List.length hnil
    simp at hlen
    omega
  · intro gate hgate
    simp at hgate
    obtain ⟨g, rfl⟩ := hgate
    refine AltA.gAnd 0 _ ?_ ?_
    · intro hnil
      have hlen := congrArg List.length hnil
      simp at hlen
      omega
    · intro gate hgate
      simp at hgate
      obtain ⟨j, rfl⟩ := hgate
      exact AltO.dnf _

@[simp] theorem paddedRectangularRestriction_target_free (key : Fin G × Fin m) :
    paddedRectangularRestriction pad G m (Fin.natAdd pad (finProdFinEquiv key)) = none := by
  simp [paddedRectangularRestriction]

/-- The padded state really lies below the all-live root. -/
theorem paddedRectangularRestriction_extends_allLive :
    RestrictionExtends (fun _ : Fin (pad + G * m) => none)
      (paddedRectangularRestriction pad G m) := by
  intro v b h
  simp at h

/-- Positive padding makes the extension strict: at least one ambient coordinate is fixed. -/
theorem paddedRectangularRestriction_ne_allLive (hpad : 0 < pad) :
    paddedRectangularRestriction pad G m ≠ (fun _ => none) := by
  intro h
  let i : Fin pad := ⟨0, hpad⟩
  have hi := congrFun h (Fin.castAdd (G * m) i)
  rw [paddedRectangularRestriction, Fin.append_left] at hi
  simp at hi

private theorem padded_rectangular_mergePass_row (g : Fin G) :
    mergePass (Layered.gAnd (List.ofFn fun j : Fin m =>
      Layered.cnf [paddedRectangularSingletonMeaning pad (g, j)])) =
      Layered.cnf (paddedRectangularSingletonGates pad G m g) := by
  have hlist : (List.ofFn fun j : Fin m =>
      Layered.cnf [paddedRectangularSingletonMeaning pad (g, j)]) =
      (List.ofFn fun j : Fin m =>
        [paddedRectangularSingletonMeaning pad (g, j)]).map Layered.cnf := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    rfl
  rw [hlist, rectangular_mergePass_gAnd_map_cnf]
  have hsingle : (List.ofFn fun j : Fin m =>
      [paddedRectangularSingletonMeaning pad (g, j)]) =
      (List.ofFn fun j : Fin m =>
        paddedRectangularSingletonMeaning pad (g, j)).map singleton := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    rfl
  rw [hsingle, rectangular_flatten_map_singleton]
  rfl

/-- The same genuine collapse round occurs at the non-root padded restriction. -/
theorem collapseRound_paddedRectangularSingletonPredecessor (hG : 0 < G) :
    collapseRound 1 (paddedRectangularRestriction pad G m)
      (paddedRectangularSingletonPredecessor pad G m) =
      paddedRectangularSingletonRoundOutput pad G m := by
  unfold collapseRound paddedRectangularSingletonPredecessor
    paddedRectangularSingletonRoundOutput
  rw [show leafCollapse 1 (paddedRectangularRestriction pad G m)
      (Layered.gOr (List.ofFn fun g : Fin G =>
        Layered.gAnd (List.ofFn fun j : Fin m =>
          Layered.dnf [paddedRectangularSingletonMeaning pad (g, j)]))) =
      Layered.gOr (List.ofFn fun g : Fin G =>
        Layered.gAnd (List.ofFn fun j : Fin m =>
          Layered.cnf [paddedRectangularSingletonMeaning pad (g, j)])) by
    rw [leafCollapse, leafCollapseList_eq]
    congr 1
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext g
    change Layered.gAnd (leafCollapseList 1 (paddedRectangularRestriction pad G m)
      (List.ofFn fun j : Fin m =>
        Layered.dnf [paddedRectangularSingletonMeaning pad (g, j)])) = _
    rw [leafCollapseList_eq, List.map_ofFn]
    congr 1
    apply congrArg List.ofFn
    funext j
    exact collapseRound_positiveSingletonDnf_of_free _ _
      (paddedRectangularRestriction_target_free (pad := pad) (key := (g, j)))]
  cases G with
  | zero => simp at hG
  | succ G =>
      have hnone : allDnf (List.ofFn fun g : Fin (G + 1) =>
          Layered.gAnd (List.ofFn fun j : Fin m =>
            Layered.cnf [paddedRectangularSingletonMeaning pad (g, j)])) = none := by
        rw [List.ofFn_succ]
        rfl
      rw [mergePass, hnone, mergePassList_eq, List.map_ofFn]
      simp only
      congr 1
      apply congrArg List.ofFn
      funext g
      exact padded_rectangular_mergePass_row g

theorem bottomGates_paddedRectangularSingletonRoundOutput :
    bottomGates (paddedRectangularSingletonRoundOutput pad G m) =
      List.ofFn (paddedRectangularSingletonGates pad G m) := by
  rw [paddedRectangularSingletonRoundOutput, bottomGates, bottomGatesList_eq,
    List.map_ofFn]
  change (List.ofFn fun g : Fin G => [paddedRectangularSingletonGates pad G m g]).flatten = _
  have hsingle : (List.ofFn fun g : Fin G =>
      [paddedRectangularSingletonGates pad G m g]) =
      (List.ofFn (paddedRectangularSingletonGates pad G m)).map singleton := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext g
    rfl
  rw [hsingle, rectangular_flatten_map_singleton]

private theorem paddedPredecessor_row_bottomClauseCount (g : Fin G) :
    bottomClauseCount (Layered.gAnd (List.ofFn fun j : Fin m =>
      Layered.dnf [paddedRectangularSingletonMeaning pad (g, j)])) = m := by
  rw [bottomClauseCount_gAnd, rectangular_bottomClauseCountList_eq_map_sum,
    List.map_ofFn, List.sum_ofFn]
  simp [Finset.sum_const]

theorem bottomClauseCount_paddedRectangularSingletonPredecessor :
    bottomClauseCount (paddedRectangularSingletonPredecessor pad G m) = G * m := by
  rw [paddedRectangularSingletonPredecessor, bottomClauseCount_gOr,
    rectangular_bottomClauseCountList_eq_map_sum, List.map_ofFn, List.sum_ofFn]
  calc
    (∑ g : Fin G, bottomClauseCountList (List.ofFn fun j : Fin m =>
        Layered.dnf [paddedRectangularSingletonMeaning pad (g, j)])) =
        ∑ _ : Fin G, m := Finset.sum_congr rfl (fun g _ =>
          paddedPredecessor_row_bottomClauseCount g)
    _ = G * m := by simp [Finset.sum_const]

theorem bottomClauseCount_paddedRectangularSingletonRoundOutput :
    bottomClauseCount (paddedRectangularSingletonRoundOutput pad G m) = G * m := by
  rw [bottomClauseCount, bottomGates_paddedRectangularSingletonRoundOutput,
    List.map_ofFn, List.sum_ofFn]
  simp [paddedRectangularSingletonGates, Finset.sum_const]

/-- Exactly the rectangular coordinates survive below the padded restriction. -/
theorem stars_paddedRectangularRestriction :
    stars (paddedRectangularRestriction pad G m) = G * m := by
  rw [stars, freeVars, Finset.card_filter, Fin.sum_univ_add]
  simp [paddedRectangularRestriction, Finset.sum_const]

/-- Every live rectangular coordinate occurs in the normalized two-polarity family of the padded
round output.  Fixed padding therefore cannot manufacture a support gap. -/
theorem paddedRectangular_liveSupport_subset_familyVariableSupport :
    Finset.univ.image (fun i : Fin (G * m) => Fin.natAdd pad i) ⊆
      familyVariableSupport
        (normalizedLayeredBottomFamily
          (paddedRectangularSingletonRoundOutput pad G m)) := by
  intro i hi
  rw [Finset.mem_image] at hi
  obtain ⟨i, _, rfl⟩ := hi
  obtain ⟨key, rfl⟩ := finProdFinEquiv.surjective i
  rcases key with ⟨g, j⟩
  have hrow : paddedRectangularSingletonGates pad G m g ∈
      bottomGates (paddedRectangularSingletonRoundOutput pad G m) := by
    rw [bottomGates_paddedRectangularSingletonRoundOutput]
    simp
  have hfamily : paddedRectangularSingletonGates pad G m g ∈
      layeredBottomFamilyList (paddedRectangularSingletonRoundOutput pad G m) :=
    List.mem_append_left _ hrow
  obtain ⟨idx, hidx⟩ := List.get_of_mem hfamily
  apply Finset.mem_biUnion.mpr
  refine ⟨idx, Finset.mem_univ idx, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨paddedRectangularSingletonMeaning pad (g, j), ?_, ?_⟩
  · rw [List.mem_toFinset]
    change paddedRectangularSingletonMeaning pad (g, j) ∈
      ((layeredBottomFamilyList
        (paddedRectangularSingletonRoundOutput pad G m)).get idx).eraseDups
    rw [hidx,
      PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.mem_eraseDups_iff]
    simp [paddedRectangularSingletonGates]
  · simp [clauseVariableSupport, paddedRectangularSingletonMeaning, litVar]

/-- The padded output owns at least one circuit coordinate for every survivor.  In particular,
the non-root scheduled state remains a regression case for every pointwise sublinear-support
claim even though its ambient dimension is enlarged by fixed padding. -/
theorem stars_paddedRectangularRestriction_le_familyVariableSupport_card :
    stars (paddedRectangularRestriction pad G m) ≤
      (familyVariableSupport
        (normalizedLayeredBottomFamily
          (paddedRectangularSingletonRoundOutput pad G m))).card := by
  rw [stars_paddedRectangularRestriction]
  calc
    G * m =
        (Finset.univ.image (fun i : Fin (G * m) => Fin.natAdd pad i)).card := by
      rw [Finset.card_image_of_injective]
      · simp
      · intro a b h
        exact Fin.natAdd_injective (G * m) pad h
    _ ≤ (familyVariableSupport
          (normalizedLayeredBottomFamily
            (paddedRectangularSingletonRoundOutput pad G m))).card :=
      Finset.card_le_card paddedRectangular_liveSupport_subset_familyVariableSupport

/-- At a strict non-root extension, the actual round output still saturates both inherited
occurrences and current live dimension. -/
theorem paddedRectangularRoundOutput_saturates_global_budgets
    (hpad : 0 < pad) (hG : 0 < G) (hm : 0 < m) :
    RestrictionExtends (fun _ : Fin (pad + G * m) => none)
        (paddedRectangularRestriction pad G m) ∧
      paddedRectangularRestriction pad G m ≠ (fun _ => none) ∧
      AltO 4 (paddedRectangularSingletonPredecessor pad G m) ∧
      collapseRound 1 (paddedRectangularRestriction pad G m)
          (paddedRectangularSingletonPredecessor pad G m) =
        paddedRectangularSingletonRoundOutput pad G m ∧
      bottomClauseCount (paddedRectangularSingletonRoundOutput pad G m) =
        bottomClauseCount (paddedRectangularSingletonPredecessor pad G m) ∧
      bottomClauseCount (paddedRectangularSingletonRoundOutput pad G m) =
        stars (paddedRectangularRestriction pad G m) := by
  exact ⟨paddedRectangularRestriction_extends_allLive,
    paddedRectangularRestriction_ne_allLive hpad,
    paddedRectangularSingletonPredecessor_altO hG hm,
    collapseRound_paddedRectangularSingletonPredecessor hG,
    by rw [bottomClauseCount_paddedRectangularSingletonRoundOutput,
      bottomClauseCount_paddedRectangularSingletonPredecessor],
    by rw [bottomClauseCount_paddedRectangularSingletonRoundOutput,
      stars_paddedRectangularRestriction]⟩

/-! ### The padded saturation state lies on the audited survivor schedule -/

/-- Every bottom clause in the padded rectangular output is a singleton. -/
theorem paddedRectangularSingletonRoundOutput_bottomWidth_one :
    BottomWidth 1 (paddedRectangularSingletonRoundOutput pad G m) := by
  intro cs hcs T hT
  rw [bottomGates_paddedRectangularSingletonRoundOutput] at hcs
  obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hcs
  rw [paddedRectangularSingletonGates] at hT
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hT
  simp [paddedRectangularSingletonMeaning]

/-! ### The scheduled saturated state is genuinely bad -/

/-- A zero-depth Boolean decision tree has the same value on every two assignments. -/
private theorem BoolDecisionTree.eval_eq_of_depth_eq_zero {n : ℕ}
    (T : BoolDecisionTree n) (hdepth : T.depth = 0)
    (x y : Fin n → Bool) : T.eval x = T.eval y := by
  cases T with
  | leaf b => rfl
  | query i lo hi => simp [BoolDecisionTree.depth] at hdepth

/-- The twenty packed singleton coordinates, with an arbitrary fixed padding prefix. -/
def paddedSingletonSupport (pad : ℕ) : Finset (Fin (pad + 20)) :=
  Finset.univ.image fun j : Fin 20 ↦
    Fin.natAdd pad (finProdFinEquiv ((0 : Fin 1), j))

@[simp] theorem paddedSingletonSupport_card (pad : ℕ) :
    (paddedSingletonSupport pad).card = 20 := by
  rw [paddedSingletonSupport, Finset.card_image_of_injective]
  · simp
  · intro a b h
    have hp := Fin.natAdd_injective 20 pad h
    have hab := finProdFinEquiv.injective hp
    exact congrArg Prod.snd hab

/-- The exact two-polarity circuit family mentions precisely the twenty packed coordinates and
no padding coordinate. -/
theorem normalizedPaddedSingleton_familyVariableSupport (pad : ℕ) :
    familyVariableSupport
        (normalizedLayeredBottomFamily
          (paddedRectangularSingletonRoundOutput pad 1 20)) =
      paddedSingletonSupport pad := by
  apply Finset.Subset.antisymm
  · intro i hi
    obtain ⟨g, _, hi⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨T, hT, hi⟩ := Finset.mem_biUnion.mp hi
    rw [List.mem_toFinset] at hT
    change T ∈ (layeredBottomFamily
      (paddedRectangularSingletonRoundOutput pad 1 20) g).eraseDups at hT
    rw [PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.mem_eraseDups_iff]
      at hT
    fin_cases g
    · change T ∈ paddedRectangularSingletonGates pad 1 20 0 at hT
      change T ∈ List.ofFn (fun j : Fin 20 ↦
        paddedRectangularSingletonMeaning pad ((0 : Fin 1), j)) at hT
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hT
      have hiEq : i = Fin.natAdd pad (finProdFinEquiv ((0 : Fin 1), j)) := by
        simpa [clauseVariableSupport, paddedRectangularSingletonMeaning, litVar] using hi
      rw [paddedSingletonSupport, Finset.mem_image]
      exact ⟨j, Finset.mem_univ j, hiEq.symm⟩
    · change T ∈ negDNF (paddedRectangularSingletonGates pad 1 20 0) at hT
      obtain ⟨U, hU, rfl⟩ := List.mem_map.mp (by simpa [negDNF] using hT)
      change U ∈ List.ofFn (fun j : Fin 20 ↦
        paddedRectangularSingletonMeaning pad ((0 : Fin 1), j)) at hU
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hU
      have hiEq : i = Fin.natAdd pad (finProdFinEquiv ((0 : Fin 1), j)) := by
        simpa [clauseVariableSupport, paddedRectangularSingletonMeaning,
          negLit, litVar] using hi
      rw [paddedSingletonSupport, Finset.mem_image]
      exact ⟨j, Finset.mem_univ j, hiEq.symm⟩
  · simpa [paddedSingletonSupport] using
      (paddedRectangular_liveSupport_subset_familyVariableSupport
        (pad := pad) (G := 1) (m := 20))

/-- The positive-polarity indexed gate of the padded round output is exactly its packed list of
twenty surviving positive singleton clauses. -/
private theorem padded_positive_family_gate (pad : ℕ) :
    layeredBottomFamily (paddedRectangularSingletonRoundOutput pad 1 20)
        ⟨0, by simp [layeredBottomFamilyList,
          bottomGates_paddedRectangularSingletonRoundOutput]⟩ =
      paddedRectangularSingletonGates pad 1 20 0 := by
  simp [layeredBottomFamily, layeredBottomFamilyList,
    bottomGates_paddedRectangularSingletonRoundOutput]

/-- The negative-polarity indexed gate is the list of the twenty negative singletons. -/
private theorem padded_negative_family_gate (pad : ℕ) :
    layeredBottomFamily (paddedRectangularSingletonRoundOutput pad 1 20)
        ⟨1, by simp [layeredBottomFamilyList,
          bottomGates_paddedRectangularSingletonRoundOutput]⟩ =
      negDNF (paddedRectangularSingletonGates pad 1 20 0) := by
  simp [layeredBottomFamily, layeredBottomFamilyList,
    bottomGates_paddedRectangularSingletonRoundOutput]

/-- The packed singleton obstruction is independent of the amount of fixed padding.  More than
ten live packed coordinates, with every other packed coordinate fixed false, rule out a
depth-ten common trunk with residual depth zero. -/
theorem paddedSingletonSupport_not_commonShallow_of_live_false (pad : ℕ)
    (σ : Restriction (pad + 20)) (hstars : stars σ = 20)
    (hlive : 10 < ((paddedSingletonSupport pad).filter fun i => σ i = none).card)
    (hfixedFalse : ∀ i ∈ paddedSingletonSupport pad,
      σ i ≠ none → σ i = some false) :
    ¬CommonShallowAt
      (normalizedLayeredBottomFamily
        (paddedRectangularSingletonRoundOutput pad 1 20)) 20 σ 10 0 := by
  intro hnormalized
  have hraw : CommonShallowAt
      (layeredBottomFamily (paddedRectangularSingletonRoundOutput pad 1 20))
      20 σ 10 0 :=
    (commonShallowAt_normalizedLayeredBottomFamily_iff
      (paddedRectangularSingletonRoundOutput pad 1 20) 20 σ 10 0).mp hnormalized
  obtain ⟨trunk, hdepth, hleaf⟩ := hraw
  let x : Fin (pad + 20) → Bool := fun v ↦ (σ v).getD false
  let path : Finset (Fin (pad + 20)) := (CommonTree.queryVars trunk x).toFinset
  have hpathCard : path.card ≤ 10 := by
    calc
      path.card ≤ (CommonTree.queryVars trunk x).length := List.toFinset_card_le _
      _ ≤ CommonTree.depth trunk := CommonTree.queryVars_length_le_depth trunk x
      _ ≤ 10 := hdepth
  have hnotSubset :
      ¬ ((paddedSingletonSupport pad).filter fun i => σ i = none) ⊆ path := by
    intro hsubset
    have := Finset.card_le_card hsubset
    omega
  obtain ⟨i, hiSupport, hiPath⟩ := Finset.not_subset.mp hnotSubset
  rw [Finset.mem_filter] at hiSupport
  have hiNone := hiSupport.2
  have hiPacked := hiSupport.1
  rw [paddedSingletonSupport, Finset.mem_image] at hiPacked
  obtain ⟨j, _, rfl⟩ := hiPacked
  let i : Fin (pad + 20) := Fin.natAdd pad (finProdFinEquiv ((0 : Fin 1), j))
  let y : Fin (pad + 20) → Bool := Function.update x i true
  have hsigmaTargetNone : σ i = none := by simpa [i] using hiNone
  have hx : Rung4Restriction.Extends σ x := by
    intro v b hv
    simp [x, hv]
  have hy : Rung4Restriction.Extends σ y := by
    intro v b hv
    have hvi : v ≠ i := by
      intro h
      subst v
      rw [hsigmaTargetNone] at hv
      simp at hv
    simpa [y, Function.update_of_ne hvi] using hx v b hv
  obtain ⟨hroot, hrunExtX, hshallow⟩ := hleaf x hx
  obtain ⟨_, hrunExtY, _⟩ := hleaf y hy
  have hrun : CommonTree.run trunk y = CommonTree.run trunk x := by
    have hxi : x i = false := by simp [x, hsigmaTargetNone]
    simpa [y, hxi] using
      CommonTree.run_update_of_not_mem_queryVars trunk x i
        (by simpa [path, i] using hiPath)
  let rho := CommonTree.run trunk x
  have hrunExtY' : Rung4Restriction.Extends rho y := by
    simpa [rho, hrun] using hrunExtY
  have hrhoStars : stars rho ≤ 20 := by
    calc
      stars rho ≤ stars σ := stars_le_of_restrictionExtends hroot
      _ = 20 := hstars
  have hgateDepth :
      (canonicalDT (paddedRectangularSingletonGates pad 1 20 0) 20 rho).depth = 0 := by
    have hg := hshallow ⟨0, by simp [layeredBottomFamilyList,
      bottomGates_paddedRectangularSingletonRoundOutput]⟩
    exact Nat.eq_zero_of_le_zero (by
      simpa only [padded_positive_family_gate] using hg)
  have hevalEq := BoolDecisionTree.eval_eq_of_depth_eq_zero
    (canonicalDT (paddedRectangularSingletonGates pad 1 20 0) 20 rho)
    hgateDepth x y
  rw [canonicalDT_eval 20 rho x hrhoStars hrunExtX,
    canonicalDT_eval 20 rho y hrhoStars hrunExtY'] at hevalEq
  have hxcoord (k : Fin 20) :
      x (Fin.natAdd pad (finProdFinEquiv ((0 : Fin 1), k))) = false := by
    let v := Fin.natAdd pad (finProdFinEquiv ((0 : Fin 1), k))
    have hvPacked : v ∈ paddedSingletonSupport pad := by
      rw [paddedSingletonSupport, Finset.mem_image]
      exact ⟨k, Finset.mem_univ k, rfl⟩
    by_cases hv : σ v = none
    · simp [x, v, hv]
    · have hvFalse := hfixedFalse v hvPacked hv
      simp [x, v, hvFalse]
  have hdnfX : dnfEval (paddedRectangularSingletonGates pad 1 20 0) x = false := by
    rw [dnfEval, List.any_eq_false]
    intro T hT
    rw [paddedRectangularSingletonGates] at hT
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hT
    simp [paddedRectangularSingletonMeaning, Rung4DNFTerm.evalLits,
      Rung4Literal.eval, hxcoord k]
  have hdnfY : dnfEval (paddedRectangularSingletonGates pad 1 20 0) y = true := by
    rw [dnfEval, List.any_eq_true]
    refine ⟨paddedRectangularSingletonMeaning pad ((0 : Fin 1), j), ?_, ?_⟩
    · rw [paddedRectangularSingletonGates]
      exact List.mem_ofFn.mpr ⟨j, rfl⟩
    · simp [paddedRectangularSingletonMeaning, Rung4DNFTerm.evalLits,
        Rung4Literal.eval, y, i]
  exact Bool.false_ne_true (hdnfX.symm.trans (hevalEq.trans hdnfY))

/-- The proposed one-sided converse is false: the opposite monochromatic profile is equally bad.
More than ten packed coordinates live while every other packed coordinate is fixed true rule out
the same depth-ten common trunk, witnessed by the negative-polarity singleton gate. -/
theorem paddedSingletonSupport_not_commonShallow_of_live_true (pad : ℕ)
    (σ : Restriction (pad + 20)) (hstars : stars σ = 20)
    (hlive : 10 < ((paddedSingletonSupport pad).filter fun i => σ i = none).card)
    (hfixedTrue : ∀ i ∈ paddedSingletonSupport pad,
      σ i ≠ none → σ i = some true) :
    ¬CommonShallowAt
      (normalizedLayeredBottomFamily
        (paddedRectangularSingletonRoundOutput pad 1 20)) 20 σ 10 0 := by
  intro hnormalized
  have hraw : CommonShallowAt
      (layeredBottomFamily (paddedRectangularSingletonRoundOutput pad 1 20))
      20 σ 10 0 :=
    (commonShallowAt_normalizedLayeredBottomFamily_iff
      (paddedRectangularSingletonRoundOutput pad 1 20) 20 σ 10 0).mp hnormalized
  obtain ⟨trunk, hdepth, hleaf⟩ := hraw
  let x : Fin (pad + 20) → Bool := fun v ↦ (σ v).getD true
  let path : Finset (Fin (pad + 20)) := (CommonTree.queryVars trunk x).toFinset
  have hpathCard : path.card ≤ 10 := by
    calc
      path.card ≤ (CommonTree.queryVars trunk x).length := List.toFinset_card_le _
      _ ≤ CommonTree.depth trunk := CommonTree.queryVars_length_le_depth trunk x
      _ ≤ 10 := hdepth
  have hnotSubset :
      ¬ ((paddedSingletonSupport pad).filter fun i => σ i = none) ⊆ path := by
    intro hsubset
    have := Finset.card_le_card hsubset
    omega
  obtain ⟨i, hiSupport, hiPath⟩ := Finset.not_subset.mp hnotSubset
  rw [Finset.mem_filter] at hiSupport
  have hiNone := hiSupport.2
  have hiPacked := hiSupport.1
  rw [paddedSingletonSupport, Finset.mem_image] at hiPacked
  obtain ⟨j, _, rfl⟩ := hiPacked
  let i : Fin (pad + 20) := Fin.natAdd pad (finProdFinEquiv ((0 : Fin 1), j))
  let y : Fin (pad + 20) → Bool := Function.update x i false
  have hsigmaTargetNone : σ i = none := by simpa [i] using hiNone
  have hx : Rung4Restriction.Extends σ x := by
    intro v b hv
    simp [x, hv]
  have hy : Rung4Restriction.Extends σ y := by
    intro v b hv
    have hvi : v ≠ i := by
      intro h
      subst v
      rw [hsigmaTargetNone] at hv
      simp at hv
    simpa [y, Function.update_of_ne hvi] using hx v b hv
  obtain ⟨hroot, hrunExtX, hshallow⟩ := hleaf x hx
  obtain ⟨_, hrunExtY, _⟩ := hleaf y hy
  have hrun : CommonTree.run trunk y = CommonTree.run trunk x := by
    have hxi : x i = true := by simp [x, hsigmaTargetNone]
    simpa [y, hxi] using
      CommonTree.run_update_of_not_mem_queryVars trunk x i
        (by simpa [path, i] using hiPath)
  let rho := CommonTree.run trunk x
  have hrunExtY' : Rung4Restriction.Extends rho y := by
    simpa [rho, hrun] using hrunExtY
  have hrhoStars : stars rho ≤ 20 := by
    calc
      stars rho ≤ stars σ := stars_le_of_restrictionExtends hroot
      _ = 20 := hstars
  have hgateDepth :
      (canonicalDT (negDNF (paddedRectangularSingletonGates pad 1 20 0))
        20 rho).depth = 0 := by
    have hg := hshallow ⟨1, by simp [layeredBottomFamilyList,
      bottomGates_paddedRectangularSingletonRoundOutput]⟩
    exact Nat.eq_zero_of_le_zero (by
      simpa only [padded_negative_family_gate] using hg)
  have hevalEq := BoolDecisionTree.eval_eq_of_depth_eq_zero
    (canonicalDT (negDNF (paddedRectangularSingletonGates pad 1 20 0)) 20 rho)
    hgateDepth x y
  rw [canonicalDT_eval 20 rho x hrhoStars hrunExtX,
    canonicalDT_eval 20 rho y hrhoStars hrunExtY'] at hevalEq
  have hxcoord (k : Fin 20) :
      x (Fin.natAdd pad (finProdFinEquiv ((0 : Fin 1), k))) = true := by
    let v := Fin.natAdd pad (finProdFinEquiv ((0 : Fin 1), k))
    have hvPacked : v ∈ paddedSingletonSupport pad := by
      rw [paddedSingletonSupport, Finset.mem_image]
      exact ⟨k, Finset.mem_univ k, rfl⟩
    by_cases hv : σ v = none
    · simp [x, v, hv]
    · have hvTrue := hfixedTrue v hvPacked hv
      simp [x, v, hvTrue]
  have hdnfX :
      dnfEval (negDNF (paddedRectangularSingletonGates pad 1 20 0)) x = false := by
    rw [dnfEval, List.any_eq_false]
    intro T hT
    rw [negDNF] at hT
    obtain ⟨U, hU, rfl⟩ := List.mem_map.mp hT
    rw [paddedRectangularSingletonGates] at hU
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hU
    simp [paddedRectangularSingletonMeaning, Rung4DNFTerm.evalLits,
      Rung4Literal.eval, negLit, hxcoord k]
  have hdnfY :
      dnfEval (negDNF (paddedRectangularSingletonGates pad 1 20 0)) y = true := by
    rw [dnfEval, List.any_eq_true]
    refine ⟨⟨[Rung4Literal.neg i]⟩, ?_, ?_⟩
    · rw [negDNF]
      apply List.mem_map.mpr
      refine ⟨paddedRectangularSingletonMeaning pad ((0 : Fin 1), j), ?_, ?_⟩
      · rw [paddedRectangularSingletonGates]
        exact List.mem_ofFn.mpr ⟨j, rfl⟩
      · simp [paddedRectangularSingletonMeaning, negLit, i]
    · simp [Rung4DNFTerm.evalLits, Rung4Literal.eval, y, i]
  exact Bool.false_ne_true (hdnfX.symm.trans (hevalEq.trans hdnfY))

/-- The live-support half of the converse is valid: when at most ten packed coordinates remain
live, the canonical common prefix queries all relevant variables within budget, regardless of
the twenty-shell survivors outside the family support. -/
theorem paddedSingletonSupport_commonShallow_of_live_le (pad : ℕ)
    (σ : Restriction (pad + 20)) (hstars : stars σ = 20)
    (hlive : ((paddedSingletonSupport pad).filter fun i => σ i = none).card ≤ 10) :
    CommonShallowAt
      (normalizedLayeredBottomFamily
        (paddedRectangularSingletonRoundOutput pad 1 20)) 20 σ 10 0 := by
  apply commonShallowAt_zero_of_live_support_le
  · omega
  · simpa [normalizedPaddedSingleton_familyVariableSupport] using hlive

/-- Mixed fixed polarities make both indexed singleton gates terminal already at the root.  A
fixed-true packed coordinate satisfies the positive DNF, while a fixed-false packed coordinate
satisfies its negative-polarity mate, so the root restriction itself is a zero-query common
trunk. -/
theorem paddedSingletonSupport_commonShallow_of_mixed_fixed (pad : ℕ)
    (σ : Restriction (pad + 20))
    (htrue : ∃ i ∈ paddedSingletonSupport pad, σ i = some true)
    (hfalse : ∃ i ∈ paddedSingletonSupport pad, σ i = some false) :
    CommonShallowAt
      (normalizedLayeredBottomFamily
        (paddedRectangularSingletonRoundOutput pad 1 20)) 20 σ 10 0 := by
  obtain ⟨itrue, hitrue, hσtrue⟩ := htrue
  obtain ⟨ifalse, hifalse, hσfalse⟩ := hfalse
  rw [paddedSingletonSupport, Finset.mem_image] at hitrue hifalse
  obtain ⟨jtrue, _, rfl⟩ := hitrue
  obtain ⟨jfalse, _, rfl⟩ := hifalse
  apply (commonShallowAt_normalizedLayeredBottomFamily_iff
    (paddedRectangularSingletonRoundOutput pad 1 20) 20 σ 10 0).mpr
  refine ⟨CommonTree.leaf σ, by simp [CommonTree.depth], ?_⟩
  intro x hx
  refine ⟨fun _ _ h ↦ h, hx, ?_⟩
  intro g
  have hglt : g.val < 2 := by
    simpa [layeredBottomFamilyList,
      bottomGates_paddedRectangularSingletonRoundOutput] using g.isLt
  interval_cases hval : g.val
  · simp only [CommonTree.run_leaf]
    have hg : g = ⟨0, by simp [layeredBottomFamilyList,
        bottomGates_paddedRectangularSingletonRoundOutput]⟩ := Fin.ext hval
    subst g
    rw [padded_positive_family_gate]
    have hany : anyTermSat (paddedRectangularSingletonGates pad 1 20 0) σ = true := by
      rw [anyTermSat, List.any_eq_true]
      refine ⟨paddedRectangularSingletonMeaning pad ((0 : Fin 1), jtrue), ?_, ?_⟩
      · rw [paddedRectangularSingletonGates]
        exact List.mem_ofFn.mpr ⟨jtrue, rfl⟩
      · simp [termSat, paddedRectangularSingletonMeaning, Depth3.litTrue,
          Depth3.litFixedVal, hσtrue]
    simp [canonicalDT, hany]
  · simp only [CommonTree.run_leaf]
    have hg : g = ⟨1, by simp [layeredBottomFamilyList,
        bottomGates_paddedRectangularSingletonRoundOutput]⟩ := Fin.ext hval
    subst g
    rw [padded_negative_family_gate]
    have hany : anyTermSat
        (negDNF (paddedRectangularSingletonGates pad 1 20 0)) σ = true := by
      rw [anyTermSat, List.any_eq_true]
      refine ⟨⟨[Rung4Literal.neg
        (Fin.natAdd pad (finProdFinEquiv ((0 : Fin 1), jfalse)))]⟩, ?_, ?_⟩
      · rw [negDNF]
        apply List.mem_map.mpr
        refine ⟨paddedRectangularSingletonMeaning pad ((0 : Fin 1), jfalse), ?_, ?_⟩
        · rw [paddedRectangularSingletonGates]
          exact List.mem_ofFn.mpr ⟨jfalse, rfl⟩
        · simp [paddedRectangularSingletonMeaning, negLit]
      · simp [termSat, Depth3.litTrue, Depth3.litFixedVal, hσfalse]
    simp [canonicalDT, hany]

/-- The exact bad event for the twenty packed singleton gates at arbitrary padding. -/
noncomputable def paddedSingletonBad (pad : ℕ) : Finset (Restriction (pad + 20)) :=
  commonShallowBad
    (normalizedLayeredBottomFamily
      (paddedRectangularSingletonRoundOutput pad 1 20)) 20 20 10 0

/-- Padding-parametric semantic membership bridge for the certified overlap criterion. -/
theorem paddedSingletonSupport_mem_bad_of_live_false (pad : ℕ)
    (σ : Restriction (pad + 20)) (hstars : stars σ = 20)
    (hlive : 10 < ((paddedSingletonSupport pad).filter fun i => σ i = none).card)
    (hfixedFalse : ∀ i ∈ paddedSingletonSupport pad,
      σ i ≠ none → σ i = some false) :
    σ ∈ paddedSingletonBad pad := by
  rw [paddedSingletonBad, mem_commonShallowBad]
  exact ⟨hstars,
    paddedSingletonSupport_not_commonShallow_of_live_false
      pad σ hstars hlive hfixedFalse⟩

/-- The symmetric all-true packed profile supplies an additional padding-parametric bad subset
which was absent from the earlier certified overlap count. -/
theorem paddedSingletonSupport_mem_bad_of_live_true (pad : ℕ)
    (σ : Restriction (pad + 20)) (hstars : stars σ = 20)
    (hlive : 10 < ((paddedSingletonSupport pad).filter fun i => σ i = none).card)
    (hfixedTrue : ∀ i ∈ paddedSingletonSupport pad,
      σ i ≠ none → σ i = some true) :
    σ ∈ paddedSingletonBad pad := by
  rw [paddedSingletonBad, mem_commonShallowBad]
  exact ⟨hstars,
    paddedSingletonSupport_not_commonShallow_of_live_true
      pad σ hstars hlive hfixedTrue⟩

/-- Exact semantic classification of the padded singleton bad event.  A shell point is bad iff
more than ten packed coordinates remain live and all fixed packed coordinates have one common
polarity.  The all-live profile satisfies both monochromatic alternatives vacuously. -/
theorem mem_paddedSingletonBad_iff (pad : ℕ) (σ : Restriction (pad + 20)) :
    σ ∈ paddedSingletonBad pad ↔
      stars σ = 20 ∧
      10 < ((paddedSingletonSupport pad).filter fun i => σ i = none).card ∧
      ((∀ i ∈ paddedSingletonSupport pad, σ i ≠ none → σ i = some false) ∨
       (∀ i ∈ paddedSingletonSupport pad, σ i ≠ none → σ i = some true)) := by
  constructor
  · intro hbad
    rw [paddedSingletonBad, mem_commonShallowBad] at hbad
    refine ⟨hbad.1, ?_, ?_⟩
    · by_contra hnot
      have hlive : ((paddedSingletonSupport pad).filter fun i => σ i = none).card ≤ 10 :=
        Nat.le_of_not_gt hnot
      exact hbad.2 (paddedSingletonSupport_commonShallow_of_live_le pad σ hbad.1 hlive)
    · by_cases hfalse :
        ∀ i ∈ paddedSingletonSupport pad, σ i ≠ none → σ i = some false
      · exact Or.inl hfalse
      · by_cases htrue :
          ∀ i ∈ paddedSingletonSupport pad, σ i ≠ none → σ i = some true
        · exact Or.inr htrue
        · exfalso
          push_neg at hfalse htrue
          obtain ⟨itrue, hitrue, hitrueFixed, hitrueNotFalse⟩ := hfalse
          obtain ⟨ifalse, hifalse, hifalseFixed, hifalseNotTrue⟩ := htrue
          have hσtrue : σ itrue = some true := by
            cases h : σ itrue with
            | none => exact False.elim (hitrueFixed h)
            | some b =>
                cases b
                · exact False.elim (hitrueNotFalse h)
                · rfl
          have hσfalse : σ ifalse = some false := by
            cases h : σ ifalse with
            | none => exact False.elim (hifalseFixed h)
            | some b =>
                cases b
                · rfl
                · exact False.elim (hifalseNotTrue h)
          exact hbad.2 (paddedSingletonSupport_commonShallow_of_mixed_fixed pad σ
            ⟨itrue, hitrue, hσtrue⟩ ⟨ifalse, hifalse, hσfalse⟩)
  · rintro ⟨hstars, hlive, hmono⟩
    rcases hmono with hfalse | htrue
    · exact paddedSingletonSupport_mem_bad_of_live_false pad σ hstars hlive hfalse
    · exact paddedSingletonSupport_mem_bad_of_live_true pad σ hstars hlive htrue

/-- The twenty coordinates used by the concrete scheduled obstruction. -/
private def scheduledSingletonSupport : Finset (Fin 164000) :=
  paddedSingletonSupport 163980

private theorem scheduledSingletonSupport_card : scheduledSingletonSupport.card = 20 := by
  simp [scheduledSingletonSupport]

/-- The positive-polarity indexed gate of the scheduled round output is exactly the packed list
of its twenty surviving positive singleton clauses. -/
private theorem scheduled_positive_family_gate :
    layeredBottomFamily (paddedRectangularSingletonRoundOutput 163980 1 20)
        ⟨0, by simp [layeredBottomFamilyList,
          bottomGates_paddedRectangularSingletonRoundOutput]⟩ =
      paddedRectangularSingletonGates 163980 1 20 0 := by
  simp [layeredBottomFamily, layeredBottomFamilyList,
    bottomGates_paddedRectangularSingletonRoundOutput]

/-- A short name for the concrete scheduled bad event, avoiding repeated elaboration of its
large ambient dimension in the support-fiber corollaries. -/
noncomputable def scheduledSingletonBad : Finset (Restriction 164000) :=
  commonShallowBad
    (normalizedLayeredBottomFamily
      (paddedRectangularSingletonRoundOutput 163980 1 20)) 20 20 10 0

/-- The packed singleton obstruction persists when the live support moves: it is enough that more
than ten of the twenty singleton coordinates remain live, while every other singleton coordinate
is fixed false.  Coordinates outside the packed gate are completely unrestricted. -/
theorem scheduledSingletonSupport_not_commonShallow_of_live_false
    (σ : Restriction 164000) (hstars : stars σ = 20)
    (hlive : 10 < (scheduledSingletonSupport.filter fun i => σ i = none).card)
    (hfixedFalse : ∀ i ∈ scheduledSingletonSupport, σ i ≠ none → σ i = some false) :
    ¬CommonShallowAt
      (normalizedLayeredBottomFamily
        (paddedRectangularSingletonRoundOutput 163980 1 20)) 20 σ 10 0 := by
    intro hnormalized
    have hraw : CommonShallowAt
        (layeredBottomFamily
          (paddedRectangularSingletonRoundOutput 163980 1 20))
        20 σ 10 0 :=
      (commonShallowAt_normalizedLayeredBottomFamily_iff
        (paddedRectangularSingletonRoundOutput 163980 1 20) 20
        σ 10 0).mp hnormalized
    obtain ⟨trunk, hdepth, hleaf⟩ := hraw
    let x : Fin 164000 → Bool := fun v ↦
      (σ v).getD false
    let path : Finset (Fin 164000) := (CommonTree.queryVars trunk x).toFinset
    have hpathCard : path.card ≤ 10 := by
      calc
        path.card ≤ (CommonTree.queryVars trunk x).length := List.toFinset_card_le _
        _ ≤ CommonTree.depth trunk := CommonTree.queryVars_length_le_depth trunk x
        _ ≤ 10 := hdepth
    have hnotSubset : ¬ (scheduledSingletonSupport.filter fun i => σ i = none) ⊆ path := by
      intro hsubset
      have := Finset.card_le_card hsubset
      omega
    obtain ⟨i, hiSupport, hiPath⟩ := Finset.not_subset.mp hnotSubset
    rw [Finset.mem_filter] at hiSupport
    have hiNone := hiSupport.2
    have hiPacked := hiSupport.1
    rw [scheduledSingletonSupport, paddedSingletonSupport, Finset.mem_image] at hiPacked
    obtain ⟨j, _, rfl⟩ := hiPacked
    let i : Fin 164000 := Fin.natAdd 163980 (finProdFinEquiv ((0 : Fin 1), j))
    let y : Fin 164000 → Bool := Function.update x i true
    have hsigmaTargetNone : σ i = none := by simpa [i] using hiNone
    have hx : Rung4Restriction.Extends
        σ x := by
      intro v b hv
      simp [x, hv]
    have hy : Rung4Restriction.Extends
        σ y := by
      intro v b hv
      have hvi : v ≠ i := by
        intro h
        subst v
        rw [hsigmaTargetNone] at hv
        simp at hv
      simpa [y, Function.update_of_ne hvi] using hx v b hv
    obtain ⟨hroot, hrunExtX, hshallow⟩ := hleaf x hx
    obtain ⟨_, hrunExtY, _⟩ := hleaf y hy
    have hrun : CommonTree.run trunk y = CommonTree.run trunk x := by
      have hxi : x i = false := by
        simp [x, hsigmaTargetNone]
      simpa [y, hxi] using
        CommonTree.run_update_of_not_mem_queryVars trunk x i
          (by simpa [path, i] using hiPath)
    let rho := CommonTree.run trunk x
    have hrunExtY' : Rung4Restriction.Extends rho y := by simpa [rho, hrun] using hrunExtY
    have hrhoStars : stars rho ≤ 20 := by
      calc
        stars rho ≤ stars σ := stars_le_of_restrictionExtends hroot
        _ = 20 := hstars
    have hgateDepth :
        (canonicalDT (paddedRectangularSingletonGates 163980 1 20 0) 20 rho).depth = 0 := by
      have hg := hshallow ⟨0, by simp [layeredBottomFamilyList,
        bottomGates_paddedRectangularSingletonRoundOutput]⟩
      exact Nat.eq_zero_of_le_zero (by
        simpa only [scheduled_positive_family_gate] using hg)
    have hevalEq := BoolDecisionTree.eval_eq_of_depth_eq_zero
      (canonicalDT (paddedRectangularSingletonGates 163980 1 20 0) 20 rho)
      hgateDepth x y
    rw [canonicalDT_eval 20 rho x hrhoStars hrunExtX,
      canonicalDT_eval 20 rho y hrhoStars hrunExtY'] at hevalEq
    have hxcoord (k : Fin 20) :
        x (Fin.natAdd 163980 (finProdFinEquiv ((0 : Fin 1), k))) = false := by
      let v := Fin.natAdd 163980 (finProdFinEquiv ((0 : Fin 1), k))
      have hvPacked : v ∈ scheduledSingletonSupport := by
        rw [scheduledSingletonSupport, paddedSingletonSupport, Finset.mem_image]
        exact ⟨k, Finset.mem_univ k, rfl⟩
      by_cases hv : σ v = none
      · simp [x, v, hv]
      · have hvFalse := hfixedFalse v hvPacked hv
        simp [x, v, hvFalse]
    have hdnfX : dnfEval
        (paddedRectangularSingletonGates 163980 1 20 0) x = false := by
      rw [dnfEval, List.any_eq_false]
      intro T hT
      rw [paddedRectangularSingletonGates] at hT
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hT
      simp [paddedRectangularSingletonMeaning, Rung4DNFTerm.evalLits,
        Rung4Literal.eval, hxcoord k]
    have hdnfY : dnfEval
        (paddedRectangularSingletonGates 163980 1 20 0) y = true := by
      rw [dnfEval, List.any_eq_true]
      refine ⟨paddedRectangularSingletonMeaning 163980 ((0 : Fin 1), j), ?_, ?_⟩
      · rw [paddedRectangularSingletonGates]
        exact List.mem_ofFn.mpr ⟨j, rfl⟩
      · simp [paddedRectangularSingletonMeaning, Rung4DNFTerm.evalLits,
          Rung4Literal.eval, y, i]
    exact Bool.false_ne_true (hdnfX.symm.trans (hevalEq.trans hdnfY))

/-- Polarity-sensitive support-overlap criterion for membership in the exact scheduled bad set. -/
theorem scheduledSingletonSupport_mem_bad_of_live_false
    (σ : Restriction 164000) (hstars : stars σ = 20)
    (hlive : 10 < (scheduledSingletonSupport.filter fun i => σ i = none).card)
    (hfixedFalse : ∀ i ∈ scheduledSingletonSupport, σ i ≠ none → σ i = some false) :
    σ ∈ scheduledSingletonBad := by
  rw [scheduledSingletonBad, mem_commonShallowBad]
  exact ⟨hstars,
    scheduledSingletonSupport_not_commonShallow_of_live_false
      σ hstars hlive hfixedFalse⟩

/-! ### The certified polarity-sensitive overlap tail -/

/-- The exact shell subfamily certified bad by the moving-support argument.  This definition keeps
the necessary false-polarity condition visible instead of replacing it by a raw support-overlap
event, which would be unsound for the positive singleton DNF. -/
noncomputable def scheduledSingletonCertifiedTail : Finset (Restriction 164000) :=
  Finset.univ.filter fun σ =>
    stars σ = 20 ∧
      10 < (scheduledSingletonSupport.filter fun i => σ i = none).card ∧
      ∀ i ∈ scheduledSingletonSupport, σ i ≠ none → σ i = some false

theorem mem_scheduledSingletonCertifiedTail_iff (σ : Restriction 164000) :
    σ ∈ scheduledSingletonCertifiedTail ↔
      stars σ = 20 ∧
        10 < (scheduledSingletonSupport.filter fun i => σ i = none).card ∧
        ∀ i ∈ scheduledSingletonSupport, σ i ≠ none → σ i = some false := by
  simp [scheduledSingletonCertifiedTail]

/-- One exact overlap class of the certified tail.  Its eventual cardinality is the single
stars-and-bars summand indexed by `q`. -/
noncomputable def scheduledSingletonCertifiedOverlap (q : ℕ) :
    Finset (Restriction 164000) :=
  Finset.univ.filter fun σ =>
    stars σ = 20 ∧
      (scheduledSingletonSupport.filter fun i => σ i = none).card = q ∧
      ∀ i ∈ scheduledSingletonSupport, σ i ≠ none → σ i = some false

theorem mem_scheduledSingletonCertifiedOverlap_iff (q : ℕ)
    (σ : Restriction 164000) :
    σ ∈ scheduledSingletonCertifiedOverlap q ↔
      stars σ = 20 ∧
        (scheduledSingletonSupport.filter fun i => σ i = none).card = q ∧
        ∀ i ∈ scheduledSingletonSupport, σ i ≠ none → σ i = some false := by
  simp [scheduledSingletonCertifiedOverlap]

set_option maxRecDepth 8192
set_option maxHeartbeats 400000
set_option linter.constructorNameAsVariable false
/-- The certified event is exactly the disjoint range of overlap classes `q = 11, ..., 20`.
This is the structural half of the requested hypergeometric count; each class now has a fixed
overlap parameter and can be counted independently. -/
theorem scheduledSingletonCertifiedTail_eq_biUnion_overlap :
    scheduledSingletonCertifiedTail =
      (Finset.Icc 11 20).biUnion scheduledSingletonCertifiedOverlap := by
  ext σ
  rw [mem_scheduledSingletonCertifiedTail_iff]
  simp only [Finset.mem_biUnion, Finset.mem_Icc]
  constructor
  · rintro ⟨hstars, hlive, hfalse⟩
    let q := (scheduledSingletonSupport.filter fun i => σ i = none).card
    have hqle : q ≤ 20 := by
      calc
        q ≤ scheduledSingletonSupport.card := Finset.card_filter_le _ _
        _ = 20 := scheduledSingletonSupport_card
    refine ⟨q, ⟨by omega, hqle⟩, ?_⟩
    rw [mem_scheduledSingletonCertifiedOverlap_iff]
    exact ⟨hstars, rfl, hfalse⟩
  · rintro ⟨q, hq, hσ⟩
    rw [mem_scheduledSingletonCertifiedOverlap_iff] at hσ
    exact ⟨hσ.1, by omega, hσ.2.2⟩

set_option maxRecDepth 1000
set_option maxHeartbeats 200000
set_option linter.constructorNameAsVariable true

/-! ### Exact cardinality of one certified overlap class -/

/-- Free-coordinate sets with `q` live packed coordinates and `20-q` live padding coordinates.
The occupancy fiber also records that the total live count is exactly twenty. -/
def scheduledSingletonOverlapFreeSets (q : ℕ) : Finset (Finset (Fin 164000)) :=
  occupancySizeFiber (fun _ : Fin 1 => scheduledSingletonSupport)
    (fun _ => q) (20 - q)

theorem mem_scheduledSingletonOverlapFreeSets_iff (q : ℕ)
    (S : Finset (Fin 164000)) :
    S ∈ scheduledSingletonOverlapFreeSets q ↔
      (S ∩ scheduledSingletonSupport).card = q ∧
        (S \ scheduledSingletonSupport).card = 20 - q := by
  rw [scheduledSingletonOverlapFreeSets, mem_occupancySizeFiber]
  simp [supportUnion]

/-- The free-set part of one overlap class is the expected hypergeometric product. -/
theorem scheduledSingletonOverlapFreeSets_card (q : ℕ) :
    (scheduledSingletonOverlapFreeSets q).card =
      Nat.choose 20 q * Nat.choose 163980 (20 - q) := by
  rw [scheduledSingletonOverlapFreeSets,
    occupancySizeFiber_card_uniform
      (fun _ : Fin 1 => scheduledSingletonSupport)
      (fun g h hne => False.elim (hne (Subsingleton.elim g h)))
      (fun _ => scheduledSingletonSupport_card)]
  norm_num

/-- Root restriction that fixes precisely the nonlive packed coordinates false. -/
def scheduledSingletonFalseRoot (S : Finset (Fin 164000)) : Restriction 164000 :=
  fun i => if i ∈ scheduledSingletonSupport \ S then some false else none

theorem freeVars_scheduledSingletonFalseRoot (S : Finset (Fin 164000)) :
    freeVars (scheduledSingletonFalseRoot S) =
      Finset.univ \ (scheduledSingletonSupport \ S) := by
  ext i
  simp [scheduledSingletonFalseRoot, mem_freeVars]

theorem scheduledSingletonFalseRoot_fiber_eq (S : Finset (Fin 164000)) :
    restrictionExtensionFreeSetFiber (scheduledSingletonFalseRoot S) S =
      Finset.univ.filter fun σ : Restriction 164000 =>
        freeVars σ = S ∧
          ∀ i ∈ scheduledSingletonSupport, σ i ≠ none → σ i = some false := by
  ext σ
  simp only [restrictionExtensionFreeSetFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hext, hfree⟩
    refine ⟨hfree, ?_⟩
    intro i hi hne
    have hiS : i ∉ S := by
      intro hiS
      apply hne
      rw [← mem_freeVars, hfree]
      exact hiS
    exact hext i false (by simp [scheduledSingletonFalseRoot, hi, hiS])
  · rintro ⟨hfree, hfalse⟩
    refine ⟨?_, hfree⟩
    intro i b hib
    have hi : i ∈ scheduledSingletonSupport \ S := by
      by_contra hnot
      simp only [scheduledSingletonFalseRoot, hnot, if_false] at hib
      exact Option.some_ne_none b hib.symm
    obtain ⟨hiSupport, hiNotS⟩ := Finset.mem_sdiff.mp hi
    have hne : σ i ≠ none := by
      intro hnone
      have hiS : i ∈ S := by rw [← hfree, mem_freeVars]; exact hnone
      exact hiNotS hiS
    have hb : b = false := by
      simpa [scheduledSingletonFalseRoot, hi] using hib
    simpa [hb] using hfalse i hiSupport hne

/-- For an admissible overlap free set, every remaining fixed padding coordinate is arbitrary,
while the `20-q` fixed packed coordinates are forced false. -/
theorem scheduledSingletonFalseRoot_fiber_card {q : ℕ}
    (hq : q ≤ 20) (S : Finset (Fin 164000))
    (hS : S ∈ scheduledSingletonOverlapFreeSets q) :
    (restrictionExtensionFreeSetFiber (scheduledSingletonFalseRoot S) S).card =
      2 ^ (163960 + q) := by
  rw [card_restrictionExtends_freeVars_eq]
  · rw [freeVars_scheduledSingletonFalseRoot]
    have hoverlap := (mem_scheduledSingletonOverlapFreeSets_iff q S).mp hS
    have hScard : S.card = 20 := by
      calc
        S.card = (S ∩ scheduledSingletonSupport).card +
            (S \ scheduledSingletonSupport).card := by
              simpa [Nat.add_comm] using
                Finset.card_sdiff_add_card_inter S scheduledSingletonSupport
        _ = q + (20 - q) := by rw [hoverlap.1, hoverlap.2]
        _ = 20 := Nat.add_sub_of_le hq
    have hdiffCard : (scheduledSingletonSupport \ S).card = 20 - q := by
      rw [Finset.card_sdiff, scheduledSingletonSupport_card]
      have hinter : (scheduledSingletonSupport ∩ S).card = q := by
        rw [Finset.inter_comm]
        exact hoverlap.1
      omega
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, hdiffCard, hScard]
    have hexp : 164000 - (20 - q) - 20 = 163960 + q := by omega
    rw [hexp]
  · intro i hi
    rw [freeVars_scheduledSingletonFalseRoot]
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro his
    exact his.2 hi

set_option maxRecDepth 16384
set_option maxHeartbeats 400000
set_option linter.constructorNameAsVariable false
theorem mem_scheduledSingletonCertifiedOverlap_iff_freeSet {q : ℕ}
    (hq : q ≤ 20) (σ : Restriction 164000) :
    σ ∈ scheduledSingletonCertifiedOverlap q ↔
      freeVars σ ∈ scheduledSingletonOverlapFreeSets q ∧
        ∀ i ∈ scheduledSingletonSupport, σ i ≠ none → σ i = some false := by
  rw [mem_scheduledSingletonCertifiedOverlap_iff,
    mem_scheduledSingletonOverlapFreeSets_iff]
  have hinter : (freeVars σ ∩ scheduledSingletonSupport).card =
      (scheduledSingletonSupport.filter fun i => σ i = none).card := by
    apply congrArg Finset.card
    ext i
    simp [mem_freeVars, and_comm]
  rw [hinter]
  constructor
  · rintro ⟨hstars, hoverlap, hfalse⟩
    refine ⟨⟨hoverlap, ?_⟩, hfalse⟩
    have hpartition :=
      Finset.card_sdiff_add_card_inter (freeVars σ) scheduledSingletonSupport
    rw [stars] at hstars
    omega
  · rintro ⟨⟨hoverlap, houtside⟩, hfalse⟩
    refine ⟨?_, hoverlap, hfalse⟩
    rw [stars]
    have hpartition :=
      Finset.card_sdiff_add_card_inter (freeVars σ) scheduledSingletonSupport
    omega

theorem freeVars_mem_scheduledSingletonOverlapFreeSets {q : ℕ} (hq : q ≤ 20)
    {σ : Restriction 164000} (hσ : σ ∈ scheduledSingletonCertifiedOverlap q) :
    freeVars σ ∈ scheduledSingletonOverlapFreeSets q := by
  rw [mem_scheduledSingletonOverlapFreeSets_iff]
  rw [mem_scheduledSingletonCertifiedOverlap_iff] at hσ
  have hinter : (freeVars σ ∩ scheduledSingletonSupport).card = q := by
    calc
      (freeVars σ ∩ scheduledSingletonSupport).card =
          (scheduledSingletonSupport.filter fun i => σ i = none).card := by
            apply congrArg Finset.card
            ext i
            simp [mem_freeVars, and_comm]
      _ = q := hσ.2.1
  refine ⟨hinter, ?_⟩
  have hpartition :=
    Finset.card_sdiff_add_card_inter (freeVars σ) scheduledSingletonSupport
  rw [stars] at hσ
  omega

/-- Exact cardinality of every certified overlap class in the relevant range.  The first two
factors choose the live packed and padding coordinates; the power of two assigns all fixed
padding coordinates, while the fixed packed coordinates are forced false. -/
theorem scheduledSingletonCertifiedOverlap_card {q : ℕ} (hq : q ≤ 20) :
    (scheduledSingletonCertifiedOverlap q).card =
      Nat.choose 20 q * Nat.choose 163980 (20 - q) * 2 ^ (163960 + q) := by
  classical
  have hmaps : Set.MapsTo (fun σ : Restriction 164000 => freeVars σ)
      (scheduledSingletonCertifiedOverlap q : Set (Restriction 164000))
      (scheduledSingletonOverlapFreeSets q : Set (Finset (Fin 164000))) := by
    intro σ hσ
    rw [Finset.mem_coe] at hσ ⊢
    rw [mem_scheduledSingletonOverlapFreeSets_iff]
    rw [mem_scheduledSingletonCertifiedOverlap_iff] at hσ
    have hinter : (freeVars σ ∩ scheduledSingletonSupport).card = q := by
      calc
        (freeVars σ ∩ scheduledSingletonSupport).card =
            (scheduledSingletonSupport.filter fun i => σ i = none).card := by
              apply congrArg Finset.card
              ext i
              simp [mem_freeVars, and_comm]
        _ = q := hσ.2.1
    refine ⟨hinter, ?_⟩
    have hpartition :=
      Finset.card_sdiff_add_card_inter (freeVars σ) scheduledSingletonSupport
    rw [stars] at hσ
    have houtsideAdd : (freeVars σ \ scheduledSingletonSupport).card + q = 20 := by
      omega
    exact Nat.eq_sub_of_add_eq houtsideAdd
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hterm : ∀ S ∈ scheduledSingletonOverlapFreeSets q,
        ((scheduledSingletonCertifiedOverlap q).filter
          (fun σ => freeVars σ = S)).card = 2 ^ (163960 + q) := by
      intro S hS
      rw [← scheduledSingletonFalseRoot_fiber_card hq S hS]
      rw [scheduledSingletonFalseRoot_fiber_eq]
      apply congrArg Finset.card
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [mem_scheduledSingletonCertifiedOverlap_iff_freeSet hq]
      constructor
      · rintro ⟨⟨_, hfalse⟩, hfree⟩
        exact ⟨hfree, hfalse⟩
      · rintro ⟨hfree, hfalse⟩
        have hSmem : freeVars σ ∈ scheduledSingletonOverlapFreeSets q := by
          rw [hfree]
          exact hS
        exact ⟨⟨hSmem, hfalse⟩, hfree⟩
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul,
    scheduledSingletonOverlapFreeSets_card]

theorem scheduledSingletonCertifiedTail_card :
    scheduledSingletonCertifiedTail.card =
      ∑ q ∈ Finset.Icc 11 20,
        Nat.choose 20 q * Nat.choose 163980 (20 - q) * 2 ^ (163960 + q) := by
  have hpair : ((Finset.Icc 11 20 : Finset ℕ) : Set ℕ).PairwiseDisjoint
      scheduledSingletonCertifiedOverlap := by
    intro q hq r hr hne
    change Disjoint (scheduledSingletonCertifiedOverlap q)
      (scheduledSingletonCertifiedOverlap r)
    rw [Finset.disjoint_left]
    intro σ hσq hσr
    rw [mem_scheduledSingletonCertifiedOverlap_iff] at hσq hσr
    exact hne (hσq.2.1.symm.trans hσr.2.1)
  have hsum :
      (∑ q ∈ Finset.Icc 11 20, (scheduledSingletonCertifiedOverlap q).card) =
        ∑ q ∈ Finset.Icc 11 20,
          Nat.choose 20 q * Nat.choose 163980 (20 - q) * 2 ^ (163960 + q) := by
    apply Finset.sum_congr rfl
    intro q hq
    exact scheduledSingletonCertifiedOverlap_card (Finset.mem_Icc.mp hq).2
  rw [scheduledSingletonCertifiedTail_eq_biUnion_overlap,
    Finset.card_biUnion hpair, hsum]

theorem scheduledSingletonCertifiedTail_coefficient_lt :
    (∑ q ∈ Finset.Icc 11 20,
      Nat.choose 20 q * Nat.choose 163980 (20 - q) * 2 ^ (q - 10)) <
        Nat.choose 164000 20 := by
  let B := ∑ q ∈ Finset.Icc 11 20,
    Nat.choose 20 q * 163980 ^ (20 - q) * 2 ^ (q - 10)
  have hupper :
      (∑ q ∈ Finset.Icc 11 20,
        Nat.choose 20 q * Nat.choose 163980 (20 - q) * 2 ^ (q - 10)) ≤ B := by
    apply Finset.sum_le_sum
    intro q hq
    exact Nat.mul_le_mul_right (2 ^ (q - 10)) <|
      Nat.mul_le_mul_left (Nat.choose 20 q) (Nat.choose_le_pow 163980 (20 - q))
  have hnumeric : B * Nat.factorial 20 < Nat.descFactorial 164000 20 := by
    norm_num [B, Finset.sum_Icc_succ_top, Nat.descFactorial, Nat.choose]
  have hscaled :
      (∑ q ∈ Finset.Icc 11 20,
        Nat.choose 20 q * Nat.choose 163980 (20 - q) * 2 ^ (q - 10)) *
          Nat.factorial 20 < Nat.choose 164000 20 * Nat.factorial 20 := by
    rw [Nat.mul_comm (Nat.choose 164000 20),
      ← Nat.descFactorial_eq_factorial_mul_choose]
    exact lt_of_le_of_lt (Nat.mul_le_mul_right (Nat.factorial 20) hupper) hnumeric
  exact (Nat.mul_lt_mul_right (Nat.factorial_pos 20)).mp hscaled

/-- A symbolic common-power factor can be restored after a strict comparison of the
coefficients.  Keeping `k` abstract prevents the kernel from reducing the common power. -/
theorem finset_sum_mul_two_pow_add_lt_mul_two_pow {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a e : ι → ℕ) {B k : ℕ}
    (h : (∑ i ∈ s, a i * 2 ^ e i) < B) :
    (∑ i ∈ s, a i * 2 ^ (k + e i)) < B * 2 ^ k := by
  have hscaled :=
    (Nat.mul_lt_mul_right (pow_pos (by omega : 0 < 2) k)).mpr h
  rw [Finset.sum_mul] at hscaled
  simpa only [pow_add, mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- The exact certified tail is smaller than the full shell after removing the requested
`2^10` saving.  This is the large-power presentation of the normalized coefficient audit. -/
theorem scheduledSingletonCertifiedTail_lt_shell_div_two_pow_ten :
    scheduledSingletonCertifiedTail.card < Nat.choose 164000 20 * 2 ^ 163970 := by
  rw [scheduledSingletonCertifiedTail_card]
  have exponent_eq : ∀ q ∈ Finset.Icc 11 20,
      163960 + q = 163970 + (q - 10) := by
    intro q hq
    have hq10 : 10 ≤ q := by
      exact le_trans (by omega) (Finset.mem_Icc.mp hq).1
    omega
  have hscaled := finset_sum_mul_two_pow_add_lt_mul_two_pow
    (Finset.Icc 11 20)
    (fun q => Nat.choose 20 q * Nat.choose 163980 (20 - q))
    (fun q => q - 10) (k := 163970)
    scheduledSingletonCertifiedTail_coefficient_lt
  refine lt_of_eq_of_lt ?_ hscaled
  apply Finset.sum_congr rfl
  intro q hq
  rw [exponent_eq q hq]

/-- Multiplying by a further power of two composes with a symbolic common-power bound. -/
theorem mul_two_pow_lt_mul_two_pow_add {A B k r : ℕ}
    (h : A < B * 2 ^ k) : A * 2 ^ r < B * 2 ^ (k + r) := by
  have hscaled :=
    (Nat.mul_lt_mul_right (pow_pos (by omega : 0 < 2) r)).mpr h
  simpa only [pow_add, mul_assoc] using hscaled

/-- Equivalently, multiplying the certified bad tail by the verified contraction factor
`2^10` still leaves it strictly below the complete twenty-star shell. -/
theorem scheduledSingletonCertifiedTail_mul_two_pow_ten_lt_shell :
    scheduledSingletonCertifiedTail.card * 2 ^ 10 <
      Nat.choose 164000 20 * 2 ^ 163980 := by
  have h := mul_two_pow_lt_mul_two_pow_add (k := 163970) (r := 10)
    scheduledSingletonCertifiedTail_lt_shell_div_two_pow_ten
  have hexp : 163970 + 10 = 163980 := by norm_num
  rw [hexp] at h
  exact h

/-! ### Padding-parametric overlap mass

The preceding certified-tail construction was originally specialized to padding `163980`.
The combinatorial quantity it computes is useful independently of that historical schedule, so
we expose the padding parameter here.  `paddedSingletonCertifiedMass pad` is the exact sum obtained
by choosing `q > 10` live coordinates from the twenty packed singleton coordinates, choosing the
remaining `20-q` live coordinates from the padding, forcing the other packed coordinates false,
and assigning every other fixed padding coordinate arbitrarily.
-/

/-- The polarity-sensitive packed-singleton overlap coefficient after factoring out the common
power `2^(pad-10)`. -/
def paddedSingletonCertifiedCoefficient (pad : ℕ) : ℕ :=
  ∑ q ∈ Finset.Icc 11 20,
    Nat.choose 20 q * Nat.choose pad (20 - q) * 2 ^ (q - 10)

/-- The full cardinality predicted by the padding-parametric overlap decomposition.  The
assumption `20 ≤ pad` used below ensures that `pad - 20 + q` is the number of freely assignable
fixed coordinates in overlap class `q`. -/
def paddedSingletonCertifiedMass (pad : ℕ) : ℕ :=
  ∑ q ∈ Finset.Icc 11 20,
    Nat.choose 20 q * Nat.choose pad (20 - q) * 2 ^ (pad - 20 + q)

/-! ### Concrete padding-parametric monochromatic tails

The numerical mass above is now realized by an actual finset.  Keeping the false and true
polarities separate makes their unique overlap -- the all-packed-live fiber -- explicit.
-/

/-- Shell points with more than ten live packed coordinates and every fixed packed coordinate
false. -/
noncomputable def paddedSingletonFalseTail (pad : ℕ) :
    Finset (Restriction (pad + 20)) :=
  Finset.univ.filter fun σ =>
    stars σ = 20 ∧
      10 < ((paddedSingletonSupport pad).filter fun i => σ i = none).card ∧
      ∀ i ∈ paddedSingletonSupport pad, σ i ≠ none → σ i = some false

/-- The symmetric all-true monochromatic tail. -/
noncomputable def paddedSingletonTrueTail (pad : ℕ) :
    Finset (Restriction (pad + 20)) :=
  Finset.univ.filter fun σ =>
    stars σ = 20 ∧
      10 < ((paddedSingletonSupport pad).filter fun i => σ i = none).card ∧
      ∀ i ∈ paddedSingletonSupport pad, σ i ≠ none → σ i = some true

theorem mem_paddedSingletonFalseTail_iff (pad : ℕ) (σ : Restriction (pad + 20)) :
    σ ∈ paddedSingletonFalseTail pad ↔
      stars σ = 20 ∧
      10 < ((paddedSingletonSupport pad).filter fun i => σ i = none).card ∧
      ∀ i ∈ paddedSingletonSupport pad, σ i ≠ none → σ i = some false := by
  simp [paddedSingletonFalseTail]

theorem mem_paddedSingletonTrueTail_iff (pad : ℕ) (σ : Restriction (pad + 20)) :
    σ ∈ paddedSingletonTrueTail pad ↔
      stars σ = 20 ∧
      10 < ((paddedSingletonSupport pad).filter fun i => σ i = none).card ∧
      ∀ i ∈ paddedSingletonSupport pad, σ i ≠ none → σ i = some true := by
  simp [paddedSingletonTrueTail]

/-- One fixed-overlap class in the false monochromatic tail. -/
noncomputable def paddedSingletonFalseOverlap (pad q : ℕ) :
    Finset (Restriction (pad + 20)) :=
  Finset.univ.filter fun σ =>
    stars σ = 20 ∧
      ((paddedSingletonSupport pad).filter fun i => σ i = none).card = q ∧
      ∀ i ∈ paddedSingletonSupport pad, σ i ≠ none → σ i = some false

theorem mem_paddedSingletonFalseOverlap_iff (pad q : ℕ)
    (σ : Restriction (pad + 20)) :
    σ ∈ paddedSingletonFalseOverlap pad q ↔
      stars σ = 20 ∧
      ((paddedSingletonSupport pad).filter fun i => σ i = none).card = q ∧
      ∀ i ∈ paddedSingletonSupport pad, σ i ≠ none → σ i = some false := by
  simp [paddedSingletonFalseOverlap]

theorem paddedSingletonFalseTail_eq_biUnion_overlap (pad : ℕ) :
    paddedSingletonFalseTail pad =
      (Finset.Icc 11 20).biUnion (paddedSingletonFalseOverlap pad) := by
  ext σ
  rw [mem_paddedSingletonFalseTail_iff]
  simp only [Finset.mem_biUnion, Finset.mem_Icc]
  constructor
  · rintro ⟨hstars, hlive, hfalse⟩
    let q := ((paddedSingletonSupport pad).filter fun i => σ i = none).card
    have hqle : q ≤ 20 := by
      calc
        q ≤ (paddedSingletonSupport pad).card := Finset.card_filter_le _ _
        _ = 20 := paddedSingletonSupport_card pad
    refine ⟨q, ⟨by omega, hqle⟩, ?_⟩
    rw [mem_paddedSingletonFalseOverlap_iff]
    exact ⟨hstars, rfl, hfalse⟩
  · rintro ⟨q, hq, hσ⟩
    rw [mem_paddedSingletonFalseOverlap_iff] at hσ
    exact ⟨hσ.1, by omega, hσ.2.2⟩

/-- Free-coordinate sets with `q` live packed and `20-q` live padding coordinates. -/
def paddedSingletonOverlapFreeSets (pad q : ℕ) :
    Finset (Finset (Fin (pad + 20))) :=
  occupancySizeFiber (fun _ : Fin 1 => paddedSingletonSupport pad)
    (fun _ => q) (20 - q)

theorem mem_paddedSingletonOverlapFreeSets_iff (pad q : ℕ)
    (S : Finset (Fin (pad + 20))) :
    S ∈ paddedSingletonOverlapFreeSets pad q ↔
      (S ∩ paddedSingletonSupport pad).card = q ∧
      (S \ paddedSingletonSupport pad).card = 20 - q := by
  rw [paddedSingletonOverlapFreeSets, mem_occupancySizeFiber]
  simp [supportUnion]

theorem paddedSingletonOverlapFreeSets_card (pad q : ℕ) :
    (paddedSingletonOverlapFreeSets pad q).card =
      Nat.choose 20 q * Nat.choose pad (20 - q) := by
  rw [paddedSingletonOverlapFreeSets,
    occupancySizeFiber_card_uniform
      (fun _ : Fin 1 => paddedSingletonSupport pad)
      (fun g h hne => False.elim (hne (Subsingleton.elim g h)))
      (fun _ => paddedSingletonSupport_card pad)]
  simp

/-- Root restriction forcing precisely the nonlive packed coordinates false. -/
def paddedSingletonFalseRoot (pad : ℕ) (S : Finset (Fin (pad + 20))) :
    Restriction (pad + 20) :=
  fun i => if i ∈ paddedSingletonSupport pad \ S then some false else none

theorem freeVars_paddedSingletonFalseRoot (pad : ℕ)
    (S : Finset (Fin (pad + 20))) :
    freeVars (paddedSingletonFalseRoot pad S) =
      Finset.univ \ (paddedSingletonSupport pad \ S) := by
  ext i
  simp [paddedSingletonFalseRoot, mem_freeVars]

theorem paddedSingletonFalseRoot_fiber_eq (pad : ℕ)
    (S : Finset (Fin (pad + 20))) :
    restrictionExtensionFreeSetFiber (paddedSingletonFalseRoot pad S) S =
      Finset.univ.filter fun σ : Restriction (pad + 20) =>
        freeVars σ = S ∧
          ∀ i ∈ paddedSingletonSupport pad, σ i ≠ none → σ i = some false := by
  ext σ
  simp only [restrictionExtensionFreeSetFiber, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hext, hfree⟩
    refine ⟨hfree, ?_⟩
    intro i hi hne
    have hiS : i ∉ S := by
      intro hiS
      apply hne
      rw [← mem_freeVars, hfree]
      exact hiS
    exact hext i false (by simp [paddedSingletonFalseRoot, hi, hiS])
  · rintro ⟨hfree, hfalse⟩
    refine ⟨?_, hfree⟩
    intro i b hib
    have hi : i ∈ paddedSingletonSupport pad \ S := by
      by_contra hnot
      simp only [paddedSingletonFalseRoot, hnot, if_false] at hib
      exact Option.some_ne_none b hib.symm
    obtain ⟨hiSupport, hiNotS⟩ := Finset.mem_sdiff.mp hi
    have hne : σ i ≠ none := by
      intro hnone
      have hiS : i ∈ S := by rw [← hfree, mem_freeVars]; exact hnone
      exact hiNotS hiS
    have hb : b = false := by
      simpa [paddedSingletonFalseRoot, hi] using hib
    simpa [hb] using hfalse i hiSupport hne

theorem paddedSingletonFalseRoot_fiber_card {pad q : ℕ} (hpad : 20 ≤ pad)
    (hq : q ≤ 20) (S : Finset (Fin (pad + 20)))
    (hS : S ∈ paddedSingletonOverlapFreeSets pad q) :
    (restrictionExtensionFreeSetFiber (paddedSingletonFalseRoot pad S) S).card =
      2 ^ (pad - 20 + q) := by
  rw [card_restrictionExtends_freeVars_eq]
  · rw [freeVars_paddedSingletonFalseRoot]
    have hoverlap := (mem_paddedSingletonOverlapFreeSets_iff pad q S).mp hS
    have hScard : S.card = 20 := by
      calc
        S.card = (S ∩ paddedSingletonSupport pad).card +
            (S \ paddedSingletonSupport pad).card := by
              simpa [Nat.add_comm] using
                Finset.card_sdiff_add_card_inter S (paddedSingletonSupport pad)
        _ = q + (20 - q) := by rw [hoverlap.1, hoverlap.2]
        _ = 20 := Nat.add_sub_of_le hq
    have hdiffCard : (paddedSingletonSupport pad \ S).card = 20 - q := by
      rw [Finset.card_sdiff, paddedSingletonSupport_card]
      have hinter : (paddedSingletonSupport pad ∩ S).card = q := by
        rw [Finset.inter_comm]
        exact hoverlap.1
      omega
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, hdiffCard, hScard]
    have hexp : pad + 20 - (20 - q) - 20 = pad - 20 + q := by omega
    rw [hexp]
  · intro i hi
    rw [freeVars_paddedSingletonFalseRoot]
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro his
    exact his.2 hi

set_option maxRecDepth 16384
set_option maxHeartbeats 400000
set_option linter.constructorNameAsVariable false
theorem mem_paddedSingletonFalseOverlap_iff_freeSet {pad q : ℕ} (hq : q ≤ 20)
    (σ : Restriction (pad + 20)) :
    σ ∈ paddedSingletonFalseOverlap pad q ↔
      freeVars σ ∈ paddedSingletonOverlapFreeSets pad q ∧
        ∀ i ∈ paddedSingletonSupport pad, σ i ≠ none → σ i = some false := by
  rw [mem_paddedSingletonFalseOverlap_iff,
    mem_paddedSingletonOverlapFreeSets_iff]
  have hinter : (freeVars σ ∩ paddedSingletonSupport pad).card =
      ((paddedSingletonSupport pad).filter fun i => σ i = none).card := by
    apply congrArg Finset.card
    ext i
    simp [mem_freeVars, and_comm]
  rw [hinter]
  constructor
  · rintro ⟨hstars, hoverlap, hfalse⟩
    refine ⟨⟨hoverlap, ?_⟩, hfalse⟩
    have hpartition :=
      Finset.card_sdiff_add_card_inter (freeVars σ) (paddedSingletonSupport pad)
    rw [stars] at hstars
    omega
  · rintro ⟨⟨hoverlap, houtside⟩, hfalse⟩
    refine ⟨?_, hoverlap, hfalse⟩
    rw [stars]
    have hpartition :=
      Finset.card_sdiff_add_card_inter (freeVars σ) (paddedSingletonSupport pad)
    omega

/-- Exact cardinality of one padding-parametric false overlap class. -/
theorem paddedSingletonFalseOverlap_card {pad q : ℕ} (hpad : 20 ≤ pad)
    (hq : q ≤ 20) :
    (paddedSingletonFalseOverlap pad q).card =
      Nat.choose 20 q * Nat.choose pad (20 - q) * 2 ^ (pad - 20 + q) := by
  classical
  have hmaps : Set.MapsTo (fun σ : Restriction (pad + 20) => freeVars σ)
      (paddedSingletonFalseOverlap pad q : Set (Restriction (pad + 20)))
      (paddedSingletonOverlapFreeSets pad q : Set (Finset (Fin (pad + 20)))) := by
    intro σ hσ
    rw [Finset.mem_coe] at hσ ⊢
    exact (mem_paddedSingletonFalseOverlap_iff_freeSet hq σ).mp hσ |>.1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hterm : ∀ S ∈ paddedSingletonOverlapFreeSets pad q,
      ((paddedSingletonFalseOverlap pad q).filter
        (fun σ => freeVars σ = S)).card = 2 ^ (pad - 20 + q) := by
    intro S hS
    rw [← paddedSingletonFalseRoot_fiber_card hpad hq S hS]
    rw [paddedSingletonFalseRoot_fiber_eq]
    apply congrArg Finset.card
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mem_paddedSingletonFalseOverlap_iff_freeSet hq]
    constructor
    · rintro ⟨⟨_, hfalse⟩, hfree⟩
      exact ⟨hfree, hfalse⟩
    · rintro ⟨hfree, hfalse⟩
      have hSmem : freeVars σ ∈ paddedSingletonOverlapFreeSets pad q := by
        rw [hfree]
        exact hS
      exact ⟨⟨hSmem, hfalse⟩, hfree⟩
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul,
    paddedSingletonOverlapFreeSets_card]

/-- The false monochromatic finset realizes the previously numerical certified mass. -/
theorem paddedSingletonFalseTail_card {pad : ℕ} (hpad : 20 ≤ pad) :
    (paddedSingletonFalseTail pad).card = paddedSingletonCertifiedMass pad := by
  have hpair : ((Finset.Icc 11 20 : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (paddedSingletonFalseOverlap pad) := by
    intro q hq r hr hne
    change Disjoint (paddedSingletonFalseOverlap pad q)
      (paddedSingletonFalseOverlap pad r)
    rw [Finset.disjoint_left]
    intro σ hσq hσr
    rw [mem_paddedSingletonFalseOverlap_iff] at hσq hσr
    exact hne (hσq.2.1.symm.trans hσr.2.1)
  rw [paddedSingletonFalseTail_eq_biUnion_overlap,
    Finset.card_biUnion hpair, paddedSingletonCertifiedMass]
  apply Finset.sum_congr rfl
  intro q hq
  exact paddedSingletonFalseOverlap_card hpad (Finset.mem_Icc.mp hq).2

/-- Complement every fixed Boolean while preserving live coordinates. -/
def complementRestriction {n : ℕ} (σ : Restriction n) : Restriction n :=
  fun i => (σ i).map (!·)

@[simp] theorem complementRestriction_none_iff {n : ℕ} (σ : Restriction n) (i : Fin n) :
    complementRestriction σ i = none ↔ σ i = none := by
  cases h : σ i <;> simp [complementRestriction, h]

@[simp] theorem complementRestriction_involutive {n : ℕ} (σ : Restriction n) :
    complementRestriction (complementRestriction σ) = σ := by
  funext i
  cases h : σ i with
  | none => simp [complementRestriction, h]
  | some b => cases b <;> simp [complementRestriction, h]

theorem stars_complementRestriction {n : ℕ} (σ : Restriction n) :
    stars (complementRestriction σ) = stars σ := by
  rw [stars, stars]
  apply congrArg Finset.card
  ext i
  simp [mem_freeVars]

@[simp] theorem freeVars_complementRestriction {n : ℕ} (σ : Restriction n) :
    freeVars (complementRestriction σ) = freeVars σ := by
  ext i
  simp [mem_freeVars]

theorem paddedSingletonFalseTail_complement_mem_iff (pad : ℕ)
    (σ : Restriction (pad + 20)) :
    complementRestriction σ ∈ paddedSingletonTrueTail pad ↔
      σ ∈ paddedSingletonFalseTail pad := by
  rw [mem_paddedSingletonTrueTail_iff, mem_paddedSingletonFalseTail_iff,
    stars_complementRestriction]
  have hfilter :
      ((paddedSingletonSupport pad).filter fun i => complementRestriction σ i = none) =
        ((paddedSingletonSupport pad).filter fun i => σ i = none) := by
    ext i
    simp
  rw [hfilter]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro htrue i hi hne
    have hcompNe : complementRestriction σ i ≠ none := by simpa using hne
    have h := htrue i hi hcompNe
    cases hσ : σ i with
    | none => exact False.elim (hne hσ)
    | some b => cases b <;> simp [complementRestriction, hσ] at h ⊢
  · intro hfalse i hi hne
    have hσne : σ i ≠ none := by simpa using hne
    have h := hfalse i hi hσne
    simpa [complementRestriction, h]

/-- Polarity complementation is a bijection between the two monochromatic tails. -/
theorem paddedSingletonTrueTail_card {pad : ℕ} (hpad : 20 ≤ pad) :
    (paddedSingletonTrueTail pad).card = paddedSingletonCertifiedMass pad := by
  rw [← paddedSingletonFalseTail_card hpad]
  symm
  apply Finset.card_bij'
      (fun σ _ => complementRestriction σ)
      (fun σ _ => complementRestriction σ)
  · intro σ hσ
    exact (paddedSingletonFalseTail_complement_mem_iff pad σ).mpr hσ
  · intro σ hσ
    apply (paddedSingletonFalseTail_complement_mem_iff pad
      (complementRestriction σ)).mp
    simpa using hσ
  · intro σ hσ
    exact complementRestriction_involutive σ
  · intro σ hσ
    exact complementRestriction_involutive σ

/-- Restrictions whose free set is exactly the twenty packed coordinates. -/
noncomputable def paddedSingletonAllLiveFiber (pad : ℕ) :
    Finset (Restriction (pad + 20)) :=
  Finset.univ.filter fun σ => freeVars σ = paddedSingletonSupport pad

set_option maxHeartbeats 1200000 in
/-- The two monochromatic tails overlap exactly when every packed coordinate is live. -/
theorem paddedSingletonFalseTail_inter_trueTail (pad : ℕ) :
    paddedSingletonFalseTail pad ∩ paddedSingletonTrueTail pad =
      paddedSingletonAllLiveFiber pad := by
  ext σ
  simp only [Finset.mem_inter, paddedSingletonAllLiveFiber,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mem_paddedSingletonFalseTail_iff, mem_paddedSingletonTrueTail_iff]
  constructor
  · rintro ⟨⟨hstars, hlive, hfalse⟩, _, _, htrue⟩
    have hsubset : paddedSingletonSupport pad ⊆ freeVars σ := by
      intro i hi
      rw [mem_freeVars]
      by_contra hne
      have hf := hfalse i hi hne
      have ht := htrue i hi hne
      rw [hf] at ht
      exact Bool.false_ne_true (Option.some.inj ht)
    exact (Finset.eq_of_subset_of_card_le hsubset (by
      rw [stars] at hstars
      rw [paddedSingletonSupport_card, hstars])).symm
  · intro hfree
    have hstars : stars σ = 20 := by
      rw [stars, hfree, paddedSingletonSupport_card]
    have hlive :
        10 < ((paddedSingletonSupport pad).filter fun i => σ i = none).card := by
      have hfilter :
          ((paddedSingletonSupport pad).filter fun i => σ i = none) =
            paddedSingletonSupport pad := by
        apply Finset.filter_eq_self.mpr
        intro i hi
        rw [← mem_freeVars, hfree]
        exact hi
      rw [hfilter, paddedSingletonSupport_card]
      omega
    refine ⟨⟨hstars, hlive, ?_⟩, hstars, hlive, ?_⟩
    · intro i hi hne
      exact False.elim (hne (by rw [← mem_freeVars, hfree]; exact hi))
    · intro i hi hne
      exact False.elim (hne (by rw [← mem_freeVars, hfree]; exact hi))

theorem paddedSingletonAllLiveFiber_card (pad : ℕ) :
    (paddedSingletonAllLiveFiber pad).card = 2 ^ pad := by
  rw [paddedSingletonAllLiveFiber, card_freeVars_eq,
    paddedSingletonSupport_card]
  congr 1

set_option maxHeartbeats 800000 in
/-- The semantic bad event is exactly the union of its two monochromatic tails. -/
theorem paddedSingletonBad_eq_falseTail_union_trueTail (pad : ℕ) :
    paddedSingletonBad pad =
      paddedSingletonFalseTail pad ∪ paddedSingletonTrueTail pad := by
  ext σ
  rw [mem_paddedSingletonBad_iff]
  simp only [Finset.mem_union]
  rw [mem_paddedSingletonFalseTail_iff, mem_paddedSingletonTrueTail_iff]
  constructor
  · rintro ⟨hstars, hlive, hfalse | htrue⟩
    · exact Or.inl ⟨hstars, hlive, hfalse⟩
    · exact Or.inr ⟨hstars, hlive, htrue⟩
  · rintro (⟨hstars, hlive, hfalse⟩ | ⟨hstars, hlive, htrue⟩)
    · exact ⟨hstars, hlive, Or.inl hfalse⟩
    · exact ⟨hstars, hlive, Or.inr htrue⟩

/-- Exact cardinality of the padding-parametric bad event. -/
theorem paddedSingletonBad_card {pad : ℕ} (hpad : 20 ≤ pad) :
    (paddedSingletonBad pad).card =
      2 * paddedSingletonCertifiedMass pad - 2 ^ pad := by
  have hcard := Finset.card_union_add_card_inter
    (paddedSingletonFalseTail pad) (paddedSingletonTrueTail pad)
  rw [← paddedSingletonBad_eq_falseTail_union_trueTail,
    paddedSingletonFalseTail_inter_trueTail,
    paddedSingletonFalseTail_card hpad,
    paddedSingletonTrueTail_card hpad,
    paddedSingletonAllLiveFiber_card] at hcard
  omega

set_option maxHeartbeats 1200000 in
/-- After inclusion-exclusion, the exact normalized bad coefficient at padding 4,080 still fits
strictly below the complete support shell coefficient. -/
theorem paddedSingletonExactCoefficient_4080_lt :
    2 * paddedSingletonCertifiedCoefficient 4080 - 2 ^ 10 <
      Nat.choose 4100 20 := by
  norm_num (config := { maxSteps := 1000000 })
    [paddedSingletonCertifiedCoefficient, Finset.sum_Icc_succ_top, Nat.choose]

theorem paddedSingletonCertifiedMass_4080_eq_coefficient_mul :
    paddedSingletonCertifiedMass 4080 =
      paddedSingletonCertifiedCoefficient 4080 * 2 ^ 4070 := by
  rw [paddedSingletonCertifiedMass, paddedSingletonCertifiedCoefficient,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  have hq10 : 10 ≤ q := le_trans (by omega) (Finset.mem_Icc.mp hq).1
  have hexp : 4080 - 20 + q = (q - 10) + 4070 := by omega
  rw [hexp, pow_add]
  ac_rfl

/-- The exact two-polarity bad union, not merely either certified half, retains the requested
`2^10` contraction at the support-specific schedule. -/
theorem paddedSingletonBad_mul_two_pow_ten_lt_shell_4080 :
    (paddedSingletonBad 4080).card * 2 ^ 10 <
      Nat.choose 4100 20 * 2 ^ 4080 := by
  rw [paddedSingletonBad_card (by norm_num : 20 ≤ 4080),
    paddedSingletonCertifiedMass_4080_eq_coefficient_mul]
  have hpow : 2 ^ 4080 = 2 ^ 10 * 2 ^ 4070 := by
    rw [← pow_add]
  rw [hpow]
  have hsub :
      2 * (paddedSingletonCertifiedCoefficient 4080 * 2 ^ 4070) -
          2 ^ 10 * 2 ^ 4070 =
        (2 * paddedSingletonCertifiedCoefficient 4080 - 2 ^ 10) * 2 ^ 4070 := by
    calc
      _ = (2 * paddedSingletonCertifiedCoefficient 4080) * 2 ^ 4070 -
          2 ^ 10 * 2 ^ 4070 := by rw [Nat.mul_assoc]
      _ = _ := (Nat.sub_mul _ _ _).symm
  rw [hsub]
  have hscaled := (Nat.mul_lt_mul_right (pow_pos (by norm_num : 0 < 2) 4080)).mpr
    paddedSingletonExactCoefficient_4080_lt
  convert hscaled using 1 <;> rw [← pow_add] <;> norm_num

/-! ### Exact width-two disjoint-block regression at `M = 10`

The intact-block lower bound is empty at the half-shell boundary, but that fact alone does not
classify the semantic bad event.  The following explicit common trunk queries one coordinate from
each of ten disjoint pairs.  It works simultaneously for both literal polarities and for arbitrary
padding, root restrictions, and fuel. -/

/-- Query a fixed coordinate list and store the accumulated restriction at every leaf. -/
def queryRestrictionList {n : ℕ} :
    Restriction n → List (Fin n) → CommonTree n (Restriction n)
  | σ, [] => .leaf σ
  | σ, i :: is => .query i
      (queryRestrictionList (fixVar σ i false) is)
      (queryRestrictionList (fixVar σ i true) is)

@[simp] theorem queryRestrictionList_depth {n : ℕ}
    (σ : Restriction n) (is : List (Fin n)) :
    (queryRestrictionList σ is).depth = is.length := by
  induction is generalizing σ with
  | nil => rfl
  | cons i is ih => simp [queryRestrictionList, CommonTree.depth, ih]

/-- Along an extending assignment, the list-query trunk preserves the root and its leaf agrees
with that assignment. -/
theorem queryRestrictionList_spec {n : ℕ} (σ : Restriction n)
    (is : List (Fin n)) (x : Fin n → Bool) (hx : Rung4Restriction.Extends σ x) :
    RestrictionExtends σ (CommonTree.run (queryRestrictionList σ is) x) ∧
      Rung4Restriction.Extends (CommonTree.run (queryRestrictionList σ is) x) x := by
  induction is generalizing σ with
  | nil => exact ⟨fun _ _ h => h, hx⟩
  | cons i is ih =>
      by_cases hxi : x i = true
      · simp only [queryRestrictionList, CommonTree.run, hxi, if_true]
        have hxfix : Rung4Restriction.Extends (fixVar σ i true) x :=
          extends_fixVar hx hxi
        obtain ⟨hroot, hleaf⟩ := ih (fixVar σ i true) hxfix
        refine ⟨?_, hleaf⟩
        intro v b hv
        apply hroot v b
        by_cases hvi : v = i
        · subst v
          have hb : b = true := (hx i b hv).symm.trans hxi
          simp [fixVar, hb]
        · simpa [fixVar, Function.update_of_ne hvi] using hv
      · have hxifalse : x i = false := Bool.eq_false_of_not_eq_true hxi
        simp only [queryRestrictionList, CommonTree.run, hxi, if_false]
        have hxfix : Rung4Restriction.Extends (fixVar σ i false) x :=
          extends_fixVar hx hxifalse
        obtain ⟨hroot, hleaf⟩ := ih (fixVar σ i false) hxfix
        refine ⟨?_, hleaf⟩
        intro v b hv
        apply hroot v b
        by_cases hvi : v = i
        · subst v
          have hb : b = false := (hx i b hv).symm.trans hxifalse
          simp [fixVar, hb]
        · simpa [fixVar, Function.update_of_ne hvi] using hv

/-- Exact coordinatewise description of the reached restriction. -/
theorem queryRestrictionList_run_apply {n : ℕ} (σ : Restriction n)
    (is : List (Fin n)) (x : Fin n → Bool) (i : Fin n) :
    CommonTree.run (queryRestrictionList σ is) x i =
      if i ∈ is then some (x i) else σ i := by
  induction is generalizing σ with
  | nil => simp [queryRestrictionList]
  | cons j is ih =>
      by_cases hxj : x j = true
      · by_cases hi : i ∈ is
        · simp [queryRestrictionList, hxj, ih, hi]
        · by_cases hij : i = j
          · subst i
            simp [queryRestrictionList, hxj, ih, hi, fixVar]
          · simp [queryRestrictionList, hxj, ih, hi, hij, fixVar]
      · by_cases hi : i ∈ is
        · simp [queryRestrictionList, hxj, ih, hi]
        · by_cases hij : i = j
          · subst i
            simp [queryRestrictionList, hxj, ih, hi, fixVar]
          · simp [queryRestrictionList, hxj, ih, hi, hij, fixVar]

/-- Every listed coordinate is fixed at the reached leaf to the followed assignment value. -/
theorem queryRestrictionList_run_eq_some_of_mem {n : ℕ} (σ : Restriction n)
    (is : List (Fin n)) (x : Fin n → Bool) {i : Fin n} (hi : i ∈ is) :
    CommonTree.run (queryRestrictionList σ is) x i = some (x i) := by
  rw [queryRestrictionList_run_apply, if_pos hi]

private theorem positiveOrderedPair_terminal_of_both_fixed {n : ℕ}
    (a b : Fin n) (ρ : Restriction n) (ha : ρ a ≠ none) (hb : ρ b ≠ none) :
    CanonicalTerminal (orderedConjunctionBlock [a, b]) ρ := by
  cases hρa : ρ a with
  | none => exact False.elim (ha hρa)
  | some va =>
      cases hρb : ρ b with
      | none => exact False.elim (hb hρb)
      | some vb =>
          cases va <;> cases vb <;>
            simp [CanonicalTerminal, orderedConjunctionBlock, anyTermSat, termSat,
              activeTerm, termFalsified, Depth3.litTrue, litVar, litFixedVal,
              litFalse, hρa, hρb]

private theorem negativeOrderedPair_terminal_of_both_fixed {n : ℕ}
    (a b : Fin n) (ρ : Restriction n) (ha : ρ a ≠ none) (hb : ρ b ≠ none) :
    CanonicalTerminal [⟨[Rung4Literal.neg a, Rung4Literal.neg b]⟩] ρ := by
  cases hρa : ρ a with
  | none => exact False.elim (ha hρa)
  | some va =>
      cases hρb : ρ b with
      | none => exact False.elim (hb hρb)
      | some vb =>
          cases va <;> cases vb <;>
            simp [CanonicalTerminal, anyTermSat, termSat, activeTerm, termFalsified,
              Depth3.litTrue, litVar, litFixedVal, litFalse, hρa, hρb]

/-- Once the first coordinate of a positive width-two conjunction is fixed, its residual
canonical depth is at most one. -/
theorem positiveOrderedPair_depth_le_one_of_first_fixed {n fuel : ℕ}
    (a b : Fin n) (ρ : Restriction n) (ha : ρ a ≠ none) :
    (canonicalDT (orderedConjunctionBlock [a, b]) fuel ρ).depth ≤ 1 := by
  cases fuel with
  | zero => rw [canonicalDT]; split <;> simp [BoolDecisionTree.depth]
  | succ fuel =>
      cases hρa : ρ a with
      | none => exact False.elim (ha hρa)
      | some va =>
          cases va with
          | false =>
              have hzero := canonicalDT_depth_eq_zero_of_terminal
                (orderedConjunctionBlock [a, b]) ρ
                (by right; simp [orderedConjunctionBlock, activeTerm, anyTermSat,
                  termSat, termFalsified, Depth3.litTrue, litFixedVal, litFalse,
                  hρa]) (Nat.succ fuel)
              exact hzero.le.trans (by omega)
          | true =>
              cases hρb : ρ b with
              | some vb =>
                  have hzero := canonicalDT_depth_eq_zero_of_terminal
                    (orderedConjunctionBlock [a, b]) ρ
                    (positiveOrderedPair_terminal_of_both_fixed a b ρ ha (by simp [hρb]))
                    (Nat.succ fuel)
                  exact hzero.le.trans (by omega)
              | none =>
                  have hab : a ≠ b := by
                    intro hab
                    subst b
                    rw [hρa] at hρb
                    contradiction
                  have hlo : (canonicalDT (orderedConjunctionBlock [a, b]) fuel
                      (fixVar ρ b false)).depth = 0 :=
                    canonicalDT_depth_eq_zero_of_terminal _ _
                      (positiveOrderedPair_terminal_of_both_fixed a b _
                        (by simp [fixVar, hab, hρa]) (by simp [fixVar])) fuel
                  have hhi : (canonicalDT (orderedConjunctionBlock [a, b]) fuel
                      (fixVar ρ b true)).depth = 0 :=
                    canonicalDT_depth_eq_zero_of_terminal _ _
                      (positiveOrderedPair_terminal_of_both_fixed a b _
                        (by simp [fixVar, hab, hρa]) (by simp [fixVar])) fuel
                  rw [canonicalDT]
                  simp [orderedConjunctionBlock, anyTermSat, termSat, activeTerm,
                    termFalsified, freeLits, Depth3.litTrue, litVar, litFixedVal,
                    litFalse, litFree, hρa, hρb]
                  change max
                    (canonicalDT (orderedConjunctionBlock [a, b]) fuel
                      (fixVar ρ b false)).depth
                    (canonicalDT (orderedConjunctionBlock [a, b]) fuel
                      (fixVar ρ b true)).depth + 1 ≤ 1
                  rw [hlo, hhi]
                  omega

/-- The same one-query residual bound holds for the all-negative polarity. -/
theorem negativeOrderedPair_depth_le_one_of_first_fixed {n fuel : ℕ}
    (a b : Fin n) (ρ : Restriction n) (ha : ρ a ≠ none) :
    (canonicalDT [⟨[Rung4Literal.neg a, Rung4Literal.neg b]⟩] fuel ρ).depth ≤ 1 := by
  cases fuel with
  | zero => rw [canonicalDT]; split <;> simp [BoolDecisionTree.depth]
  | succ fuel =>
      cases hρa : ρ a with
      | none => exact False.elim (ha hρa)
      | some va =>
          cases va with
          | true =>
              have hzero := canonicalDT_depth_eq_zero_of_terminal
                [⟨[Rung4Literal.neg a, Rung4Literal.neg b]⟩] ρ
                (by right; simp [activeTerm, anyTermSat, termSat, termFalsified,
                  Depth3.litTrue, litFixedVal, litFalse, hρa]) (Nat.succ fuel)
              exact hzero.le.trans (by omega)
          | false =>
              cases hρb : ρ b with
              | some vb =>
                  have hzero := canonicalDT_depth_eq_zero_of_terminal
                    [⟨[Rung4Literal.neg a, Rung4Literal.neg b]⟩] ρ
                    (negativeOrderedPair_terminal_of_both_fixed a b ρ ha (by simp [hρb]))
                    (Nat.succ fuel)
                  exact hzero.le.trans (by omega)
              | none =>
                  have hab : a ≠ b := by
                    intro hab
                    subst b
                    rw [hρa] at hρb
                    contradiction
                  have hlo : (canonicalDT
                      [⟨[Rung4Literal.neg a, Rung4Literal.neg b]⟩] fuel
                      (fixVar ρ b false)).depth = 0 :=
                    canonicalDT_depth_eq_zero_of_terminal _ _
                      (negativeOrderedPair_terminal_of_both_fixed a b _
                        (by simp [fixVar, hab, hρa]) (by simp [fixVar])) fuel
                  have hhi : (canonicalDT
                      [⟨[Rung4Literal.neg a, Rung4Literal.neg b]⟩] fuel
                      (fixVar ρ b true)).depth = 0 :=
                    canonicalDT_depth_eq_zero_of_terminal _ _
                      (negativeOrderedPair_terminal_of_both_fixed a b _
                        (by simp [fixVar, hab, hρa]) (by simp [fixVar])) fuel
                  rw [canonicalDT]
                  simp [anyTermSat, termSat, activeTerm, termFalsified, freeLits,
                    Depth3.litTrue, litVar, litFixedVal, litFalse, litFree, hρa, hρb]
                  change max
                    (canonicalDT [⟨[Rung4Literal.neg a, Rung4Literal.neg b]⟩] fuel
                      (fixVar ρ b false)).depth
                    (canonicalDT [⟨[Rung4Literal.neg a, Rung4Literal.neg b]⟩] fuel
                      (fixVar ρ b true)).depth + 1 ≤ 1
                  rw [hlo, hhi]
                  omega

/-- The first and second coordinates of padded disjoint pair `g`. -/
def paddedPairFirst (pad : ℕ) (g : Fin 10) : Fin (pad + 20) :=
  Fin.natAdd pad ⟨2 * g.val, by omega⟩

def paddedPairSecond (pad : ℕ) (g : Fin 10) : Fin (pad + 20) :=
  Fin.natAdd pad ⟨2 * g.val + 1, by omega⟩

/-- Exact two-polarity family of ten disjoint width-two conjunction blocks. -/
def paddedDisjointPairFamily (pad : ℕ) : Fin 20 → List (Depth3.Clause (pad + 20)) := fun idx =>
  let key : Fin 2 × Fin 10 := finProdFinEquiv.symm idx
  if key.1 = 0 then
    orderedConjunctionBlock [paddedPairFirst pad key.2, paddedPairSecond pad key.2]
  else
    [⟨[Rung4Literal.neg (paddedPairFirst pad key.2),
      Rung4Literal.neg (paddedPairSecond pad key.2)]⟩]

/-- One selected coordinate per pair. -/
def paddedPairQueryCoordinates (pad : ℕ) : List (Fin (pad + 20)) :=
  List.ofFn fun g : Fin 10 => paddedPairFirst pad g

@[simp] theorem paddedPairQueryCoordinates_length (pad : ℕ) :
    (paddedPairQueryCoordinates pad).length = 10 := by
  simp [paddedPairQueryCoordinates]

/-- The ten-query trunk makes all twenty indexed polarity gates residual-depth one. -/
theorem paddedDisjointPairFamily_commonShallow (pad fuel : ℕ)
    (σ : Restriction (pad + 20)) :
    CommonShallowAt (paddedDisjointPairFamily pad) fuel σ 10 1 := by
  let trunk := queryRestrictionList σ (paddedPairQueryCoordinates pad)
  refine ⟨trunk, ?_, ?_⟩
  · simp [trunk]
  · intro x hx
    obtain ⟨hroot, hleaf⟩ := queryRestrictionList_spec
      σ (paddedPairQueryCoordinates pad) x hx
    refine ⟨hroot, hleaf, ?_⟩
    intro idx
    let key : Fin 2 × Fin 10 := finProdFinEquiv.symm idx
    have hmem : paddedPairFirst pad key.2 ∈ paddedPairQueryCoordinates pad := by
      exact List.mem_ofFn.mpr ⟨key.2, rfl⟩
    have hfixed : CommonTree.run trunk x (paddedPairFirst pad key.2) ≠ none := by
      rw [show trunk = queryRestrictionList σ (paddedPairQueryCoordinates pad) by rfl,
        queryRestrictionList_run_eq_some_of_mem σ _ x hmem]
      simp
    change (canonicalDT (if key.1 = 0 then
      orderedConjunctionBlock [paddedPairFirst pad key.2, paddedPairSecond pad key.2]
      else [⟨[Rung4Literal.neg (paddedPairFirst pad key.2),
        Rung4Literal.neg (paddedPairSecond pad key.2)]⟩]) fuel
      (CommonTree.run trunk x)).depth ≤ 1
    by_cases hk : key.1 = 0
    · rw [if_pos hk]
      exact positiveOrderedPair_depth_le_one_of_first_fixed _ _ _ hfixed
    · rw [if_neg hk]
      exact negativeOrderedPair_depth_le_one_of_first_fixed _ _ _ hfixed

/-- Hence the exact width-two `M = 10` support-shell bad event is empty, for every padding. -/
theorem paddedDisjointPairBad_eq_empty (pad : ℕ) :
    commonShallowBad (paddedDisjointPairFamily pad) (pad + 20) 20 10 1 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro σ hσ
  have hbad := (mem_commonShallowBad.mp hσ).2
  exact hbad (paddedDisjointPairFamily_commonShallow pad (pad + 20) σ)

/-- In particular the exact padded event contracts with zero bad mass on every corresponding
twenty-live-coordinate shell, including the support-schedule instance `pad = 4080`. -/
theorem paddedDisjointPairBad_mul_two_pow_ten_lt_shell (pad : ℕ) :
    (commonShallowBad (paddedDisjointPairFamily pad) (pad + 20) 20 10 1).card * 2 ^ 10 <
      Nat.choose (pad + 20) 20 * 2 ^ pad := by
  rw [paddedDisjointPairBad_eq_empty]
  simp only [Finset.card_empty, zero_mul]
  exact Nat.mul_pos (Nat.choose_pos (by omega)) (pow_pos (by norm_num) _)

/-! ### Two disjoint width-two clauses per gate

The next clause-rich regression has a subtle local cost.  Querying one coordinate from each
clause can leave two live singleton terms in one polarity, so the one-clause transversal does not
immediately extend.  The following local certificate fixes both coordinates of the first clause
and one coordinate of the second.  It is deliberately polarity symmetric. -/

/-- A positive DNF consisting of two ordered, disjoint width-two clauses. -/
def positiveTwoPairGate {n : ℕ} (a b c d : Fin n) : List (Depth3.Clause n) :=
  orderedConjunctionBlock [a, b] ++ orderedConjunctionBlock [c, d]

/-- Its termwise-negative indexed polarity. -/
def negativeTwoPairGate {n : ℕ} (a b c d : Fin n) : List (Depth3.Clause n) :=
  [⟨[Rung4Literal.neg a, Rung4Literal.neg b]⟩,
    ⟨[Rung4Literal.neg c, Rung4Literal.neg d]⟩]

set_option linter.unusedSimpArgs false in
/-- If at least three distinct owned coordinates remain free and none is fixed false, the
positive two-pair gate has residual canonical depth at least two.  The proof follows two steps of
the canonical all-falsify replay.  The three-live threshold is deliberate: it avoids the genuine
two-live opposite-cross certificate characterized below. -/
theorem positiveTwoPair_depth_ge_two_of_three_free {n fuel : ℕ}
    (a b c d : Fin n) (rho : Restriction n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hnotFalse : ∀ i ∈ ({a, b, c, d} : Finset (Fin n)), rho i ≠ some false)
    (hcard : 3 ≤ (({a, b, c, d} : Finset (Fin n)) ∩ freeVars rho).card)
    (hfuel : 2 ≤ fuel) :
    2 ≤ (canonicalDT (positiveTwoPairGate a b c d) fuel rho).depth := by
  generalize ha : rho a = oa at *
  generalize hb : rho b = ob at *
  generalize hc : rho c = oc at *
  generalize hd : rho d = od at *
  fin_cases oa <;> fin_cases ob <;> fin_cases oc <;> fin_cases od
  all_goals
    try { exact False.elim (hnotFalse a (by simp) ha) }
    try { exact False.elim (hnotFalse b (by simp) hb) }
    try { exact False.elim (hnotFalse c (by simp) hc) }
    try { exact False.elim (hnotFalse d (by simp) hd) }
  all_goals
    try { simp [freeVars, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd,
      Ne.symm hab, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd,
      Ne.symm hcd] at hcard }
  all_goals
    apply canonicalDT_depth_ge_replay _ 2 rho fuel hfuel
    intro i hi
    interval_cases i <;>
      simp [positiveTwoPairGate, orderedConjunctionBlock, replayPath, replayStep,
        activeTermLit, anyTermSat, termSat, activeTerm, termFalsified, freeLits,
        Depth3.litTrue, litVar, falValue, litFixedVal, litFalse, litFree, falFix,
        fixVar, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd,
        Ne.symm hab, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd,
        Ne.symm hcd]

set_option linter.unusedSimpArgs false in
/-- The polarity-symmetric local depth certificate.  If at least three distinct owned
coordinates remain free and none is fixed true, the negative two-pair gate has residual
canonical depth at least two. -/
theorem negativeTwoPair_depth_ge_two_of_three_free {n fuel : ℕ}
    (a b c d : Fin n) (rho : Restriction n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hnotTrue : ∀ i ∈ ({a, b, c, d} : Finset (Fin n)), rho i ≠ some true)
    (hcard : 3 ≤ (({a, b, c, d} : Finset (Fin n)) ∩ freeVars rho).card)
    (hfuel : 2 ≤ fuel) :
    2 ≤ (canonicalDT (negativeTwoPairGate a b c d) fuel rho).depth := by
  generalize ha : rho a = oa at *
  generalize hb : rho b = ob at *
  generalize hc : rho c = oc at *
  generalize hd : rho d = od at *
  fin_cases oa <;> fin_cases ob <;> fin_cases oc <;> fin_cases od
  all_goals
    try { exact False.elim (hnotTrue a (by simp) ha) }
    try { exact False.elim (hnotTrue b (by simp) hb) }
    try { exact False.elim (hnotTrue c (by simp) hc) }
    try { exact False.elim (hnotTrue d (by simp) hd) }
  all_goals
    try { simp [freeVars, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd,
      Ne.symm hab, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd,
      Ne.symm hcd] at hcard }
  all_goals
    apply canonicalDT_depth_ge_replay _ 2 rho fuel hfuel
    intro i hi
    interval_cases i <;>
      simp [negativeTwoPairGate, replayPath, replayStep, activeTermLit, anyTermSat,
        termSat, activeTerm, termFalsified, freeLits, Depth3.litTrue, litVar, falValue,
        litFixedVal, litFalse, litFree, falFix, fixVar, ha, hb, hc, hd, hab, hac, had,
        hbc, hbd, hcd, Ne.symm hab, Ne.symm hac, Ne.symm had, Ne.symm hbc,
        Ne.symm hbd, Ne.symm hcd]

/-- Fixing all four owned coordinates makes the positive gate terminal. -/
theorem positiveTwoPair_depth_eq_zero_of_four_fixed {n fuel : ℕ}
    (a b c d : Fin n) (ρ : Restriction n)
    (ha : ρ a ≠ none) (hb : ρ b ≠ none) (hc : ρ c ≠ none) (hd : ρ d ≠ none) :
    (canonicalDT (positiveTwoPairGate a b c d) fuel ρ).depth = 0 := by
  apply canonicalDT_depth_eq_zero_of_terminal
  cases hρa : ρ a with | none => exact False.elim (ha hρa) | some va =>
  cases hρb : ρ b with | none => exact False.elim (hb hρb) | some vb =>
  cases hρc : ρ c with | none => exact False.elim (hc hρc) | some vc =>
  cases hρd : ρ d with | none => exact False.elim (hd hρd) | some vd =>
  cases va <;> cases vb <;> cases vc <;> cases vd <;>
    simp [CanonicalTerminal, positiveTwoPairGate, orderedConjunctionBlock, anyTermSat,
      termSat, activeTerm, termFalsified, Depth3.litTrue, litFixedVal, litFalse,
      hρa, hρb, hρc, hρd]

/-- Fixing all four owned coordinates makes the negative gate terminal as well. -/
theorem negativeTwoPair_depth_eq_zero_of_four_fixed {n fuel : ℕ}
    (a b c d : Fin n) (ρ : Restriction n)
    (ha : ρ a ≠ none) (hb : ρ b ≠ none) (hc : ρ c ≠ none) (hd : ρ d ≠ none) :
    (canonicalDT (negativeTwoPairGate a b c d) fuel ρ).depth = 0 := by
  apply canonicalDT_depth_eq_zero_of_terminal
  cases hρa : ρ a with | none => exact False.elim (ha hρa) | some va =>
  cases hρb : ρ b with | none => exact False.elim (hb hρb) | some vb =>
  cases hρc : ρ c with | none => exact False.elim (hc hρc) | some vc =>
  cases hρd : ρ d with | none => exact False.elim (hd hρd) | some vd =>
  cases va <;> cases vb <;> cases vc <;> cases vd <;>
    simp [CanonicalTerminal, negativeTwoPairGate, anyTermSat, termSat, activeTerm,
      termFalsified, Depth3.litTrue, litFixedVal, litFalse, hρa, hρb, hρc, hρd]

/-- Coordinate `k` of the four-coordinate block owned by gate `g`. -/
def paddedTwoPairCoord (pad : ℕ) (g : Fin 10) (k : Fin 4) : Fin (pad + 40) :=
  Fin.natAdd pad ⟨4 * g.val + k.val, by omega⟩

/-- The forty padded gadget coordinates retain their product indexing. -/
theorem paddedTwoPairCoord_injective (pad : ℕ) :
    Function.Injective (fun p : Fin 10 × Fin 4 => paddedTwoPairCoord pad p.1 p.2) := by
  intro p q hpq
  have hv := congrArg Fin.val hpq
  simp [paddedTwoPairCoord] at hv
  have hg : p.1 = q.1 := by
    apply Fin.ext
    omega
  have hgval := congrArg Fin.val hg
  have hk : p.2 = q.2 := by
    apply Fin.ext
    omega
  exact Prod.ext hg hk

/-- Static four-coordinate support of one padded two-pair gadget. -/
def paddedTwoPairSupport (pad : ℕ) (g : Fin 10) : Finset (Fin (pad + 40)) :=
  Finset.univ.image (paddedTwoPairCoord pad g)

@[simp] theorem paddedTwoPairSupport_card (pad : ℕ) (g : Fin 10) :
    (paddedTwoPairSupport pad g).card = 4 := by
  rw [paddedTwoPairSupport, Finset.card_image_iff.mpr]
  · simp
  · intro k _ l _ h
    exact congrArg Prod.snd
      ((@paddedTwoPairCoord_injective pad (g, k) (g, l)) h)

theorem paddedTwoPairSupport_pairwiseDisjoint (pad : ℕ) :
    ∀ g h, g ≠ h → Disjoint (paddedTwoPairSupport pad g) (paddedTwoPairSupport pad h) := by
  intro g h hne
  rw [Finset.disjoint_left]
  intro i hig hih
  rw [paddedTwoPairSupport, Finset.mem_image] at hig hih
  obtain ⟨k, _, rfl⟩ := hig
  obtain ⟨l, _, heq⟩ := hih
  have hp := (@paddedTwoPairCoord_injective pad (g, k) (h, l)) heq.symm
  exact hne (congrArg Prod.fst hp)

/-- The two polarities of one padded two-pair gadget before flattening the indices. -/
def paddedTwoPairGates (pad : ℕ) (polarity : Fin 2) (g : Fin 10) :
    List (Depth3.Clause (pad + 40)) :=
  if polarity = 0 then
    positiveTwoPairGate
      (paddedTwoPairCoord pad g 0) (paddedTwoPairCoord pad g 1)
      (paddedTwoPairCoord pad g 2) (paddedTwoPairCoord pad g 3)
  else
    negativeTwoPairGate
      (paddedTwoPairCoord pad g 0) (paddedTwoPairCoord pad g 1)
      (paddedTwoPairCoord pad g 2) (paddedTwoPairCoord pad g 3)

/-- The exact normalized two-polarity family of ten gates, each containing two disjoint
width-two clauses. -/
def paddedTwoPairFamily (pad : ℕ) : Fin 20 → List (Depth3.Clause (pad + 40)) := fun idx =>
  let key : Fin 2 × Fin 10 := finProdFinEquiv.symm idx
  paddedTwoPairGates pad key.1 key.2

def paddedTwoPairQueryCoordinates (pad : ℕ) : List (Fin (pad + 40)) :=
  (List.finRange 10).flatMap fun g =>
    [paddedTwoPairCoord pad g 0, paddedTwoPairCoord pad g 1,
      paddedTwoPairCoord pad g 2, paddedTwoPairCoord pad g 3]

@[simp] theorem paddedTwoPairQueryCoordinates_length (pad : ℕ) :
    (paddedTwoPairQueryCoordinates pad).length = 40 := by
  simp [paddedTwoPairQueryCoordinates]

/-- Four static queries per gate give the exact family a residual-depth-one common trunk. -/
theorem paddedTwoPairFamily_commonShallow_forty (pad fuel : ℕ)
    (σ : Restriction (pad + 40)) :
    CommonShallowAt (paddedTwoPairFamily pad) fuel σ 40 1 := by
  let trunk := queryRestrictionList σ (paddedTwoPairQueryCoordinates pad)
  refine ⟨trunk, by simp [trunk], ?_⟩
  intro x hx
  obtain ⟨hroot, hleaf⟩ := queryRestrictionList_spec
    σ (paddedTwoPairQueryCoordinates pad) x hx
  refine ⟨hroot, hleaf, ?_⟩
  intro idx
  let key : Fin 2 × Fin 10 := finProdFinEquiv.symm idx
  have hmem0 : paddedTwoPairCoord pad key.2 0 ∈ paddedTwoPairQueryCoordinates pad := by
    rw [paddedTwoPairQueryCoordinates, List.mem_flatMap]
    exact ⟨key.2, List.mem_finRange key.2, by simp⟩
  have hmem1 : paddedTwoPairCoord pad key.2 1 ∈ paddedTwoPairQueryCoordinates pad := by
    rw [paddedTwoPairQueryCoordinates, List.mem_flatMap]
    exact ⟨key.2, List.mem_finRange key.2, by simp⟩
  have hmem2 : paddedTwoPairCoord pad key.2 2 ∈ paddedTwoPairQueryCoordinates pad := by
    rw [paddedTwoPairQueryCoordinates, List.mem_flatMap]
    exact ⟨key.2, List.mem_finRange key.2, by simp⟩
  have hmem3 : paddedTwoPairCoord pad key.2 3 ∈ paddedTwoPairQueryCoordinates pad := by
    rw [paddedTwoPairQueryCoordinates, List.mem_flatMap]
    exact ⟨key.2, List.mem_finRange key.2, by simp⟩
  have hfixed0 : CommonTree.run trunk x (paddedTwoPairCoord pad key.2 0) ≠ none := by
    rw [show trunk = queryRestrictionList σ (paddedTwoPairQueryCoordinates pad) by rfl,
      queryRestrictionList_run_eq_some_of_mem σ _ x hmem0]
    simp
  have hfixed1 : CommonTree.run trunk x (paddedTwoPairCoord pad key.2 1) ≠ none := by
    rw [show trunk = queryRestrictionList σ (paddedTwoPairQueryCoordinates pad) by rfl,
      queryRestrictionList_run_eq_some_of_mem σ _ x hmem1]
    simp
  have hfixed2 : CommonTree.run trunk x (paddedTwoPairCoord pad key.2 2) ≠ none := by
    rw [show trunk = queryRestrictionList σ (paddedTwoPairQueryCoordinates pad) by rfl,
      queryRestrictionList_run_eq_some_of_mem σ _ x hmem2]
    simp
  have hfixed3 : CommonTree.run trunk x (paddedTwoPairCoord pad key.2 3) ≠ none := by
    rw [show trunk = queryRestrictionList σ (paddedTwoPairQueryCoordinates pad) by rfl,
      queryRestrictionList_run_eq_some_of_mem σ _ x hmem3]
    simp
  change (canonicalDT (if key.1 = 0 then
    positiveTwoPairGate
      (paddedTwoPairCoord pad key.2 0) (paddedTwoPairCoord pad key.2 1)
      (paddedTwoPairCoord pad key.2 2) (paddedTwoPairCoord pad key.2 3)
    else negativeTwoPairGate
      (paddedTwoPairCoord pad key.2 0) (paddedTwoPairCoord pad key.2 1)
      (paddedTwoPairCoord pad key.2 2) (paddedTwoPairCoord pad key.2 3)) fuel
    (CommonTree.run trunk x)).depth ≤ 1
  by_cases hk : key.1 = 0
  · rw [if_pos hk]
    rw [positiveTwoPair_depth_eq_zero_of_four_fixed _ _ _ _ _ hfixed0 hfixed1 hfixed2 hfixed3]
    omega
  · rw [if_neg hk]
    rw [negativeTwoPair_depth_eq_zero_of_four_fixed _ _ _ _ _ hfixed0 hfixed1 hfixed2 hfixed3]
    omega

def twoPairFirstCoordinatesTrue : Restriction 4 := fun i =>
  if i = 0 ∨ i = 2 then some true else none

set_option maxHeartbeats 2000000 in
/-- One query in each clause fails on the all-true branch: positive residual depth is exactly two. -/
theorem positiveTwoPair_first_coordinates_true_depth_eq_two :
    (canonicalDT (positiveTwoPairGate (0 : Fin 4) 1 2 3) 4
      twoPairFirstCoordinatesTrue).depth = 2 := by
  decide

set_option maxHeartbeats 2000000 in
/-- Exact classification of the possible shallow leaves while at least two coordinates remain
live.  Both termwise polarities have residual depth at most one precisely when the restriction
fixes a coordinate of each clause to opposite Boolean values.  In particular, the tempting
stronger claim that every two-live restriction leaves one polarity deep is false. -/
theorem twoPair_both_depth_le_one_iff_opposite_cross_fixed (ρ : Restriction 4)
    (hρ : 2 ≤ stars ρ) :
    ((canonicalDT (positiveTwoPairGate (0 : Fin 4) 1 2 3) 4 ρ).depth ≤ 1 ∧
      (canonicalDT (negativeTwoPairGate (0 : Fin 4) 1 2 3) 4 ρ).depth ≤ 1) ↔
      (((ρ 0 = some true ∨ ρ 1 = some true) ∧
          (ρ 2 = some false ∨ ρ 3 = some false)) ∨
        ((ρ 0 = some false ∨ ρ 1 = some false) ∧
          (ρ 2 = some true ∨ ρ 3 = some true))) := by
  revert ρ
  decide

/-- The two indexed polarities of the four-coordinate, two-clause gadget. -/
def twoPairPolarityFamily : Fin 2 → List (Depth3.Clause 4) := fun g =>
  if g = 0 then positiveTwoPairGate 0 1 2 3 else negativeTwoPairGate 0 1 2 3

/-- A depth-two adaptive common trunk cannot make both polarities of the fully live two-pair
gadget residual-depth one.  Along the all-true path, at most two coordinates are queried.  Every
unqueried coordinate must remain live (otherwise flipping it would reach the same leaf while
violating leaf agreement), while every fixed coordinate at that leaf is true.  The exact shallow
leaf classification would instead require a fixed false coordinate in one of the two clauses. -/
theorem twoPairPolarities_not_commonShallowAt_two :
    ¬CommonShallowAt twoPairPolarityFamily 4 (fun _ : Fin 4 => none) 2 1 := by
  rintro ⟨trunk, hdepth, hleaf⟩
  let x : Fin 4 → Bool := fun _ => true
  let path : Finset (Fin 4) := (CommonTree.queryVars trunk x).toFinset
  have hpathCard : path.card ≤ 2 := by
    calc
      path.card ≤ (CommonTree.queryVars trunk x).length := List.toFinset_card_le _
      _ ≤ CommonTree.depth trunk := CommonTree.queryVars_length_le_depth trunk x
      _ ≤ 2 := hdepth
  have hx : Rung4Restriction.Extends (fun _ : Fin 4 => none) x := by
    intro i b hi
    simp at hi
  have hfree (i : Fin 4) (hi : i ∉ path) : CommonTree.run trunk x i = none := by
    let y : Fin 4 → Bool := Function.update x i false
    have hy : Rung4Restriction.Extends (fun _ : Fin 4 => none) y := by
      intro j b hj
      simp at hj
    obtain ⟨_, htx, _⟩ := hleaf x hx
    obtain ⟨_, hty, _⟩ := hleaf y hy
    have hrun : CommonTree.run trunk y = CommonTree.run trunk x := by
      exact CommonTree.run_update_of_not_mem_queryVars trunk x i
        (by simpa [path] using hi)
    cases ht : CommonTree.run trunk x i with
    | none => rfl
    | some b =>
        have hbx : b = true := by
          simpa [x] using htx i b ht
        have hby : b = false := by
          have : CommonTree.run trunk y i = some b := by simpa [hrun] using ht
          simpa [y, x] using hty i b this
        exact False.elim (Bool.false_ne_true (hby.symm.trans hbx))
  let ρ := CommonTree.run trunk x
  have hstars : 2 ≤ stars ρ := by
    have hsubset : Finset.univ \ path ⊆ freeVars ρ := by
      intro i hi
      rw [Finset.mem_sdiff] at hi
      rw [mem_freeVars]
      change CommonTree.run trunk x i = none
      exact hfree i hi.2
    have hcompCard : (Finset.univ \ path).card = 4 - path.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ path), Finset.card_univ,
        Fintype.card_fin]
    rw [stars]
    calc
      2 ≤ 4 - path.card := by omega
      _ = (Finset.univ \ path).card := hcompCard.symm
      _ ≤ (freeVars ρ).card := Finset.card_le_card hsubset
  obtain ⟨_, hρx, hshallow⟩ := hleaf x hx
  have hboth :
      (canonicalDT (positiveTwoPairGate (0 : Fin 4) 1 2 3) 4 ρ).depth ≤ 1 ∧
        (canonicalDT (negativeTwoPairGate (0 : Fin 4) 1 2 3) 4 ρ).depth ≤ 1 := by
    constructor
    · simpa [twoPairPolarityFamily, ρ] using hshallow (0 : Fin 2)
    · simpa [twoPairPolarityFamily, ρ] using hshallow (1 : Fin 2)
  have hopp := (twoPair_both_depth_le_one_iff_opposite_cross_fixed ρ hstars).mp hboth
  have hnotFalse (i : Fin 4) : ρ i ≠ some false := by
    intro hi
    have := hρx i false hi
    simpa [x] using this
  rcases hopp with h | h
  · rcases h.2 with h | h <;> exact hnotFalse _ h
  · rcases h.1 with h | h <;> exact hnotFalse _ h

/-- The adaptive one-gate obstruction is an actual member of the four-live fixed-shell bad
event, not merely an external statement about common trees. -/
theorem allFreeFour_mem_twoPairPolarityBad_two :
    (fun _ : Fin 4 => none) ∈ commonShallowBad twoPairPolarityFamily 4 4 2 1 := by
  rw [mem_commonShallowBad]
  exact ⟨by decide, twoPairPolarities_not_commonShallowAt_two⟩

/-- Three adaptive queries suffice for the fully live two-pair gadget.  Query both coordinates
of the first clause and one coordinate of the second.  On every Boolean branch, either one
polarity is already terminal or its only remaining live clause is a singleton, so both indexed
polarities have residual canonical depth at most one.  Together with
`twoPairPolarities_not_commonShallowAt_two`, this gives an exact local trunk cost of three. -/
theorem twoPairPolarities_commonShallowAt_three :
    CommonShallowAt twoPairPolarityFamily 4 (fun _ : Fin 4 => none) 3 1 := by
  let trunk := queryRestrictionList (fun _ : Fin 4 => none) [0, 1, 2]
  refine ⟨trunk, by simp [trunk], ?_⟩
  intro x hx
  obtain ⟨hroot, hleaf⟩ := queryRestrictionList_spec
    (fun _ : Fin 4 => none) [0, 1, 2] x hx
  refine ⟨hroot, hleaf, ?_⟩
  intro g
  fin_cases g <;> cases hx0 : x 0 <;> cases hx1 : x 1 <;> cases hx2 : x 2 <;>
    simp [trunk, queryRestrictionList, hx0, hx1, hx2, twoPairPolarityFamily,
      positiveTwoPairGate, negativeTwoPairGate, orderedConjunctionBlock, canonicalDT,
      anyTermSat, termSat, activeTerm, termFalsified, freeLits, Depth3.litTrue, litVar,
      litFixedVal, litFalse, litFree, fixVar, BoolDecisionTree.depth]

/-- The fully live local profile has minimum common-trunk depth exactly three at residual depth
one: depth two is impossible, while the explicit three-query trunk above succeeds. -/
theorem twoPairPolarities_exact_trunk_cost_three :
    (¬ CommonShallowAt twoPairPolarityFamily 4 (fun _ : Fin 4 => none) 2 1) ∧
      CommonShallowAt twoPairPolarityFamily 4 (fun _ : Fin 4 => none) 3 1 :=
  ⟨twoPairPolarities_not_commonShallowAt_two,
    twoPairPolarities_commonShallowAt_three⟩

/-- A zero-depth common trunk cannot secretly strengthen its root restriction.  Hence every gate
must already be residually shallow at the root.  This converse is also the base case of the finite
query-game normalization below. -/
theorem CommonShallowAt.root_shallow_of_trunkDepth_zero {n G fuel residualDepth : ℕ}
    {gates : Fin G → List (Depth3.Clause n)} {sigma : Restriction n}
    (h : CommonShallowAt gates fuel sigma 0 residualDepth) :
    ∀ g, (canonicalDT (gates g) fuel sigma).depth ≤ residualDepth := by
  obtain ⟨trunk, hdepth, hleaf⟩ := h
  cases trunk with
  | leaf tau =>
      have htau : tau = sigma := by
        funext i
        cases hsigma : sigma i with
        | some b =>
            let x : Fin n → Bool := fun j => (sigma j).getD false
            have hx : Rung4Restriction.Extends sigma x := by
              intro j c hj
              simp [x, hj]
            exact (hleaf x hx).1 i b hsigma
        | none =>
            cases htau : tau i with
            | none => rfl
            | some b =>
                let x : Fin n → Bool := fun j =>
                  if j = i then !b else (sigma j).getD false
                have hx : Rung4Restriction.Extends sigma x := by
                  intro j c hj
                  have hji : j ≠ i := by
                    intro h
                    subst j
                    rw [hsigma] at hj
                    simp at hj
                  simp [x, hji, hj]
                have hagree := (hleaf x hx).2.1 i b htau
                have hxb : x i = !b := by simp [x]
                rw [hxb] at hagree
                cases b <;> simp at hagree
      intro g
      simpa [htau] using (hleaf (fun i => (sigma i).getD false) (by
        intro i b hi
        simp [hi])).2.2 g
  | query i left right =>
      simp [CommonTree.depth] at hdepth

/-! ### Executable classification of all 81 local restrictions

The arbitrary common-tree search has a finite read-once game presentation.  A state wins at
budget zero exactly when both polarities are already residual-depth one.  At positive budget it
also wins when some currently free coordinate has winning false and true children.  The
soundness theorem below turns every such finite-game certificate into a genuine
`CommonShallowAt` tree; the converse is deliberately left as the next structural audit. -/

/-- Base-three decoding of one coordinate: zero is live, one is fixed false, and two is fixed
true. -/
def twoPairLocalDigitState (x : Fin 3) : Option Bool :=
  if x = 0 then none else if x = 1 then some false else some true

/-- The `81 = 3^4` local restrictions, with coordinate `i` read from base-three digit `i`. -/
def twoPairLocalRestriction (code : Fin 81) : Restriction 4 := fun i =>
  twoPairLocalDigitState ⟨(code.val / (3 ^ i.val)) % 3, by omega⟩

/-- Boolean root test for simultaneous residual depth at most one. -/
def twoPairRootShallow (rho : Restriction 4) : Bool :=
  decide ((canonicalDT (twoPairPolarityFamily 0) 4 rho).depth ≤ 1 ∧
    (canonicalDT (twoPairPolarityFamily 1) 4 rho).depth ≤ 1)

/-- Finite read-once common-query game for the two-pair gadget. -/
def twoPairLocalQueryWin : Nat → Restriction 4 → Bool
  | 0, rho => twoPairRootShallow rho
  | k + 1, rho => twoPairRootShallow rho ||
      ((List.ofFn id : List (Fin 4)).any fun i => decide (rho i = none) &&
        twoPairLocalQueryWin k (fixVar rho i false) &&
        twoPairLocalQueryWin k (fixVar rho i true))

/-- First winning budget in the corrected range `0,1,2,3`. -/
def twoPairLocalQueryCost (rho : Restriction 4) : Nat :=
  if twoPairLocalQueryWin 0 rho then 0 else if twoPairLocalQueryWin 1 rho then 1 else
    if twoPairLocalQueryWin 2 rho then 2 else 3

/-- Every finite-game win supplies an actual common trunk of the same depth. -/
theorem twoPairLocalQueryWin_sound : ∀ k rho,
    twoPairLocalQueryWin k rho = true →
      CommonShallowAt twoPairPolarityFamily 4 rho k 1 := by
  intro k
  induction k with
  | zero =>
      intro rho hwin
      simp only [twoPairLocalQueryWin, twoPairRootShallow, decide_eq_true_eq] at hwin
      refine ⟨CommonTree.leaf rho, by simp [CommonTree.depth], ?_⟩
      intro x hx
      exact ⟨by intro i b hi; exact hi, hx, fun g => by fin_cases g <;> simp_all⟩
  | succ k ih =>
      intro rho hwin
      simp only [twoPairLocalQueryWin, Bool.or_eq_true, twoPairRootShallow,
        decide_eq_true_eq] at hwin
      rcases hwin with hroot | hquery
      · refine ⟨CommonTree.leaf rho, by simp [CommonTree.depth], ?_⟩
        intro x hx
        exact ⟨by intro i b hi; exact hi, hx, fun g => by fin_cases g <;> simp_all⟩
      · rw [List.any_eq_true] at hquery
        obtain ⟨i, _hi, hpred⟩ := hquery
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred
        have hfree : rho i = none := hpred.1.1
        have hlo : twoPairLocalQueryWin k (fixVar rho i false) = true := hpred.1.2
        have hhi : twoPairLocalQueryWin k (fixVar rho i true) = true := hpred.2
        obtain ⟨lo, hloDepth, hloLeaf⟩ := ih _ hlo
        obtain ⟨hi, hhiDepth, hhiLeaf⟩ := ih _ hhi
        refine ⟨CommonTree.query i lo hi, ?_, ?_⟩
        · simp only [CommonTree.depth]
          omega
        · intro x hx
          cases hxi : x i with
          | false =>
            have hxlo : Rung4Restriction.Extends (fixVar rho i false) x :=
              extends_fixVar hx hxi
            obtain ⟨hext, hagree, hshallow⟩ := hloLeaf x hxlo
            simp only [CommonTree.run, hxi]
            refine ⟨?_, hagree, hshallow⟩
            intro j b hj
            apply hext j b
            by_cases hji : j = i
            · subst j
              rw [hfree] at hj
              contradiction
            · simpa [fixVar, Function.update_of_ne hji] using hj
          | true =>
            have hxhi : Rung4Restriction.Extends (fixVar rho i true) x :=
              extends_fixVar hx hxi
            obtain ⟨hext, hagree, hshallow⟩ := hhiLeaf x hxhi
            simp only [CommonTree.run, hxi]
            refine ⟨?_, hagree, hshallow⟩
            intro j b hj
            apply hext j b
            by_cases hji : j = i
            · subst j
              rw [hfree] at hj
              contradiction
            · simpa [fixVar, Function.update_of_ne hji] using hj

/-- Canonical residual depth is not monotone under restriction extension, even for the local
two-pair gadget.  State `11` is root-shallow, but fixing coordinate zero to false makes one
polarity deeper than one.  This refutes the tempting converse proof that completes every trunk
leaf by inserting all values queried on its path. -/
theorem twoPairRootShallow_not_monotone_fixVar :
    twoPairRootShallow (twoPairLocalRestriction ⟨11, by omega⟩) = true ∧
      twoPairRootShallow
        (fixVar (twoPairLocalRestriction ⟨11, by omega⟩) (0 : Fin 4) false) = false := by
  decide

/-- Boolean restriction extension for the finite arbitrary-leaf audit. -/
def twoPairRestrictionExtendsB (rho tau : Restriction 4) : Bool :=
  (List.ofFn id : List (Fin 4)).all fun i =>
    match rho i with
    | none => true
    | some b => decide (tau i = some b)

/-- At a legal arbitrary trunk leaf, the payload may retain any subset of values queried on the
path.  It must extend the original root, agree with the accumulated path, and already be shallow.
This explicitly models the omission that invalidates the direct read-once normalization. -/
def twoPairFlexibleLeafWin (root path : Restriction 4) : Bool :=
  (List.ofFn twoPairLocalRestriction).any fun tau =>
    twoPairRestrictionExtendsB root tau && twoPairRestrictionExtendsB tau path &&
      twoPairRootShallow tau

/-- Finite query game with the exact arbitrary-leaf freedom permitted by `CommonShallowAt`. -/
def twoPairFlexibleQueryWin (root : Restriction 4) : Nat → Restriction 4 → Bool
  | 0, path => twoPairFlexibleLeafWin root path
  | k + 1, path => twoPairFlexibleLeafWin root path ||
      ((List.ofFn id : List (Fin 4)).any fun i => decide (path i = none) &&
        twoPairFlexibleQueryWin root k (fixVar path i false) &&
        twoPairFlexibleQueryWin root k (fixVar path i true))

/-- Base-three digit of one local coordinate state. -/
def twoPairRestrictionDigit : Option Bool → Nat
  | none => 0
  | some false => 1
  | some true => 2

/-- A compact base-three code for an arbitrary four-coordinate restriction. -/
def twoPairRestrictionCode (rho : Restriction 4) : Fin 81 :=
  ⟨twoPairRestrictionDigit (rho 0) + 3 * twoPairRestrictionDigit (rho 1) +
    9 * twoPairRestrictionDigit (rho 2) + 27 * twoPairRestrictionDigit (rho 3), by
    have hd (i : Fin 4) : twoPairRestrictionDigit (rho i) ≤ 2 := by
      cases h : rho i with
      | none => simp [twoPairRestrictionDigit]
      | some b => cases b <;> simp [twoPairRestrictionDigit]
    have h0 := hd 0
    have h1 := hd 1
    have h2 := hd 2
    have h3 := hd 3
    omega⟩

/-- Base-three decoding enumerates every local restriction. -/
theorem twoPairLocalRestriction_code (rho : Restriction 4) :
    twoPairLocalRestriction (twoPairRestrictionCode rho) = rho := by
  funext i
  generalize h0 : rho 0 = x0
  generalize h1 : rho 1 = x1
  generalize h2 : rho 2 = x2
  generalize h3 : rho 3 = x3
  fin_cases i <;> fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;>
    simp_all [twoPairLocalRestriction, twoPairRestrictionCode,
      twoPairRestrictionDigit, twoPairLocalDigitState]

/-- The executable extension test agrees with the propositional relation. -/
theorem twoPairRestrictionExtendsB_eq_true {rho tau : Restriction 4} :
    twoPairRestrictionExtendsB rho tau = true ↔ RestrictionExtends rho tau := by
  rw [twoPairRestrictionExtendsB, List.all_eq_true]
  constructor
  · intro h i b hi
    simpa [hi] using h i (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h i _hi
    cases hi : rho i with
    | none => simp
    | some b => simpa [hi] using h i b hi

/-- The total assignment obtained from a restriction extends it. -/
theorem extends_getD {n : ℕ} (rho : Restriction n) :
    Rung4Restriction.Extends rho (fun i => (rho i).getD false) := by
  intro i b hi
  simp [hi]

/-- If one fixed leaf payload agrees with every assignment extending a path, it cannot fix a
coordinate left live by that path.  This is the structural fact that replaces the false canonical
depth monotonicity route above. -/
theorem restrictionExtends_path_of_agrees_everywhere {n : ℕ}
    {path tau : Restriction n}
    (hagree : ∀ x : Fin n → Bool, Rung4Restriction.Extends path x →
      Rung4Restriction.Extends tau x) :
    RestrictionExtends tau path := by
  intro i b htau
  cases hpath : path i with
  | some c =>
      have hx := hagree (fun j => (path j).getD false) (extends_getD path)
      have hcb : c = b := by
        have := hx i b htau
        simpa [hpath] using this
      simpa [hcb] using hpath
  | none =>
      let x : Fin n → Bool := fun j => if j = i then !b else (path j).getD false
      have hx : Rung4Restriction.Extends path x := by
        intro j c hj
        have hji : j ≠ i := by
          intro h
          subst j
          rw [hpath] at hj
          simp at hj
        simp [x, hji, hj]
      have hcontra := hagree x hx i b htau
      have hxi : x i = !b := by simp [x]
      rw [hxi] at hcontra
      cases b <;> simp at hcontra

/-- A flexible-game win remains a win when one more query is allowed. -/
theorem twoPairFlexibleQueryWin_succ {root path : Restriction 4} : ∀ k,
    twoPairFlexibleQueryWin root k path = true →
      twoPairFlexibleQueryWin root (k + 1) path = true := by
  intro k
  induction k generalizing path with
  | zero =>
      intro hwin
      simp only [twoPairFlexibleQueryWin, Bool.or_eq_true]
      exact Or.inl hwin
  | succ k ih =>
      simp only [twoPairFlexibleQueryWin, Bool.or_eq_true]
      rintro (hleaf | hquery)
      · exact Or.inl hleaf
      · right
        rw [List.any_eq_true] at hquery ⊢
        obtain ⟨i, hi, hpred⟩ := hquery
        refine ⟨i, hi, ?_⟩
        simp only [Bool.and_eq_true] at hpred ⊢
        exact ⟨⟨hpred.1.1, ih hpred.1.2⟩, ih hpred.2⟩

/-- Monotonicity of the flexible query budget. -/
theorem twoPairFlexibleQueryWin_mono {root path : Restriction 4} {k l : Nat}
    (hkl : k ≤ l) (hwin : twoPairFlexibleQueryWin root k path = true) :
    twoPairFlexibleQueryWin root l path = true := by
  induction l generalizing k with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      exact hwin
  | succ l ih =>
      by_cases hk : k = l + 1
      · subst k
        exact hwin
      · apply twoPairFlexibleQueryWin_succ l
        exact ih (by omega) hwin

/-- Structural completeness of the arbitrary-leaf game.  After resolving repeated or already
fixed queries, every common tree contributes either a legal flexible leaf or one fresh query; the
game budget is bounded by the original tree depth. -/
theorem twoPairFlexibleQueryWin_of_tree (root path : Restriction 4)
    (trunk : CommonTree 4 (Restriction 4))
    (hroot : RestrictionExtends root path)
    (hleaf : ∀ x : Fin 4 → Bool, Rung4Restriction.Extends path x →
      RestrictionExtends root (CommonTree.run trunk x) ∧
      Rung4Restriction.Extends (CommonTree.run trunk x) x ∧
      ∀ g, (canonicalDT (twoPairPolarityFamily g) 4
        (CommonTree.run trunk x)).depth ≤ 1) :
    twoPairFlexibleQueryWin root (CommonTree.depth trunk) path = true := by
  induction trunk generalizing path with
  | leaf tau =>
      have hx := extends_getD path
      have hdata := hleaf (fun i => (path i).getD false) hx
      have htauPath : RestrictionExtends tau path :=
        restrictionExtends_path_of_agrees_everywhere (fun x hx => (hleaf x hx).2.1)
      simp only [CommonTree.depth, twoPairFlexibleQueryWin, twoPairFlexibleLeafWin]
      rw [List.any_eq_true]
      refine ⟨tau, List.mem_ofFn.mpr ⟨twoPairRestrictionCode tau,
        twoPairLocalRestriction_code tau⟩, ?_⟩
      simp only [Bool.and_eq_true,
        twoPairRestrictionExtendsB_eq_true, twoPairRootShallow, decide_eq_true_eq]
      refine ⟨⟨hdata.1, htauPath⟩, ?_⟩
      exact ⟨hdata.2.2 (0 : Fin 2), hdata.2.2 (1 : Fin 2)⟩
  | query i lo hi ihlo ihhi =>
      cases hpath : path i with
      | none =>
          have hrootLo : RestrictionExtends root (fixVar path i false) := by
            intro j b hj
            have hp := hroot j b hj
            by_cases hji : j = i
            · subst j; rw [hpath] at hp; contradiction
            · simpa [fixVar, Function.update_of_ne hji] using hp
          have hrootHi : RestrictionExtends root (fixVar path i true) := by
            intro j b hj
            have hp := hroot j b hj
            by_cases hji : j = i
            · subst j; rw [hpath] at hp; contradiction
            · simpa [fixVar, Function.update_of_ne hji] using hp
          have hlo := ihlo (fixVar path i false) hrootLo (fun x hx => by
            have hrun : CommonTree.run (CommonTree.query i lo hi) x =
                CommonTree.run lo x := by
              have := hx i false (by simp [fixVar])
              simp [CommonTree.run, this]
            have hxPath : Rung4Restriction.Extends path x := by
              intro j b hj
              exact hx j b (by
                by_cases hji : j = i
                · subst j; rw [hpath] at hj; contradiction
                · simpa [fixVar, Function.update_of_ne hji] using hj)
            simpa [hrun] using hleaf x hxPath)
          have hhi := ihhi (fixVar path i true) hrootHi (fun x hx => by
            have hrun : CommonTree.run (CommonTree.query i lo hi) x =
                CommonTree.run hi x := by
              have := hx i true (by simp [fixVar])
              simp [CommonTree.run, this]
            have hxPath : Rung4Restriction.Extends path x := by
              intro j b hj
              exact hx j b (by
                by_cases hji : j = i
                · subst j; rw [hpath] at hj; contradiction
                · simpa [fixVar, Function.update_of_ne hji] using hj)
            simpa [hrun] using hleaf x hxPath)
          simp only [CommonTree.depth, twoPairFlexibleQueryWin, Bool.or_eq_true]
          right
          rw [List.any_eq_true]
          refine ⟨i, List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq, hpath, true_and]
          exact ⟨twoPairFlexibleQueryWin_mono (Nat.le_max_left _ _) hlo,
            twoPairFlexibleQueryWin_mono (Nat.le_max_right _ _) hhi⟩
      | some b =>
          have hchild : twoPairFlexibleQueryWin root
              (if b then CommonTree.depth hi else CommonTree.depth lo) path = true := by
            cases b
            · apply ihlo path hroot
              intro x hx
              have hxi := hx i false hpath
              simpa [CommonTree.run, hxi] using hleaf x hx
            · apply ihhi path hroot
              intro x hx
              have hxi := hx i true hpath
              simpa [CommonTree.run, hxi] using hleaf x hx
          apply twoPairFlexibleQueryWin_mono _ hchild
          cases b <;> simp only [Bool.false_eq_true, if_false, if_true, CommonTree.depth]
          · omega
          · omega

/-- Every semantic common-shallow certificate for the two-pair gadget is recognized by the
flexible finite query game at the same budget. -/
theorem twoPairCommonShallowAt_implies_flexibleQueryWin {rho : Restriction 4} {k : Nat}
    (h : CommonShallowAt twoPairPolarityFamily 4 rho k 1) :
    twoPairFlexibleQueryWin rho k rho = true := by
  obtain ⟨trunk, hdepth, hleaf⟩ := h
  exact twoPairFlexibleQueryWin_mono hdepth
    (twoPairFlexibleQueryWin_of_tree rho rho trunk (by intro i b hi; exact hi) hleaf)

/-- A winning flexible leaf is already a depth-zero common trunk. -/
theorem twoPairFlexibleLeafWin_sound (root path : Restriction 4)
    (hwin : twoPairFlexibleLeafWin root path = true) :
    ∃ trunk : CommonTree 4 (Restriction 4),
      CommonTree.depth trunk = 0 ∧
      ∀ x : Fin 4 → Bool, Rung4Restriction.Extends path x →
        RestrictionExtends root (CommonTree.run trunk x) ∧
        Rung4Restriction.Extends (CommonTree.run trunk x) x ∧
        ∀ g, (canonicalDT (twoPairPolarityFamily g) 4
          (CommonTree.run trunk x)).depth ≤ 1 := by
  simp only [twoPairFlexibleLeafWin] at hwin
  rw [List.any_eq_true] at hwin
  obtain ⟨tau, _htau, hdata⟩ := hwin
  simp only [Bool.and_eq_true, twoPairRestrictionExtendsB_eq_true,
    twoPairRootShallow, decide_eq_true_eq] at hdata
  refine ⟨CommonTree.leaf tau, rfl, ?_⟩
  intro x hx
  refine ⟨hdata.1.1, ?_, fun g => ?_⟩
  · intro i b hi
    exact hx i b (hdata.1.2 i b hi)
  · fin_cases g
    · exact hdata.2.1
    · exact hdata.2.2

/-- Conversely, a flexible-game certificate assembles into a common trunk.  The more general path
form records the invariant needed by recursive children. -/
theorem twoPairFlexibleQueryWin_sound_aux (root path : Restriction 4) : ∀ k,
    RestrictionExtends root path → twoPairFlexibleQueryWin root k path = true →
      ∃ trunk : CommonTree 4 (Restriction 4),
        CommonTree.depth trunk ≤ k ∧
        ∀ x : Fin 4 → Bool, Rung4Restriction.Extends path x →
          RestrictionExtends root (CommonTree.run trunk x) ∧
          Rung4Restriction.Extends (CommonTree.run trunk x) x ∧
          ∀ g, (canonicalDT (twoPairPolarityFamily g) 4
            (CommonTree.run trunk x)).depth ≤ 1 := by
  intro k
  induction k generalizing path with
  | zero =>
      intro hroot hwin
      obtain ⟨trunk, hdepth, hleaf⟩ := twoPairFlexibleLeafWin_sound root path hwin
      exact ⟨trunk, hdepth.le, hleaf⟩
  | succ k ih =>
      intro hroot hwin
      simp only [twoPairFlexibleQueryWin, Bool.or_eq_true] at hwin
      rcases hwin with hleaf | hquery
      · obtain ⟨trunk, hdepth, hrun⟩ := twoPairFlexibleLeafWin_sound root path hleaf
        exact ⟨trunk, by omega, hrun⟩
      · rw [List.any_eq_true] at hquery
        obtain ⟨i, _hi, hpred⟩ := hquery
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred
        have hfree : path i = none := hpred.1.1
        have hrootBit (bit : Bool) : RestrictionExtends root (fixVar path i bit) := by
          intro j b hj
          have hp := hroot j b hj
          by_cases hji : j = i
          · subst j
            rw [hfree] at hp
            contradiction
          · simpa [fixVar, Function.update_of_ne hji] using hp
        obtain ⟨lo, hloDepth, hloLeaf⟩ := ih (fixVar path i false)
          (hrootBit false) hpred.1.2
        obtain ⟨hi, hhiDepth, hhiLeaf⟩ := ih (fixVar path i true)
          (hrootBit true) hpred.2
        refine ⟨CommonTree.query i lo hi, ?_, ?_⟩
        · simp only [CommonTree.depth]
          omega
        · intro x hx
          cases hxi : x i with
          | false =>
              have hxlo : Rung4Restriction.Extends (fixVar path i false) x :=
                extends_fixVar hx hxi
              simpa [CommonTree.run, hxi] using hloLeaf x hxlo
          | true =>
              have hxhi : Rung4Restriction.Extends (fixVar path i true) x :=
                extends_fixVar hx hxi
              simpa [CommonTree.run, hxi] using hhiLeaf x hxhi

/-- The flexible finite game and semantic common-shallow certificates coincide pointwise. -/
theorem twoPairFlexibleQueryWin_iff_commonShallowAt (rho : Restriction 4) (k : Nat) :
    twoPairFlexibleQueryWin rho k rho = true ↔
      CommonShallowAt twoPairPolarityFamily 4 rho k 1 := by
  constructor
  · intro hwin
    obtain ⟨trunk, hdepth, hleaf⟩ := twoPairFlexibleQueryWin_sound_aux rho rho k
      (by intro i b hi; exact hi) hwin
    exact ⟨trunk, hdepth, hleaf⟩
  · exact twoPairCommonShallowAt_implies_flexibleQueryWin

/-- First winning budget for the arbitrary-leaf game. -/
def twoPairFlexibleQueryCost (rho : Restriction 4) : Nat :=
  if twoPairFlexibleQueryWin rho 0 rho then 0 else
    if twoPairFlexibleQueryWin rho 1 rho then 1 else
      if twoPairFlexibleQueryWin rho 2 rho then 2 else 3

set_option maxHeartbeats 2000000 in
/-- Despite the genuine nonmonotonicity above, exhaustive arbitrary-leaf search has the same
local cost histogram as the stricter read-once game.  A structural bridge to `CommonShallowAt`
is still required before this may be called the exact semantic minimum distribution. -/
theorem twoPairFlexibleQueryCost_multiplicity_exact :
    let costs := List.ofFn fun code : Fin 81 =>
      twoPairFlexibleQueryCost (twoPairLocalRestriction code)
    (costs.count 0, costs.count 1, costs.count 2, costs.count 3) = (56, 16, 8, 1) := by
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
/-- On all 81 roots, allowing a leaf to forget earlier query values does not change the first
winning budget through depth three. -/
theorem twoPairFlexibleQueryCost_eq_readOnceCost :
    ∀ code : Fin 81, twoPairFlexibleQueryCost (twoPairLocalRestriction code) =
      twoPairLocalQueryCost (twoPairLocalRestriction code) := by
  decide +revert

set_option maxHeartbeats 2000000 in
/-- Kernel-checked histogram of the finite query game over all `3^4 = 81` local states. -/
theorem twoPairLocalQueryCost_multiplicity_exact :
    let costs := List.ofFn fun code : Fin 81 =>
      twoPairLocalQueryCost (twoPairLocalRestriction code)
    (costs.count 0, costs.count 1, costs.count 2, costs.count 3) = (56, 16, 8, 1) := by
  decide

/-! ### Local adversary potential for the disjoint-product bridge

The exact local histogram becomes useful for ten adaptively interleaved gadgets only if one
global query can discharge at most one unit of their summed local cost.  The finite lemma below
checks the required one-step adversary property on all `81 * 4` fresh-coordinate states.  Its
quantified form then removes the base-three presentation, and the final theorem lifts it to the
sum of ten independently updated local states. -/

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
/-- At every fresh local coordinate, one Boolean child retains all but at most one unit of the
exact flexible-game cost. -/
theorem twoPairFlexibleQueryCost_fixVar_adversary_code :
    ∀ (code : Fin 81) (i : Fin 4),
      twoPairLocalRestriction code i = none →
        ∃ b, twoPairFlexibleQueryCost (twoPairLocalRestriction code) ≤
          twoPairFlexibleQueryCost (fixVar (twoPairLocalRestriction code) i b) + 1 := by
  decide +revert

/-- Presentation-free form of the local one-step adversary property. -/
theorem twoPairFlexibleQueryCost_fixVar_adversary (rho : Restriction 4) (i : Fin 4)
    (hi : rho i = none) :
    ∃ b, twoPairFlexibleQueryCost rho ≤
      twoPairFlexibleQueryCost (fixVar rho i b) + 1 := by
  have h := twoPairFlexibleQueryCost_fixVar_adversary_code
    (twoPairRestrictionCode rho) i
  rw [twoPairLocalRestriction_code] at h
  exact h hi

/-- Sum of the ten exact local semantic costs.  This is the potential that a direct-sum
normalization must compare with the depth of an arbitrarily interleaved global common trunk. -/
def twoPairTenFlexibleCost (rhos : Fin 10 → Restriction 4) : Nat :=
  ∑ g, twoPairFlexibleQueryCost (rhos g)

/-- Updating one fresh coordinate of one gadget has an adversarial branch on which the summed
ten-gadget potential falls by at most one.  Queries in different gadgets may be interleaved
arbitrarily; the other nine summands are unchanged. -/
theorem twoPairTenFlexibleCost_update_adversary (rhos : Fin 10 → Restriction 4)
    (g : Fin 10) (i : Fin 4) (hi : rhos g i = none) :
    ∃ b, twoPairTenFlexibleCost rhos ≤
      twoPairTenFlexibleCost (Function.update rhos g (fixVar (rhos g) i b)) + 1 := by
  obtain ⟨b, hb⟩ := twoPairFlexibleQueryCost_fixVar_adversary (rhos g) i hi
  refine ⟨b, ?_⟩
  have hrest :
      (∑ h ∈ Finset.univ.erase g, twoPairFlexibleQueryCost
        (Function.update rhos g (fixVar (rhos g) i b) h)) =
      ∑ h ∈ Finset.univ.erase g, twoPairFlexibleQueryCost (rhos h) := by
    apply Finset.sum_congr rfl
    intro h hh
    have hhg : h ≠ g := Finset.ne_of_mem_erase hh
    simp [Function.update, hhg]
  have hsum :
      (∑ h, twoPairFlexibleQueryCost
        (Function.update rhos g (fixVar (rhos g) i b) h)) =
      (∑ h ∈ Finset.univ.erase g, twoPairFlexibleQueryCost (rhos h)) +
        twoPairFlexibleQueryCost (fixVar (rhos g) i b) := by
    rw [← hrest, ← Finset.sum_erase_add _ _ (Finset.mem_univ g)]
    simp
  rw [twoPairTenFlexibleCost, twoPairTenFlexibleCost]
  calc
    (∑ h, twoPairFlexibleQueryCost (rhos h)) =
        (∑ h ∈ Finset.univ.erase g, twoPairFlexibleQueryCost (rhos h)) +
          twoPairFlexibleQueryCost (rhos g) := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ g)]
    _ ≤ (∑ h ∈ Finset.univ.erase g, twoPairFlexibleQueryCost (rhos h)) +
          twoPairFlexibleQueryCost (fixVar (rhos g) i b) + 1 := by omega
    _ = (∑ h, twoPairFlexibleQueryCost
          (Function.update rhos g (fixVar (rhos g) i b) h)) + 1 := by rw [hsum]

/-! ### Conditional adversary audit for arbitrary leaf payloads

The root-only potential above is sufficient for a read-once tree whose leaves retain every
queried value.  `CommonShallowAt` deliberately permits a leaf payload to omit queried values, so
the direct-sum recursion must instead keep the immutable local root separate from the accumulated
query path.  The following finite cost is the least remaining flexible-game budget for that
root/path pair. -/

/-- Least remaining flexible-game budget for an immutable root and accumulated query path. -/
def twoPairFlexibleConditionalCost (root path : Restriction 4) : Nat :=
  if twoPairFlexibleQueryWin root 0 path then 0 else
    if twoPairFlexibleQueryWin root 1 path then 1 else
      if twoPairFlexibleQueryWin root 2 path then 2 else 3

@[simp] theorem twoPairFlexibleConditionalCost_self (rho : Restriction 4) :
    twoPairFlexibleConditionalCost rho rho = twoPairFlexibleQueryCost rho := by
  rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 4000000 in
/-- Exhaustive audit of the conditional potential.  Even when an arbitrary legal leaf may omit
previous query values, querying any fresh coordinate has a Boolean branch on which the remaining
conditional cost drops by at most one. -/
theorem twoPairFlexibleConditionalCost_fixVar_adversary_code :
    ∀ (rootCode pathCode : Fin 81) (i : Fin 4),
      twoPairRestrictionExtendsB (twoPairLocalRestriction rootCode)
        (twoPairLocalRestriction pathCode) = true →
      twoPairLocalRestriction pathCode i = none →
        ∃ b, twoPairFlexibleConditionalCost
            (twoPairLocalRestriction rootCode) (twoPairLocalRestriction pathCode) ≤
          twoPairFlexibleConditionalCost (twoPairLocalRestriction rootCode)
            (fixVar (twoPairLocalRestriction pathCode) i b) + 1 := by
  decide +revert

/-- Presentation-free conditional one-step adversary property. -/
theorem twoPairFlexibleConditionalCost_fixVar_adversary
    (root path : Restriction 4) (i : Fin 4)
    (hroot : RestrictionExtends root path) (hi : path i = none) :
    ∃ b, twoPairFlexibleConditionalCost root path ≤
      twoPairFlexibleConditionalCost root (fixVar path i b) + 1 := by
  have h := twoPairFlexibleConditionalCost_fixVar_adversary_code
    (twoPairRestrictionCode root) (twoPairRestrictionCode path) i
  rw [twoPairLocalRestriction_code, twoPairLocalRestriction_code] at h
  exact h (twoPairRestrictionExtendsB_eq_true.mpr hroot) hi

/-- Sum of the ten conditional costs with immutable roots and independently accumulated paths. -/
def twoPairTenFlexibleConditionalCost (roots paths : Fin 10 → Restriction 4) : Nat :=
  ∑ g, twoPairFlexibleConditionalCost (roots g) (paths g)

@[simp] theorem twoPairTenFlexibleConditionalCost_self
    (rhos : Fin 10 → Restriction 4) :
    twoPairTenFlexibleConditionalCost rhos rhos = twoPairTenFlexibleCost rhos := by
  simp [twoPairTenFlexibleConditionalCost, twoPairTenFlexibleCost]

/-- One fresh gadget query has a branch losing at most one unit of the correct conditional
potential.  This is the additive step that remains valid when final leaf payloads omit queried
values. -/
theorem twoPairTenFlexibleConditionalCost_update_adversary
    (roots paths : Fin 10 → Restriction 4) (g : Fin 10) (i : Fin 4)
    (hroot : ∀ h, RestrictionExtends (roots h) (paths h)) (hi : paths g i = none) :
    ∃ b, twoPairTenFlexibleConditionalCost roots paths ≤
      twoPairTenFlexibleConditionalCost roots
        (Function.update paths g (fixVar (paths g) i b)) + 1 := by
  obtain ⟨b, hb⟩ := twoPairFlexibleConditionalCost_fixVar_adversary
    (roots g) (paths g) i (hroot g) hi
  refine ⟨b, ?_⟩
  have hrest :
      (∑ h ∈ Finset.univ.erase g, twoPairFlexibleConditionalCost (roots h)
        (Function.update paths g (fixVar (paths g) i b) h)) =
      ∑ h ∈ Finset.univ.erase g, twoPairFlexibleConditionalCost (roots h) (paths h) := by
    apply Finset.sum_congr rfl
    intro h hh
    have hhg : h ≠ g := Finset.ne_of_mem_erase hh
    simp [Function.update, hhg]
  have hsum :
      (∑ h, twoPairFlexibleConditionalCost (roots h)
        (Function.update paths g (fixVar (paths g) i b) h)) =
      (∑ h ∈ Finset.univ.erase g,
        twoPairFlexibleConditionalCost (roots h) (paths h)) +
        twoPairFlexibleConditionalCost (roots g) (fixVar (paths g) i b) := by
    rw [← hrest, ← Finset.sum_erase_add _ _ (Finset.mem_univ g)]
    simp
  rw [twoPairTenFlexibleConditionalCost, twoPairTenFlexibleConditionalCost]
  calc
    (∑ h, twoPairFlexibleConditionalCost (roots h) (paths h)) =
        (∑ h ∈ Finset.univ.erase g,
          twoPairFlexibleConditionalCost (roots h) (paths h)) +
          twoPairFlexibleConditionalCost (roots g) (paths g) := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ g)]
    _ ≤ (∑ h ∈ Finset.univ.erase g,
          twoPairFlexibleConditionalCost (roots h) (paths h)) +
          twoPairFlexibleConditionalCost (roots g) (fixVar (paths g) i b) + 1 := by
      omega
    _ = (∑ h, twoPairFlexibleConditionalCost (roots h)
          (Function.update paths g (fixVar (paths g) i b) h)) + 1 := by
      rw [hsum]

/-! ### A one-query mixed-branch profile

The monochromatic charging classes deliberately discard a gadget as soon as it contains fixed
values of both polarities.  The following same-clause mixed profile shows that this discarded
region is not uniformly shallow at the root.  It has an exact adaptive cost of one query. -/

/-- Opposite fixed values in the first clause, with the second clause still fully live. -/
def twoPairSameClauseMixedRestriction : Restriction 4 := fun i =>
  if i = 0 then some true else if i = 1 then some false else none

set_option maxHeartbeats 2000000 in
/-- At the mixed root, both indexed polarities have canonical depth exactly two. -/
theorem twoPairSameClauseMixedRestriction_root_depths :
    (canonicalDT (twoPairPolarityFamily 0) 4
        twoPairSameClauseMixedRestriction).depth = 2 ∧
      (canonicalDT (twoPairPolarityFamily 1) 4
        twoPairSameClauseMixedRestriction).depth = 2 := by
  decide

/-- Therefore the mixed profile is not common-shallow without spending a trunk query. -/
theorem twoPairSameClauseMixedRestriction_not_commonShallowAt_zero :
    ¬ CommonShallowAt twoPairPolarityFamily 4
      twoPairSameClauseMixedRestriction 0 1 := by
  intro h
  have hroot := h.root_shallow_of_trunkDepth_zero
  have hdepth := twoPairSameClauseMixedRestriction_root_depths.1
  have := hroot (0 : Fin 2)
  omega

/-- Querying coordinate two is sufficient on both Boolean branches: one polarity retains a
singleton residual term and the other becomes terminal.  Thus the exact mixed-profile trunk cost
is one query. -/
theorem twoPairSameClauseMixedRestriction_commonShallowAt_one :
    CommonShallowAt twoPairPolarityFamily 4
      twoPairSameClauseMixedRestriction 1 1 := by
  let trunk := queryRestrictionList twoPairSameClauseMixedRestriction [2]
  refine ⟨trunk, by simp [trunk], ?_⟩
  intro x hx
  obtain ⟨hroot, hleaf⟩ := queryRestrictionList_spec
    twoPairSameClauseMixedRestriction [2] x hx
  refine ⟨hroot, hleaf, ?_⟩
  intro g
  fin_cases g <;> cases hx2 : x 2 <;>
    simp [trunk, queryRestrictionList, hx2, twoPairPolarityFamily,
      twoPairSameClauseMixedRestriction, positiveTwoPairGate,
      negativeTwoPairGate, orderedConjunctionBlock, canonicalDT, anyTermSat,
      termSat, activeTerm, termFalsified, freeLits, Depth3.litTrue, litVar,
      litFixedVal, litFalse, litFree, fixVar, BoolDecisionTree.depth]

/-! ### Disjoint-product charging for paired polarities

The one-gadget obstruction is useful globally only after accounting for the fact that the two
polarities of one gadget share their support.  The ordinary supported-gate charging lemma cannot
be applied to the flattened polarity family because those two supports are not disjoint.  The
following wrapper charges once per underlying gadget and lets the local semantic premise choose
which polarity remains deep at the reached leaf. -/

/-- Flatten a polarity and an underlying gadget index into the exact `Fin (2 * G)` family used by
the multi-switching interface. -/
def pairedPolarityFamily {n G : ℕ}
    (gates : Fin 2 → Fin G → List (Depth3.Clause n)) :
    Fin (2 * G) → List (Depth3.Clause n) := fun idx =>
  let key : Fin 2 × Fin G := finProdFinEquiv.symm idx
  gates key.1 key.2

@[simp] theorem pairedPolarityFamily_paddedTwoPairGates (pad : ℕ) :
    pairedPolarityFamily (paddedTwoPairGates pad) = paddedTwoPairFamily pad := by
  rfl

/-- Weighted disjoint-product charging lemma for a two-polarity gadget family.  Along the
root-compatible all-true path, disjoint underlying supports ensure that distinct queries can pay
the live-coordinate deficit of at most one gadget.  If a gadget retains too many live coordinates,
the local premise may select either polarity as the deep one.

This is the paired analogue of
`supportedGates_not_commonShallowAt_of_compatible_sum_deficit`; importantly, no disjointness is
incorrectly demanded between the two polarities of the same gadget. -/
theorem pairedPolarity_not_commonShallowAt_of_compatible_sum_deficit_threshold
    {n G fuel trunkDepth liveThreshold residualDepth : ℕ}
    (gates : Fin 2 → Fin G → List (Depth3.Clause n))
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (σ : Restriction n)
    (hdeficit : trunkDepth <
      ∑ g, compatibleResidualQueryDeficit support σ liveThreshold g)
    (hdeep : ∀ (rho : Restriction n) (g : Fin G),
      (∀ i ∈ support g, rho i ≠ some false) →
      liveThreshold < (support g ∩ freeVars rho).card →
      ∃ polarity : Fin 2,
        residualDepth < (canonicalDT (gates polarity g) fuel rho).depth) :
    ¬ CommonShallowAt (pairedPolarityFamily gates) fuel σ trunkDepth residualDepth := by
  rintro ⟨trunk, htrunkDepth, hleaf⟩
  let x : Fin n → Bool := fun i => (σ i).getD true
  have hx : Rung4Restriction.Extends σ x := by
    intro i b hi
    simp [x, hi]
  let path : Finset (Fin n) := (CommonTree.queryVars trunk x).toFinset
  have hpathCard : path.card ≤ trunkDepth := by
    calc
      path.card ≤ (CommonTree.queryVars trunk x).length := List.toFinset_card_le _
      _ ≤ CommonTree.depth trunk := CommonTree.queryVars_length_le_depth trunk x
      _ ≤ trunkDepth := htrunkDepth
  obtain ⟨g, hcompat, hremain⟩ :=
    exists_compatible_liveSupport_sdiff_card_gt_of_sum_deficit
      support hpair σ path (lt_of_le_of_lt hpathCard hdeficit)
  have hfree (i : Fin n) (hiσ : σ i = none) (hi : i ∉ path) :
      CommonTree.run trunk x i = none := by
    let y : Fin n → Bool := Function.update x i (!x i)
    have hy : Rung4Restriction.Extends σ y := by
      intro j b hj
      have hji : j ≠ i := by
        intro h
        subst j
        rw [hiσ] at hj
        simp at hj
      simpa [y, Function.update_of_ne hji] using hx j b hj
    obtain ⟨_, htx, _⟩ := hleaf x hx
    obtain ⟨_, hty, _⟩ := hleaf y hy
    have hrun : CommonTree.run trunk y = CommonTree.run trunk x := by
      exact CommonTree.run_update_of_not_mem_queryVars trunk x i
        (by simpa [path] using hi)
    cases ht : CommonTree.run trunk x i with
    | none => rfl
    | some b =>
        have hbx : x i = b := htx i b ht
        have hby : y i = b := by
          apply hty i b
          simpa [hrun] using ht
        cases hxi : x i with
        | false =>
            have hbfalse : b = false := by simpa [hxi] using hbx.symm
            have hbtrue : b = true := by simpa [y, hxi] using hby.symm
            exact False.elim (Bool.false_ne_true (hbfalse.symm.trans hbtrue))
        | true =>
            have hbtrue : b = true := by simpa [hxi] using hbx.symm
            have hbfalse : b = false := by simpa [y, hxi] using hby.symm
            exact False.elim (Bool.false_ne_true (hbfalse.symm.trans hbtrue))
  obtain ⟨_, hagree, hshallow⟩ := hleaf x hx
  have hsupportNotFalse (i : Fin n) (hi : i ∈ support g) :
      CommonTree.run trunk x i ≠ some false := by
    intro hfalse
    have hxi : x i = false := hagree i false hfalse
    cases hσi : σ i with
    | none => simp [x, hσi] at hxi
    | some b =>
        cases b
        · exact hcompat i hi hσi
        · simp [x, hσi] at hxi
  have hremainingSubset : (liveSupport support σ g \ path) ⊆
      support g ∩ freeVars (CommonTree.run trunk x) := by
    intro i hi
    have hilive := (Finset.mem_sdiff.mp hi).1
    have hipath := (Finset.mem_sdiff.mp hi).2
    have hisupport := (Finset.mem_inter.mp hilive).1
    have hiσ := mem_freeVars.mp (Finset.mem_inter.mp hilive).2
    exact Finset.mem_inter.mpr ⟨hisupport, mem_freeVars.mpr (hfree i hiσ hipath)⟩
  have hfreeCard : liveThreshold <
      (support g ∩ freeVars (CommonTree.run trunk x)).card :=
    lt_of_lt_of_le hremain (Finset.card_le_card hremainingSubset)
  obtain ⟨polarity, hpolarityDeep⟩ :=
    hdeep (CommonTree.run trunk x) g hsupportNotFalse hfreeCard
  let idx : Fin (2 * G) := finProdFinEquiv (polarity, g)
  have hgateShallow := hshallow idx
  have hfamily : pairedPolarityFamily gates idx = gates polarity g := by
    simp [pairedPolarityFamily, idx]
  rw [hfamily] at hgateShallow
  exact (Nat.not_lt_of_ge hgateShallow) hpolarityDeep

/-- All-false counterpart of the paired charging lemma.  The numerical deficit is read from the
complemented root restriction, so it reuses the same verified compatible-deficit machinery and
differs only in following the all-false common-tree branch. -/
theorem pairedPolarity_not_commonShallowAt_of_false_compatible_sum_deficit_threshold
    {n G fuel trunkDepth liveThreshold residualDepth : ℕ}
    (gates : Fin 2 → Fin G → List (Depth3.Clause n))
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (σ : Restriction n)
    (hdeficit : trunkDepth <
      ∑ g, compatibleResidualQueryDeficit support (complementRestriction σ) liveThreshold g)
    (hdeep : ∀ (rho : Restriction n) (g : Fin G),
      (∀ i ∈ support g, rho i ≠ some true) →
      liveThreshold < (support g ∩ freeVars rho).card →
      ∃ polarity : Fin 2,
        residualDepth < (canonicalDT (gates polarity g) fuel rho).depth) :
    ¬ CommonShallowAt (pairedPolarityFamily gates) fuel σ trunkDepth residualDepth := by
  rintro ⟨trunk, htrunkDepth, hleaf⟩
  let x : Fin n → Bool := fun i => (σ i).getD false
  have hx : Rung4Restriction.Extends σ x := by
    intro i b hi
    simp [x, hi]
  let path : Finset (Fin n) := (CommonTree.queryVars trunk x).toFinset
  have hpathCard : path.card ≤ trunkDepth := by
    calc
      path.card ≤ (CommonTree.queryVars trunk x).length := List.toFinset_card_le _
      _ ≤ CommonTree.depth trunk := CommonTree.queryVars_length_le_depth trunk x
      _ ≤ trunkDepth := htrunkDepth
  obtain ⟨g, hcompat, hremain⟩ :=
    exists_compatible_liveSupport_sdiff_card_gt_of_sum_deficit
      support hpair (complementRestriction σ) path
        (lt_of_le_of_lt hpathCard hdeficit)
  have hfree (i : Fin n) (hiσ : σ i = none) (hi : i ∉ path) :
      CommonTree.run trunk x i = none := by
    let y : Fin n → Bool := Function.update x i (!x i)
    have hy : Rung4Restriction.Extends σ y := by
      intro j b hj
      have hji : j ≠ i := by
        intro h
        subst j
        rw [hiσ] at hj
        simp at hj
      simpa [y, Function.update_of_ne hji] using hx j b hj
    obtain ⟨_, htx, _⟩ := hleaf x hx
    obtain ⟨_, hty, _⟩ := hleaf y hy
    have hrun : CommonTree.run trunk y = CommonTree.run trunk x := by
      exact CommonTree.run_update_of_not_mem_queryVars trunk x i
        (by simpa [path] using hi)
    cases ht : CommonTree.run trunk x i with
    | none => rfl
    | some b =>
        have hbx : x i = b := htx i b ht
        have hby : y i = b := by
          apply hty i b
          simpa [hrun] using ht
        cases hxi : x i with
        | false =>
            have hbfalse : b = false := by simpa [hxi] using hbx.symm
            have hbtrue : b = true := by simpa [y, hxi] using hby.symm
            exact False.elim (Bool.false_ne_true (hbfalse.symm.trans hbtrue))
        | true =>
            have hbtrue : b = true := by simpa [hxi] using hbx.symm
            have hbfalse : b = false := by simpa [y, hxi] using hby.symm
            exact False.elim (Bool.false_ne_true (hbfalse.symm.trans hbtrue))
  obtain ⟨_, hagree, hshallow⟩ := hleaf x hx
  have hsupportNotTrue (i : Fin n) (hi : i ∈ support g) :
      CommonTree.run trunk x i ≠ some true := by
    intro htrue
    have hxi : x i = true := hagree i true htrue
    cases hσi : σ i with
    | none => simp [x, hσi] at hxi
    | some b =>
        cases b
        · simp [x, hσi] at hxi
        · apply hcompat i hi
          simp [complementRestriction, hσi]
  have hremainingSubset :
      (liveSupport support (complementRestriction σ) g \ path) ⊆
        support g ∩ freeVars (CommonTree.run trunk x) := by
    intro i hi
    have hilive := (Finset.mem_sdiff.mp hi).1
    have hipath := (Finset.mem_sdiff.mp hi).2
    have hisupport := (Finset.mem_inter.mp hilive).1
    have hicomp := mem_freeVars.mp (Finset.mem_inter.mp hilive).2
    have hiσ : σ i = none := by simpa using hicomp
    exact Finset.mem_inter.mpr ⟨hisupport, mem_freeVars.mpr (hfree i hiσ hipath)⟩
  have hfreeCard : liveThreshold <
      (support g ∩ freeVars (CommonTree.run trunk x)).card :=
    lt_of_lt_of_le hremain (Finset.card_le_card hremainingSubset)
  obtain ⟨polarity, hpolarityDeep⟩ :=
    hdeep (CommonTree.run trunk x) g hsupportNotTrue hfreeCard
  let idx : Fin (2 * G) := finProdFinEquiv (polarity, g)
  have hgateShallow := hshallow idx
  have hfamily : pairedPolarityFamily gates idx = gates polarity g := by
    simp [pairedPolarityFamily, idx]
  rw [hfamily] at hgateShallow
  exact (Nat.not_lt_of_ge hgateShallow) hpolarityDeep

/-- The original same-threshold paired charging theorem is the diagonal specialization of the
more flexible live-threshold statement. -/
theorem pairedPolarity_not_commonShallowAt_of_compatible_sum_deficit
    {n G fuel trunkDepth residualDepth : ℕ}
    (gates : Fin 2 → Fin G → List (Depth3.Clause n))
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (σ : Restriction n)
    (hdeficit : trunkDepth <
      ∑ g, compatibleResidualQueryDeficit support σ residualDepth g)
    (hdeep : ∀ (rho : Restriction n) (g : Fin G),
      (∀ i ∈ support g, rho i ≠ some false) →
      residualDepth < (support g ∩ freeVars rho).card →
      ∃ polarity : Fin 2,
        residualDepth < (canonicalDT (gates polarity g) fuel rho).depth) :
    ¬ CommonShallowAt (pairedPolarityFamily gates) fuel σ trunkDepth residualDepth :=
  pairedPolarity_not_commonShallowAt_of_compatible_sum_deficit_threshold
    gates support hpair σ hdeficit hdeep

/-- The exact partially-consumed profile criterion for the ten padded two-pair gadgets.  Unlike
the fully-live specialization below, this permits arbitrary owned coordinates to have already
been fixed.  A gadget contributes only when none of its fixed owned coordinates is false, and
then contributes its number of live owned coordinates above the threshold two.  Total compatible
deficit above ten is sufficient to defeat every depth-ten common trunk. -/
theorem paddedTwoPair_not_commonShallow_ten_of_compatible_sum_deficit (pad : ℕ)
    (σ : Restriction (pad + 40))
    (hdeficit : 10 < ∑ g,
      compatibleResidualQueryDeficit (paddedTwoPairSupport pad) σ 2 g) :
    ¬ CommonShallowAt (paddedTwoPairFamily pad) (pad + 40) σ 10 1 := by
  rw [← pairedPolarityFamily_paddedTwoPairGates]
  apply pairedPolarity_not_commonShallowAt_of_compatible_sum_deficit_threshold
    (fuel := pad + 40) (trunkDepth := 10) (liveThreshold := 2) (residualDepth := 1)
    (paddedTwoPairGates pad) (paddedTwoPairSupport pad)
    (paddedTwoPairSupport_pairwiseDisjoint pad) σ hdeficit
  intro rho g hnotFalse hfree
  refine ⟨0, ?_⟩
  change 1 < (canonicalDT (positiveTwoPairGate
    (paddedTwoPairCoord pad g 0) (paddedTwoPairCoord pad g 1)
    (paddedTwoPairCoord pad g 2) (paddedTwoPairCoord pad g 3)) (pad + 40) rho).depth
  apply positiveTwoPair_depth_ge_two_of_three_free
  · intro h
    have hk := congrArg Fin.val h
    simp [paddedTwoPairCoord] at hk
  · intro h
    have hk := congrArg Fin.val h
    simp [paddedTwoPairCoord] at hk
  · intro h
    have hk := congrArg Fin.val h
    simp [paddedTwoPairCoord] at hk
  · intro h
    have hk := congrArg Fin.val h
    simp [paddedTwoPairCoord] at hk
  · intro h
    have hk := congrArg Fin.val h
    simp [paddedTwoPairCoord] at hk
  · intro h
    have hk := congrArg Fin.val h
    simp [paddedTwoPairCoord] at hk
  · intro i hi
    apply hnotFalse i
    rw [paddedTwoPairSupport, Finset.mem_image]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨0, Finset.mem_univ _, rfl⟩
    · exact ⟨1, Finset.mem_univ _, rfl⟩
    · exact ⟨2, Finset.mem_univ _, rfl⟩
    · exact ⟨3, Finset.mem_univ _, rfl⟩
  · have hsupport : paddedTwoPairSupport pad g =
        {paddedTwoPairCoord pad g 0, paddedTwoPairCoord pad g 1,
          paddedTwoPairCoord pad g 2, paddedTwoPairCoord pad g 3} := by
      apply Finset.Subset.antisymm
      · intro i hi
        rw [paddedTwoPairSupport, Finset.mem_image] at hi
        obtain ⟨k, _, rfl⟩ := hi
        fin_cases k <;> simp
      · intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rw [paddedTwoPairSupport, Finset.mem_image]
        rcases hi with rfl | rfl | rfl | rfl
        all_goals first | exact ⟨0, Finset.mem_univ _, rfl⟩ |
          exact ⟨1, Finset.mem_univ _, rfl⟩ | exact ⟨2, Finset.mem_univ _, rfl⟩ |
          exact ⟨3, Finset.mem_univ _, rfl⟩
    rw [← hsupport]
    exact hfree
  · omega

/-- Symmetric partially-consumed profile criterion along the all-false branch.  Complementing
the root restriction converts its compatibility charge to the already audited numerical
deficit, while the negative indexed gate supplies the local depth obstruction. -/
theorem paddedTwoPair_not_commonShallow_ten_of_false_compatible_sum_deficit (pad : ℕ)
    (σ : Restriction (pad + 40))
    (hdeficit : 10 < ∑ g,
      compatibleResidualQueryDeficit (paddedTwoPairSupport pad)
        (complementRestriction σ) 2 g) :
    ¬ CommonShallowAt (paddedTwoPairFamily pad) (pad + 40) σ 10 1 := by
  rw [← pairedPolarityFamily_paddedTwoPairGates]
  apply pairedPolarity_not_commonShallowAt_of_false_compatible_sum_deficit_threshold
    (fuel := pad + 40) (trunkDepth := 10) (liveThreshold := 2) (residualDepth := 1)
    (paddedTwoPairGates pad) (paddedTwoPairSupport pad)
    (paddedTwoPairSupport_pairwiseDisjoint pad) σ hdeficit
  intro rho g hnotTrue hfree
  refine ⟨1, ?_⟩
  change 1 < (canonicalDT (negativeTwoPairGate
    (paddedTwoPairCoord pad g 0) (paddedTwoPairCoord pad g 1)
    (paddedTwoPairCoord pad g 2) (paddedTwoPairCoord pad g 3)) (pad + 40) rho).depth
  apply negativeTwoPair_depth_ge_two_of_three_free
  · intro h
    have hk := congrArg Fin.val h
    simp [paddedTwoPairCoord] at hk
  · intro h
    have hk := congrArg Fin.val h
    simp [paddedTwoPairCoord] at hk
  · intro h
    have hk := congrArg Fin.val h
    simp [paddedTwoPairCoord] at hk
  · intro h
    have hk := congrArg Fin.val h
    simp [paddedTwoPairCoord] at hk
  · intro h
    have hk := congrArg Fin.val h
    simp [paddedTwoPairCoord] at hk
  · intro h
    have hk := congrArg Fin.val h
    simp [paddedTwoPairCoord] at hk
  · intro i hi
    apply hnotTrue i
    rw [paddedTwoPairSupport, Finset.mem_image]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨0, Finset.mem_univ _, rfl⟩
    · exact ⟨1, Finset.mem_univ _, rfl⟩
    · exact ⟨2, Finset.mem_univ _, rfl⟩
    · exact ⟨3, Finset.mem_univ _, rfl⟩
  · have hsupport : paddedTwoPairSupport pad g =
        {paddedTwoPairCoord pad g 0, paddedTwoPairCoord pad g 1,
          paddedTwoPairCoord pad g 2, paddedTwoPairCoord pad g 3} := by
      apply Finset.Subset.antisymm
      · intro i hi
        rw [paddedTwoPairSupport, Finset.mem_image] at hi
        obtain ⟨k, _, rfl⟩ := hi
        fin_cases k <;> simp
      · intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rw [paddedTwoPairSupport, Finset.mem_image]
        rcases hi with rfl | rfl | rfl | rfl
        all_goals first | exact ⟨0, Finset.mem_univ _, rfl⟩ |
          exact ⟨1, Finset.mem_univ _, rfl⟩ | exact ⟨2, Finset.mem_univ _, rfl⟩ |
          exact ⟨3, Finset.mem_univ _, rfl⟩
    rw [← hsupport]
    exact hfree
  · omega

/-- Every restriction leaving all forty gadget coordinates live defeats a depth-ten common trunk,
independently of the Boolean values fixed on the padding.  This is the profile-parametric form of
the padded-root obstruction. -/
theorem paddedTwoPair_not_commonShallow_ten_of_support_free (pad : ℕ)
    (σ : Restriction (pad + 40))
    (hsupportFree : ∀ g k, σ (paddedTwoPairCoord pad g k) = none) :
    ¬ CommonShallowAt (paddedTwoPairFamily pad) (pad + 40) σ 10 1 := by
  apply paddedTwoPair_not_commonShallow_ten_of_compatible_sum_deficit pad σ
  classical
  have hlive (g : Fin 10) :
      paddedTwoPairSupport pad g ∩ freeVars σ = paddedTwoPairSupport pad g := by
    apply Finset.inter_eq_left.mpr
    intro i hi
    rw [paddedTwoPairSupport, Finset.mem_image] at hi
    obtain ⟨k, _, rfl⟩ := hi
    exact mem_freeVars.mpr (hsupportFree g k)
  have hcompat (g : Fin 10) :
      supportTrueCompatible (paddedTwoPairSupport pad) σ g := by
    intro i hi hfalse
    rw [paddedTwoPairSupport, Finset.mem_image] at hi
    obtain ⟨k, _, rfl⟩ := hi
    cases (hsupportFree g k).symm.trans hfalse
  have hdeficit (g : Fin 10) :
      compatibleResidualQueryDeficit (paddedTwoPairSupport pad) σ 2 g = 2 := by
    rw [compatibleResidualQueryDeficit, if_pos (hcompat g), residualQueryDeficit,
      liveSupport, hlive, paddedTwoPairSupport_card]
  norm_num [hdeficit]

/-- The padded forty-live root is the all-false-padding specialization of the profile theorem. -/
theorem paddedTwoPairRestriction_not_commonShallow_ten (pad : ℕ) :
    ¬ CommonShallowAt (paddedTwoPairFamily pad) (pad + 40)
      (paddedRectangularRestriction pad 10 4) 10 1 := by
  apply paddedTwoPair_not_commonShallow_ten_of_support_free
  intro g k
  rw [show paddedTwoPairCoord pad g k =
      Fin.natAdd pad (finProdFinEquiv (g, k)) by
    apply Fin.ext
    simp [paddedTwoPairCoord, finProdFinEquiv]
    omega]
  exact paddedRectangularRestriction_target_free (pad := pad) (key := (g, k))

/-- Hence the exact padded forty-live root is a member of the semantic bad event. -/
theorem paddedTwoPairRestriction_mem_bad_ten (pad : ℕ) :
    paddedRectangularRestriction pad 10 4 ∈
      commonShallowBad (paddedTwoPairFamily pad) (pad + 40) 40 10 1 := by
  rw [mem_commonShallowBad]
  exact ⟨by simpa using
    (stars_paddedRectangularRestriction (pad := pad) (G := 10) (m := 4)),
    paddedTwoPairRestriction_not_commonShallow_ten pad⟩

/-- The full fixed-shell class certified by the compatible-deficit charge.  It includes partially
consumed gadget supports; no owned-coordinate profile is discarded except by the exact semantic
conditions used by the charging proof. -/
noncomputable def paddedTwoPairCompatibleDeficitProfiles (pad : ℕ) :
    Finset (Restriction (pad + 40)) :=
  Finset.univ.filter fun σ =>
    stars σ = 40 ∧ 10 < ∑ g,
      compatibleResidualQueryDeficit (paddedTwoPairSupport pad) σ 2 g

/-- Every partially-consumed profile accepted by the exact compatible-deficit predicate is a
member of the semantic depth-ten bad event. -/
theorem paddedTwoPairCompatibleDeficitProfiles_subset_bad (pad : ℕ) :
    paddedTwoPairCompatibleDeficitProfiles pad ⊆
      commonShallowBad (paddedTwoPairFamily pad) (pad + 40) 40 10 1 := by
  classical
  intro σ hσ
  rw [paddedTwoPairCompatibleDeficitProfiles, Finset.mem_filter] at hσ
  rw [mem_commonShallowBad]
  exact ⟨hσ.2.1,
    paddedTwoPair_not_commonShallow_ten_of_compatible_sum_deficit pad σ hσ.2.2⟩

/-- The symmetric fixed-shell class certified along the all-false branch.  Its charge is the
same compatible deficit evaluated after complementing every fixed Boolean value. -/
noncomputable def paddedTwoPairFalseCompatibleDeficitProfiles (pad : ℕ) :
    Finset (Restriction (pad + 40)) :=
  Finset.univ.filter fun σ =>
    stars σ = 40 ∧ 10 < ∑ g,
      compatibleResidualQueryDeficit (paddedTwoPairSupport pad)
        (complementRestriction σ) 2 g

/-- Every profile accepted by the symmetric all-false certificate is semantically bad. -/
theorem paddedTwoPairFalseCompatibleDeficitProfiles_subset_bad (pad : ℕ) :
    paddedTwoPairFalseCompatibleDeficitProfiles pad ⊆
      commonShallowBad (paddedTwoPairFamily pad) (pad + 40) 40 10 1 := by
  classical
  intro σ hσ
  rw [paddedTwoPairFalseCompatibleDeficitProfiles, Finset.mem_filter] at hσ
  rw [mem_commonShallowBad]
  exact ⟨hσ.2.1,
    paddedTwoPair_not_commonShallow_ten_of_false_compatible_sum_deficit
      pad σ hσ.2.2⟩

/-- Restriction complementation identifies the all-false class with the all-true class exactly. -/
theorem paddedTwoPair_complement_mem_compatible_iff (pad : ℕ)
    (σ : Restriction (pad + 40)) :
    complementRestriction σ ∈ paddedTwoPairCompatibleDeficitProfiles pad ↔
      σ ∈ paddedTwoPairFalseCompatibleDeficitProfiles pad := by
  simp only [paddedTwoPairCompatibleDeficitProfiles,
    paddedTwoPairFalseCompatibleDeficitProfiles, Finset.mem_filter, Finset.mem_univ,
    true_and, stars_complementRestriction, complementRestriction_involutive]

/-- Therefore the symmetric profile class has exactly the already audited one-sided size. -/
theorem paddedTwoPairFalseCompatibleDeficitProfiles_card (pad : ℕ) :
    (paddedTwoPairFalseCompatibleDeficitProfiles pad).card =
      (paddedTwoPairCompatibleDeficitProfiles pad).card := by
  classical
  apply Finset.card_bij'
      (fun σ _ => complementRestriction σ)
      (fun σ _ => complementRestriction σ)
  · intro σ hσ
    exact (paddedTwoPair_complement_mem_compatible_iff pad σ).mpr hσ
  · intro σ hσ
    apply (paddedTwoPair_complement_mem_compatible_iff pad
      (complementRestriction σ)).mp
    simpa using hσ
  · intro σ hσ
    exact complementRestriction_involutive σ
  · intro σ hσ
    exact complementRestriction_involutive σ

/-! ### Exact one-gadget profile partition

The global coefficient calculation has only six local states.  We record them on the canonical
four-coordinate support before transporting them to the ten padded copies.  A fixed false value
kills compatibility and hence contributes zero deficit; otherwise the deficit is `stars - 2`.
The multiplicities below include every choice of which coordinates are live and every Boolean
value on the fixed coordinates. -/

/-- The threshold-two compatible deficit of one canonical four-coordinate gadget. -/
def twoPairLocalCompatibleDeficit (ρ : Restriction 4) : ℕ :=
  if ∀ i, ρ i ≠ some false then stars ρ - 2 else 0

/-- Restrictions of one gadget with a specified live count and compatible deficit. -/
def twoPairLocalProfileClass (q d : ℕ) : Finset (Restriction 4) :=
  Finset.univ.filter fun ρ =>
    stars ρ = q ∧ twoPairLocalCompatibleDeficit ρ = d

/-- The multiplicity used by the ten-fold convolution. -/
def twoPairLocalProfileMultiplicity (q d : ℕ) : ℕ :=
  (twoPairLocalProfileClass q d).card

/-- The exact six-state local table:

```text
(live, deficit, multiplicity)
  (0, 0, 16), (1, 0, 32), (2, 0, 24),
  (3, 0,  4), (3, 1,  4), (4, 2,  1).
```

These multiplicities sum to `81 = 3^4`, the number of restrictions on four coordinates. -/
theorem twoPairLocalProfileMultiplicity_exact :
    twoPairLocalProfileMultiplicity 0 0 = 16 ∧
      twoPairLocalProfileMultiplicity 1 0 = 32 ∧
      twoPairLocalProfileMultiplicity 2 0 = 24 ∧
      twoPairLocalProfileMultiplicity 3 0 = 4 ∧
      twoPairLocalProfileMultiplicity 3 1 = 4 ∧
      twoPairLocalProfileMultiplicity 4 2 = 1 := by
  decide

set_option maxRecDepth 100000 in
/-- The six rows above are exhaustive, not merely six sampled coefficients. -/
theorem twoPairLocalProfileClass_partition :
    twoPairLocalProfileClass 0 0 ∪
      twoPairLocalProfileClass 1 0 ∪
      twoPairLocalProfileClass 2 0 ∪
      twoPairLocalProfileClass 3 0 ∪
      twoPairLocalProfileClass 3 1 ∪
      twoPairLocalProfileClass 4 2 = Finset.univ := by
  decide

/-! ### Exact ten-fold deficit convolution

For the immediate quantitative decision, the live-coordinate grading can be discarded.  Summing
the six proved rows by deficit gives multiplicities `76`, `4`, and `1` at deficits zero, one, and
two.  The following recurrence is therefore the exact coefficient recurrence for
`(76 + 4*y + y^2)^g`.  The finer bivariate transport remains a separate structural task. -/

/-- The `g`-fold convolution of the local deficit distribution `(76,4,1)`. -/
def twoPairDeficitConvolution : ℕ → ℕ → ℕ
  | 0, d => if d = 0 then 1 else 0
  | g + 1, d =>
      76 * twoPairDeficitConvolution g d +
      (if 1 ≤ d then 4 * twoPairDeficitConvolution g (d - 1) else 0) +
      (if 2 ≤ d then twoPairDeficitConvolution g (d - 2) else 0)

/-- The local table really does aggregate to 76 zero-deficit states, four one-deficit states,
and one two-deficit state. -/
theorem twoPairLocalDeficitMultiplicity_exact :
    (∑ q ∈ Finset.range 5, twoPairLocalProfileMultiplicity q 0) = 76 ∧
      (∑ q ∈ Finset.range 5, twoPairLocalProfileMultiplicity q 1) = 4 ∧
      (∑ q ∈ Finset.range 5, twoPairLocalProfileMultiplicity q 2) = 1 := by
  decide

/-- Exact ten-fold coefficient tail above the depth-ten trunk budget. -/
def twoPairTenFoldDeficitTail : ℕ :=
  ∑ d ∈ (Finset.range 21).filter (fun d => 10 < d),
    twoPairDeficitConvolution 10 d

/-- Exactly 333,840,111,649 of the `81^10` local gadget profiles have compatible deficit at
least eleven. -/
theorem twoPairTenFoldDeficitTail_exact :
    twoPairTenFoldDeficitTail = 333840111649 := by
  decide

/-! ### Deficit-to-support transport

The coarse arithmetic certificate below uses only one fact from the live-coordinate grading:
total compatible deficit at least eleven forces at least twenty-three live coordinates in the
ten owned supports.  This follows without enumerating the six local states.  On a support of
cardinality four, twice the threshold-two deficit is at most the live-support cardinality; the
ten disjoint supports then turn the sum of those cardinalities into the cardinality of their
union. -/

/-- Pull one padded gadget back to the canonical four-coordinate restriction used by the exact
local profile table. -/
def paddedTwoPairLocalRestriction (pad : ℕ) (σ : Restriction (pad + 40))
    (g : Fin 10) : Restriction 4 :=
  fun k => σ (paddedTwoPairCoord pad g k)

set_option maxHeartbeats 4000000 in
/-- A residual-depth-one bound for the positive padded gadget transports to its four-coordinate
pullback once fuel exposes at least the first four canonical queries. -/
theorem positiveTwoPair_local_depth_le_one_of_padded (pad : ℕ)
    (σ : Restriction (pad + 40)) (g : Fin 10) (fuel : ℕ) (hfuel : 4 ≤ fuel)
    (hpadded : (canonicalDT (positiveTwoPairGate
      (paddedTwoPairCoord pad g 0) (paddedTwoPairCoord pad g 1)
      (paddedTwoPairCoord pad g 2) (paddedTwoPairCoord pad g 3)) fuel σ).depth ≤ 1) :
    (canonicalDT (positiveTwoPairGate (0 : Fin 4) 1 2 3) 4
      (paddedTwoPairLocalRestriction pad σ g)).depth ≤ 1 := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  rw [Nat.add_comm 4 extra] at hpadded
  generalize h0 : σ (paddedTwoPairCoord pad g 0) = o0
  generalize h1 : σ (paddedTwoPairCoord pad g 1) = o1
  generalize h2 : σ (paddedTwoPairCoord pad g 2) = o2
  generalize h3 : σ (paddedTwoPairCoord pad g 3) = o3
  have h01 : paddedTwoPairCoord pad g 0 ≠ paddedTwoPairCoord pad g 1 := by
    intro h
    have := congrArg Prod.snd ((@paddedTwoPairCoord_injective pad (g, 0) (g, 1)) h)
    simp at this
  have h02 : paddedTwoPairCoord pad g 0 ≠ paddedTwoPairCoord pad g 2 := by
    intro h
    have := congrArg Prod.snd ((@paddedTwoPairCoord_injective pad (g, 0) (g, 2)) h)
    simp at this
  have h03 : paddedTwoPairCoord pad g 0 ≠ paddedTwoPairCoord pad g 3 := by
    intro h
    have := congrArg Prod.snd ((@paddedTwoPairCoord_injective pad (g, 0) (g, 3)) h)
    simp at this
  have h12 : paddedTwoPairCoord pad g 1 ≠ paddedTwoPairCoord pad g 2 := by
    intro h
    have := congrArg Prod.snd ((@paddedTwoPairCoord_injective pad (g, 1) (g, 2)) h)
    simp at this
  have h13 : paddedTwoPairCoord pad g 1 ≠ paddedTwoPairCoord pad g 3 := by
    intro h
    have := congrArg Prod.snd ((@paddedTwoPairCoord_injective pad (g, 1) (g, 3)) h)
    simp at this
  have h23 : paddedTwoPairCoord pad g 2 ≠ paddedTwoPairCoord pad g 3 := by
    intro h
    have := congrArg Prod.snd ((@paddedTwoPairCoord_injective pad (g, 2) (g, 3)) h)
    simp at this
  fin_cases o0 <;> fin_cases o1 <;> fin_cases o2 <;> fin_cases o3 <;>
    simp [paddedTwoPairLocalRestriction, positiveTwoPairGate, orderedConjunctionBlock,
      canonicalDT, anyTermSat, termSat, activeTerm, termFalsified, freeLits,
      Depth3.litTrue, litVar, litFixedVal, litFalse, litFree, fixVar,
      BoolDecisionTree.depth, positiveTwoPair_depth_eq_zero_of_four_fixed,
      h0, h1, h2, h3, h01, h02, h03, h12, h13, h23,
      Ne.symm h01, Ne.symm h02, Ne.symm h03, Ne.symm h12, Ne.symm h13, Ne.symm h23]
      at hpadded ⊢ <;> omega

set_option maxHeartbeats 4000000 in
/-- The corresponding residual-depth-one transport for the negative padded gadget. -/
theorem negativeTwoPair_local_depth_le_one_of_padded (pad : ℕ)
    (σ : Restriction (pad + 40)) (g : Fin 10) (fuel : ℕ) (hfuel : 4 ≤ fuel)
    (hpadded : (canonicalDT (negativeTwoPairGate
      (paddedTwoPairCoord pad g 0) (paddedTwoPairCoord pad g 1)
      (paddedTwoPairCoord pad g 2) (paddedTwoPairCoord pad g 3)) fuel σ).depth ≤ 1) :
    (canonicalDT (negativeTwoPairGate (0 : Fin 4) 1 2 3) 4
      (paddedTwoPairLocalRestriction pad σ g)).depth ≤ 1 := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  rw [Nat.add_comm 4 extra] at hpadded
  generalize h0 : σ (paddedTwoPairCoord pad g 0) = o0
  generalize h1 : σ (paddedTwoPairCoord pad g 1) = o1
  generalize h2 : σ (paddedTwoPairCoord pad g 2) = o2
  generalize h3 : σ (paddedTwoPairCoord pad g 3) = o3
  have h01 : paddedTwoPairCoord pad g 0 ≠ paddedTwoPairCoord pad g 1 := by
    intro h
    have := congrArg Prod.snd ((@paddedTwoPairCoord_injective pad (g, 0) (g, 1)) h)
    simp at this
  have h02 : paddedTwoPairCoord pad g 0 ≠ paddedTwoPairCoord pad g 2 := by
    intro h
    have := congrArg Prod.snd ((@paddedTwoPairCoord_injective pad (g, 0) (g, 2)) h)
    simp at this
  have h03 : paddedTwoPairCoord pad g 0 ≠ paddedTwoPairCoord pad g 3 := by
    intro h
    have := congrArg Prod.snd ((@paddedTwoPairCoord_injective pad (g, 0) (g, 3)) h)
    simp at this
  have h12 : paddedTwoPairCoord pad g 1 ≠ paddedTwoPairCoord pad g 2 := by
    intro h
    have := congrArg Prod.snd ((@paddedTwoPairCoord_injective pad (g, 1) (g, 2)) h)
    simp at this
  have h13 : paddedTwoPairCoord pad g 1 ≠ paddedTwoPairCoord pad g 3 := by
    intro h
    have := congrArg Prod.snd ((@paddedTwoPairCoord_injective pad (g, 1) (g, 3)) h)
    simp at this
  have h23 : paddedTwoPairCoord pad g 2 ≠ paddedTwoPairCoord pad g 3 := by
    intro h
    have := congrArg Prod.snd ((@paddedTwoPairCoord_injective pad (g, 2) (g, 3)) h)
    simp at this
  fin_cases o0 <;> fin_cases o1 <;> fin_cases o2 <;> fin_cases o3 <;>
    simp [paddedTwoPairLocalRestriction, negativeTwoPairGate, canonicalDT, anyTermSat,
      termSat, activeTerm, termFalsified, freeLits, Depth3.litTrue, litVar,
      litFixedVal, litFalse, litFree, fixVar, BoolDecisionTree.depth,
      negativeTwoPair_depth_eq_zero_of_four_fixed, h0, h1, h2, h3,
      h01, h02, h03, h12, h13, h23,
      Ne.symm h01, Ne.symm h02, Ne.symm h03, Ne.symm h12, Ne.symm h13, Ne.symm h23]
      at hpadded ⊢ <;> omega

/-- Ambient residual-depth-one bounds for both padded polarities imply the executable local
shallow predicate used by the exact four-coordinate game. -/
theorem twoPairRootShallow_of_padded_depths (pad : ℕ)
    (σ : Restriction (pad + 40)) (g : Fin 10) (fuel : ℕ) (hfuel : 4 ≤ fuel)
    (hpos : (canonicalDT (positiveTwoPairGate
      (paddedTwoPairCoord pad g 0) (paddedTwoPairCoord pad g 1)
      (paddedTwoPairCoord pad g 2) (paddedTwoPairCoord pad g 3)) fuel σ).depth ≤ 1)
    (hneg : (canonicalDT (negativeTwoPairGate
      (paddedTwoPairCoord pad g 0) (paddedTwoPairCoord pad g 1)
      (paddedTwoPairCoord pad g 2) (paddedTwoPairCoord pad g 3)) fuel σ).depth ≤ 1) :
    twoPairRootShallow (paddedTwoPairLocalRestriction pad σ g) = true := by
  simp only [twoPairRootShallow, decide_eq_true_eq]
  constructor
  · simpa [twoPairPolarityFamily] using
      positiveTwoPair_local_depth_le_one_of_padded pad σ g fuel hfuel hpos
  · simpa [twoPairPolarityFamily] using
      negativeTwoPair_local_depth_le_one_of_padded pad σ g fuel hfuel hneg

/-- Fixing one owned ambient coordinate is exactly a point update of the corresponding local
gadget restriction.  This is the decoding identity used by the padded direct-sum recursion. -/
theorem paddedTwoPairLocalRestriction_fixVar (pad : ℕ)
    (σ : Restriction (pad + 40)) (g : Fin 10) (k : Fin 4) (b : Bool) :
    (fun h => paddedTwoPairLocalRestriction pad
      (fixVar σ (paddedTwoPairCoord pad g k) b) h) =
      Function.update (fun h => paddedTwoPairLocalRestriction pad σ h) g
        (fixVar (paddedTwoPairLocalRestriction pad σ g) k b) := by
  funext h
  by_cases hhg : h = g
  · subst h
    funext l
    by_cases hlk : l = k
    · subst l
      simp [paddedTwoPairLocalRestriction, fixVar]
    · have hcoord : paddedTwoPairCoord pad g l ≠ paddedTwoPairCoord pad g k := by
        intro heq
        exact hlk (congrArg Prod.snd
          ((@paddedTwoPairCoord_injective pad (g, l) (g, k)) heq))
      simp [paddedTwoPairLocalRestriction, fixVar, hlk, hcoord]
  · funext l
    have hcoord : paddedTwoPairCoord pad h l ≠ paddedTwoPairCoord pad g k := by
      intro heq
      exact hhg (congrArg Prod.fst
        ((@paddedTwoPairCoord_injective pad (h, l) (g, k)) heq))
    simp [paddedTwoPairLocalRestriction, fixVar, hhg, hcoord]

/-- Pulling back restriction extension to any owned four-coordinate gadget. -/
theorem paddedTwoPairLocalRestriction_extends {pad : ℕ}
    {σ τ : Restriction (pad + 40)} (hστ : RestrictionExtends σ τ) (g : Fin 10) :
    RestrictionExtends (paddedTwoPairLocalRestriction pad σ g)
      (paddedTwoPairLocalRestriction pad τ g) := by
  intro k b hk
  exact hστ (paddedTwoPairCoord pad g k) b hk

/-- A query in the first `pad` coordinates is pure padding and changes no local gadget state. -/
theorem paddedTwoPairLocalRestriction_fixVar_padding (pad : ℕ)
    (σ : Restriction (pad + 40)) (i : Fin (pad + 40)) (b : Bool)
    (hi : i.val < pad) :
    (fun g => paddedTwoPairLocalRestriction pad (fixVar σ i b) g) =
      fun g => paddedTwoPairLocalRestriction pad σ g := by
  funext g k
  have hne : paddedTwoPairCoord pad g k ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    simp [paddedTwoPairCoord] at hv
    omega
  simp [paddedTwoPairLocalRestriction, fixVar, hne]

/-- The owned component of the ambient point-update identity. -/
theorem paddedTwoPairLocalRestriction_fixVar_self (pad : ℕ)
    (sigma : Restriction (pad + 40)) (g : Fin 10) (k : Fin 4) (b : Bool) :
    paddedTwoPairLocalRestriction pad (fixVar sigma (paddedTwoPairCoord pad g k) b) g =
      fixVar (paddedTwoPairLocalRestriction pad sigma g) k b := by
  have h := congrFun (paddedTwoPairLocalRestriction_fixVar pad sigma g k b) g
  simpa using h

/-- A locally shallow payload lying between the immutable root and accumulated path makes the
conditional cost vanish.  This packages the exact terminal obligation of the global adversary. -/
theorem twoPairFlexibleConditionalCost_eq_zero_of_leaf
    (root path tau : Restriction 4)
    (hroot : RestrictionExtends root tau)
    (hpath : RestrictionExtends tau path)
    (hshallow : twoPairRootShallow tau = true) :
    twoPairFlexibleConditionalCost root path = 0 := by
  have hleaf : twoPairFlexibleLeafWin root path = true := by
    rw [twoPairFlexibleLeafWin, List.any_eq_true]
    refine ⟨tau, List.mem_ofFn.mpr
      ⟨twoPairRestrictionCode tau, twoPairLocalRestriction_code tau⟩, ?_⟩
    simp [twoPairRestrictionExtendsB_eq_true, hroot, hpath, hshallow]
  simp [twoPairFlexibleConditionalCost, twoPairFlexibleQueryWin, hleaf]

/-- If every returned gadget payload is locally shallow and lies between its root and endpoint,
the entire terminal direct-sum potential is exactly zero. -/
theorem twoPairTenFlexibleConditionalCost_eq_zero_of_leaf
    (roots paths taus : Fin 10 → Restriction 4)
    (hroot : ∀ g, RestrictionExtends (roots g) (taus g))
    (hpath : ∀ g, RestrictionExtends (taus g) (paths g))
    (hshallow : ∀ g, twoPairRootShallow (taus g) = true) :
    twoPairTenFlexibleConditionalCost roots paths = 0 := by
  simp [twoPairTenFlexibleConditionalCost,
    twoPairFlexibleConditionalCost_eq_zero_of_leaf _ _ _ (hroot _) (hpath _) (hshallow _)]

/-- The conditional ten-gadget potential can be followed adversarially through an arbitrary
padded common tree.  The returned restriction records the selected root-to-leaf query path, and
the returned payload is reached by every assignment extending that path.  Padding queries cost
nothing; owned queries cost at most one by the exhaustive local adversary inequality. -/
theorem twoPairTenFlexibleConditionalCost_tree_adversary (pad : ℕ)
    (roots : Fin 10 → Restriction 4) (path : Restriction (pad + 40))
    (trunk : CommonTree (pad + 40) (Restriction (pad + 40)))
    (hroot : ∀ g, RestrictionExtends (roots g)
      (paddedTwoPairLocalRestriction pad path g)) :
    ∃ endpoint : Restriction (pad + 40), ∃ tau : Restriction (pad + 40),
      RestrictionExtends path endpoint ∧
      (∀ x : Fin (pad + 40) → Bool, Rung4Restriction.Extends endpoint x →
        CommonTree.run trunk x = tau) ∧
      twoPairTenFlexibleConditionalCost roots
          (fun g => paddedTwoPairLocalRestriction pad path g) ≤
        twoPairTenFlexibleConditionalCost roots
          (fun g => paddedTwoPairLocalRestriction pad endpoint g) +
          CommonTree.depth trunk := by
  induction trunk generalizing path with
  | leaf tau =>
      exact ⟨path, tau, (by intro i b hi; exact hi), (by simp [CommonTree.run]), by simp⟩
  | query i lo hi ihlo ihhi =>
      cases hpi : path i with
      | some bit =>
          cases bit with
          | false =>
              obtain ⟨endpoint, tau, hpath, hrun, hcost⟩ := ihlo path hroot
              refine ⟨endpoint, tau, hpath, ?_, ?_⟩
              · intro x hx
                have hxi : x i = false := hx i false (hpath i false hpi)
                simpa [CommonTree.run, hxi] using hrun x hx
              · simp only [CommonTree.depth]
                omega
          | true =>
              obtain ⟨endpoint, tau, hpath, hrun, hcost⟩ := ihhi path hroot
              refine ⟨endpoint, tau, hpath, ?_, ?_⟩
              · intro x hx
                have hxi : x i = true := hx i true (hpath i true hpi)
                simpa [CommonTree.run, hxi] using hrun x hx
              · simp only [CommonTree.depth]
                omega
      | none =>
          by_cases hipad : i.val < pad
          · have hlocals := paddedTwoPairLocalRestriction_fixVar_padding pad path i false hipad
            have hroot' : ∀ g, RestrictionExtends (roots g)
                (paddedTwoPairLocalRestriction pad (fixVar path i false) g) := by
              simpa [hlocals] using hroot
            obtain ⟨endpoint, tau, hpath', hrun, hcost⟩ :=
              ihlo (fixVar path i false) hroot'
            have hpathFix : RestrictionExtends path (fixVar path i false) := by
              intro j b hj
              by_cases hji : j = i
              · subst j; rw [hpi] at hj; contradiction
              · simpa [fixVar, Function.update_of_ne hji] using hj
            refine ⟨endpoint, tau, fun j b hj => hpath' j b (hpathFix j b hj), ?_, ?_⟩
            · intro x hx
              have hxi : x i = false := hx i false (hpath' i false (by simp [fixVar]))
              simpa [CommonTree.run, hxi] using hrun x hx
            · rw [hlocals] at hcost
              simp only [CommonTree.depth]
              exact hcost.trans (Nat.add_le_add_left
                (Nat.le_succ_of_le (Nat.le_max_left _ _)) _)
          · let q : Fin 40 := ⟨i.val - pad, by omega⟩
            let key : Fin 10 × Fin 4 := finProdFinEquiv.symm q
            have hkey : paddedTwoPairCoord pad key.1 key.2 = i := by
              apply Fin.ext
              simp [paddedTwoPairCoord, key, q, finProdFinEquiv]
              omega
            have hlocalNone : paddedTwoPairLocalRestriction pad path key.1 key.2 = none := by
              simpa [paddedTwoPairLocalRestriction, hkey] using hpi
            obtain ⟨bit, hbit⟩ := twoPairTenFlexibleConditionalCost_update_adversary
              roots (fun g => paddedTwoPairLocalRestriction pad path g) key.1 key.2 hroot hlocalNone
            have hlocals := paddedTwoPairLocalRestriction_fixVar pad path key.1 key.2 bit
            rw [hkey] at hlocals
            have hroot' : ∀ g, RestrictionExtends (roots g)
                (paddedTwoPairLocalRestriction pad (fixVar path i bit) g) := by
              intro g
              change RestrictionExtends (roots g)
                ((fun h => paddedTwoPairLocalRestriction pad (fixVar path i bit) h) g)
              rw [hlocals]
              by_cases hg : g = key.1
              · subst g
                intro k b hk
                by_cases hkkey : k = key.2
                · subst k
                  have hc := hroot key.1 key.2 b hk
                  rw [hlocalNone] at hc
                  contradiction
                · simpa [Function.update, fixVar, hkkey] using hroot key.1 k b hk
              · simpa [Function.update, hg] using hroot g
            have hpathFix : RestrictionExtends path (fixVar path i bit) := by
              intro j b hj
              by_cases hji : j = i
              · subst j; rw [hpi] at hj; contradiction
              · simpa [fixVar, Function.update_of_ne hji] using hj
            have hbitAmbient :
                twoPairTenFlexibleConditionalCost roots
                    (fun g => paddedTwoPairLocalRestriction pad path g) ≤
                  twoPairTenFlexibleConditionalCost roots
                      (fun g => paddedTwoPairLocalRestriction pad (fixVar path i bit) g) + 1 := by
              change twoPairTenFlexibleConditionalCost roots
                  (fun g => paddedTwoPairLocalRestriction pad path g) ≤
                twoPairTenFlexibleConditionalCost roots
                    ((fun h => paddedTwoPairLocalRestriction pad (fixVar path i bit) h)) + 1
              rw [hlocals]
              exact hbit
            cases bit with
            | false =>
                obtain ⟨endpoint, tau, hpath', hrun, hcost⟩ :=
                  ihlo (fixVar path i false) hroot'
                refine ⟨endpoint, tau, fun j b hj => hpath' j b (hpathFix j b hj), ?_, ?_⟩
                · intro x hx
                  have hxi : x i = false := hx i false (hpath' i false (by simp [fixVar]))
                  simpa [CommonTree.run, hxi] using hrun x hx
                · simp only [CommonTree.depth]
                  omega

            | true =>
                obtain ⟨endpoint, tau, hpath', hrun, hcost⟩ :=
                  ihhi (fixVar path i true) hroot'
                refine ⟨endpoint, tau, fun j b hj => hpath' j b (hpathFix j b hj), ?_, ?_⟩
                · intro x hx
                  have hxi : x i = true := hx i true (hpath' i true (by simp [fixVar]))
                  simpa [CommonTree.run, hxi] using hrun x hx
                · simp only [CommonTree.depth]
                  omega

/-- Semantic direct-sum capstone for the padded family.  Any ambient common trunk making both
polarities residually depth one must pay at least the sum of the ten exact local flexible costs.
Padding queries and adaptive interleaving are already absorbed by the conditional adversary. -/
theorem twoPairTenFlexibleCost_le_of_padded_commonShallow (pad fuel trunkDepth : ℕ)
    (σ : Restriction (pad + 40)) (hfuel : 4 ≤ fuel)
    (hshallow : CommonShallowAt (paddedTwoPairFamily pad) fuel σ trunkDepth 1) :
    twoPairTenFlexibleCost (fun g => paddedTwoPairLocalRestriction pad σ g) ≤ trunkDepth := by
  obtain ⟨trunk, htrunkDepth, hleaf⟩ := hshallow
  let roots : Fin 10 → Restriction 4 :=
    fun g => paddedTwoPairLocalRestriction pad σ g
  have hrootSelf : ∀ g, RestrictionExtends (roots g)
      (paddedTwoPairLocalRestriction pad σ g) := by
    intro g i b hi
    exact hi
  obtain ⟨endpoint, tau, hσendpoint, hrun, hcost⟩ :=
    twoPairTenFlexibleConditionalCost_tree_adversary pad roots σ trunk hrootSelf
  let x : Fin (pad + 40) → Bool := fun i => (endpoint i).getD false
  have hxendpoint : Rung4Restriction.Extends endpoint x := extends_getD endpoint
  have hxσ : Rung4Restriction.Extends σ x := by
    intro i b hi
    exact hxendpoint i b (hσendpoint i b hi)
  obtain ⟨hστau, htaux, hambientShallow⟩ := hleaf x hxσ
  have hruntau : CommonTree.run trunk x = tau := hrun x hxendpoint
  rw [hruntau] at hστau htaux hambientShallow
  have htauEndpoint : RestrictionExtends tau endpoint := by
    apply restrictionExtends_path_of_agrees_everywhere
    intro y hyendpoint
    have hyσ : Rung4Restriction.Extends σ y := by
      intro i b hi
      exact hyendpoint i b (hσendpoint i b hi)
    have hyagree := (hleaf y hyσ).2.1
    simpa [hrun y hyendpoint] using hyagree
  have hrootLocal : ∀ g, RestrictionExtends (roots g)
      (paddedTwoPairLocalRestriction pad tau g) := by
    intro g
    exact paddedTwoPairLocalRestriction_extends hστau g
  have hpathLocal : ∀ g, RestrictionExtends
      (paddedTwoPairLocalRestriction pad tau g)
      (paddedTwoPairLocalRestriction pad endpoint g) := by
    intro g
    exact paddedTwoPairLocalRestriction_extends htauEndpoint g
  have hlocalShallow : ∀ g,
      twoPairRootShallow (paddedTwoPairLocalRestriction pad tau g) = true := by
    intro g
    apply twoPairRootShallow_of_padded_depths pad tau g fuel hfuel
    · simpa [paddedTwoPairFamily, paddedTwoPairGates] using
        hambientShallow (finProdFinEquiv ((0 : Fin 2), g))
    · simpa [paddedTwoPairFamily, paddedTwoPairGates] using
        hambientShallow (finProdFinEquiv ((1 : Fin 2), g))
  have hterminal : twoPairTenFlexibleConditionalCost roots
      (fun g => paddedTwoPairLocalRestriction pad endpoint g) = 0 :=
    twoPairTenFlexibleConditionalCost_eq_zero_of_leaf roots
      (fun g => paddedTwoPairLocalRestriction pad endpoint g)
      (fun g => paddedTwoPairLocalRestriction pad tau g)
      hrootLocal hpathLocal hlocalShallow
  rw [twoPairTenFlexibleConditionalCost_self, hterminal, zero_add] at hcost
  exact hcost.trans htrunkDepth

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
/-- Exact bivariate local profile, with rows indexed by live coordinates `0..4` and columns by
semantic cost `0..3`.  Equivalently the generating polynomial is
`16 + 32*x + (8 + 16*z)*x^2 + 8*z^2*x^3 + z^3*x^4`. -/
theorem twoPairFlexibleQueryCost_stars_profile_exact :
    (List.range 5).map (fun q => (List.range 4).map (fun c =>
      ((List.ofFn fun code : Fin 81 => code).filter (fun code =>
        stars (twoPairLocalRestriction code) = q &&
          twoPairFlexibleQueryCost (twoPairLocalRestriction code) = c)).length)) =
      [[16, 0, 0, 0], [32, 0, 0, 0], [8, 16, 0, 0],
        [0, 0, 8, 0], [0, 0, 0, 1]] := by
  decide

/-! ### Exact bivariate semantic-cost convolution

The local profile above can be convolved while retaining both live support and semantic cost.
This is the arithmetic object needed to locate the padding transition; unlike the earlier coarse
`81^10` bound, it does not discard either grading. -/

/-- Coefficient of `x^q z^c` in
`(16 + 32*x + 8*x^2 + 16*x^2*z + 8*x^3*z^2 + x^4*z^3)^g`. -/
def twoPairCostLiveConvolution : ℕ → ℕ → ℕ → ℕ
  | 0, q, c => if q = 0 ∧ c = 0 then 1 else 0
  | g + 1, q, c =>
      16 * twoPairCostLiveConvolution g q c +
      (if 1 ≤ q then 32 * twoPairCostLiveConvolution g (q - 1) c else 0) +
      (if 2 ≤ q then 8 * twoPairCostLiveConvolution g (q - 2) c else 0) +
      (if 2 ≤ q ∧ 1 ≤ c then
        16 * twoPairCostLiveConvolution g (q - 2) (c - 1) else 0) +
      (if 3 ≤ q ∧ 2 ≤ c then
        8 * twoPairCostLiveConvolution g (q - 3) (c - 2) else 0) +
      (if 4 ≤ q ∧ 3 ≤ c then
        twoPairCostLiveConvolution g (q - 4) (c - 3) else 0)

/-- The live-support coefficients obtained by summing the cost columns strictly above ten in the
ten-fold bivariate recurrence.  Keeping this small explicit table makes the boundary arithmetic
resource-safe; identifying it with the actual finite product is deliberately the next structural
lemma, rather than an appeal to an opaque evaluator. -/
def twoPairTenFlexibleCostTailCoefficient : ℕ → ℕ
  | 15 => 112742891520
  | 16 => 15562042245120
  | 17 => 329815236280320
  | 18 => 2642541878968320
  | 19 => 10407821275299840
  | 20 => 22389731006349312
  | 21 => 27618472833843200
  | 22 => 20568593190092800
  | 23 => 10401074475171840
  | 24 => 4029196851609600
  | 25 => 1315170979676160
  | 26 => 380197424332800
  | 27 => 98576161832960
  | 28 => 22883751854080
  | 29 => 4734569349120
  | 30 => 868004380672
  | 31 => 140000706560
  | 32 => 19687599360
  | 33 => 2386375680
  | 34 => 245656320
  | 35 => 21056256
  | 36 => 1462240
  | 37 => 79040
  | 38 => 3120
  | 39 => 80
  | 40 => 1
  | _ => 0

/-- The tabulated bivariate padding mass.  A profile with `q` live owned coordinates forces the
padding restriction to have exactly `40-q` stars. -/
def paddedTwoPairFlexibleCostTabulatedMass (pad : ℕ) : ℕ :=
  ∑ q ∈ Finset.range 41, twoPairTenFlexibleCostTailCoefficient q *
    (Nat.choose pad (40 - q) * 2 ^ (pad - (40 - q)))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The exact bivariate arithmetic still violates the requested `2^-10` contraction at padding
eighty-six. -/
theorem paddedTwoPairFlexibleCostTabulatedMass_scaled_not_le_shell_86 :
    ¬ paddedTwoPairFlexibleCostTabulatedMass 86 * 2 ^ 10 ≤
      Nat.choose 126 40 * 2 ^ 86 := by
  norm_num (config := { maxSteps := 1000000 })
    [paddedTwoPairFlexibleCostTabulatedMass, twoPairTenFlexibleCostTailCoefficient, Nat.choose,
      Finset.sum_range_succ]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- One additional padding coordinate reverses the exact bivariate comparison. -/
theorem paddedTwoPairFlexibleCostTabulatedMass_scaled_le_shell_87 :
    paddedTwoPairFlexibleCostTabulatedMass 87 * 2 ^ 10 ≤
      Nat.choose 127 40 * 2 ^ 87 := by
  norm_num (config := { maxSteps := 1000000 })
    [paddedTwoPairFlexibleCostTabulatedMass, twoPairTenFlexibleCostTailCoefficient, Nat.choose,
      Finset.sum_range_succ]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
/-- The exact semantic local cost never exceeds the number of live owned coordinates.  This
finite statement is stronger than the univariate histogram: jointly by `(stars,cost)`, the only
nonzero multiplicities are `(0,0):16`, `(1,0):32`, `(2,0):8`, `(2,1):16`, `(3,2):8`, and
`(4,3):1`. -/
theorem twoPairFlexibleQueryCost_le_stars (rho : Restriction 4) :
    twoPairFlexibleQueryCost rho ≤ stars rho := by
  rw [← twoPairLocalRestriction_code rho]
  exact (by decide +revert : ∀ code : Fin 81,
    twoPairFlexibleQueryCost (twoPairLocalRestriction code) ≤
      stars (twoPairLocalRestriction code)) (twoPairRestrictionCode rho)

/-- The actual one-gadget fiber with prescribed live support and semantic cost.  This is the
structural base object whose finite products must be convolved; unlike the preceding displayed
table, it can be used directly in fiberwise cardinality proofs. -/
def twoPairLocalCostLiveFiber (q c : ℕ) : Finset (Restriction 4) :=
  Finset.univ.filter fun rho =>
    stars rho = q ∧ twoPairFlexibleQueryCost rho = c

/-- The arithmetic recurrence's first layer is exactly the cardinality of the corresponding
semantic local fiber, for every pair of natural-number indices (including the zero region outside
the possible `0..4` live and `0..3` cost ranges). -/
theorem twoPairLocalCostLiveFiber_card_eq_convolution_one (q c : ℕ) :
    (twoPairLocalCostLiveFiber q c).card = twoPairCostLiveConvolution 1 q c := by
  by_cases hq : q ≤ 4
  · by_cases hc : c ≤ 3
    · interval_cases q <;> interval_cases c <;> decide
    · have hempty : twoPairLocalCostLiveFiber q c = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro rho hrho
        simp only [twoPairLocalCostLiveFiber, Finset.mem_filter, Finset.mem_univ,
          true_and] at hrho
        have hcost : twoPairFlexibleQueryCost rho ≤ 3 := by
          rw [← twoPairLocalRestriction_code rho]
          exact (by decide +revert : ∀ code : Fin 81,
            twoPairFlexibleQueryCost (twoPairLocalRestriction code) ≤ 3)
            (twoPairRestrictionCode rho)
        rw [hrho.2] at hcost
        omega
      rw [hempty]
      simp only [Finset.card_empty]
      simp [twoPairCostLiveConvolution]
      split_ifs <;> omega
  · have hempty : twoPairLocalCostLiveFiber q c = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro rho hrho
      simp only [twoPairLocalCostLiveFiber, Finset.mem_filter, Finset.mem_univ,
        true_and] at hrho
      have hstars : stars rho ≤ 4 := by
        rw [stars]
        exact Finset.card_le_univ _
      omega
    rw [hempty]
    simp only [Finset.card_empty]
    simp [twoPairCostLiveConvolution]
    split_ifs <;> omega

/-- The actual `g`-gadget fiber with prescribed total live support and total semantic cost.
Unlike the arithmetic recurrence, this definition ranges over genuine vectors of local
restrictions and records both additive gradings directly. -/
def twoPairProductCostLiveFiber (g q c : ℕ) :
    Finset (Fin g → Restriction 4) :=
  Finset.univ.filter fun roots =>
    (∑ i, stars (roots i)) = q ∧
      (∑ i, twoPairFlexibleQueryCost (roots i)) = c

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- Splitting off the last local restriction gives the exact structural successor equation for
the semantic product fiber.  The guards are essential: natural-number subtraction represents
the remaining grading only when the last gadget does not exceed the requested totals. -/
theorem twoPairProductCostLiveFiber_card_succ (g q c : ℕ) :
    (twoPairProductCostLiveFiber (g + 1) q c).card =
      ∑ rho : Restriction 4,
        if stars rho ≤ q ∧ twoPairFlexibleQueryCost rho ≤ c then
          (twoPairProductCostLiveFiber g (q - stars rho)
            (c - twoPairFlexibleQueryCost rho)).card
        else 0 := by
  classical
  rw [twoPairProductCostLiveFiber, Finset.card_filter]
  change (∑ roots : Fin (g + 1) → Restriction 4,
      if (∑ i, stars (roots i)) = q ∧
        (∑ i, twoPairFlexibleQueryCost (roots i)) = c then 1 else 0) = _
  rw [Fintype.sum_equiv (Fin.succFunEquiv (Restriction 4) g)
    (fun roots => if (∑ i, stars (roots i)) = q ∧
      (∑ i, twoPairFlexibleQueryCost (roots i)) = c then 1 else 0)
    (fun pair => if (∑ i, stars (pair.1 i)) + stars pair.2 = q ∧
      (∑ i, twoPairFlexibleQueryCost (pair.1 i)) +
        twoPairFlexibleQueryCost pair.2 = c then 1 else 0)]
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro rho _
    by_cases hle : stars rho ≤ q ∧ twoPairFlexibleQueryCost rho ≤ c
    · rw [if_pos hle, twoPairProductCostLiveFiber, Finset.card_filter]
      change (∑ roots : Fin g → Restriction 4,
        if (∑ i, stars (roots i)) = q - stars rho ∧
          (∑ i, twoPairFlexibleQueryCost (roots i)) =
            c - twoPairFlexibleQueryCost rho then 1 else 0) = _
      apply Finset.sum_congr rfl
      intro roots _
      split_ifs with hleft hright
      · rfl
      · exfalso
        apply hright
        constructor <;> omega
      · exfalso
        apply hleft
        constructor <;> omega
      · rfl
    · rw [if_neg hle]
      apply Finset.sum_eq_zero
      intro roots _
      rw [if_neg]
      intro htotals
      apply hle
      constructor <;> omega
  · intro roots
    simp [Fin.succFunEquiv, Fin.sum_univ_castSucc, Fin.castAdd, Fin.natAdd, Fin.last]

/-- The exact forty-star semantic cost tail supplied by the padded ten-gadget direct sum. -/
def paddedTwoPairFlexibleCostTail (pad : ℕ) :
    Finset (Restriction (pad + 40)) :=
  Finset.univ.filter fun sigma =>
    stars sigma = 40 ∧
      10 < twoPairTenFlexibleCost
        (fun g => paddedTwoPairLocalRestriction pad sigma g)

/-- Every point of the exact semantic cost tail is genuinely bad for a depth-ten common trunk. -/
theorem paddedTwoPairFlexibleCostTail_subset_bad (pad : ℕ) :
    paddedTwoPairFlexibleCostTail pad ⊆
      commonShallowBad (paddedTwoPairFamily pad) (pad + 40) 40 10 1 := by
  intro sigma hsigma
  rw [paddedTwoPairFlexibleCostTail, Finset.mem_filter] at hsigma
  rw [mem_commonShallowBad]
  refine ⟨hsigma.2.1, ?_⟩
  intro hshallow
  have hcost := twoPairTenFlexibleCost_le_of_padded_commonShallow
    pad (pad + 40) 10 sigma (by omega) hshallow
  omega

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
/-- The fully live local gadget has exact flexible cost three.  This executable specialization
will distinguish the unpadded schedule from the heavily padded schedule below. -/
theorem twoPairFlexibleQueryCost_allFree :
    twoPairFlexibleQueryCost (fun _ : Fin 4 => none) = 3 := by
  decide

/-- With no padding, the unique forty-live restriction lies in the complete semantic cost tail:
all ten gadgets are fully live and contribute cost three, far above trunk budget ten. -/
theorem allFreeForty_mem_paddedTwoPairFlexibleCostTail_zero :
    (fun _ : Fin 40 => none) ∈ paddedTwoPairFlexibleCostTail 0 := by
  simp only [paddedTwoPairFlexibleCostTail, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · simpa using
      (stars_rectangularDistinctSingleton_allLive (G := 10) (m := 4))
  · have hlocal : (fun g : Fin 10 =>
        paddedTwoPairLocalRestriction 0 (fun _ : Fin 40 => none) g) =
        fun _ => (fun _ : Fin 4 => none) := by
      funext g i
      rfl
    rw [hlocal, twoPairTenFlexibleCost]
    simp [twoPairFlexibleQueryCost_allFree]

/-- At zero padding the semantic tail is the entire forty-live shell (which has one point). -/
theorem paddedTwoPairFlexibleCostTail_card_zeroPadding :
    (paddedTwoPairFlexibleCostTail 0).card = 1 := by
  have hpos : 1 ≤ (paddedTwoPairFlexibleCostTail 0).card :=
    Finset.one_le_card.mpr
      ⟨_, allFreeForty_mem_paddedTwoPairFlexibleCostTail_zero⟩
  have hle : (paddedTwoPairFlexibleCostTail 0).card ≤
      (Finset.univ.filter fun sigma : Restriction 40 => stars sigma = 40).card := by
    apply Finset.card_le_card
    intro sigma hsigma
    rw [paddedTwoPairFlexibleCostTail, Finset.mem_filter] at hsigma
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hsigma.2.1⟩
  rw [card_stars_eq] at hle
  norm_num at hle
  omega

/-- Therefore the requested `2^10` scaled shell contraction is false for the unpadded schedule.
The same semantic family fails only after the padding mass dilutes its near-unit cost support. -/
theorem not_paddedTwoPair_scaled_contraction_zeroPadding :
    ¬ (commonShallowBad (paddedTwoPairFamily 0) 40 40 10 1).card * 2 ^ 10 ≤
        (Finset.univ.filter fun sigma : Restriction 40 => stars sigma = 40).card := by
  have htail := Finset.card_le_card (paddedTwoPairFlexibleCostTail_subset_bad 0)
  rw [paddedTwoPairFlexibleCostTail_card_zeroPadding] at htail
  intro hcontraction
  have hlower : 1024 ≤
      (commonShallowBad (paddedTwoPairFamily 0) 40 40 10 1).card * 1024 := by
    exact Nat.mul_le_mul_right 1024 htail
  have hupper :
      (commonShallowBad (paddedTwoPairFamily 0) 40 40 10 1).card * 1024 ≤ 1 := by
    simpa only [card_stars_eq, Nat.choose_self, Nat.sub_self, pow_zero, mul_one,
      pow_succ, Nat.mul_one] using hcontraction
  have himpossible := hlower.trans hupper
  norm_num at himpossible

/-- Restrict an ambient assignment to its first `pad` coordinates. -/
def paddedTwoPairPaddingRestriction (pad : ℕ) (σ : Restriction (pad + 40)) :
    Restriction pad :=
  fun i => σ (Fin.castAdd 40 i)

/-- The exact product code for a padded restriction: ten ordered local gadget states and the
ordered padding state.  No Boolean or live-coordinate information is discarded. -/
def paddedTwoPairRestrictionCode (pad : ℕ) (σ : Restriction (pad + 40)) :
    (Fin 10 → Restriction 4) × Restriction pad :=
  (fun g => paddedTwoPairLocalRestriction pad σ g,
    paddedTwoPairPaddingRestriction pad σ)

/-- The ambient-to-product decomposition is injective.  Thus subsequent counting may charge a
restriction by its ten local states and padding state without hidden fiber multiplicity. -/
theorem paddedTwoPairRestrictionCode_injective (pad : ℕ) :
    Function.Injective (paddedTwoPairRestrictionCode pad) := by
  intro σ τ hcode
  have hlocal : (fun g => paddedTwoPairLocalRestriction pad σ g) =
      fun g => paddedTwoPairLocalRestriction pad τ g := congrArg Prod.fst hcode
  have hpadding : paddedTwoPairPaddingRestriction pad σ =
      paddedTwoPairPaddingRestriction pad τ := congrArg Prod.snd hcode
  funext i
  by_cases hi : i.val < pad
  · let j : Fin pad := ⟨i.val, hi⟩
    have hij : Fin.castAdd 40 j = i := by
      apply Fin.ext
      rfl
    have hj := congrFun hpadding j
    simpa [paddedTwoPairPaddingRestriction, hij] using hj
  · let q : Fin 40 := ⟨i.val - pad, by omega⟩
    let key : Fin 10 × Fin 4 := finProdFinEquiv.symm q
    have hiq : paddedTwoPairCoord pad key.1 key.2 = i := by
      apply Fin.ext
      simp [paddedTwoPairCoord, key, q, finProdFinEquiv]
      omega
    have hg := congrFun hlocal key.1
    have hk := congrFun hg key.2
    simpa [paddedTwoPairLocalRestriction, hiq] using hk

/-- Reassemble an ambient restriction from its ten local states and its padding state.  This is
the explicit inverse needed for exact, rather than merely upper-bound, product counting. -/
def paddedTwoPairRestrictionOfCode (pad : ℕ)
    (code : (Fin 10 → Restriction 4) × Restriction pad) :
    Restriction (pad + 40) :=
  fun i => if hi : i.val < pad then code.2 ⟨i.val, hi⟩ else
    let q : Fin 40 := ⟨i.val - pad, by omega⟩
    let key : Fin 10 × Fin 4 := finProdFinEquiv.symm q
    code.1 key.1 key.2

/-- The product code is onto: the ten four-coordinate blocks and the padding block partition the
ambient coordinates exactly. -/
theorem paddedTwoPairRestrictionCode_surjective (pad : ℕ) :
    Function.Surjective (paddedTwoPairRestrictionCode pad) := by
  intro code
  refine ⟨paddedTwoPairRestrictionOfCode pad code, ?_⟩
  apply Prod.ext
  · funext g k
    simp only [paddedTwoPairRestrictionCode, paddedTwoPairLocalRestriction,
      paddedTwoPairRestrictionOfCode]
    have hcoord : ¬(paddedTwoPairCoord pad g k).val < pad := by
      simp [paddedTwoPairCoord]
    rw [dif_neg hcoord]
    let q : Fin 40 := ⟨(paddedTwoPairCoord pad g k).val - pad, by omega⟩
    have hq : q = finProdFinEquiv (g, k) := by
      apply Fin.ext
      change (Fin.natAdd pad ⟨4 * g.val + k.val, by omega⟩).val - pad =
        (finProdFinEquiv (g, k)).val
      rw [Fin.val_natAdd]
      simp [finProdFinEquiv]
      omega
    change code.1 ((finProdFinEquiv : Fin 10 × Fin 4 ≃ Fin 40).symm q).1
        ((finProdFinEquiv : Fin 10 × Fin 4 ≃ Fin 40).symm q).2 = code.1 g k
    rw [hq, Equiv.symm_apply_apply]
  · funext i
    simp [paddedTwoPairRestrictionCode, paddedTwoPairPaddingRestriction,
      paddedTwoPairRestrictionOfCode]

/-- The exact padded/local decomposition as an equivalence. -/
noncomputable def paddedTwoPairRestrictionEquiv (pad : ℕ) :
    Restriction (pad + 40) ≃
      (Fin 10 → Restriction 4) × Restriction pad :=
  Equiv.ofBijective (paddedTwoPairRestrictionCode pad)
    ⟨paddedTwoPairRestrictionCode_injective pad,
      paddedTwoPairRestrictionCode_surjective pad⟩

/-- Pullback identifies the canonical local live count with the padded gadget's owned-live
count. -/
theorem stars_paddedTwoPairLocalRestriction (pad : ℕ)
    (σ : Restriction (pad + 40)) (g : Fin 10) :
    stars (paddedTwoPairLocalRestriction pad σ g) =
      (liveSupport (paddedTwoPairSupport pad) σ g).card := by
  classical
  rw [stars, liveSupport, paddedTwoPairSupport, freeVars, freeVars]
  apply Finset.card_bij (fun k _ => paddedTwoPairCoord pad g k)
  · intro k hk
    rw [Finset.mem_filter] at hk
    rw [Finset.mem_inter, Finset.mem_image, Finset.mem_filter]
    exact ⟨⟨k, Finset.mem_univ _, rfl⟩, Finset.mem_univ _, hk.2⟩
  · intro a ha b hb hab
    exact congrArg Prod.snd
      ((@paddedTwoPairCoord_injective pad (g, a) (g, b)) hab)
  · intro i hi
    rw [Finset.mem_inter, Finset.mem_image, Finset.mem_filter] at hi
    obtain ⟨⟨k, _, rfl⟩, hk⟩ := hi
    exact ⟨k, by simpa [paddedTwoPairLocalRestriction] using hk, rfl⟩

/-- Truth compatibility is exactly the canonical local condition that no coordinate is fixed
false. -/
theorem paddedTwoPair_supportTrueCompatible_iff (pad : ℕ)
    (σ : Restriction (pad + 40)) (g : Fin 10) :
    supportTrueCompatible (paddedTwoPairSupport pad) σ g ↔
      ∀ k, paddedTwoPairLocalRestriction pad σ g k ≠ some false := by
  constructor
  · intro h k
    apply h (paddedTwoPairCoord pad g k)
    rw [paddedTwoPairSupport, Finset.mem_image]
    exact ⟨k, Finset.mem_univ _, rfl⟩
  · intro h i hi
    rw [paddedTwoPairSupport, Finset.mem_image] at hi
    obtain ⟨k, _, rfl⟩ := hi
    exact h k

/-- Each padded compatible deficit is precisely the deficit read from the corresponding row of
the canonical six-state table. -/
theorem twoPairLocalCompatibleDeficit_paddedTwoPairLocalRestriction (pad : ℕ)
    (σ : Restriction (pad + 40)) (g : Fin 10) :
    twoPairLocalCompatibleDeficit (paddedTwoPairLocalRestriction pad σ g) =
      compatibleResidualQueryDeficit (paddedTwoPairSupport pad) σ 2 g := by
  classical
  rw [twoPairLocalCompatibleDeficit, compatibleResidualQueryDeficit]
  rw [paddedTwoPair_supportTrueCompatible_iff]
  split_ifs with h
  · rw [residualQueryDeficit, stars_paddedTwoPairLocalRestriction]
  · rfl

/-- On one padded four-coordinate gadget, twice the compatible threshold-two deficit is bounded
by the number of owned coordinates that remain live. -/
theorem two_mul_paddedTwoPair_compatibleDeficit_le_liveSupport_card (pad : ℕ)
    (σ : Restriction (pad + 40)) (g : Fin 10) :
    2 * compatibleResidualQueryDeficit (paddedTwoPairSupport pad) σ 2 g ≤
      (liveSupport (paddedTwoPairSupport pad) σ g).card := by
  classical
  rw [compatibleResidualQueryDeficit]
  split_ifs with hcompat
  · rw [residualQueryDeficit]
    have hcard : (liveSupport (paddedTwoPairSupport pad) σ g).card ≤ 4 := by
      rw [← paddedTwoPairSupport_card pad g]
      exact Finset.card_le_card Finset.inter_subset_left
    omega
  · simp

/-- The live coordinates owned by the ten padded gadgets. -/
def paddedTwoPairOwnedLive (pad : ℕ) (σ : Restriction (pad + 40)) :
    Finset (Fin (pad + 40)) :=
  Finset.univ.biUnion fun g => liveSupport (paddedTwoPairSupport pad) σ g

/-- Pairwise disjointness makes the owned-live cardinality exactly the sum of the ten local live
cardinalities. -/
theorem paddedTwoPairOwnedLive_card (pad : ℕ) (σ : Restriction (pad + 40)) :
    (paddedTwoPairOwnedLive pad σ).card =
      ∑ g, (liveSupport (paddedTwoPairSupport pad) σ g).card := by
  classical
  rw [paddedTwoPairOwnedLive, Finset.card_biUnion]
  intro g _ h _ hne
  apply (paddedTwoPairSupport_pairwiseDisjoint pad g h hne).mono
  · exact Finset.inter_subset_left
  · exact Finset.inter_subset_left

/-- The support bound obtained from the coarse pointwise inequality alone.  This is only `22`,
not `23`: total deficit eleven is the arithmetic boundary where doubling loses the extra live
coordinate carried by a deficit-one local state. -/
theorem paddedTwoPair_twentyTwo_le_ownedLive_of_ten_lt_deficit (pad : ℕ)
    (σ : Restriction (pad + 40))
    (hdeficit : 10 < ∑ g,
      compatibleResidualQueryDeficit (paddedTwoPairSupport pad) σ 2 g) :
    22 ≤ (paddedTwoPairOwnedLive pad σ).card := by
  rw [paddedTwoPairOwnedLive_card]
  have hsum :
      ∑ g, 2 * compatibleResidualQueryDeficit (paddedTwoPairSupport pad) σ 2 g ≤
        ∑ g, (liveSupport (paddedTwoPairSupport pad) σ g).card :=
    Finset.sum_le_sum fun g _ =>
      two_mul_paddedTwoPair_compatibleDeficit_le_liveSupport_card pad σ g
  rw [← Finset.mul_sum] at hsum
  omega

/-- The missing unit at odd deficit is visible in the exact local state: a deficit-one gadget
has three, rather than merely two, live coordinates. -/
theorem twoPairLocal_live_lower_bound (rho : Restriction 4) :
    2 * twoPairLocalCompatibleDeficit rho +
        (if twoPairLocalCompatibleDeficit rho = 1 then 1 else 0) ≤ stars rho := by
  decide +revert

/-- No four-coordinate gadget contributes compatible deficit above two. -/
theorem twoPairLocalCompatibleDeficit_le_two (rho : Restriction 4) :
    twoPairLocalCompatibleDeficit rho ≤ 2 := by
  decide +revert

/-! ### Exact ten-local filtered product count

The recurrence above was evaluated arithmetically, but the ambient counting argument also needs
to know that it counts the actual ten-tuples of local restrictions.  We prove that identification
without reducing the `81^10`-element function space.  Instead, map a local tuple to its
`Fin 3`-valued deficit vector, partition fiberwise over the `3^10` possible vectors, and factor
each fiber as a finite product of the one-coordinate deficit classes. -/

/-- The actual ten-gadget local tuples whose total compatible deficit exceeds ten. -/
def twoPairTenLocalDeficitTailProfiles :
    Finset (Fin 10 → Restriction 4) :=
  Finset.univ.filter fun rho => 10 < ∑ g, twoPairLocalCompatibleDeficit (rho g)

/-- The three local deficit fibers, now aggregated over live-coordinate counts. -/
def twoPairLocalDeficitClass (d : ℕ) : Finset (Restriction 4) :=
  Finset.univ.filter fun rho => twoPairLocalCompatibleDeficit rho = d

/-- The proved local table gives the exact fiber sizes `76`, `4`, and `1`. -/
theorem twoPairLocalDeficitClass_card (d : Fin 3) :
    (twoPairLocalDeficitClass d).card =
      if d = 0 then 76 else if d = 1 then 4 else 1 := by
  fin_cases d <;> decide

/-- Package the pointwise deficit of a ten-local tuple as a three-valued vector. -/
def twoPairDeficitVector (rho : Fin 10 → Restriction 4) : Fin 10 → Fin 3 :=
  fun g => ⟨twoPairLocalCompatibleDeficit (rho g), by
    have h := twoPairLocalCompatibleDeficit_le_two (rho g)
    omega⟩

/-- The much smaller set of deficit vectors in the required tail. -/
def twoPairTenDeficitTailVectors : Finset (Fin 10 → Fin 3) :=
  Finset.univ.filter fun d => 10 < ∑ g, (d g).val

/-- Once its deficit vector is fixed, a tuple fiber is the independent product of the ten local
deficit classes.  The tail predicate is redundant on a tail vector. -/
theorem twoPairTenLocalDeficitTailProfiles_vector_fiber_card
    (d : Fin 10 → Fin 3) (hd : d ∈ twoPairTenDeficitTailVectors) :
    ((twoPairTenLocalDeficitTailProfiles.filter fun rho =>
      twoPairDeficitVector rho = d)).card =
        ∏ g, (twoPairLocalDeficitClass (d g).val).card := by
  classical
  rw [show (twoPairTenLocalDeficitTailProfiles.filter fun rho =>
        twoPairDeficitVector rho = d) =
      Fintype.piFinset (fun g => twoPairLocalDeficitClass (d g).val) by
    ext rho
    simp only [twoPairTenLocalDeficitTailProfiles, Finset.mem_filter,
      Finset.mem_univ, true_and, Fintype.mem_piFinset,
      twoPairLocalDeficitClass, twoPairDeficitVector]
    rw [twoPairTenDeficitTailVectors, Finset.mem_filter] at hd
    constructor
    · intro h g
      have hg := congrFun h.2 g
      exact Fin.ext_iff.mp hg
    · intro h
      have hvec : (fun g =>
          (⟨twoPairLocalCompatibleDeficit (rho g), by
            have hle := twoPairLocalCompatibleDeficit_le_two (rho g)
            omega⟩ : Fin 3)) = d := by
        funext g
        apply Fin.ext
        exact h g
      refine ⟨?_, hvec⟩
      have hsum : (∑ g, twoPairLocalCompatibleDeficit (rho g)) =
          ∑ g, (d g).val := by
        apply Finset.sum_congr rfl
        intro g _
        exact congrArg Fin.val (congrFun hvec g)
      rw [hsum]
      exact hd.2]
  exact Fintype.card_piFinset _

/-- A resource-safe fallback retained after direct reduction of the `3^10` weighted vector sum
overflowed Lean's process stack.  The filtered product is still bounded by the full `81^10`
local tuple space; recovering the sharper convolution equality requires a structural recurrence
proof rather than direct `decide`. -/
theorem twoPairTenLocalDeficitTailProfiles_card_le_full :
    twoPairTenLocalDeficitTailProfiles.card ≤ 81 ^ 10 := by
  calc
    twoPairTenLocalDeficitTailProfiles.card ≤
        (Finset.univ : Finset (Fin 10 → Restriction 4)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = 81 ^ 10 := by norm_num [Fintype.card_congr]

/-- The exact support premise used by the coarse insufficiency certificate.  Unlike the invalid
doubling-only route, this proof transports to the canonical local states and charges the extra
live coordinate forced whenever total deficit is exactly eleven. -/
theorem paddedTwoPair_twentyThree_le_ownedLive_of_ten_lt_deficit (pad : ℕ)
    (σ : Restriction (pad + 40))
    (hdeficit : 10 < ∑ g,
      compatibleResidualQueryDeficit (paddedTwoPairSupport pad) σ 2 g) :
    23 ≤ (paddedTwoPairOwnedLive pad σ).card := by
  let d : Fin 10 → ℕ := fun g =>
    twoPairLocalCompatibleDeficit (paddedTwoPairLocalRestriction pad σ g)
  let q : Fin 10 → ℕ := fun g =>
    stars (paddedTwoPairLocalRestriction pad σ g)
  have hdEq (g : Fin 10) : d g =
      compatibleResidualQueryDeficit (paddedTwoPairSupport pad) σ 2 g :=
    twoPairLocalCompatibleDeficit_paddedTwoPairLocalRestriction pad σ g
  have hqEq (g : Fin 10) : q g =
      (liveSupport (paddedTwoPairSupport pad) σ g).card :=
    stars_paddedTwoPairLocalRestriction pad σ g
  have hdeficit' : 10 < ∑ g, d g := by simpa only [hdEq] using hdeficit
  have hlower : (∑ g, (2 * d g + if d g = 1 then 1 else 0)) ≤ ∑ g, q g := by
    apply Finset.sum_le_sum
    intro g _
    exact twoPairLocal_live_lower_bound _
  rw [paddedTwoPairOwnedLive_card]
  have hqsum : (∑ g, q g) =
      ∑ g, (liveSupport (paddedTwoPairSupport pad) σ g).card := by
    apply Finset.sum_congr rfl
    intro g _
    exact hqEq g
  by_cases hlarge : 12 ≤ ∑ g, d g
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hqsum] at hlower
    omega
  · have hsum : (∑ g, d g) = 11 := by omega
    have hexists : ∃ g, d g = 1 := by
      by_contra hnone
      push_neg at hnone
      have hform (g : Fin 10) : d g = 0 ∨ d g = 2 := by
        have hle : d g ≤ 2 := by
          simpa [d] using twoPairLocalCompatibleDeficit_le_two
            (paddedTwoPairLocalRestriction pad σ g)
        have hne := hnone g
        omega
      have heven : (∑ g, d g) =
          2 * ∑ g, (if d g = 2 then 1 else 0) := by
        calc
          (∑ g, d g) = ∑ g, 2 * (if d g = 2 then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro g _
            rcases hform g with hg | hg <;> simp [hg]
          _ = 2 * ∑ g, if d g = 2 then 1 else 0 := by
            rw [Finset.mul_sum]
      omega
    obtain ⟨g, hg⟩ := hexists
    have hextra : 1 ≤ ∑ h, if d h = 1 then 1 else 0 := by
      calc
        1 = (if d g = 1 then 1 else 0) := by simp [hg]
        _ ≤ ∑ h, if d h = 1 then 1 else 0 := Finset.single_le_sum
          (s := Finset.univ) (f := fun h : Fin 10 => if d h = 1 then 1 else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hqsum] at hlower
    omega

/-- The ambient star count splits without loss into the first `pad` coordinates and the ten
ordered four-coordinate gadget states.  This is the cardinality counterpart of the injective
product code above. -/
theorem stars_paddedTwoPairRestrictionCode (pad : ℕ)
    (σ : Restriction (pad + 40)) :
    stars σ = stars (paddedTwoPairPaddingRestriction pad σ) +
      ∑ g, stars (paddedTwoPairLocalRestriction pad σ g) := by
  rw [stars, freeVars, Finset.card_filter, Fin.sum_univ_add]
  rw [stars, freeVars, Finset.card_filter]
  have hprod := Equiv.sum_comp (finProdFinEquiv : Fin 10 × Fin 4 ≃ Fin 40)
    (fun i : Fin 40 => if σ (Fin.natAdd pad i) = none then 1 else 0)
  rw [Fintype.sum_prod_type] at hprod
  simp_rw [stars, freeVars, Finset.card_filter]
  rw [← hprod]
  simp [paddedTwoPairPaddingRestriction, paddedTwoPairLocalRestriction,
    paddedTwoPairCoord, finProdFinEquiv, Nat.add_comm]

/-- A forty-star point in the exact semantic cost tail has at most twenty-nine live padding
coordinates.  Unlike the earlier compatible-deficit bound, this applies to the whole direct-sum
cost tail. -/
theorem paddedTwoPairFlexibleCostTail_padding_stars_le_twentyNine (pad : ℕ)
    (sigma : Restriction (pad + 40))
    (hsigma : sigma ∈ paddedTwoPairFlexibleCostTail pad) :
    stars (paddedTwoPairPaddingRestriction pad sigma) ≤ 29 := by
  rw [paddedTwoPairFlexibleCostTail, Finset.mem_filter] at hsigma
  have hlocal : twoPairTenFlexibleCost
      (fun g => paddedTwoPairLocalRestriction pad sigma g) ≤
      ∑ g, stars (paddedTwoPairLocalRestriction pad sigma g) := by
    rw [twoPairTenFlexibleCost]
    apply Finset.sum_le_sum
    intro g _
    exact twoPairFlexibleQueryCost_le_stars _
  have hsplit := stars_paddedTwoPairRestrictionCode pad sigma
  omega

/-- Restrictions on `pad` coordinates with at most twenty-nine live coordinates. -/
def paddingRestrictionsAtMostTwentyNine (pad : ℕ) : Finset (Restriction pad) :=
  Finset.univ.filter fun rho => stars rho ≤ 29

/-- The bounded-star padding count is the sum of its thirty exact star layers. -/
theorem paddingRestrictionsAtMostTwentyNine_card (pad : ℕ) :
    (paddingRestrictionsAtMostTwentyNine pad).card =
      ∑ k ∈ Finset.range 30, Nat.choose pad k * 2 ^ (pad - k) := by
  classical
  have hmaps : Set.MapsTo (fun rho : Restriction pad => stars rho)
      (paddingRestrictionsAtMostTwentyNine pad : Set (Restriction pad))
      (Finset.range 30 : Set ℕ) := by
    intro rho hrho
    rw [Finset.mem_coe, paddingRestrictionsAtMostTwentyNine,
      Finset.mem_filter] at hrho
    rw [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le hrho.2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro k hk
  have hk29 : k ≤ 29 := by
    rw [Finset.mem_range] at hk
    omega
  rw [show (paddingRestrictionsAtMostTwentyNine pad).filter (fun rho => stars rho = k) =
      Finset.univ.filter (fun rho : Restriction pad => stars rho = k) by
    ext rho
    simp only [paddingRestrictionsAtMostTwentyNine, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hk29, h⟩⟩]
  exact card_stars_eq pad k

/-- Up to level twenty-nine, each successive padding layer absorbs one lost fixed-value bit once
the padding dimension is at least eighty-six. -/
theorem two_pow_twentyNine_sub_mul_choose_le_choose_twentyNine
    (pad k : ℕ) (hpad : 86 ≤ pad) (hk : k ≤ 29) :
    2 ^ (29 - k) * Nat.choose pad k ≤ Nat.choose pad 29 := by
  induction hk using Nat.decreasingInduction with
  | self => simp
  | of_succ k hk ih =>
      have hklt : k < 29 := by omega
      have hdouble : 2 * Nat.choose pad k ≤ Nat.choose pad (k + 1) := by
        apply Nat.le_of_mul_le_mul_right _ (Nat.zero_lt_succ k)
        rw [Nat.choose_succ_right_eq]
        calc
          (2 * Nat.choose pad k) * (k + 1) =
              Nat.choose pad k * (2 * (k + 1)) := by ring
          _ ≤ Nat.choose pad k * (pad - k) := by
            apply Nat.mul_le_mul_left
            omega
      calc
        2 ^ (29 - k) * Nat.choose pad k =
            2 ^ (29 - (k + 1)) * (2 * Nat.choose pad k) := by
              rw [show 29 - k = (29 - (k + 1)) + 1 by omega, pow_succ]
              ring
        _ ≤ 2 ^ (29 - (k + 1)) * Nat.choose pad (k + 1) :=
          Nat.mul_le_mul_left _ hdouble
        _ ≤ Nat.choose pad 29 := ih

/-- At ambient padding at least eighty-six, the thirty bounded-star layers fit below one top
binomial coefficient times the full fixed-value mass. -/
theorem paddingRestrictionsAtMostTwentyNine_card_le (pad : ℕ) (hpad : 86 ≤ pad) :
    (paddingRestrictionsAtMostTwentyNine pad).card ≤
      Nat.choose pad 29 * 2 ^ pad := by
  rw [paddingRestrictionsAtMostTwentyNine_card]
  calc
    (∑ k ∈ Finset.range 30, Nat.choose pad k * 2 ^ (pad - k)) ≤
        ∑ _k ∈ Finset.range 30,
          Nat.choose pad 29 * 2 ^ (pad - 29) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk29 : k ≤ 29 := by
        rw [Finset.mem_range] at hk
        omega
      calc
        Nat.choose pad k * 2 ^ (pad - k) =
            (2 ^ (29 - k) * Nat.choose pad k) * 2 ^ (pad - 29) := by
          rw [show pad - k = (29 - k) + (pad - 29) by omega, pow_add]
          ring
        _ ≤ Nat.choose pad 29 * 2 ^ (pad - 29) :=
          Nat.mul_le_mul_right _
            (two_pow_twentyNine_sub_mul_choose_le_choose_twentyNine pad k hpad hk29)
    _ = 30 * (Nat.choose pad 29 * 2 ^ (pad - 29)) := by simp
    _ ≤ 2 ^ 29 * (Nat.choose pad 29 * 2 ^ (pad - 29)) := by
      exact Nat.mul_le_mul_right _ (by norm_num)
    _ = Nat.choose pad 29 * 2 ^ pad := by
      rw [show pad = 29 + (pad - 29) by omega, pow_add]
      simp only [Nat.add_sub_cancel_left]
      ring

/-- The complete exact semantic cost tail injects into all ten local states paired with a
padding restriction of at most twenty-nine stars.  This deliberately overcounts local states;
it is enough to decide the concrete shell comparison without a large bivariate convolution. -/
theorem paddedTwoPairFlexibleCostTail_card_le_product (pad : ℕ) :
    (paddedTwoPairFlexibleCostTail pad).card ≤
      81 ^ 10 * (paddingRestrictionsAtMostTwentyNine pad).card := by
  rw [← Finset.card_image_of_injective _ (paddedTwoPairRestrictionCode_injective pad)]
  calc
    ((paddedTwoPairFlexibleCostTail pad).image
      (paddedTwoPairRestrictionCode pad)).card ≤
        (Finset.univ ×ˢ paddingRestrictionsAtMostTwentyNine pad).card := by
      apply Finset.card_le_card
      intro code hcode
      rw [Finset.mem_image] at hcode
      obtain ⟨sigma, hsigma, rfl⟩ := hcode
      rw [Finset.mem_product]
      exact ⟨Finset.mem_univ _, by
        rw [paddingRestrictionsAtMostTwentyNine, Finset.mem_filter]
        exact ⟨Finset.mem_univ _,
          paddedTwoPairFlexibleCostTail_padding_stars_le_twentyNine pad sigma hsigma⟩⟩
    _ = 81 ^ 10 * (paddingRestrictionsAtMostTwentyNine pad).card := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin]
      norm_num [Fintype.card_congr (Equiv.refl (Restriction 4))]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- Even the coarse overcount of the complete exact semantic cost tail is far below the requested
`2^-10` fraction of the forty-star shell at the audited padding.  Hence exact bivariate
convolution cannot make this particular ten-gadget witness refute the half-shell contraction. -/
theorem paddedTwoPairFlexibleCostTail_coarse_scaled_insufficient_4080 :
    81 ^ 10 * (paddingRestrictionsAtMostTwentyNine 4080).card * 2 ^ 10 <
      Nat.choose 4120 40 * 2 ^ 4080 := by
  have hcard := paddingRestrictionsAtMostTwentyNine_card_le 4080 (by norm_num)
  have hcoeff : 81 ^ 10 * Nat.choose 4080 29 * 2 ^ 10 < Nat.choose 4120 40 := by
    norm_num (config := { maxSteps := 1000000 }) [Nat.choose]
  have hscaled := (Nat.mul_lt_mul_right (pow_pos (by norm_num : 0 < 2) 4080)).mpr hcoeff
  calc
    81 ^ 10 * (paddingRestrictionsAtMostTwentyNine 4080).card * 2 ^ 10 ≤
        81 ^ 10 * (Nat.choose 4080 29 * 2 ^ 4080) * 2 ^ 10 := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcard)
    _ = (81 ^ 10 * Nat.choose 4080 29 * 2 ^ 10) * 2 ^ 4080 := by ac_rfl
    _ < Nat.choose 4120 40 * 2 ^ 4080 := hscaled

/-- The exact semantic tail itself is therefore quantitatively insufficient at the audited
schedule, although every one of its points is a genuine bad restriction. -/
theorem paddedTwoPairFlexibleCostTail_scaled_insufficient_4080 :
    (paddedTwoPairFlexibleCostTail 4080).card * 2 ^ 10 <
      Nat.choose 4120 40 * 2 ^ 4080 := by
  exact lt_of_le_of_lt
    (Nat.mul_le_mul_right (2 ^ 10)
      (paddedTwoPairFlexibleCostTail_card_le_product 4080))
    paddedTwoPairFlexibleCostTail_coarse_scaled_insufficient_4080

/-- A certified forty-star deficit-tail profile has at most seventeen live padding coordinates.
This is the exact support consequence needed by the coarse padding charge. -/
theorem paddedTwoPair_padding_stars_le_seventeen (pad : ℕ)
    (σ : Restriction (pad + 40))
    (hstars : stars σ = 40)
    (hdeficit : 10 < ∑ g,
      compatibleResidualQueryDeficit (paddedTwoPairSupport pad) σ 2 g) :
    stars (paddedTwoPairPaddingRestriction pad σ) ≤ 17 := by
  have howned :=
    paddedTwoPair_twentyThree_le_ownedLive_of_ten_lt_deficit pad σ hdeficit
  rw [paddedTwoPairOwnedLive_card] at howned
  have hsplit := stars_paddedTwoPairRestrictionCode pad σ
  have hlocal : (∑ g, stars (paddedTwoPairLocalRestriction pad σ g)) =
      ∑ g, (liveSupport (paddedTwoPairSupport pad) σ g).card := by
    apply Finset.sum_congr rfl
    intro g _
    exact stars_paddedTwoPairLocalRestriction pad σ g
  rw [hlocal] at hsplit
  omega

/-! ### Generic bounded-star padding count

The concrete `Fin 4080` filter is too large to reduce during elaboration.  Keep the finite type
parametric, partition by the star count, and do the remaining binomial comparison symbolically.
The threshold `50 ≤ pad` is more than enough for the needed instance and makes every successive
binomial coefficient through level seventeen grow by a factor of at least two. -/

/-- Restrictions on `pad` coordinates with at most seventeen live coordinates. -/
def paddingRestrictionsAtMostSeventeen (pad : ℕ) : Finset (Restriction pad) :=
  Finset.univ.filter fun rho => stars rho ≤ 17

/-- The bounded-star padding count is the sum of its eighteen exact star layers. -/
theorem paddingRestrictionsAtMostSeventeen_card (pad : ℕ) :
    (paddingRestrictionsAtMostSeventeen pad).card =
      ∑ k ∈ Finset.range 18, Nat.choose pad k * 2 ^ (pad - k) := by
  classical
  have hmaps : Set.MapsTo (fun rho : Restriction pad => stars rho)
      (paddingRestrictionsAtMostSeventeen pad : Set (Restriction pad))
      (Finset.range 18 : Set ℕ) := by
    intro rho hrho
    rw [Finset.mem_coe, paddingRestrictionsAtMostSeventeen,
      Finset.mem_filter] at hrho
    rw [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le hrho.2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro k hk
  have hk17 : k ≤ 17 := by
    rw [Finset.mem_range] at hk
    omega
  rw [show (paddingRestrictionsAtMostSeventeen pad).filter (fun rho => stars rho = k) =
      Finset.univ.filter (fun rho : Restriction pad => stars rho = k) by
    ext rho
    simp only [paddingRestrictionsAtMostSeventeen, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hk17, h⟩⟩]
  exact card_stars_eq pad k

/-- Up to level seventeen, each step in the binomial row at ambient size at least fifty more
than compensates for one lost fixed-value bit. -/
theorem two_pow_seventeen_sub_mul_choose_le_choose_seventeen
    (pad k : ℕ) (hpad : 50 ≤ pad) (hk : k ≤ 17) :
    2 ^ (17 - k) * Nat.choose pad k ≤ Nat.choose pad 17 := by
  induction hk using Nat.decreasingInduction with
  | self => simp
  | of_succ k hk ih =>
      have hklt : k < 17 := by omega
      have hdouble : 2 * Nat.choose pad k ≤ Nat.choose pad (k + 1) := by
        apply Nat.le_of_mul_le_mul_right _ (Nat.zero_lt_succ k)
        rw [Nat.choose_succ_right_eq]
        calc
          (2 * Nat.choose pad k) * (k + 1) =
              Nat.choose pad k * (2 * (k + 1)) := by ring
          _ ≤ Nat.choose pad k * (pad - k) := by
            apply Nat.mul_le_mul_left
            omega
      calc
        2 ^ (17 - k) * Nat.choose pad k =
            2 ^ (17 - (k + 1)) * (2 * Nat.choose pad k) := by
              rw [show 17 - k = (17 - (k + 1)) + 1 by omega, pow_succ]
              ring
        _ ≤ 2 ^ (17 - (k + 1)) * Nat.choose pad (k + 1) :=
          Nat.mul_le_mul_left _ hdouble
        _ ≤ Nat.choose pad 17 := ih

/-- Generic shell bound used by the padded two-pair transport.  The proof never specializes the
restriction type to `Fin 4080`; all large arithmetic remains in the theorem parameters. -/
theorem paddingRestrictionsAtMostSeventeen_card_le (pad : ℕ) (hpad : 50 ≤ pad) :
    (paddingRestrictionsAtMostSeventeen pad).card ≤
      Nat.choose pad 17 * 2 ^ pad := by
  rw [paddingRestrictionsAtMostSeventeen_card]
  calc
    (∑ k ∈ Finset.range 18, Nat.choose pad k * 2 ^ (pad - k)) ≤
        ∑ _k ∈ Finset.range 18,
          Nat.choose pad 17 * 2 ^ (pad - 17) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk17 : k ≤ 17 := by
        rw [Finset.mem_range] at hk
        omega
      calc
        Nat.choose pad k * 2 ^ (pad - k) =
            (2 ^ (17 - k) * Nat.choose pad k) * 2 ^ (pad - 17) := by
          rw [show pad - k = (17 - k) + (pad - 17) by omega, pow_add]
          ring
        _ ≤ Nat.choose pad 17 * 2 ^ (pad - 17) :=
          Nat.mul_le_mul_right _
            (two_pow_seventeen_sub_mul_choose_le_choose_seventeen pad k hpad hk17)
    _ = 18 * (Nat.choose pad 17 * 2 ^ (pad - 17)) := by simp
    _ ≤ 2 ^ 17 * (Nat.choose pad 17 * 2 ^ (pad - 17)) := by
      exact Nat.mul_le_mul_right _ (by norm_num)
    _ = Nat.choose pad 17 * 2 ^ pad := by
      rw [show pad = 17 + (pad - 17) by omega, pow_add]
      simp only [Nat.add_sub_cancel_left]
      ring

/-- The exact ambient deficit-tail class injects into the product of the ten-local deficit tail
and the bounded-star padding class.  This is the resource-safe counting bridge: it uses the
structural product code and never enumerates `Restriction (pad + 40)`. -/
theorem paddedTwoPairCompatibleDeficitProfiles_card_le_product (pad : ℕ) :
    (paddedTwoPairCompatibleDeficitProfiles pad).card ≤
      twoPairTenLocalDeficitTailProfiles.card *
        (paddingRestrictionsAtMostSeventeen pad).card := by
  classical
  rw [← Finset.card_product]
  calc
    (paddedTwoPairCompatibleDeficitProfiles pad).card =
        ((paddedTwoPairCompatibleDeficitProfiles pad).image
          (paddedTwoPairRestrictionCode pad)).card :=
      (Finset.card_image_of_injective _
        (paddedTwoPairRestrictionCode_injective pad)).symm
    _ ≤ (twoPairTenLocalDeficitTailProfiles ×ˢ
          paddingRestrictionsAtMostSeventeen pad).card := by
      apply Finset.card_le_card
      intro code hcode
      rw [Finset.mem_image] at hcode
      obtain ⟨sigma, hsigma, rfl⟩ := hcode
      rw [Finset.mem_product]
      rw [paddedTwoPairCompatibleDeficitProfiles, Finset.mem_filter] at hsigma
      refine ⟨?_, ?_⟩
      · rw [twoPairTenLocalDeficitTailProfiles, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        change 10 < ∑ g,
          twoPairLocalCompatibleDeficit (paddedTwoPairLocalRestriction pad sigma g)
        simpa only [twoPairLocalCompatibleDeficit_paddedTwoPairLocalRestriction] using
          hsigma.2.2
      · rw [paddingRestrictionsAtMostSeventeen, Finset.mem_filter]
        exact ⟨Finset.mem_univ _,
          paddedTwoPair_padding_stars_le_seventeen pad sigma hsigma.2.1 hsigma.2.2⟩

/-- Combining the product bridge with the full `81^10` local fallback and the generic padding
bound already controls the ambient profile class.  Thus the sharper weighted `3^10` sum is not
needed for this one-sided quantitative test. -/
theorem paddedTwoPairCompatibleDeficitProfiles_card_le_full (pad : ℕ) (hpad : 50 ≤ pad) :
    (paddedTwoPairCompatibleDeficitProfiles pad).card ≤
      81 ^ 10 * (Nat.choose pad 17 * 2 ^ pad) := by
  calc
    (paddedTwoPairCompatibleDeficitProfiles pad).card ≤
        twoPairTenLocalDeficitTailProfiles.card *
          (paddingRestrictionsAtMostSeventeen pad).card :=
      paddedTwoPairCompatibleDeficitProfiles_card_le_product pad
    _ ≤ 81 ^ 10 * (Nat.choose pad 17 * 2 ^ pad) :=
      Nat.mul_le_mul twoPairTenLocalDeficitTailProfiles_card_le_full
        (paddingRestrictionsAtMostSeventeen_card_le pad hpad)

/-- The all-false class inherits the same coarse product bound by the proved complement
bijection; no second local-state count or padding argument is needed. -/
theorem paddedTwoPairFalseCompatibleDeficitProfiles_card_le_full
    (pad : ℕ) (hpad : 50 ≤ pad) :
    (paddedTwoPairFalseCompatibleDeficitProfiles pad).card ≤
      81 ^ 10 * (Nat.choose pad 17 * 2 ^ pad) := by
  rw [paddedTwoPairFalseCompatibleDeficitProfiles_card]
  exact paddedTwoPairCompatibleDeficitProfiles_card_le_full pad hpad

set_option maxRecDepth 100000 in
/-- Even charging all `81^10` local tuples, rather than only the compatible-deficit tail, is
strictly too small to supply the requested `2^-10` fraction of the forty-star shell at padding
4,080. -/
theorem twoPairFullLocalSpace_4080_padding_scaled_insufficient :
    81 ^ 10 * (Nat.choose 4080 17 * 2 ^ 4080) * 2 ^ 10 <
      Nat.choose 4120 40 * 2 ^ 4080 := by
  decide

set_option maxRecDepth 100000 in
/-- Even two disjoint copies of the deliberately coarse full-local-space charge remain strictly
below the requested tenth-bit shell fraction.  Consequently, once the all-false symmetric class
has the same product bound as the all-true class, their union is already known to be insufficient;
computing the intersection can only decrease that union and is not needed for this quantitative
decision. -/
theorem two_mul_twoPairFullLocalSpace_4080_padding_scaled_insufficient :
    2 * (81 ^ 10 * (Nat.choose 4080 17 * 2 ^ 4080)) * 2 ^ 10 <
      Nat.choose 4120 40 * 2 ^ 4080 := by
  decide

/-- Abstract union wrapper for the preceding arithmetic certificate.  It deliberately assumes
only the two one-sided cardinality bounds and makes no disjointness or intersection hypothesis. -/
theorem twoPair_two_coarse_profile_classes_union_scaled_insufficient
    (A B : Finset (Restriction 4120))
    (hA : A.card ≤ 81 ^ 10 * (Nat.choose 4080 17 * 2 ^ 4080))
    (hB : B.card ≤ 81 ^ 10 * (Nat.choose 4080 17 * 2 ^ 4080)) :
    (A ∪ B).card * 2 ^ 10 < Nat.choose 4120 40 * 2 ^ 4080 := by
  calc
    (A ∪ B).card * 2 ^ 10 ≤ (A.card + B.card) * 2 ^ 10 :=
      Nat.mul_le_mul_right _ (Finset.card_union_le A B)
    _ ≤ (2 * (81 ^ 10 * (Nat.choose 4080 17 * 2 ^ 4080))) * 2 ^ 10 := by
      apply Nat.mul_le_mul_right
      omega
    _ < Nat.choose 4120 40 * 2 ^ 4080 :=
      two_mul_twoPairFullLocalSpace_4080_padding_scaled_insufficient

/-- The two symmetric semantic certificates together remain a subset of the actual bad event. -/
theorem paddedTwoPair_two_compatible_classes_union_subset_bad (pad : ℕ) :
    paddedTwoPairCompatibleDeficitProfiles pad ∪
        paddedTwoPairFalseCompatibleDeficitProfiles pad ⊆
      commonShallowBad (paddedTwoPairFamily pad) (pad + 40) 40 10 1 := by
  exact Finset.union_subset
    (paddedTwoPairCompatibleDeficitProfiles_subset_bad pad)
    (paddedTwoPairFalseCompatibleDeficitProfiles_subset_bad pad)

/-- The completed two-sided compatible-deficit strategy is quantitatively insufficient at the
support schedule, even before subtracting the overlap of its two profile classes. -/
theorem paddedTwoPair_two_compatible_classes_union_scaled_insufficient :
    (paddedTwoPairCompatibleDeficitProfiles 4080 ∪
        paddedTwoPairFalseCompatibleDeficitProfiles 4080).card * 2 ^ 10 <
      Nat.choose 4120 40 * 2 ^ 4080 := by
  apply twoPair_two_coarse_profile_classes_union_scaled_insufficient
  · exact paddedTwoPairCompatibleDeficitProfiles_card_le_full 4080 (by norm_num)
  · exact paddedTwoPairFalseCompatibleDeficitProfiles_card_le_full 4080 (by norm_num)

/-- The entire certified compatible-deficit profile class is therefore quantitatively
insufficient at the audited shell parameters, without any exact weighted-vector enumeration. -/
theorem paddedTwoPairCompatibleDeficitProfiles_4080_scaled_insufficient :
    (paddedTwoPairCompatibleDeficitProfiles 4080).card * 2 ^ 10 <
      Nat.choose 4120 40 * 2 ^ 4080 := by
  exact lt_of_le_of_lt
    (Nat.mul_le_mul_right (2 ^ 10)
      (paddedTwoPairCompatibleDeficitProfiles_card_le_full 4080 (by norm_num)))
    twoPairFullLocalSpace_4080_padding_scaled_insufficient

set_option maxRecDepth 100000 in
/-- A conservative arithmetic certificate for insufficiency at padding 4,080.  Any contributing
profile has at least 23 owned-live coordinates, hence at most 17 live padding coordinates; even
charging every tail profile the largest resulting padding choice and all `2^40` owned-value
choices remains strictly below the required `2^-10` shell fraction.  The semantic transport must
still justify that charging bound. -/
theorem twoPairTenFoldDeficitTail_4080_coarse_insufficient :
    twoPairTenFoldDeficitTail * Nat.choose 4080 17 * 2 ^ 40 * 2 ^ 10 <
      Nat.choose 4120 40 * 2 ^ 40 := by
  rw [twoPairTenFoldDeficitTail_exact]
  decide

/-- The same numerical certificate with the actual padding-value factor.  The earlier `2^40`
was only a cancellable common factor; an ambient restriction count must carry `2^4080`. -/
theorem twoPairTenFoldDeficitTail_4080_padding_scaled_insufficient :
    twoPairTenFoldDeficitTail * Nat.choose 4080 17 * 2 ^ 4080 * 2 ^ 10 <
      Nat.choose 4120 40 * 2 ^ 4080 := by
  have h := twoPairTenFoldDeficitTail_4080_coarse_insufficient
  have hcommon :
      (twoPairTenFoldDeficitTail * Nat.choose 4080 17 * 2 ^ 10) * 2 ^ 40 <
        Nat.choose 4120 40 * 2 ^ 40 := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have hbase : twoPairTenFoldDeficitTail * Nat.choose 4080 17 * 2 ^ 10 <
      Nat.choose 4120 40 :=
    (Nat.mul_lt_mul_right (by positivity : 0 < 2 ^ 40)).mp hcommon
  have hscaled :=
    (Nat.mul_lt_mul_right (by positivity : 0 < 2 ^ 4080)).mpr hbase
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hscaled

/-- The exact profile class obtained by fixing every padding coordinate arbitrarily while keeping
the forty gadget coordinates live. -/
noncomputable def paddedTwoPairFullyLiveFiber (pad : ℕ) :
    Finset (Restriction (pad + 40)) :=
  restrictionExtensionFreeSetFiber (fun _ => none)
    (freeVars (paddedRectangularRestriction pad 10 4))

/-- Every member of the fully-live profile fiber belongs to the semantic bad event. -/
theorem paddedTwoPairFullyLiveFiber_subset_bad (pad : ℕ) :
    paddedTwoPairFullyLiveFiber pad ⊆
      commonShallowBad (paddedTwoPairFamily pad) (pad + 40) 40 10 1 := by
  classical
  intro σ hσ
  rw [paddedTwoPairFullyLiveFiber, restrictionExtensionFreeSetFiber,
    Finset.mem_filter] at hσ
  rw [mem_commonShallowBad]
  have hstars : stars σ = 40 := by
    rw [stars, hσ.2.2, ← stars,
      stars_paddedRectangularRestriction (pad := pad) (G := 10) (m := 4)]
  refine ⟨hstars, paddedTwoPair_not_commonShallow_ten_of_support_free pad σ ?_⟩
  intro g k
  apply mem_freeVars.mp
  rw [hσ.2.2]
  apply mem_freeVars.mpr
  rw [show paddedTwoPairCoord pad g k =
      Fin.natAdd pad (finProdFinEquiv (g, k)) by
    apply Fin.ext
    simp [paddedTwoPairCoord, finProdFinEquiv]
    omega]
  exact paddedRectangularRestriction_target_free (pad := pad) (key := (g, k))

/-- The certified fully-live bad profile class has exactly one Boolean choice per padding
coordinate. -/
theorem paddedTwoPairFullyLiveFiber_card (pad : ℕ) :
    (paddedTwoPairFullyLiveFiber pad).card = 2 ^ pad := by
  classical
  rw [paddedTwoPairFullyLiveFiber, card_restrictionExtends_freeVars_eq]
  · rw [show (freeVars (fun _ : Fin (pad + 40) => none)).card = pad + 40 by
        simp [freeVars],
      show (freeVars (paddedRectangularRestriction pad 10 4)).card = 40 by
        rw [← stars, stars_paddedRectangularRestriction]]
    rw [Nat.add_sub_cancel]
  · intro i hi
    simp [mem_freeVars]

/-- Even after the requested `2^10` scaling, this first certified profile fiber is strictly
smaller than the ambient forty-live shell as soon as padding is present.  Thus the class is exact
and substantial (`2^pad` roots), but is still quantitatively insufficient by itself. -/
theorem paddedTwoPairFullyLiveFiber_scaled_lt_shell (pad : ℕ) (hpad : 3 ≤ pad) :
    (paddedTwoPairFullyLiveFiber pad).card * 2 ^ 10 <
      Nat.choose (pad + 40) 40 * 2 ^ pad := by
  rw [paddedTwoPairFullyLiveFiber_card]
  have hchoose : 2 ^ 10 < Nat.choose (pad + 40) 40 := by
    have hmono : Nat.choose 43 40 ≤ Nat.choose (pad + 40) 40 := by
      apply Nat.choose_le_choose
      omega
    have hbase : 2 ^ 10 < Nat.choose 43 40 := by norm_num [Nat.choose]
    exact hbase.trans_le hmono
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ pad)).mpr hchoose

theorem paddedTwoPairBad_forty_eq_empty (pad : ℕ) :
    commonShallowBad (paddedTwoPairFamily pad) (pad + 40) 40 40 1 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro σ hσ
  have hbad := (mem_commonShallowBad.mp hσ).2
  exact hbad (paddedTwoPairFamily_commonShallow_forty pad (pad + 40) σ)

set_option maxRecDepth 1000
set_option maxHeartbeats 200000
set_option linter.constructorNameAsVariable true

/-- The old hard-coded certified tail is exactly the `pad = 163980` instance of the new mass
function.  This connects the parameterization to the already proved bad-event subset rather than
introducing an unrelated numerical expression. -/
theorem scheduledSingletonCertifiedTail_card_eq_paddedMass :
    scheduledSingletonCertifiedTail.card = paddedSingletonCertifiedMass 163980 := by
  rw [scheduledSingletonCertifiedTail_card]
  rfl

/-- At the support-specific padding, the normalized overlap coefficient is still strictly below
the complete 4,100-coordinate support shell coefficient. -/
theorem paddedSingletonCertifiedCoefficient_4080_lt :
    paddedSingletonCertifiedCoefficient 4080 < Nat.choose 4100 20 := by
  let B := ∑ q ∈ Finset.Icc 11 20,
    Nat.choose 20 q * 4080 ^ (20 - q) * 2 ^ (q - 10)
  have hupper : paddedSingletonCertifiedCoefficient 4080 ≤ B := by
    rw [paddedSingletonCertifiedCoefficient]
    apply Finset.sum_le_sum
    intro q hq
    exact Nat.mul_le_mul_right (2 ^ (q - 10)) <|
      Nat.mul_le_mul_left (Nat.choose 20 q) (Nat.choose_le_pow 4080 (20 - q))
  have hnumeric : B * Nat.factorial 20 < Nat.descFactorial 4100 20 := by
    norm_num [B, Finset.sum_Icc_succ_top, Nat.descFactorial, Nat.choose]
  have hscaled : paddedSingletonCertifiedCoefficient 4080 * Nat.factorial 20 <
      Nat.choose 4100 20 * Nat.factorial 20 := by
    rw [Nat.mul_comm (Nat.choose 4100 20),
      ← Nat.descFactorial_eq_factorial_mul_choose]
    exact lt_of_le_of_lt (Nat.mul_le_mul_right (Nat.factorial 20) hupper) hnumeric
  exact (Nat.mul_lt_mul_right (Nat.factorial_pos 20)).mp hscaled

/-- Factoring the common padding power turns the full parametric mass into its coefficient. -/
theorem paddedSingletonCertifiedMass_lt_shell_div_two_pow_ten_4080 :
    paddedSingletonCertifiedMass 4080 < Nat.choose 4100 20 * 2 ^ 4070 := by
  have hscaled := finset_sum_mul_two_pow_add_lt_mul_two_pow
    (Finset.Icc 11 20)
    (fun q => Nat.choose 20 q * Nat.choose 4080 (20 - q))
    (fun q => q - 10) (k := 4070)
    paddedSingletonCertifiedCoefficient_4080_lt
  rw [paddedSingletonCertifiedMass]
  refine lt_of_eq_of_lt ?_ hscaled
  apply Finset.sum_congr rfl
  intro q hq
  have hq10 : 10 ≤ q := le_trans (by omega) (Finset.mem_Icc.mp hq).1
  have hexp : 4080 - 20 + q = 4070 + (q - 10) := by omega
  rw [hexp]

/-- Even after multiplying by the requested `2^10` contraction factor, the parameterized
packed-singleton mass at `pad = 4080` is strictly smaller than the complete shell of restrictions
with twenty live coordinates in ambient dimension 4,100. -/
theorem paddedSingletonCertifiedMass_mul_two_pow_ten_lt_shell_4080 :
    paddedSingletonCertifiedMass 4080 * 2 ^ 10 <
      Nat.choose 4100 20 * 2 ^ 4080 := by
  have h := mul_two_pow_lt_mul_two_pow_add (k := 4070) (r := 10)
    paddedSingletonCertifiedMass_lt_shell_div_two_pow_ten_4080
  norm_num at h ⊢
  exact h

set_option maxRecDepth 1000
set_option maxHeartbeats 200000
set_option linter.constructorNameAsVariable true

/-- Badness is local to the twenty-coordinate live support: the values of all fixed padding
coordinates are irrelevant.  No restriction with exactly the scheduled singleton support free
admits the depth-ten, residual-depth-zero common-shallow certificate. -/
theorem scheduledSingletonSupport_not_commonShallow
    (σ : Restriction 164000) (hfree : freeVars σ = scheduledSingletonSupport) :
    ¬CommonShallowAt
      (normalizedLayeredBottomFamily
        (paddedRectangularSingletonRoundOutput 163980 1 20)) 20 σ 10 0 := by
  apply scheduledSingletonSupport_not_commonShallow_of_live_false σ
  · rw [stars, hfree, scheduledSingletonSupport_card]
  · have hfilter : scheduledSingletonSupport.filter (fun i => σ i = none) =
        scheduledSingletonSupport := by
      apply Finset.filter_eq_self.mpr
      intro i hi
      rw [← mem_freeVars, hfree]
      exact hi
    rw [hfilter, scheduledSingletonSupport_card]
    omega
  · intro i hi hne
    exfalso
    apply hne
    rw [← mem_freeVars, hfree]
    exact hi

/-- Every exact-support restriction lies in the scheduled bad finset. -/
theorem scheduledSingletonSupport_fiber_mem_bad
    (σ : Restriction 164000) (hfree : freeVars σ = scheduledSingletonSupport) :
    σ ∈ scheduledSingletonBad := by
  rw [scheduledSingletonBad, mem_commonShallowBad]
  exact ⟨by rw [stars, hfree, scheduledSingletonSupport_card],
    scheduledSingletonSupport_not_commonShallow σ hfree⟩

set_option maxRecDepth 8192 in
/-- The exact saturated restriction used by the schedule capstone is one member of the full bad
support fiber. -/
theorem paddedRectangularRoundOutput_schedule_restriction_mem_bad :
    paddedRectangularRestriction 163980 1 20 ∈ scheduledSingletonBad := by
  have hfree : freeVars (paddedRectangularRestriction 163980 1 20) =
      scheduledSingletonSupport := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      rw [scheduledSingletonSupport, paddedSingletonSupport, Finset.mem_image] at hi
      obtain ⟨j, _, rfl⟩ := hi
      rw [mem_freeVars]
      exact paddedRectangularRestriction_target_free
        (pad := 163980) (key := ((0 : Fin 1), j))
    · rw [scheduledSingletonSupport_card]
      exact le_of_eq (by
        simpa [stars] using
          (stars_paddedRectangularRestriction (pad := 163980) (G := 1) (m := 20)))
  rw [scheduledSingletonBad, mem_commonShallowBad]
  exact ⟨by rw [stars, hfree, scheduledSingletonSupport_card],
    scheduledSingletonSupport_not_commonShallow
      (paddedRectangularRestriction 163980 1 20) hfree⟩

set_option maxRecDepth 8192 in
/-- Every assignment to the fixed padding coordinates gives a distinct bad scheduled restriction.
Consequently the bad event contains at least `2^163980` shell points, all with the same live
support. -/
theorem scheduledSingletonSupport_bad_card_lower_bound :
    2 ^ 163980 ≤ scheduledSingletonBad.card := by
  classical
  let BadProp (σ : Restriction 164000) : Prop :=
    stars σ = 20 ∧
      ¬CommonShallowAt
        (normalizedLayeredBottomFamily
          (paddedRectangularSingletonRoundOutput 163980 1 20)) 20 σ 10 0
  let embed : {σ : Restriction 164000 // freeVars σ = scheduledSingletonSupport} →
      {σ : Restriction 164000 // BadProp σ} := fun σ => ⟨σ.1, by
        exact ⟨by rw [stars, σ.2, scheduledSingletonSupport_card],
          scheduledSingletonSupport_not_commonShallow σ.1 σ.2⟩⟩
  have hinjective : Function.Injective embed := by
    intro σ τ h
    have hv : (embed σ).1 = (embed τ).1 :=
      congrArg (fun z : {ρ : Restriction 164000 // BadProp ρ} => z.1) h
    exact Subtype.ext hv
  have hcard :
      Fintype.card {σ : Restriction 164000 // freeVars σ = scheduledSingletonSupport} ≤
        Fintype.card {σ : Restriction 164000 // BadProp σ} :=
    Fintype.card_le_of_injective embed hinjective
  have hfiber := card_freeVars_eq (N := 164000) scheduledSingletonSupport
  rw [← Fintype.card_subtype, scheduledSingletonSupport_card] at hfiber
  have hbadCard : Fintype.card {σ : Restriction 164000 // BadProp σ} =
      scheduledSingletonBad.card := by
    rw [scheduledSingletonBad, commonShallowBad, ← Fintype.card_subtype]
  rw [hfiber, hbadCard] at hcard
  exact hcard

/-- The non-root saturation obstruction is compatible with the exact probabilistic shell
schedule, not merely with an arbitrary sparse restriction.  At the concrete level-zero
parameters `M = 10`, `s = 0`, and `r = 1`, the schedule has ambient dimension `164000`, shell
size `20`, and exact two-polarity key cap `40`.  Taking one row of twenty independent singleton
clauses and padding by `163980` fixed coordinates realizes all three values simultaneously.

The schedule's global half-shell contraction theorem still applies to this circuit family.  Thus
the density premise does not exclude the saturated state; any argument that gives it negligible
weight must use information beyond occurrence count, live count, and membership in the scheduled
shell. -/
theorem paddedRectangularRoundOutput_realizes_actual_schedule :
    let C := paddedRectangularSingletonRoundOutput 163980 1 20
    let σ := paddedRectangularRestriction 163980 1 20
    RestrictionExtends (fun _ : Fin 164000 => none) σ ∧
      σ ≠ (fun _ => none) ∧
      collapseRound 1 σ (paddedRectangularSingletonPredecessor 163980 1 20) = C ∧
      bottomClauseCount C = stars σ ∧
      σ ∈ (Finset.univ.filter fun τ : Restriction
          (layeredRoundActualLive 10 0 1 0) =>
        stars τ = layeredRoundActualShell 10 0 1 0) ∧
      (∑ g, (normalizedLayeredBottomFamily C g).length) ≤
        layeredRoundActualKeyCap 10 0 ∧
      (commonShallowBad (normalizedLayeredBottomFamily C) 20
          (layeredRoundActualShell 10 0 1 0)
          (10 * (1 * layeredRoundActualScale 10 0 ^ 0)) 0).card *
          2 ^ (10 * (1 * layeredRoundActualScale 10 0 ^ 0)) ≤
        (Finset.univ.filter fun τ : Restriction
            (layeredRoundActualLive 10 0 1 0) =>
          stars τ = layeredRoundActualShell 10 0 1 0).card := by
  dsimp only
  have hsat := paddedRectangularRoundOutput_saturates_global_budgets
    (pad := 163980) (G := 1) (m := 20) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, hsat.2.1, hsat.2.2.2.1, hsat.2.2.2.2.2, ?_, ?_, ?_⟩
  · simpa using hsat.1
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [stars_paddedRectangularRestriction]
    norm_num [layeredRoundActualShell]
  · calc
      (∑ g, (normalizedLayeredBottomFamily
          (paddedRectangularSingletonRoundOutput 163980 1 20) g).length) ≤
          2 * bottomClauseCount
            (paddedRectangularSingletonRoundOutput 163980 1 20) :=
        normalizedLayeredBottomFamily_total_length_le _
      _ = layeredRoundActualKeyCap 10 0 := by
        rw [bottomClauseCount_paddedRectangularSingletonRoundOutput]
        norm_num [layeredRoundActualKeyCap]
  · apply normalizedLayered_commonShallowBad_scaled_le_actual_schedule
      (M := 10) (s := 0) (r := 1) (j := 0) (fuel := 20)
    · norm_num
    · exact paddedRectangularSingletonRoundOutput_bottomWidth_one
    · calc
        (∑ g, (normalizedLayeredBottomFamily
            (paddedRectangularSingletonRoundOutput 163980 1 20) g).length) ≤
            2 * bottomClauseCount
              (paddedRectangularSingletonRoundOutput 163980 1 20) :=
          normalizedLayeredBottomFamily_total_length_le _
        _ = layeredRoundActualKeyCap 10 0 := by
          rw [bottomClauseCount_paddedRectangularSingletonRoundOutput]
          norm_num [layeredRoundActualKeyCap]
    · norm_num [layeredRoundActualShell]

/-- The same padded singleton state fits the twenty-times-smaller support-specific schedule.
At `M = 10`, `s = 0`, and `r = 1`, the improved ambient dimension is `4100`, the shell remains
twenty, and the exact normalized key cap remains forty.  The output owns at least all twenty live
coordinates, yet the support-specific global contraction still applies. -/
theorem paddedRectangularRoundOutput_realizes_support_schedule :
    let C := paddedRectangularSingletonRoundOutput 4080 1 20
    let σ := paddedRectangularRestriction 4080 1 20
    RestrictionExtends (fun _ : Fin 4100 => none) σ ∧
      σ ≠ (fun _ => none) ∧
      collapseRound 1 σ (paddedRectangularSingletonPredecessor 4080 1 20) = C ∧
      bottomClauseCount C = stars σ ∧
      stars σ ≤
        (familyVariableSupport (normalizedLayeredBottomFamily C)).card ∧
      σ ∈ (Finset.univ.filter fun τ : Restriction
          (layeredRoundSupportLive 10 0 1 0) =>
        stars τ = layeredRoundSupportShell 10 0 1 0) ∧
      (∑ g, (normalizedLayeredBottomFamily C g).length) ≤
        layeredRoundActualKeyCap 10 0 ∧
      (commonShallowBad (normalizedLayeredBottomFamily C) 20
          (layeredRoundSupportShell 10 0 1 0)
          (10 * (1 * layeredRoundSupportScale 10 0 ^ 0)) 0).card *
          2 ^ (10 * (1 * layeredRoundSupportScale 10 0 ^ 0)) ≤
        (Finset.univ.filter fun τ : Restriction
            (layeredRoundSupportLive 10 0 1 0) =>
          stars τ = layeredRoundSupportShell 10 0 1 0).card := by
  dsimp only
  have hsat := paddedRectangularRoundOutput_saturates_global_budgets
    (pad := 4080) (G := 1) (m := 20) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hsat.1, hsat.2.1, hsat.2.2.2.1, hsat.2.2.2.2.2, ?_, ?_, ?_, ?_⟩
  · exact stars_paddedRectangularRestriction_le_familyVariableSupport_card
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [stars_paddedRectangularRestriction]
    norm_num [layeredRoundSupportShell]
  · calc
      (∑ g, (normalizedLayeredBottomFamily
          (paddedRectangularSingletonRoundOutput 4080 1 20) g).length) ≤
          2 * bottomClauseCount
            (paddedRectangularSingletonRoundOutput 4080 1 20) :=
        normalizedLayeredBottomFamily_total_length_le _
      _ = layeredRoundActualKeyCap 10 0 := by
        rw [bottomClauseCount_paddedRectangularSingletonRoundOutput]
        norm_num [layeredRoundActualKeyCap]
  · apply normalizedLayered_commonShallowBad_scaled_le_support_schedule
      (M := 10) (s := 0) (r := 1) (j := 0) (fuel := 20)
    · norm_num
    · exact paddedRectangularSingletonRoundOutput_bottomWidth_one
    · calc
        (∑ g, (normalizedLayeredBottomFamily
            (paddedRectangularSingletonRoundOutput 4080 1 20) g).length) ≤
            2 * bottomClauseCount
              (paddedRectangularSingletonRoundOutput 4080 1 20) :=
          normalizedLayeredBottomFamily_total_length_le _
        _ = layeredRoundActualKeyCap 10 0 := by
          rw [bottomClauseCount_paddedRectangularSingletonRoundOutput]
          norm_num [layeredRoundActualKeyCap]
    · norm_num [layeredRoundSupportShell]

/-- Counting the injective charge gives the exact two-walk occurrence budget.  Repeated edge
values on a walk can only shrink the slot type, so no walk-simplicity premise is needed here. -/
theorem InclusionMinimalUnsatisfiableCore.card_le_twoWalk_lengths
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2)
    (ell : Lit n)
    (forward : EdgeWalk (implicationEdges
      (outsideCoreTwoSATClauses hnonempty hwidth)) ell (neg ell))
    (backward : EdgeWalk (implicationEdges
      (outsideCoreTwoSATClauses hnonempty hwidth)) (neg ell) ell) :
    core.card ≤ EdgeWalk.length forward + EdgeWalk.length backward := by
  have hcard : Fintype.card (↑core) ≤
      Fintype.card (TwoWalkUsedEdgeSlot forward backward) :=
    Fintype.card_le_of_injective
      (hminimal.coreOutsideEdgeCharge hnonempty hwidth ell forward backward)
      (hminimal.coreOutsideEdgeCharge_injective hnonempty hwidth ell forward backward)
  rw [Fintype.card_coe, Fintype.card_sum] at hcard
  calc
    core.card ≤
        (TwoSATPathCharge.EdgeWalk.usedEdges forward).toFinset.card +
          (TwoSATPathCharge.EdgeWalk.usedEdges backward).toFinset.card := by
      simpa only [Fintype.card_coe] using hcard
    _ ≤ (TwoSATPathCharge.EdgeWalk.usedEdges forward).length +
          (TwoSATPathCharge.EdgeWalk.usedEdges backward).length :=
      Nat.add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)
    _ = EdgeWalk.length forward + EdgeWalk.length backward := by
      rw [TwoSATPathCharge.EdgeWalk.usedEdges_length,
        TwoSATPathCharge.EdgeWalk.usedEdges_length]

/-- Ambient linear clause bound for the semantic minimal width-two core.  This is the complete
classical two-path count after transport through the outside-literal representation. -/
theorem InclusionMinimalUnsatisfiableCore.card_le_four_mul_sub_two
    {target : Fin G → Depth3.Clause n} {core : Finset (Fin G × Depth3.Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hnonempty : ∀ p ∈ core,
      (competitorOutsideTargetLiteralSet target p.2).Nonempty)
    (hwidth : ∀ p ∈ core, p.2.lits.length ≤ 2) :
    core.card ≤ 4 * n - 2 := by
  obtain ⟨ell, forward, backward, _, _, _, _, hsum⟩ :=
    hminimal.exists_twoSAT_simple_contradiction_walks hnonempty hwidth
  exact (hminimal.card_le_twoWalk_lengths hnonempty hwidth ell forward backward).trans hsum

#print axioms outsideLiteralToTwoSAT
#print axioms outsideLiteralToTwoSAT_injective
#print axioms exists_outsidePairClause_semantics
#print axioms edge_singleton_outsidePairClause_iff
#print axioms hitsOutsideCompetitorCore_iff_twoSATClauses
#print axioms twoSat_outsideCore_iff
#print axioms InclusionMinimalUnsatisfiableCore.coreOutsideClause_injective
#print axioms InclusionMinimalUnsatisfiableCore.outsideCoreTwoSATClauses_nodup
#print axioms InclusionMinimalUnsatisfiableCore.twoSat_erase_coreOutsideClause
#print axioms InclusionMinimalUnsatisfiableCore.exists_twoSAT_contradiction_reaches
#print axioms InclusionMinimalUnsatisfiableCore.exists_twoSAT_simple_contradiction_walks
#print axioms TwoSATPathCharge.EdgeWalk.exists_of_usedEdges_subset
#print axioms TwoSATPathCharge.EdgeWalk.usedEdges_length
#print axioms TwoSATPathCharge.mem_implicationEdges_erase_of_ne
#print axioms TwoSATPathCharge.clause_edge_used_of_twoSat_erase
#print axioms InclusionMinimalUnsatisfiableCore.coreOutsideClause_edge_used
#print axioms unorderedClause_eq_of_shared_implicationEdge
#print axioms InclusionMinimalUnsatisfiableCore.eq_of_shared_coreOutsideClause_edge
#print axioms CoreOutsideEdgeChargeValid.endpoints_mem_incidentQueriedVars
#print axioms InclusionMinimalUnsatisfiableCore.coreOutsideEdgeCharge_endpoints_mem_incidentUnion
#print axioms InclusionMinimalUnsatisfiableCore.coreOutsideEdgeCharge_injective
#print axioms TwoSATPathCharge.EdgeWalk.internalUsedEdges_card_le_two_mul
#print axioms InclusionMinimalUnsatisfiableCore.subfamily_card_le_four_mul_incidentUnion_twoSAT
#print axioms InclusionMinimalUnsatisfiableCore.subfamily_card_le_four_mul_incidentUnion_of_incident
#print axioms InclusionMinimalUnsatisfiableCore.exists_incidentCoordinateOwner_load_le_four
#print axioms InclusionMinimalUnsatisfiableCore.exists_incidentWidthTwoOwnedKeyEmbedding
#print axioms canonicalMinimalUnsatisfiableCore_minimal
#print axioms canonicalMinimalUnsatisfiableCore_proof_irrel
#print axioms incidentWidthTwoOwnedKeyEmbedding_injective
#print axioms incidentWidthTwoOwnedKeyEmbedding_incident
#print axioms incidentWidthTwoOwnedKeyEmbedding_proof_irrel
#print axioms endpoint_position_do_not_transport_realizedPrefixTargetData
#print axioms endpoint_position_do_not_transport_realizedPrefixKeys
#print axioms endpoint_sourceGate_position_do_not_transport_realizedPrefixTargetData
#print axioms endpoint_sourceGate_position_do_not_transport_realizedPrefixKeys
#print axioms independentRealizedPrefix_sharedDecoder_card_lower_bound
#print axioms independentRealizedRoots_subset_commonShallowBad
#print axioms independentRealizedRoots_inter_commonShallowBad
#print axioms independentBadRealizedPrefix_sharedDecoder_card_lower_bound
#print axioms independentLiteralGates_actualAlphabet_eq
#print axioms independentLiteralGates_not_actualDensity
#print axioms canonicalDT_queriedVars_subset_gateVariableSupport
#print axioms canonicalFamily_trace_length_le_live_support
#print axioms commonShallowAt_zero_of_live_support_le
#print axioms familyVariableSupport_card_le
#print axioms freshTaggedPrefixVars_subset_familyVariableSupport
#print axioms realizedPrefixVariableSets_card_le_choose_support
#print axioms realizedPrefixVariableSets_card_le_choose_actualAlphabet
#print axioms commonShallowBad_realizedPrefixVariableSets_card_le
#print axioms commonShallowBadEndpointFiber_card_le_realizedPrefixVariableSets
#print axioms commonShallowBad_card_le_shell_mul_choose_actualAlphabet
#print axioms commonShallowBad_card_le_shell_mul_choose_actualAlphabet_of_le_fuel
#print axioms normalizedLayered_commonShallowBad_card_le_shell_mul_choose_actualAlphabet
#print axioms normalizedLayered_commonShallowBad_scaled_le_of_support_balance
#print axioms support_factor_strict_lt_realizedPrefix_factor_depth_one
#print axioms choose_mul_le_pow_mul_multichoose
#print axioms support_factor_le_realizedPrefix_factor
#print axioms supportSubset_factor_le_pow
#print axioms supportSubset_balance_of_density
#print axioms normalizedLayered_commonShallowBad_scaled_le_of_support_density
#print axioms twenty_mul_layeredRoundSupportScale_le_actualScale
#print axioms layeredRoundSupport_density
#print axioms not_layeredRoundSupport_worstCase_density_of_live_le_gateBound
#print axioms layeredRoundSupport_gateBound_lt_live_of_density
#print axioms normalizedLayered_commonShallowBad_scaled_le_support_schedule
#print axioms stableTermKey_card_le_of_leftInverse
#print axioms stableTargetMeaning_card_le_of_decoder
#print axioms rectangularDistinctSingletonSemantics_injective
#print axioms rectangularDistinctSingletonGates_width_one
#print axioms rectangularDistinctSingleton_card_le_of_semanticDecoder
#print axioms collapseRound_positiveSingletonDnf
#print axioms collapseRound_positiveSingletonDnf_of_free
#print axioms rectangularDistinctSingletonPredecessor_altO
#print axioms collapseRound_rectangularDistinctSingletonPredecessor
#print axioms bottomGates_rectangularDistinctSingletonRoundOutput
#print axioms familyVariableSupport_rectangularDistinctSingletonGates
#print axioms normalizedLayeredBottomFamily_rectangularRoundOutput_support
#print axioms rectangularDistinctSingletonRoundOutput_support_saturates_live
#print axioms bottomClauseCount_rectangularDistinctSingletonPredecessor
#print axioms bottomClauseCount_rectangularDistinctSingletonRoundOutput
#print axioms bottomGates_length_rectangularDistinctSingletonRoundOutput
#print axioms stars_rectangularDistinctSingleton_allLive
#print axioms rectangularDistinctSingletonRoundOutput_saturates_global_budgets
#print axioms paddedRectangularRoundOutput_saturates_global_budgets
#print axioms paddedRectangular_liveSupport_subset_familyVariableSupport
#print axioms stars_paddedRectangularRestriction_le_familyVariableSupport_card
#print axioms paddedRectangularSingletonRoundOutput_bottomWidth_one
#print axioms normalizedPaddedSingleton_familyVariableSupport
#print axioms paddedSingletonSupport_not_commonShallow_of_live_false
#print axioms paddedSingletonSupport_not_commonShallow_of_live_true
#print axioms paddedSingletonSupport_commonShallow_of_live_le
#print axioms paddedSingletonSupport_commonShallow_of_mixed_fixed
#print axioms paddedSingletonSupport_mem_bad_of_live_false
#print axioms paddedSingletonSupport_mem_bad_of_live_true
#print axioms mem_paddedSingletonBad_iff
#print axioms scheduledSingletonSupport_not_commonShallow_of_live_false
#print axioms scheduledSingletonSupport_mem_bad_of_live_false
#print axioms mem_scheduledSingletonCertifiedTail_iff
#print axioms mem_scheduledSingletonCertifiedOverlap_iff
#print axioms scheduledSingletonCertifiedTail_eq_biUnion_overlap
#print axioms scheduledSingletonOverlapFreeSets_card
#print axioms scheduledSingletonFalseRoot_fiber_card
#print axioms scheduledSingletonCertifiedOverlap_card
#print axioms scheduledSingletonCertifiedTail_card
#print axioms scheduledSingletonCertifiedTail_coefficient_lt
set_option maxRecDepth 16384 in
#print axioms finset_sum_mul_two_pow_add_lt_mul_two_pow
set_option maxRecDepth 16384 in
#print axioms scheduledSingletonCertifiedTail_lt_shell_div_two_pow_ten
set_option maxRecDepth 16384 in
#print axioms mul_two_pow_lt_mul_two_pow_add
set_option maxRecDepth 16384 in
#print axioms scheduledSingletonCertifiedTail_mul_two_pow_ten_lt_shell
#print axioms scheduledSingletonCertifiedTail_card_eq_paddedMass
#print axioms paddedSingletonCertifiedCoefficient_4080_lt
set_option maxRecDepth 16384 in
#print axioms paddedSingletonCertifiedMass_lt_shell_div_two_pow_ten_4080
set_option maxRecDepth 16384 in
#print axioms paddedSingletonCertifiedMass_mul_two_pow_ten_lt_shell_4080
#print axioms paddedSingletonFalseTail_card
#print axioms paddedSingletonTrueTail_card
#print axioms paddedSingletonFalseTail_inter_trueTail
#print axioms paddedSingletonBad_eq_falseTail_union_trueTail
#print axioms paddedSingletonBad_card
#print axioms paddedSingletonExactCoefficient_4080_lt
#print axioms paddedSingletonBad_mul_two_pow_ten_lt_shell_4080
#print axioms queryRestrictionList_spec
#print axioms queryRestrictionList_run_apply
#print axioms positiveOrderedPair_depth_le_one_of_first_fixed
#print axioms negativeOrderedPair_depth_le_one_of_first_fixed
#print axioms paddedDisjointPairFamily_commonShallow
#print axioms paddedDisjointPairBad_eq_empty
#print axioms paddedDisjointPairBad_mul_two_pow_ten_lt_shell
#print axioms positiveTwoPair_depth_eq_zero_of_four_fixed
#print axioms negativeTwoPair_depth_eq_zero_of_four_fixed
#print axioms positiveTwoPair_depth_ge_two_of_three_free
#print axioms negativeTwoPair_depth_ge_two_of_three_free
#print axioms paddedTwoPairCoord_injective
#print axioms paddedTwoPairSupport_card
#print axioms paddedTwoPairSupport_pairwiseDisjoint
#print axioms paddedTwoPairFamily_commonShallow_forty
#print axioms positiveTwoPair_first_coordinates_true_depth_eq_two
#print axioms twoPair_both_depth_le_one_iff_opposite_cross_fixed
#print axioms twoPairPolarities_not_commonShallowAt_two
#print axioms allFreeFour_mem_twoPairPolarityBad_two
#print axioms twoPairPolarities_commonShallowAt_three
#print axioms twoPairPolarities_exact_trunk_cost_three
#print axioms twoPairLocalQueryWin_sound
#print axioms twoPairRootShallow_not_monotone_fixVar
#print axioms twoPairFlexibleQueryCost_multiplicity_exact
#print axioms twoPairFlexibleQueryCost_eq_readOnceCost
#print axioms twoPairFlexibleQueryCost_fixVar_adversary_code
#print axioms twoPairFlexibleQueryCost_fixVar_adversary
#print axioms twoPairTenFlexibleCost_update_adversary
#print axioms twoPairFlexibleConditionalCost_fixVar_adversary_code
#print axioms twoPairFlexibleConditionalCost_fixVar_adversary
#print axioms twoPairTenFlexibleConditionalCost_update_adversary
#print axioms paddedTwoPairLocalRestriction_fixVar
#print axioms paddedTwoPairLocalRestriction_fixVar_padding
#print axioms twoPairTenFlexibleConditionalCost_tree_adversary
#print axioms paddedTwoPairLocalRestriction_fixVar_self
#print axioms positiveTwoPair_local_depth_le_one_of_padded
#print axioms negativeTwoPair_local_depth_le_one_of_padded
#print axioms twoPairRootShallow_of_padded_depths
#print axioms twoPairFlexibleConditionalCost_eq_zero_of_leaf
#print axioms twoPairTenFlexibleConditionalCost_eq_zero_of_leaf
#print axioms twoPairTenFlexibleCost_le_of_padded_commonShallow
#print axioms twoPairFlexibleQueryCost_stars_profile_exact
#print axioms twoPairLocalCostLiveFiber_card_eq_convolution_one
#print axioms paddedTwoPairFlexibleCostTabulatedMass_scaled_not_le_shell_86
#print axioms paddedTwoPairFlexibleCostTabulatedMass_scaled_le_shell_87
#print axioms twoPairFlexibleQueryCost_le_stars
#print axioms paddedTwoPairFlexibleCostTail_subset_bad
#print axioms twoPairFlexibleQueryCost_allFree
#print axioms allFreeForty_mem_paddedTwoPairFlexibleCostTail_zero
#print axioms paddedTwoPairFlexibleCostTail_card_zeroPadding
#print axioms not_paddedTwoPair_scaled_contraction_zeroPadding
#print axioms restrictionExtends_path_of_agrees_everywhere
#print axioms twoPairFlexibleQueryWin_of_tree
#print axioms twoPairFlexibleQueryWin_sound_aux
#print axioms twoPairFlexibleQueryWin_iff_commonShallowAt
#print axioms twoPairLocalQueryCost_multiplicity_exact
#print axioms CommonShallowAt.root_shallow_of_trunkDepth_zero
#print axioms twoPairSameClauseMixedRestriction_root_depths
#print axioms twoPairSameClauseMixedRestriction_not_commonShallowAt_zero
#print axioms twoPairSameClauseMixedRestriction_commonShallowAt_one
#print axioms pairedPolarity_not_commonShallowAt_of_compatible_sum_deficit
#print axioms pairedPolarity_not_commonShallowAt_of_compatible_sum_deficit_threshold
#print axioms paddedTwoPair_not_commonShallow_ten_of_compatible_sum_deficit
#print axioms paddedTwoPair_not_commonShallow_ten_of_support_free
#print axioms paddedTwoPairRestriction_not_commonShallow_ten
#print axioms paddedTwoPairRestriction_mem_bad_ten
#print axioms paddedTwoPairCompatibleDeficitProfiles_subset_bad
#print axioms pairedPolarity_not_commonShallowAt_of_false_compatible_sum_deficit_threshold
#print axioms paddedTwoPair_not_commonShallow_ten_of_false_compatible_sum_deficit
#print axioms paddedTwoPairFalseCompatibleDeficitProfiles_subset_bad
#print axioms paddedTwoPair_complement_mem_compatible_iff
#print axioms paddedTwoPairFalseCompatibleDeficitProfiles_card
#print axioms twoPairLocalProfileMultiplicity_exact
#print axioms twoPairLocalProfileClass_partition
#print axioms twoPairLocalDeficitMultiplicity_exact
#print axioms twoPairTenFoldDeficitTail_exact
#print axioms paddedTwoPairRestrictionCode_injective
#print axioms stars_paddedTwoPairLocalRestriction
#print axioms paddedTwoPair_supportTrueCompatible_iff
#print axioms twoPairLocalCompatibleDeficit_paddedTwoPairLocalRestriction
#print axioms two_mul_paddedTwoPair_compatibleDeficit_le_liveSupport_card
#print axioms paddedTwoPairOwnedLive_card
#print axioms paddedTwoPair_twentyTwo_le_ownedLive_of_ten_lt_deficit
#print axioms twoPairLocal_live_lower_bound
#print axioms twoPairLocalCompatibleDeficit_le_two
#print axioms twoPairTenLocalDeficitTailProfiles_vector_fiber_card
#print axioms twoPairTenLocalDeficitTailProfiles_card_le_full
#print axioms paddedTwoPair_twentyThree_le_ownedLive_of_ten_lt_deficit
#print axioms stars_paddedTwoPairRestrictionCode
#print axioms paddedTwoPairFlexibleCostTail_padding_stars_le_twentyNine
#print axioms paddingRestrictionsAtMostTwentyNine_card
#print axioms two_pow_twentyNine_sub_mul_choose_le_choose_twentyNine
#print axioms paddingRestrictionsAtMostTwentyNine_card_le
#print axioms paddedTwoPairFlexibleCostTail_card_le_product
#print axioms paddedTwoPairFlexibleCostTail_coarse_scaled_insufficient_4080
#print axioms paddedTwoPairFlexibleCostTail_scaled_insufficient_4080
#print axioms paddedTwoPair_padding_stars_le_seventeen
#print axioms paddingRestrictionsAtMostSeventeen_card
#print axioms two_pow_seventeen_sub_mul_choose_le_choose_seventeen
#print axioms paddingRestrictionsAtMostSeventeen_card_le
#print axioms paddedTwoPairCompatibleDeficitProfiles_card_le_product
#print axioms paddedTwoPairCompatibleDeficitProfiles_card_le_full
#print axioms paddedTwoPairFalseCompatibleDeficitProfiles_card_le_full
#print axioms twoPairFullLocalSpace_4080_padding_scaled_insufficient
#print axioms two_mul_twoPairFullLocalSpace_4080_padding_scaled_insufficient
#print axioms twoPair_two_coarse_profile_classes_union_scaled_insufficient
#print axioms paddedTwoPair_two_compatible_classes_union_subset_bad
#print axioms paddedTwoPair_two_compatible_classes_union_scaled_insufficient
#print axioms paddedTwoPairCompatibleDeficitProfiles_4080_scaled_insufficient
#print axioms twoPairTenFoldDeficitTail_4080_coarse_insufficient
#print axioms twoPairTenFoldDeficitTail_4080_padding_scaled_insufficient
#print axioms paddedTwoPairFullyLiveFiber_subset_bad
#print axioms paddedTwoPairFullyLiveFiber_card
#print axioms paddedTwoPairFullyLiveFiber_scaled_lt_shell
#print axioms paddedTwoPairBad_forty_eq_empty
#print axioms scheduledSingletonSupport_not_commonShallow
#print axioms scheduledSingletonSupport_fiber_mem_bad
#print axioms paddedRectangularRoundOutput_schedule_restriction_mem_bad
#print axioms scheduledSingletonSupport_bad_card_lower_bound
#print axioms paddedRectangularRoundOutput_realizes_actual_schedule
#print axioms paddedRectangularRoundOutput_realizes_support_schedule
#print axioms card_widthTwoOwnedPrefixCode
#print axioms widthTwoOwnedPrefix_balance
#print axioms InclusionMinimalUnsatisfiableCore.card_le_twoWalk_lengths
#print axioms InclusionMinimalUnsatisfiableCore.card_le_four_mul_sub_two

end PallLean.Paper93.DeepMath.PathB.MultiSwitching
