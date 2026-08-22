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

variable {n G : ℕ}

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
  decide

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

/-- The twenty coordinates used by the concrete scheduled obstruction. -/
private def scheduledSingletonSupport : Finset (Fin 164000) :=
  Finset.univ.image fun j : Fin 20 ↦
    Fin.natAdd 163980 (finProdFinEquiv ((0 : Fin 1), j))

private theorem scheduledSingletonSupport_card : scheduledSingletonSupport.card = 20 := by
  rw [scheduledSingletonSupport, Finset.card_image_of_injective]
  · simp
  · intro a b h
    have hp := Fin.natAdd_injective 20 163980 h
    have hab := finProdFinEquiv.injective hp
    exact congrArg Prod.snd hab

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
    rw [scheduledSingletonSupport, Finset.mem_image] at hiPacked
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
        rw [scheduledSingletonSupport, Finset.mem_image]
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
      rw [scheduledSingletonSupport, Finset.mem_image] at hi
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
#print axioms bottomClauseCount_rectangularDistinctSingletonPredecessor
#print axioms bottomClauseCount_rectangularDistinctSingletonRoundOutput
#print axioms bottomGates_length_rectangularDistinctSingletonRoundOutput
#print axioms stars_rectangularDistinctSingleton_allLive
#print axioms rectangularDistinctSingletonRoundOutput_saturates_global_budgets
#print axioms paddedRectangularRoundOutput_saturates_global_budgets
#print axioms paddedRectangularSingletonRoundOutput_bottomWidth_one
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
#print axioms scheduledSingletonSupport_not_commonShallow
#print axioms scheduledSingletonSupport_fiber_mem_bad
#print axioms paddedRectangularRoundOutput_schedule_restriction_mem_bad
#print axioms scheduledSingletonSupport_bad_card_lower_bound
#print axioms paddedRectangularRoundOutput_realizes_actual_schedule
#print axioms card_widthTwoOwnedPrefixCode
#print axioms widthTwoOwnedPrefix_balance
#print axioms InclusionMinimalUnsatisfiableCore.card_le_twoWalk_lengths
#print axioms InclusionMinimalUnsatisfiableCore.card_le_four_mul_sub_two

end PallLean.Paper93.DeepMath.PathB.MultiSwitching
