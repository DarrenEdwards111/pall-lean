import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3WidthLowerBound

/-!
# Final instantiation: connecting the chain to the concrete Tseitin axioms

The chain (`canonicalDT` → relabel → `DTRef` → `LDeriv`) and the semantic decoders produce a
resolution refutation over the `Fin n × Bool` literal model (`SearchDischarge.RLit`); the
expander-Tseitin width lower bound (`dtRef_refuting_depth_ge`) lives over `TLit Edge = Edge × ZMod 2`.
This file supplies the two pieces that join them into a single lower-bound statement.

* `LDeriv.mapLit` — **the literal-transport bridge.**  An injective, complement-compatible map
  `φ : Lit → Lit'` (`φ (compl x) = compl' (φ x)`) transports any `LDeriv` refutation to one over
  `Lit'`, mapping each clause by `Finset.image φ`.  Resolution structure is preserved (the resolvent
  identity commutes with `image φ` since `φ` is injective), and **width is preserved** (an injective
  image has the same cardinality).  With the bijection `Fin n × Bool ≃ TLit Edge` (variable+polarity
  ↦ edge-literal, `Bool ↔ ZMod 2`) sending `rcompl` to `tcompl`, this carries the chain's refutation
  onto the Tseitin literal model.

* `depth3_tseitin_lower_bound` — **the squeeze contradiction.**  No refuting decision tree over the
  expander-Tseitin axioms can be shallow: if a clause-labelled refutation tree `T` over `Ax` has
  `T.depth ≤ D < c·t`, that is impossible (`dtRef_refuting_depth_ge` forces `c·t ≤ T.depth`).

Putting it together with the collapse (`depth3_collapse_*`) and the binomial regime
(`short_family_ratio`, ratio `≤ 1`): a small depth-3 circuit yields, via switching, a good
restriction whose canonical tree is *shallow* (`D < c·t`); transported onto `TLit Edge` by
`LDeriv.mapLit` it is a refuting tree over `Ax`, contradicting `depth3_tseitin_lower_bound`.  Hence
no small circuit refutes expander Tseitin at that depth.

**The one remaining concrete obligation (honest):** exhibiting the De Morgan–dual identity
`AxiomOf cs = (· ∈ Ax)` under the bijection — i.e. choosing the DNF `cs` (the negation of the
concrete circuit) so its dual clauses are exactly the Tseitin vertex constraints.  That is the
circuit-construction step; the *logical pipeline* closing the squeeze is proved here.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

/-- **Literal transport for `LDeriv`.**  An injective, complement-compatible relabelling `φ`
carries a refutation over `Lit` to one over `Lit'`, clause-by-clause via `Finset.image φ`.
Resolution, weakening, and axioms all transport; width is preserved by injectivity. -/
theorem LDeriv.mapLit {Lit Lit' : Type*} [DecidableEq Lit] [DecidableEq Lit']
    {compl : Lit → Lit} {compl' : Lit' → Lit'} {Axiom : ResolutionClause Lit → Prop}
    (φ : Lit → Lit') (hφ : Function.Injective φ) (hcompl : ∀ x, φ (compl x) = compl' (φ x)) :
    ∀ {L : List (ResolutionClause Lit)}, LDeriv compl Axiom L →
      LDeriv compl' (fun C' => ∃ C, Axiom C ∧ C.image φ = C') (L.map (fun C => C.image φ)) := by
  intro L h
  induction h with
  | nil => exact LDeriv.nil
  | @cons C L just _ ih =>
    refine LDeriv.cons ?_ ih
    rcases just with hax | ⟨D, E, p, hD, hE, heq⟩ | ⟨D, hD, hsub⟩
    · exact Or.inl ⟨C, hax, rfl⟩
    · refine Or.inr (Or.inl ⟨D.image φ, E.image φ, φ p,
        List.mem_map_of_mem hD, List.mem_map_of_mem hE, ?_⟩)
      rw [heq]
      simp only [ResolutionClause.resolvent, Finset.image_union, Finset.image_erase hφ, hcompl]
    · exact Or.inr (Or.inr ⟨D.image φ, List.mem_map_of_mem hD, Finset.image_subset_image hsub⟩)

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]
  [Nonempty Edge]

/-- **The squeeze contradiction.**  A refuting decision tree over the expander-Tseitin axioms cannot
be shallow: depth `≤ D < c·t` is impossible, since `dtRef_refuting_depth_ge` forces `c·t ≤ T.depth`. -/
theorem depth3_tseitin_lower_bound (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    (Ax : List (ResolutionClause (TLit Edge)))
    (hAxiom : ∀ C, C ∈ Ax → ∃ v : V, SemanticMeasure.Implies TSat (TConstr G charge) {v} C)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht2 : 2 ≤ t)
    (hcard : 4 * t ≤ Fintype.card V)
    (T : DTRef (TLit Edge)) (hlab : DTRef.Labeled (· ∈ Ax) T)
    (href : DTRef.Refutes tcompl T (∅ : ResolutionClause (TLit Edge)))
    {D : ℕ} (hdepth : T.depth ≤ D) (hshallow : D < c * t) : False := by
  have hge := dtRef_refuting_depth_ge G charge hunsat Ax hAxiom hc hexp ht2 hcard T hlab href
  omega

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.mapLit
#print axioms PallLean.Paper93.DeepMath.PathB.depth3_tseitin_lower_bound
