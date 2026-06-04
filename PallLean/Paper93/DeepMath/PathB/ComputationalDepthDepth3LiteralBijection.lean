import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CircuitKernel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinResolutionWidth

/-!
# Literal bijection bookkeeping: `RLit n` ⟷ `TLit (Fin n)`, and `DTRef` transport

`tautDNF_to_dtRef` produces a `DTRef` over the `Fin n × Bool` model (`RLit n`); the Tseitin
machinery lives over `TLit Edge = Edge × ZMod 2`.  This file supplies the bookkeeping to move between
them, with `Edge = Fin n` and `Bool ↔ ZMod 2`.

* `DTRef.mapLit` — transport a `DTRef` along any literal map `φ` (map node pivots and leaf-clause
  literals), with `mapLit_depth` (depth unchanged), `Labeled_mapLit`, and `Refutes_mapLit` (under
  complement-compatibility `φ (compl x) = compl' (φ x)`).
* `boolToZMod2` / `rlitToTlit` — the complement-compatible bijection `RLit n → TLit (Fin n)`,
  `(i, b) ↦ (i, [b])`, with `rlitToTlit_tcompl` (`φ ∘ rcompl = tcompl ∘ φ`).
* `tautDNF_to_dtRef_tlit` — the transported kernel: a tautological DNF yields a `DTRef` over
  `TLit (Fin n)` that is `Labeled` (over the `φ`-image axioms), `Refutes tcompl ∅`, and `depth ≤ fuel`.

So the concrete circuit ⟹ refuting-`DTRef` kernel now lands in the Tseitin literal model — pure
bookkeeping, all proved, no `sorry`.  (The only thing still open is the *smallness* of `depth`, the
switching lemma.)
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

namespace DTRef

variable {Lit Lit' : Type*} [DecidableEq Lit] [DecidableEq Lit']

/-- Transport a refutation tree along a literal map. -/
def mapLit (φ : Lit → Lit') : DTRef Lit → DTRef Lit'
  | leaf C => leaf (C.image φ)
  | node ℓ t0 t1 => node (φ ℓ) (mapLit φ t0) (mapLit φ t1)

/-- `mapLit` preserves depth (the tree structure is unchanged). -/
theorem mapLit_depth (φ : Lit → Lit') : ∀ T : DTRef Lit, (T.mapLit φ).depth = T.depth
  | leaf _ => rfl
  | node _ t0 t1 => by rw [mapLit, depth, depth, mapLit_depth φ t0, mapLit_depth φ t1]

/-- `mapLit` preserves `Labeled` (the leaf axioms map by `image φ`). -/
theorem Labeled_mapLit (φ : Lit → Lit') {Axiom : ResolutionClause Lit → Prop} :
    ∀ T : DTRef Lit, DTRef.Labeled Axiom T →
      DTRef.Labeled (fun C' => ∃ C, Axiom C ∧ C.image φ = C') (T.mapLit φ)
  | leaf C, h => ⟨C, h, rfl⟩
  | node ℓ t0 t1, h => ⟨Labeled_mapLit φ t0 h.1, Labeled_mapLit φ t1 h.2⟩

/-- `mapLit` preserves `Refutes` under complement-compatibility. -/
theorem Refutes_mapLit {compl : Lit → Lit} {compl' : Lit' → Lit'} (φ : Lit → Lit')
    (hcompl : ∀ x, φ (compl x) = compl' (φ x)) :
    ∀ (T : DTRef Lit) (F : Finset Lit),
      DTRef.Refutes compl T F → DTRef.Refutes compl' (T.mapLit φ) (F.image φ)
  | leaf C, F, h => Finset.image_subset_image h
  | node ℓ t0 t1, F, h => by
    refine ⟨?_, ?_⟩
    · have := Refutes_mapLit φ hcompl t0 (insert ℓ F) h.1
      rwa [Finset.image_insert] at this
    · have := Refutes_mapLit φ hcompl t1 (insert (compl ℓ) F) h.2
      rwa [Finset.image_insert, hcompl] at this

end DTRef

namespace SearchDischarge

open Depth3 SwitchingCounting

variable {n : ℕ}

/-- `Bool → ZMod 2`: `false ↦ 0`, `true ↦ 1`. -/
def boolToZMod2 : Bool → ZMod 2 := fun b => if b then 1 else 0

theorem boolToZMod2_injective : Function.Injective boolToZMod2 := by
  intro a b h; cases a <;> cases b <;> simp_all [boolToZMod2]

theorem boolToZMod2_not (b : Bool) : boolToZMod2 (!b) = boolToZMod2 b + 1 := by
  cases b <;> decide

/-- The complement-compatible literal bijection `RLit n → TLit (Fin n)`, `(i,b) ↦ (i, [b])`. -/
def rlitToTlit : RLit n → TLit (Fin n) := fun p => (p.1, boolToZMod2 p.2)

theorem rlitToTlit_injective : Function.Injective (rlitToTlit (n := n)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  simp only [rlitToTlit, Prod.mk.injEq] at h
  exact Prod.ext h.1 (boolToZMod2_injective h.2)

/-- The bijection sends `rcompl` to `tcompl`. -/
theorem rlitToTlit_tcompl (p : RLit n) : rlitToTlit (rcompl p) = tcompl (rlitToTlit p) := by
  obtain ⟨i, b⟩ := p
  simp only [rcompl, rlitToTlit, tcompl, boolToZMod2_not]

/-- **The transported kernel.**  A tautological DNF yields a `DTRef` over `TLit (Fin n)` that is
`Labeled` (over the `rlitToTlit`-image of `AxiomOf cs`), `Refutes tcompl` the empty clause, and has
`depth ≤ fuel`.  The concrete circuit ⟹ refuting-tree kernel, in the Tseitin literal model. -/
theorem tautDNF_to_dtRef_tlit (cs : List (Clause n)) (htaut : ∀ x, Depth3.dnfEval cs x = true)
    (fuel : ℕ) (hfuel : SwitchingCounting.stars (fun _ : Fin n => (none : Option Bool)) ≤ fuel) :
    ∃ T : DTRef (TLit (Fin n)),
      DTRef.Labeled (fun C' => ∃ C, AxiomOf cs C ∧ C.image rlitToTlit = C') T ∧
      DTRef.Refutes tcompl T (∅ : ResolutionClause (TLit (Fin n))) ∧
      T.depth ≤ fuel := by
  obtain ⟨T, hlab, href, hdepth⟩ := tautDNF_to_dtRef cs htaut fuel hfuel
  refine ⟨T.mapLit rlitToTlit, DTRef.Labeled_mapLit rlitToTlit T hlab, ?_, ?_⟩
  · have := DTRef.Refutes_mapLit rlitToTlit rlitToTlit_tcompl T ∅ href
    rwa [Finset.image_empty] at this
  · rw [DTRef.mapLit_depth]; exact hdepth

/-- The Tseitin axiom list of a DNF: the `rlitToTlit`-images of the De Morgan–dual clauses. -/
def tautAx (cs : List (Clause n)) : List (ResolutionClause (TLit (Fin n))) :=
  cs.map (fun T => (negTermClause T).image rlitToTlit)

/-- The transported `Labeled` predicate is exactly membership in the dual-image axiom list. -/
theorem axiomOf_image_eq_mem_tautAx (cs : List (Clause n)) :
    (fun C' => ∃ C, AxiomOf cs C ∧ C.image rlitToTlit = C') = (· ∈ tautAx cs) := by
  funext C'
  apply propext
  constructor
  · rintro ⟨C, ⟨T, hT, rfl⟩, rfl⟩
    exact List.mem_map.mpr ⟨T, hT, rfl⟩
  · intro hC'
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hC'
    exact ⟨negTermClause T, ⟨T, hT, rfl⟩, rfl⟩

/-- **The transported kernel, in `(· ∈ Ax)` list form.**  A tautological DNF yields a `DTRef` over
`TLit (Fin n)` that is `Labeled (· ∈ tautAx cs)`, `Refutes tcompl ∅`, `depth ≤ fuel` — exactly the
shape `collapseModel_of_dtRefKernel` / `circuit_lower_bound_of_kernel` consume (with `Ax := tautAx cs`). -/
theorem tautDNF_to_dtRef_tautAx (cs : List (Clause n)) (htaut : ∀ x, Depth3.dnfEval cs x = true)
    (fuel : ℕ) (hfuel : SwitchingCounting.stars (fun _ : Fin n => (none : Option Bool)) ≤ fuel) :
    ∃ T : DTRef (TLit (Fin n)),
      DTRef.Labeled (· ∈ tautAx cs) T ∧
      DTRef.Refutes tcompl T (∅ : ResolutionClause (TLit (Fin n))) ∧
      T.depth ≤ fuel := by
  obtain ⟨T, hlab, href, hd⟩ := tautDNF_to_dtRef_tlit cs htaut fuel hfuel
  exact ⟨T, axiomOf_image_eq_mem_tautAx cs ▸ hlab, href, hd⟩

end SearchDischarge

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.tautDNF_to_dtRef_tlit
#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.tautDNF_to_dtRef_tautAx
