import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SearchCoupling

/-!
# A concrete circuit ⟹ refuting-`DTRef` kernel (tautological-DNF class), fully proved

The collapse gate factors through a *switching kernel* (`collapseModel_of_dtRefKernel`): each refuting
object yields a shallow refuting `DTRef` over the axioms.  Here is a **concrete, fully-proved** kernel
for a real circuit class — the **tautological DNFs** (`∀ x, dnfEval cs x = true`, i.e. the negated
circuit is unsatisfiable):

* `tautDNF_to_dtRef` — for a tautological DNF `cs`, the relabelled canonical decision tree is a
  `DTRef` over `AxiomOf cs` (the De Morgan–dual axioms) that is `Labeled`, `Refutes` the empty clause,
  and has `depth ≤ fuel`.  Built entirely from proved results: `validSearch_canonicalDT` (the
  threading coupling) → `labeled_of_validSearch` / `refutes_of_validSearch` (the relabel bridge) →
  `relabel_depth` + `canonicalDT_depth_le`.

So the kernel is **not** an axiom-socket: a concrete refuting object yields a concrete refuting
decision tree, with the whole construction proved.  The depth bound here is `fuel` (take
`fuel = stars` ⟹ `depth ≤ stars = n`), the *unconditional* bound.  The **open switching** is only the
*smallness* of this depth (`depth ≤ s` with `s ≪ n` for a good restriction); the construction itself
is real and complete.  This is the genuinely-provable half of the circuit-side kernel.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SearchDischarge

open Depth3 SwitchingCounting

variable {n : ℕ}

/-- **Concrete circuit ⟹ refuting `DTRef` kernel (tautological DNF).**  A tautological DNF `cs` yields
a refuting `DTRef` over its De Morgan–dual axioms `AxiomOf cs`, of depth `≤ fuel`.  Fully proved via
the canonical tree + relabelling; no open switching in the construction (only its depth's smallness is
the switching lemma). -/
theorem tautDNF_to_dtRef (cs : List (Clause n)) (htaut : ∀ x, Depth3.dnfEval cs x = true)
    (fuel : ℕ) (hfuel : SwitchingCounting.stars (fun _ : Fin n => (none : Option Bool)) ≤ fuel) :
    ∃ T : DTRef (RLit n),
      DTRef.Labeled (AxiomOf cs) T ∧
      DTRef.Refutes rcompl T (∅ : ResolutionClause (RLit n)) ∧
      T.depth ≤ fuel := by
  have hfs : falseSet (fun _ : Fin n => (none : Option Bool)) = (∅ : ResolutionClause (RLit n)) := by
    ext p; simp [mem_falseSet]
  have hvalid : ValidSearch rpos rcompl (labSearch cs) (AxiomOf cs) ∅
      (Depth3.canonicalDT cs fuel (fun _ => none)) := by
    have h := validSearch_canonicalDT cs htaut fuel (fun _ => none) hfuel
    rwa [hfs] at h
  refine ⟨relabel rpos rcompl (labSearch cs) ∅ (Depth3.canonicalDT cs fuel (fun _ => none)),
    ?_, ?_, ?_⟩
  · exact labeled_of_validSearch rpos rcompl (labSearch cs)
      (Depth3.canonicalDT cs fuel (fun _ => none)) ∅ hvalid
  · exact refutes_of_validSearch rpos rcompl (labSearch cs)
      (Depth3.canonicalDT cs fuel (fun _ => none)) ∅ hvalid
  · rw [relabel_depth rpos rcompl (labSearch cs) (Depth3.canonicalDT cs fuel (fun _ => none)) ∅]
    exact Depth3.canonicalDT_depth_le cs fuel (fun _ => none)

end SearchDischarge

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.tautDNF_to_dtRef
