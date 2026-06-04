import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseInterface
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTRefutation

/-!
# Factoring the collapse gate through the switching kernel

`Depth3CollapseModel.collapse` (the open gate) reduces, for **any** circuit class, to a *switching
kernel*: a map sending each refuting object to a **shallow refuting `DTRef`** over the Tseitin
axioms.  The remaining `DTRef → bounded LDeriv refutation` step (and the length bound) is **proved**
(`dtRef_to_ldderiv`).  So the gate's entire content is the kernel, made explicit.

* `collapseModel_of_dtRefKernel` — given `kernel : ∀ D, Refutes D → ∃ T : DTRef, (refuting tree over
  Ax) ∧ T.depth ≤ treeDepth (size D)`, build a `Depth3CollapseModel` with `collapseLen s =
  2^(treeDepth s + 1)` and the **`collapse` field proved** (length `< 2^(T.depth+1) ≤
  2^(treeDepth(size D)+1)`).

This pins the open gate precisely: it is *exactly* the switching kernel "refuting circuit ⟹ shallow
refuting decision tree" — i.e. Håstad's switching lemma for the circuit's bottom plus the relabelling.
Everything downstream of the kernel is discharged here; the kernel itself (the satisfy-variable
reconstruction / `ReconstructionCorrect`) is the open core, **not** faked.  (`dtRefCollapseModel` is
the `Circ = DTRef`, `kernel = id`, `treeDepth = id` instance.)
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

variable {V Edge : Type} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]
  [Nonempty Edge]

/-- **The collapse gate factors through the switching kernel.**  A kernel producing a shallow
refuting `DTRef` from each refuting object yields a `Depth3CollapseModel` with the `collapse` field
proved (via `dtRef_to_ldderiv` + monotonicity of `2^·`). -/
def collapseModel_of_dtRefKernel (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    {Circ : Type} (Refutes : Circ → Prop) (sz : Circ → ℕ)
    (Ax : List (ResolutionClause (TLit Edge)))
    (hAx : ∀ C, C ∈ Ax → ∃ v : V, SemanticMeasure.Implies TSat (TConstr G charge) {v} C)
    (w0 : ℕ) (hw0' : ∀ C, C ∈ Ax → ResolutionClause.width C ≤ w0)
    (treeDepth : ℕ → ℕ)
    (kernel : ∀ D : Circ, Refutes D → ∃ T : DTRef (TLit Edge),
      DTRef.Labeled (· ∈ Ax) T ∧ DTRef.Refutes tcompl T (∅ : ResolutionClause (TLit Edge)) ∧
        T.depth ≤ treeDepth (sz D)) :
    Depth3CollapseModel G charge where
  Circuit := Circ
  size := sz
  Refutes := Refutes
  Ax := Ax
  hAxiom := hAx
  w₀ := w0
  hw0 := hw0'
  collapseLen := fun s => 2 ^ (treeDepth s + 1)
  collapse := fun D hD => by
    obtain ⟨T, hlab, href, hdepth⟩ := kernel D hD
    obtain ⟨hLD, hmt, hlen, _⟩ := DTRef.dtRef_to_ldderiv T hlab href
    refine ⟨DTRef.toList tcompl T, hLD, hmt, ?_⟩
    exact (lt_of_lt_of_le hlen (Nat.pow_le_pow_right (by norm_num) (by omega))).le

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.collapseModel_of_dtRefKernel
