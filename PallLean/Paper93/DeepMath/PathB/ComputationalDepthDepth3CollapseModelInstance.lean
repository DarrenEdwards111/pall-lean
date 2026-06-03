import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseInterface
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTRefutation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Hypercube

/-!
# A `Depth3CollapseModel` with the collapse gate **discharged** (DTRef class)

`Depth3CollapseModel.collapse` is the open gate: every refuting object collapses (under restrictions)
to a bounded `LDeriv` refutation of the Tseitin axioms.  In general this is the switching lemma.  But
the gate is **not vacuous** — it is genuinely dischargeable for the **clause-labelled refutation-tree**
class `DTRef`, where collapse *is* the proved `DTRef.dtRef_to_ldderiv`.

* `dtRefCollapseModel` — a `Depth3CollapseModel` whose objects are `DTRef (TLit Edge)` refuting the
  Tseitin axioms, `size = depth`, `collapseLen s = 2^(s+1)`, and whose **`collapse` field is proved**
  by `dtRef_to_ldderiv` (the refutation tree *is* the collapsed `LDeriv`, length `< 2^(depth+1)`).
* `hypercube_dtRefCollapseModel` — the same at the concrete hypercube `Q_k`.
* `hypercube_dtRef_depth_lower_bound` — running the model's `size_lower_exp` on it gives an
  **unconditional** `2^j ≤ 2^(depth+1)` (hence `j ≤ depth+1`) for refuting `DTRef` trees in the BSW
  regime — the lower-bound machinery firing with the gate discharged.

**Honest fence.**  This discharges `collapse` only for the refutation-tree class (the object already
*is* a refutation).  The *general* gate — an arbitrary ΣΠΣ depth-3 **circuit** collapsing to a
refutation under a random restriction — is the genuine switching lemma (`ReconstructionCorrect` /
the satisfy-variable encoding), and is **not** discharged here.  No socket, no custom axiom: the
`collapse` field of `dtRefCollapseModel` is a real proof.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

variable {V Edge : Type} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]
  [Nonempty Edge]

/-- **A collapse model with the gate proved.**  Objects are refuting `DTRef` trees over the Tseitin
axioms; the `collapse` field is `dtRef_to_ldderiv` — the tree's clause list is a genuine `LDeriv`
refutation of length `< 2^(depth+1)`.  No axiom-socket. -/
@[reducible] def dtRefCollapseModel (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (Ax : List (ResolutionClause (TLit Edge)))
    (hAx : ∀ C, C ∈ Ax → ∃ v : V, SemanticMeasure.Implies TSat (TConstr G charge) {v} C)
    (w0 : ℕ) (hw0' : ∀ C, C ∈ Ax → ResolutionClause.width C ≤ w0) :
    Depth3CollapseModel G charge where
  Circuit := DTRef (TLit Edge)
  size := fun D => D.depth
  Refutes := fun D => DTRef.Labeled (· ∈ Ax) D ∧ DTRef.Refutes tcompl D ∅
  Ax := Ax
  hAxiom := hAx
  w₀ := w0
  hw0 := hw0'
  collapseLen := fun s => 2 ^ (s + 1)
  collapse := fun D hD =>
    ⟨DTRef.toList tcompl D, (DTRef.dtRef_to_ldderiv D hD.1 hD.2).1,
      (DTRef.dtRef_to_ldderiv D hD.1 hD.2).2.1, le_of_lt (DTRef.dtRef_to_ldderiv D hD.1 hD.2).2.2.1⟩

/-- The collapse model with the gate proved, at the concrete hypercube `Q_k`. -/
@[reducible] def hypercube_dtRefCollapseModel (k : ℕ) [Nonempty (Hypercube.HCEdge k)]
    (Ax : List (ResolutionClause (TLit (Hypercube.HCEdge k))))
    (hAx : ∀ C, C ∈ Ax → ∃ v : (Fin k → ZMod 2),
      SemanticMeasure.Implies TSat (TConstr (Hypercube.hypercubeGraph k) (hypercubeCharge k)) {v} C)
    (w0 : ℕ) (hw0' : ∀ C, C ∈ Ax → ResolutionClause.width C ≤ w0) :
    Depth3CollapseModel (Hypercube.hypercubeGraph k) (hypercubeCharge k) :=
  dtRefCollapseModel (Hypercube.hypercubeGraph k) (hypercubeCharge k) Ax hAx w0 hw0'

/-- **Unconditional depth lower bound via the discharged-gate model.**  For refuting `DTRef` trees
over the hypercube-Tseitin axioms, in the BSW regime, `2^j ≤ 2^(depth+1)` — the `Depth3CollapseModel`
machinery (`size_lower_exp`) yielding a genuine bound with the collapse gate *proved*, not assumed. -/
theorem hypercube_dtRef_depth_lower_bound (k : ℕ) [Nonempty (Hypercube.HCEdge k)]
    (Ax : List (ResolutionClause (TLit (Hypercube.HCEdge k))))
    (hAx : ∀ C, C ∈ Ax → ∃ v : (Fin k → ZMod 2),
      SemanticMeasure.Implies TSat (TConstr (Hypercube.hypercubeGraph k) (hypercubeCharge k)) {v} C)
    (w0 : ℕ) (hw0' : ∀ C, C ∈ Ax → ResolutionClause.width C ≤ w0)
    {t : ℕ} (ht2 : 2 ≤ t) (hcard : 4 * t ≤ 2 ^ k) {d kk j : ℕ} (hd : 0 < d) (hk1 : 1 ≤ kk)
    (hdn : d < Fintype.card (TLit (Hypercube.HCEdge k)))
    (hkd : Fintype.card (TLit (Hypercube.HCEdge k)) - d ≤ kk * d)
    (hsmall : w0 + d + kk * j < t)
    (D : DTRef (TLit (Hypercube.HCEdge k)))
    (hlab : DTRef.Labeled (· ∈ Ax) D) (href : DTRef.Refutes tcompl D ∅) :
    2 ^ j ≤ 2 ^ (D.depth + 1) := by
  have hunsat := tseitin_unsat (Hypercube.hypercubeGraph k) (hypercubeCharge k)
    (hypercubeCharge_odd k)
  exact Depth3CollapseModel.size_lower_exp hunsat
    (hypercube_dtRefCollapseModel k Ax hAx w0 hw0') (le_refl 1)
    (Hypercube.hypercube_hasExpansion k) ht2 (by rw [hypercube_card_V]; exact hcard)
    hd hk1 hdn hkd (by rw [one_mul]; exact hsmall) D ⟨hlab, href⟩

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.dtRefCollapseModel
#print axioms PallLean.Paper93.DeepMath.PathB.hypercube_dtRef_depth_lower_bound
