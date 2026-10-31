import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer8GeneralCircuit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer7CircuitFamily

/-!
# Layer 9 (open-frontier infrastructure) — `P/poly` and the Karp–Lipton collapse core

Honest Layer-9 infrastructure (per `SCOPE_LAYER8_EXPLICIT_LOWER_BOUND_FRONTIER.md` §6's "could" list):
a `P/poly` definition over general circuit families, and the **logical core** of the Karp–Lipton theorem
as a genuine, sorry-free, conditional theorem.

## What is and is not claimed

* **`Ppoly`** — a clean definition of `P/poly` (poly-size general-circuit families).  Real infrastructure.
* **`karpLipton_collapse`** — the quantifier-exchange skeleton of Karp–Lipton: a `Π₂`-form predicate
  `∀y ∃z R x y z` equals the `Σ₂`-form `∃g ∀y R x y (w g x y)` **given** the advice-extraction hypothesis
  `hadv`.  This is **proved, axiom-free** (pure logic).

**The honest fence.**  The *full* Karp–Lipton theorem is `NP ⊆ P/poly ⇒ PH = Σ₂` (the polynomial hierarchy
collapses).  Its genuine content is: (i) the `∀∃ → ∃∀` exchange — captured *and proved* here; (ii) that the
advice `g` is a **poly-size** object, so `∃g` is a real `Σ₂` existential — captured by instantiating the
advice space `G` as poly-size circuits; (iii) that `NP ⊆ P/poly` actually *provides* such advice with
correct witness extraction (the SAT advice circuit + **self-reducibility**) — this is `hadv`.  Step (iii)
is the hard, complexity-specific part; it requires the polynomial hierarchy and SAT self-reducibility over
the (off-limits, TM-based) uniform model.  **It is left as an explicit named hypothesis `hadv`, never
asserted.**  Without a size bound on `G` the collapse is a trivial currying; the content lives entirely in
"the advice is small and works", i.e. in `hadv` + the choice of `G` — exactly where the open difficulty is.

So this file is the *logical mechanism* of Karp–Lipton, honestly conditional; it is **not** an
unconditional PH collapse and makes **no** progress toward `NP ⊄ P/poly` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer9

open PallLean.Paper93.DeepMath.PathB

/-- **`P/poly`**: a length-indexed boolean language is in `P/poly` iff some polynomially-size-bounded
general-circuit family computes it at every length. -/
def Ppoly (L : Layer7.BoolLang) : Prop :=
  ∃ p : ℕ → ℕ, Layer7.IsPolyBounded p ∧ ∀ n, (fun x => L n x) ∈ Layer8.SIZE n (p n)

/-- **Karp–Lipton collapse — the logical core (proved, axiom-free).**  Given the advice-extraction
hypothesis `hadv` (whenever `∀ y, ∃ z, R x y z`, a single advice `g : G` yields a uniform witness
`w g x y` for every `y`), the `Π₂`-form predicate `∀ y, ∃ z, R x y z` is equivalent to the `Σ₂`-form
`∃ g, ∀ y, R x y (w g x y)`.

With `G` = poly-size circuits, `∃ g` is a `Σ₂` existential and `hadv` is `NP ⊆ P/poly` + SAT
self-reducibility — the hard complexity step, fenced here as a hypothesis. -/
theorem karpLipton_collapse {X Y Z G : Type*} (R : X → Y → Z → Prop) (w : G → X → Y → Z)
    (hadv : ∀ x : X, (∀ y, ∃ z, R x y z) → ∃ g : G, ∀ y, R x y (w g x y)) :
    ∀ x : X, ((∀ y, ∃ z, R x y z) ↔ (∃ g : G, ∀ y, R x y (w g x y))) := by
  intro x
  constructor
  · intro h; exact hadv x h
  · rintro ⟨g, hg⟩ y; exact ⟨w g x y, hg y⟩

/-- The Karp–Lipton collapse at the language/class level: the `Π₂`-language equals the `Σ₂`-language
(given the advice-extraction hypothesis). -/
theorem karpLipton_set_collapse {X Y Z G : Type*} (R : X → Y → Z → Prop) (w : G → X → Y → Z)
    (hadv : ∀ x : X, (∀ y, ∃ z, R x y z) → ∃ g : G, ∀ y, R x y (w g x y)) :
    {x : X | ∀ y, ∃ z, R x y z} = {x : X | ∃ g : G, ∀ y, R x y (w g x y)} := by
  ext x; exact karpLipton_collapse R w hadv x

end PallLean.Paper93.DeepMath.PathB.Layer9

#print axioms PallLean.Paper93.DeepMath.PathB.Layer9.karpLipton_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.Layer9.karpLipton_set_collapse
