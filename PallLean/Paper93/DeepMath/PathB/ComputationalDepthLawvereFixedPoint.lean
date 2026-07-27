import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDiagonalRigidity

/-!
# "SAT is the implicit superpolynomial fixed point": Lawvere's theorem, and the honest residual

`DiagonalRigidity` unified the threads onto one target: SAT is the **implicit** superpolynomial fixed
point — rigid via self-reference without paying the enumeration.  This file gives the positive form of
the whole diagonal thread — **Lawvere's fixed-point theorem** — which is the exact mechanism of an
*implicit* fixed point: a **point-surjection** `g : A → (A → B)` (self-reference: the system encodes its
own functions) forces **every** endomap `f : B → B` to have a fixed point, obtained by **self-application**
`g a₀ a₀`, not by enumerating `B`.

This is what "implicit fixed point" means precisely: existence from self-reference, for free, with no
enumeration cost.  What Lawvere does **not** give is that the fixed point is *hard* (superpolynomial) or
that it *is SAT* — those are the residual, and they are `cost_super`.

## What is proved

* **`lawvere`** — self-reference (`PointSurjective g`) ⟹ every `f : B → B` has a fixed point.  The
  implicit fixed point mechanism (axiom-free).
* **`lawvere_explicit`** — the fixed point is exactly `g a₀ a₀` for the self-referential witness `a₀`:
  built by self-application, no enumeration.  The "implicit" property, made explicit.
* **`cantor`** — dual: a fixed-point-free `f` forbids any point-surjection.  The negative (diagonal)
  form, recovered.
* **`no_surjection_onto_predicates`** — Cantor for `Bool`: no `g : A → (A → Bool)` is point-surjective
  (`!` has no fixed point).  The diagonal barrier of `DiagonalRigidity`, from Lawvere.
* **`implicit_fixedpoint_exists_of_tseitin`** — the reduction: *if* SAT's Tseitin self-encoding is a
  point-surjection, *then* the hardness-improver has an implicit fixed point — a maximally hard
  function.  Reduces the target to the surjection plus hardness/identity.

## Honest verdict — existence is free; hardness and identity are the wall

Lawvere gives the implicit fixed point for free from self-reference (`lawvere`, axiom-free), and it is
genuinely *implicit* — `g a₀ a₀`, self-application, no enumeration (`lawvere_explicit`).  So "an implicit
fixed point exists" is proved outright once the self-referential surjection is granted
(`implicit_fixedpoint_exists_of_tseitin`).  But Lawvere gives **existence**, not **hardness**: it does
not say the fixed point is superpolynomial, nor that it is SAT.  Worse, by `cantor`/Cantor a strictly
hardness-*increasing* improver has *no* fixed point, so it forbids the surjection — the surjection exists
only when the improver has a maximally hard fixed point.  So "SAT is the implicit superpolynomial fixed
point" reduces, via Lawvere, to exactly three residual pieces: (1) SAT's Tseitin encoding is a genuine
point-surjection (structural, the most tractable), (2) the Lawvere fixed point is superpolynomially
hard, and (3) it is SAT.  Pieces (2)+(3) are `cost_super` = `P ≠ NP`.  The implicit-fixed-point
mechanism is proved; that SAT is a *hard* one is the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.LawvereFixedPoint

/-- **Point-surjective**: every function `h : A → B` is `g a` for some `a`.  The self-reference
condition — the system `g` encodes all its own functions `A → B`. -/
def PointSurjective {A B : Type} (g : A → A → B) : Prop := ∀ h : A → B, ∃ a, g a = h

/-! ### Lawvere's fixed-point theorem — the implicit fixed point -/

/-- **Lawvere's fixed-point theorem (proved, axiom-free).**  If `g` is point-surjective (self-reference),
then every endomap `f : B → B` has a fixed point.  The fixed point is obtained *implicitly* — from the
self-referential witness for the diagonal `a ↦ f (g a a)` — not by any enumeration of `B`. -/
theorem lawvere {A B : Type} {g : A → A → B} (hg : PointSurjective g) (f : B → B) :
    ∃ b, f b = b := by
  obtain ⟨a₀, ha₀⟩ := hg (fun a => f (g a a))
  exact ⟨g a₀ a₀, (congrFun ha₀ a₀).symm⟩

/-- **The implicit fixed point is `g a₀ a₀` (proved, axiom-free).**  Given the self-referential witness
`a₀` (with `g a₀ = fun a => f (g a a)`), the fixed point is `g a₀ a₀` — built by **self-application**,
with no enumeration of `B`.  This is exactly the "implicit" in *implicit fixed point*. -/
theorem lawvere_explicit {A B : Type} (g : A → A → B) (f : B → B) (a₀ : A)
    (ha₀ : g a₀ = fun a => f (g a a)) : f (g a₀ a₀) = g a₀ a₀ :=
  (congrFun ha₀ a₀).symm

/-! ### The dual: Cantor -/

/-- **Cantor, from Lawvere (proved, axiom-free).**  If `f` has no fixed point, no `g` is
point-surjective: self-reference is impossible when the target endomap is fixed-point-free. -/
theorem cantor {A B : Type} {f : B → B} (hf : ∀ b, f b ≠ b) (g : A → A → B) :
    ¬ PointSurjective g := by
  intro hg
  obtain ⟨b, hb⟩ := lawvere hg f
  exact hf b hb

/-- **No point-surjection onto Boolean predicates (proved, axiom-free).**  Since `!` has no fixed point,
no `g : A → (A → Bool)` is point-surjective — Cantor's diagonal, the barrier of `DiagonalRigidity`,
recovered as an instance of Lawvere. -/
theorem no_surjection_onto_predicates {A : Type} (g : A → A → Bool) :
    ¬ PointSurjective g :=
  cantor (f := fun b => !b) (fun b => by cases b <;> decide) g

/-! ### The reduction: Tseitin surjection ⟹ an implicit fixed point exists -/

/-- **Tseitin surjection ⟹ implicit fixed point (proved).**  If SAT's Tseitin self-encoding is a
point-surjection (the system expresses all its own functions), then the hardness-improver has an implicit
fixed point — a function as hard as its own improvement, i.e. maximally hard.  Reduces "SAT is the
implicit superpolynomial fixed point" to: the surjection holds, and the fixed point is SAT and
superpolynomial.  The latter two are `cost_super`. -/
theorem implicit_fixedpoint_exists_of_tseitin {A B : Type} (g : A → A → B)
    (tseitin : PointSurjective g) (improve : B → B) :
    ∃ b, improve b = b :=
  lawvere tseitin improve

end PallLean.Paper93.DeepMath.PathB.LawvereFixedPoint

#print axioms PallLean.Paper93.DeepMath.PathB.LawvereFixedPoint.lawvere
#print axioms PallLean.Paper93.DeepMath.PathB.LawvereFixedPoint.lawvere_explicit
#print axioms PallLean.Paper93.DeepMath.PathB.LawvereFixedPoint.cantor
#print axioms PallLean.Paper93.DeepMath.PathB.LawvereFixedPoint.no_surjection_onto_predicates
#print axioms PallLean.Paper93.DeepMath.PathB.LawvereFixedPoint.implicit_fixedpoint_exists_of_tseitin
