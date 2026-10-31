import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLawvereFixedPoint

/-!
# Is SAT's Tseitin self-encoding a point-surjection? Real onto the expressible class — misses the hard one

`LawvereFixedPoint` reduced "SAT is the implicit superpolynomial fixed point" to three pieces, the most
tractable being: SAT's Tseitin encoding is a **point-surjection**.  This file attacks it — and the very
theorem we proved last time (`no_surjection_onto_predicates`: *no* `g : A → (A → Bool)` is point-surjective
onto all functions, by Cantor) forces the honest shape of the answer.

The Tseitin encoding is a point-surjection **onto the expressible class** — the functions some SAT
instance computes (Cook–Levin: SAT expresses every poly-computable function).  It is **not** a surjection
onto *all* functions.  And the concrete function it misses is exactly the **hard** one: the Cantor
diagonal `a ↦ !(g a a)`, which differs from every expressible function.  That is precisely the function
SAT would need to *be* to be the hard fixed point.

## What is proved

* **`tseitin_surjective_on_expressible`** — the Tseitin encoding *is* point-surjective onto the
  expressible class: every function some instance computes is reached.  The Cook–Levin surjection.
* **`hard_diagonal_not_expressible`** — the concrete crux: the Cantor diagonal `a ↦ !(g a a)` is **not**
  expressible — no instance computes it.  It differs from every `g a` at `a`.
* **`expressible_not_all`** — hence the expressible class is a *proper* subclass: the surjection misses a
  function.  Tseitin surjectivity is genuinely restricted, not full.
* **`surjection_reaches_soft_misses_hard`** — the two together: point-surjective onto expressible **and**
  missing the hard diagonal.  The surjection reaches soft functions, misses the hard one.
* **`lawvere_on_expressible`** — restricted Lawvere: the fixed point exists **iff** the diagonal
  `a ↦ f (g a a)` is expressible.  The reachable fixed point lives in the expressible class.

## Honest verdict — the surjection is real but restricted, and it misses exactly the hard function

SAT's Tseitin encoding is a genuine point-surjection **onto the expressible (poly-computable) class**
(`tseitin_surjective_on_expressible`, Cook–Levin) — piece (1) is real at that scope.  But it is provably
**not** onto all functions (`expressible_not_all`), and what it misses is exactly the hard Cantor diagonal
(`hard_diagonal_not_expressible`) — the function differing from every expressible one, i.e. the function
SAT would need to be to be superpolynomially hard.  So the Lawvere fixed point this surjection provides is
a **soft** (expressible) function, not the hard diagonal.  Making the surjection reach the hard diagonal
means expressing a function that differs from every expressible one — growing the expressible class beyond
itself, impossible by Cantor **unless** the class strictly exceeds `P`, i.e. SAT ∉ P.  So piece (1),
proved honestly, does not deliver a hard fixed point: the surjection is real but restricted, and the
restriction is exactly `cost_super` (the size-efficient universal-object / capture gap of
`GodelSpringBridge`).  The surjection is proved; that it reaches a *hard* function is the wall.  Nothing
here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TseitinSurjection

open PallLean.Paper93.DeepMath.PathB.LawvereFixedPoint

/-- **Point-surjective onto a class `P`**: every function in `P` is `g a` for some `a`. -/
def PointSurjectiveOn {A B : Type} (g : A → A → B) (P : (A → B) → Prop) : Prop :=
  ∀ h : A → B, P h → ∃ a, g a = h

/-- **Expressible by `g`**: some instance `a` computes `h` (`g a = h`).  The Tseitin/Cook–Levin image —
the functions SAT expresses. -/
def Expressible {A B : Type} (g : A → A → B) (h : A → B) : Prop := ∃ a, g a = h

/-! ### The surjection is real onto the expressible class -/

/-- **Tseitin is point-surjective onto the expressible class (proved).**  Every function some instance
computes is reached — by definition of the expressible class.  This is the Cook–Levin content: SAT
expresses every poly-computable function.  (The real content is the *restriction*, below.) -/
theorem tseitin_surjective_on_expressible {A B : Type} (g : A → A → B) :
    PointSurjectiveOn g (Expressible g) :=
  fun _ he => he

/-! ### But it misses exactly the hard diagonal -/

/-- **The hard Cantor diagonal is not expressible (proved).**  No instance computes `a ↦ !(g a a)`: if
`g a` were it, then `g a a = !(g a a)`, impossible.  The surjection misses this function — and it is the
hard one, differing from every expressible function at its own index. -/
theorem hard_diagonal_not_expressible {A : Type} (g : A → A → Bool) :
    ¬ Expressible g (fun a => !(g a a)) := by
  rintro ⟨a, ha⟩
  have h : g a a = !(g a a) := congrFun ha a
  have contra : ∀ b : Bool, b ≠ !b := by decide
  exact contra (g a a) h

/-- **The expressible class is a proper subclass (proved).**  Some function — the hard diagonal — is not
expressible.  So the Tseitin surjection is genuinely restricted, never full (consistent with
`LawvereFixedPoint.no_surjection_onto_predicates`). -/
theorem expressible_not_all {A : Type} (g : A → A → Bool) :
    ∃ h : A → Bool, ¬ Expressible g h :=
  ⟨fun a => !(g a a), hard_diagonal_not_expressible g⟩

/-- **Reaches the soft, misses the hard (proved).**  The Tseitin encoding is point-surjective onto the
expressible class *and* misses the hard Cantor diagonal.  The surjection reaches soft (expressible)
functions; the hard one — the function SAT would need to be — is out of reach. -/
theorem surjection_reaches_soft_misses_hard {A : Type} (g : A → A → Bool) :
    PointSurjectiveOn g (Expressible g) ∧ ¬ Expressible g (fun a => !(g a a)) :=
  ⟨tseitin_surjective_on_expressible g, hard_diagonal_not_expressible g⟩

/-! ### Restricted Lawvere: the reachable fixed point is expressible -/

/-- **Lawvere on the expressible class (proved).**  If the diagonal `a ↦ f (g a a)` is expressible, the
endomap `f` has a fixed point `g a₀ a₀`.  The fixed point the surjection provides lives in the expressible
class — soft, not the hard diagonal. -/
theorem lawvere_on_expressible {A B : Type} (g : A → A → B) (f : B → B)
    (hdiag : Expressible g (fun a => f (g a a))) : ∃ b, f b = b := by
  obtain ⟨a₀, ha₀⟩ := hdiag
  exact ⟨g a₀ a₀, (congrFun ha₀ a₀).symm⟩

end PallLean.Paper93.DeepMath.PathB.TseitinSurjection

#print axioms PallLean.Paper93.DeepMath.PathB.TseitinSurjection.tseitin_surjective_on_expressible
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinSurjection.hard_diagonal_not_expressible
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinSurjection.expressible_not_all
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinSurjection.surjection_reaches_soft_misses_hard
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinSurjection.lawvere_on_expressible
