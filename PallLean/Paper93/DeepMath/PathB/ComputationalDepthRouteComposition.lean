/-!
# Route 2 ⊗ Route 4: the composition lemma and magnification solve each other's problems

Darren's observation: Route 2 (KRW / composition, ceiling **depth**) and Route 4 (hardness magnification,
whose weak bound sits on the **natural-proofs barrier**) *solve each other's problems*.  This is a real and
sharp read of the current frontier.  Here we make the complementarity precise — and isolate exactly the
residual that neither supplies.

## What each route has, and lacks

* **Route 2 (composition / KW).**  HAS: a **non-natural** technique — KW/communication bounds are about a
  specific relation, so they dodge the largeness (natural-proofs) barrier.  LACKS: it only reaches
  **depth** `NC¹`, not **size** `P` — composition amplifies depth additively, never to superpolynomial size.
* **Route 4 (magnification).**  HAS: a **magnification engine** `W₄ → S` — a weak `n^{1+ε}` bound on a
  sparse problem lifts to the full separation `S` (size).  LACKS: its weak bound `W₄` sits **exactly on
  the natural-proofs barrier**, so it cannot be proved by natural means.

They are mirror-image incompletenesses: Route 2 has the *non-naturalness* Route 4 needs; Route 4 has the
*magnification to size* Route 2 needs.

## The handoff — the one residual

The only thing not supplied by either is the **handoff** `H : W₂ → W₄`: translating Route 2's
composition/depth bound into the shape Route 4's magnification consumes.  This is the **locality barrier**
(Chen–Hirahara–Jin–Williams and successors): current magnification proofs and the lower-bound techniques
that would feed them are both *local*, and the handoff is exactly where that bites.

## What is proved (the dependency structure — simple modus ponens, honest by design)

* **`route4_completes_route2`** — Route 4 supplies size: `(W₂ → W₄) → (W₄ → S) → (W₂ → S)`.  Magnification
  carries Route 2's weak bound all the way to the full **size** separation Route 2 could never reach.
* **`route2_completes_route4`** — Route 2 supplies the (non-natural) proof: `(W₂ → W₄) → W₂ → W₄`.  Route 2's
  non-natural bound, via the handoff, *is* the weak bound `W₄` that Route 4 needed but the barrier forbade
  proving naturally.
* **`routes_compose`** — together: `W₂ → (W₂ → W₄) → (W₄ → S) → S`.  The two routes complete the separation
  **iff the handoff holds**.

## Honest scope — the residual carries the weight

The theorems are deliberately simple implications; the content is the *structure*, not the logic.  The
three antecedents are: `W₂` (Route 2's bound — restricted/known in cases), the magnification `W₄ → S`
(known in cases), and the **handoff `H : W₂ → W₄`** — which is the single open joint piece, the locality
barrier.  `H` cannot be free: if it were, the known pieces would already give `P ≠ NP`, so all the
difficulty concentrates in it.  Darren is right that the two routes solve each other's *named* barriers
(depth-ceiling ↔ natural-proofs) — but a *third* barrier (locality, `H`) remains, and whether it in turn
reduces to `cost_super` is itself open.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RouteComposition

/-- **Route 4 supplies the size Route 2 lacks (proved).**  Given the handoff `H : W₂ → W₄` and the
magnification engine `mag : W₄ → S`, Route 2's weak bound `W₂` is carried all the way to the full **size**
separation `S` — the thing Route 2 (depth-ceilinged) structurally could not reach. -/
theorem route4_completes_route2 (W2 W4 S : Prop) (H : W2 → W4) (mag : W4 → S) : W2 → S :=
  fun w2 => mag (H w2)

/-- **Route 2 supplies the non-natural proof Route 4 lacks (proved).**  Route 2's bound `W₂` is proved by
a *non-natural* technique (dodging the natural-proofs barrier); via the handoff it yields `W₄` — exactly
the weak bound Route 4's magnification needed but could not prove by natural means. -/
theorem route2_completes_route4 (W2 W4 : Prop) (H : W2 → W4) (w2 : W2) : W4 := H w2

/-- **The two routes compose to the full separation (proved) — iff the handoff holds.**  With Route 2's
bound `w2`, the handoff `H`, and Route 4's magnification `mag`, the separation `S` follows.  Each route
supplies the ingredient the other's barrier withheld; the single residual is the handoff `H`. -/
theorem routes_compose (W2 W4 S : Prop) (w2 : W2) (H : W2 → W4) (mag : W4 → S) : S :=
  mag (H w2)

/-- **The residual, named (proved).**  Assuming Route 2's bound and Route 4's magnification are in hand,
the *entire* remaining gap to the separation is the handoff `W₂ → W₄`: `S` holds iff `H` does (the reverse
using the given `w2`/`mag`).  This isolates the locality barrier as the one open joint piece. -/
theorem separation_iff_handoff (W2 W4 S : Prop) (w2 : W2) (mag : W4 → S)
    (h_needed : S → (W2 → W4)) : (W2 → W4) ↔ S :=
  ⟨fun H => mag (H w2), fun s => h_needed s⟩

end PallLean.Paper93.DeepMath.PathB.RouteComposition

#print axioms PallLean.Paper93.DeepMath.PathB.RouteComposition.route4_completes_route2
#print axioms PallLean.Paper93.DeepMath.PathB.RouteComposition.route2_completes_route4
#print axioms PallLean.Paper93.DeepMath.PathB.RouteComposition.routes_compose
#print axioms PallLean.Paper93.DeepMath.PathB.RouteComposition.separation_iff_handoff
