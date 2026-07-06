import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityStdDrag

/-!
# N-Frame: the route supply — edge-mediated pins with scaffold-covered companions

Expander-discharge arc, rung E1 (… → standard drag → **route supply**).  The
generalization of `singleton_supply` that the kill-accounting needs: the pin forcing a
priced coordinate `j` may be either the DIRECT complement singleton `(e_j, b_j+1)` or an
EDGE literal `(e_j + e_{j''}, b_j + 1)` whose companion `j''` lies OUTSIDE `K ∪ {j*}` — so
the companion is SCAFFOLD-COVERED (the failure-forced literal `(e_{j''},1)` pins
`a j'' = 0`) and needs NO liveness of its own.

This is the load-bearing simplification of the discharge design (design doc §E): because
companions are scaffold-covered, killed coordinates remain usable as companions, deadness
does NOT close under decomposition, and the kill-cost of a coordinate set `A` is its full
incident-edge-column count — `≥ (1 + d/2)·|A|` on ANY `d`-regular graph, no spectral
expansion required.  The certified interface weakens accordingly.

  `dotp_add_left` — linearity of the pairing in the functional slot.
  `route_supply` — **PROVED, THE GENERALIZED SUPPLY PACKAGE**: for every target `(j*, b*)`
        and priced set `K ∌ j*` with values `bval`, and ANY route assignment `r` (direct or
        edge with off-`K∪{j*}` companion), explicit `(w, a₀)` satisfying all the linear
        slots: `hlw`, the route `w`-kernels, the `a₀`-falsifications, route consistency at
        `a₀`, and the pair-solution identity (routes hold ∧ scaffold-false ⟺
        `a ∈ {a₀, a₀ + w}`).  `singleton_supply` is the all-direct special case.

## Honest scope

Coordinate-level algebra only: the position-level bookkeeping (extended codebook with edge
indices, the route-general re-threading of the 28e/28g pair machinery, and the
kill-accounting `|V| = Θ(T)` at real cuts) are rungs E2–E5.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityRouteSupply

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook

variable {v : ℕ}

/-- Linearity of the pairing in the functional slot. -/
theorem dotp_add_left (l l' a : Fin v → ZMod 2) :
    dotp (l + l') a = dotp l a + dotp l' a := by
  unfold dotp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  show (l i + l' i) * a i = l i * a i + l' i * a i
  ring

/-- A route assignment for the priced set: each priced coordinate is forced either
directly or through an edge whose companion is outside `K ∪ {j*}`. -/
def RouteAssignment (v : ℕ) (jstar : Fin v) (K : Finset (Fin v))
    (bval : Fin v → ZMod 2) (r : Fin v → Lit v) : Prop :=
  ∀ j ∈ K,
    r j = ((single v j, bval j + 1) : Lit v)
    ∨ ∃ j'' : Fin v, j'' ∉ K ∧ j'' ≠ jstar
        ∧ r j = ((single v j + single v j'', bval j + 1) : Lit v)

set_option maxHeartbeats 1600000 in
/-- **THE GENERALIZED SUPPLY PACKAGE (proved)**: the `singleton_supply` conclusions with
the pins replaced by any route assignment — direct singletons or edge literals with
scaffold-covered companions. -/
theorem route_supply (v : ℕ) (jstar : Fin v) (bstar : ZMod 2)
    (K : Finset (Fin v)) (hK : jstar ∉ K) (bval : Fin v → ZMod 2)
    (r : Fin v → Lit v) (hr : RouteAssignment v jstar K bval r) :
    ∃ w a₀ : Fin v → ZMod 2,
      dotp (single v jstar) w = 1
      ∧ (∀ j ∈ K, dotp (r j).1 w = 0)
      ∧ ¬ litHolds a₀ (single v jstar, bstar)
      ∧ (∀ j ∈ K, ¬ litHolds a₀ (single v j, bval j))
      ∧ (∀ j ∈ K, litHolds a₀ (r j))
      ∧ (∀ a : Fin v → ZMod 2,
          ((∀ j ∈ K, litHolds a (r j))
            ∧ ∀ j : Fin v, j ∉ K → j ≠ jstar → ¬ litHolds a (single v j, 1))
          ↔ (a = a₀ ∨ a = a₀ + w)) := by
  classical
  have hy1 : ∀ x y : ZMod 2, ¬ x = y ↔ x = y + 1 := by decide
  have hy2 : ∀ y : ZMod 2, ¬ (y + 1 = y) := by decide
  have hz : ∀ x : ZMod 2, ¬ x = 1 → x = 0 := by decide
  set a₀ : Fin v → ZMod 2 := fun j =>
    if j = jstar then bstar + 1 else if j ∈ K then bval j + 1 else 0 with ha₀
  have ha₀star : a₀ jstar = bstar + 1 := by
    rw [ha₀]
    exact if_pos rfl
  have ha₀K : ∀ j ∈ K, a₀ j = bval j + 1 := by
    intro j hj
    have hne : j ≠ jstar := fun hcon => hK (hcon ▸ hj)
    rw [ha₀]
    show (if j = jstar then bstar + 1 else if j ∈ K then bval j + 1 else 0)
      = bval j + 1
    rw [if_neg hne, if_pos hj]
  have ha₀off : ∀ j : Fin v, j ∉ K → j ≠ jstar → a₀ j = 0 := by
    intro j hjK hjs
    rw [ha₀]
    show (if j = jstar then bstar + 1 else if j ∈ K then bval j + 1 else 0) = 0
    rw [if_neg hjs, if_neg hjK]
  -- the route kernels
  have hker : ∀ j ∈ K, dotp (r j).1 (single v jstar) = 0 := by
    intro j hj
    have hjs : j ≠ jstar := fun hcon => hK (hcon ▸ hj)
    rcases hr j hj with hdir | ⟨j'', hj''K, hj''s, hedge⟩
    · rw [hdir]
      show dotp (single v j) (single v jstar) = 0
      rw [dotp_single]
      show (if j = jstar then (1 : ZMod 2) else 0) = 0
      rw [if_neg hjs]
    · rw [hedge]
      show dotp (single v j + single v j'') (single v jstar) = 0
      rw [dotp_add_left, dotp_single, dotp_single]
      show (if j = jstar then (1 : ZMod 2) else 0)
        + (if j'' = jstar then (1 : ZMod 2) else 0) = 0
      rw [if_neg hjs, if_neg hj''s]
      decide
  -- routes hold at a₀
  have hpins₀ : ∀ j ∈ K, litHolds a₀ (r j) := by
    intro j hj
    rcases hr j hj with hdir | ⟨j'', hj''K, hj''s, hedge⟩
    · rw [hdir]
      show dotp (single v j) a₀ = bval j + 1
      rw [dotp_single]
      exact ha₀K j hj
    · rw [hedge]
      show dotp (single v j + single v j'') a₀ = bval j + 1
      rw [dotp_add_left, dotp_single, dotp_single, ha₀K j hj,
        ha₀off j'' hj''K hj''s, add_zero]
  refine ⟨single v jstar, a₀, ?_, hker, ?_, ?_, hpins₀, ?_⟩
  · rw [dotp_single]
    show (if jstar = jstar then (1 : ZMod 2) else 0) = 1
    rw [if_pos rfl]
  · show ¬ dotp (single v jstar) a₀ = bstar
    rw [dotp_single, ha₀star]
    exact hy2 bstar
  · intro j hj
    show ¬ dotp (single v j) a₀ = bval j
    rw [dotp_single, ha₀K j hj]
    exact hy2 (bval j)
  · intro a
    constructor
    · rintro ⟨hpins, hscaf⟩
      -- a agrees with a₀ off jstar
      have hoffK : ∀ j ∈ K, a j = a₀ j := by
        intro j hj
        rcases hr j hj with hdir | ⟨j'', hj''K, hj''s, hedge⟩
        · have h1 := hpins j hj
          rw [hdir] at h1
          have h2 : dotp (single v j) a = bval j + 1 := h1
          rw [dotp_single] at h2
          rw [h2, ha₀K j hj]
        · have h1 := hpins j hj
          rw [hedge] at h1
          have h2 : dotp (single v j + single v j'') a = bval j + 1 := h1
          rw [dotp_add_left, dotp_single, dotp_single] at h2
          have h3 : ¬ dotp (single v j'') a = 1 := hscaf j'' hj''K hj''s
          rw [dotp_single] at h3
          have h4 : a j'' = 0 := hz _ h3
          rw [h4, add_zero] at h2
          rw [h2, ha₀K j hj]
      have hoffO : ∀ j : Fin v, j ∉ K → j ≠ jstar → a j = a₀ j := by
        intro j hjK hjs
        have h1 : ¬ dotp (single v j) a = 1 := hscaf j hjK hjs
        rw [dotp_single] at h1
        rw [hz _ h1, ha₀off j hjK hjs]
      by_cases hstar : a jstar = a₀ jstar
      · left
        funext j
        by_cases hjs : j = jstar
        · rw [hjs]
          exact hstar
        · by_cases hjK : j ∈ K
          · exact hoffK j hjK
          · exact hoffO j hjK hjs
      · right
        funext j
        show a j = a₀ j + single v jstar j
        by_cases hjs : j = jstar
        · subst hjs
          show a j = a₀ j + (if j = j then (1 : ZMod 2) else 0)
          rw [if_pos rfl]
          exact (hy1 _ _).mp hstar
        · show a j = a₀ j + (if j = jstar then (1 : ZMod 2) else 0)
          rw [if_neg hjs, add_zero]
          by_cases hjK : j ∈ K
          · exact hoffK j hjK
          · exact hoffO j hjK hjs
    · rintro (rfl | rfl)
      · refine ⟨hpins₀, ?_⟩
        intro j hjK hjs
        show ¬ dotp (single v j) a₀ = 1
        rw [dotp_single, ha₀off j hjK hjs]
        decide
      · constructor
        · intro j hj
          show dotp (r j).1 (a₀ + single v jstar) = (r j).2
          rw [dotp_add_right, hker j hj, add_zero]
          exact hpins₀ j hj
        · intro j hjK hjs
          show ¬ dotp (single v j) (a₀ + single v jstar) = 1
          rw [dotp_add_right, dotp_single, dotp_single,
            ha₀off j hjK hjs]
          show ¬ (0 : ZMod 2) + (if j = jstar then (1 : ZMod 2) else 0) = 1
          rw [if_neg hjs]
          decide

/-- **The specialization check (proved)**: the all-direct route assignment is a
`RouteAssignment` — `route_supply` strictly generalizes `singleton_supply`. -/
theorem direct_routes_are_routes (v : ℕ) (jstar : Fin v) (K : Finset (Fin v))
    (bval : Fin v → ZMod 2) :
    RouteAssignment v jstar K bval
      (fun j => ((single v j, bval j + 1) : Lit v)) :=
  fun _ _ => Or.inl rfl

end PallLean.Paper93.DeepMath.PathB.NFrameParityRouteSupply

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityRouteSupply.dotp_add_left
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityRouteSupply.route_supply
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityRouteSupply.direct_routes_are_routes
