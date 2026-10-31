import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCirculantLayer

/-!
# N-Frame: the `z`-general route supply — scaffold values freed for the absorber

Expander-discharge arc, rung E5-prep (… → circulant layer → **`z`-general supply**).  The
E5 paper round found that the taut-burial hole (design doc, finding (a)) is closed by the
TAUT-PAIR ABSORBER — and that fix makes the target block's row-side absorber half enter
the target system as one more failure-forced row, which is consistent only if the
supply's off-`K∪{j*}` values generalize from the constant `0` to a designer vector `z`:
the scaffold literal at coordinate `j` becomes `(e_j, z j + 1)` (failure forces
`a j = z j`), `a₀` takes value `z j` off the priced coordinates, and the edge-route pin
value becomes `bval j + 1 + z j''`.

  `RouteAssignmentZ` — the `z`-aware route predicate.
  `route_supply_z` — **PROVED, THE `z`-GENERAL SUPPLY PACKAGE**: all conclusions of
        `route_supply` with the scaffold clause at values `z j + 1`;  `z = 0` recovers
        the original.
  `routeAssignment_z_zero` — **PROVED**: the specialization check.

## Honest scope

Safe under every variant of the E5 design (the absorber fix consumes it; the original
machinery is the `z = 0` case).  The kill-accounting itself remains BLOCKED on the
full-block concentration wall (design doc, finding (b)) — an open design round, not
mechanical.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameRouteSupplyZ

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook
open PallLean.Paper93.DeepMath.PathB.NFrameParityRouteSupply

variable {v : ℕ}

/-- The `z`-aware route assignment: each priced coordinate is forced directly or through
an edge whose companion is outside `K ∪ {j*}`, with the edge pin value adjusted by the
companion's scaffold value. -/
def RouteAssignmentZ (v : ℕ) (jstar : Fin v) (K : Finset (Fin v))
    (bval : Fin v → ZMod 2) (z : Fin v → ZMod 2) (r : Fin v → Lit v) : Prop :=
  ∀ j ∈ K,
    r j = ((single v j, bval j + 1) : Lit v)
    ∨ ∃ j'' : Fin v, j'' ∉ K ∧ j'' ≠ jstar
        ∧ r j = ((single v j + single v j'', bval j + 1 + z j'') : Lit v)

/-- **The specialization check (proved)**: at `z = 0` the `z`-aware predicate is the
original route assignment. -/
theorem routeAssignment_z_zero (v : ℕ) (jstar : Fin v) (K : Finset (Fin v))
    (bval : Fin v → ZMod 2) (r : Fin v → Lit v)
    (h : RouteAssignment v jstar K bval r) :
    RouteAssignmentZ v jstar K bval (fun _ => 0) r := by
  intro j hj
  rcases h j hj with hdir | ⟨j'', hj''K, hj''s, hedge⟩
  · exact Or.inl hdir
  · refine Or.inr ⟨j'', hj''K, hj''s, ?_⟩
    rw [hedge]
    congr 1
    show bval j + 1 = bval j + 1 + 0
    rw [add_zero]

set_option maxHeartbeats 1600000 in
/-- **THE `z`-GENERAL SUPPLY PACKAGE (proved)**: the full `route_supply` conclusion set
with the scaffold clause at designer values `z` — failure of `(e_j, z j + 1)` forces
`a j = z j` off the priced coordinates. -/
theorem route_supply_z (v : ℕ) (jstar : Fin v) (bstar : ZMod 2)
    (K : Finset (Fin v)) (hK : jstar ∉ K) (bval : Fin v → ZMod 2)
    (z : Fin v → ZMod 2)
    (r : Fin v → Lit v) (hr : RouteAssignmentZ v jstar K bval z r) :
    ∃ w a₀ : Fin v → ZMod 2,
      dotp (single v jstar) w = 1
      ∧ (∀ j ∈ K, dotp (r j).1 w = 0)
      ∧ (∀ j ∈ K, dotp (single v j) w = 0)
      ∧ ¬ litHolds a₀ (single v jstar, bstar)
      ∧ (∀ j ∈ K, ¬ litHolds a₀ (single v j, bval j))
      ∧ (∀ j ∈ K, litHolds a₀ (r j))
      ∧ (∀ a : Fin v → ZMod 2,
          ((∀ j ∈ K, litHolds a (r j))
            ∧ ∀ j : Fin v, j ∉ K → j ≠ jstar →
                ¬ litHolds a (single v j, z j + 1))
          ↔ (a = a₀ ∨ a = a₀ + w)) := by
  classical
  have hy1 : ∀ x y : ZMod 2, ¬ x = y ↔ x = y + 1 := by decide
  have hy2 : ∀ y : ZMod 2, ¬ (y + 1 = y) := by decide
  have hy3 : ∀ y : ZMod 2, ¬ (y = y + 1) := by decide
  have hz2 : ∀ x y : ZMod 2, ¬ x = y + 1 → x = y := by decide
  set a₀ : Fin v → ZMod 2 := fun j =>
    if j = jstar then bstar + 1 else if j ∈ K then bval j + 1 else z j with ha₀
  have ha₀star : a₀ jstar = bstar + 1 := by
    rw [ha₀]
    exact if_pos rfl
  have ha₀K : ∀ j ∈ K, a₀ j = bval j + 1 := by
    intro j hj
    have hne : j ≠ jstar := fun hcon => hK (hcon ▸ hj)
    rw [ha₀]
    show (if j = jstar then bstar + 1 else if j ∈ K then bval j + 1 else z j)
      = bval j + 1
    rw [if_neg hne, if_pos hj]
  have ha₀off : ∀ j : Fin v, j ∉ K → j ≠ jstar → a₀ j = z j := by
    intro j hjK hjs
    rw [ha₀]
    show (if j = jstar then bstar + 1 else if j ∈ K then bval j + 1 else z j) = z j
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
      show dotp (single v j + single v j'') a₀ = bval j + 1 + z j''
      rw [dotp_add_left, dotp_single, dotp_single, ha₀K j hj,
        ha₀off j'' hj''K hj''s]
  have hsker : ∀ j ∈ K, dotp (single v j) (single v jstar) = 0 := by
    intro j hj
    have hjs : j ≠ jstar := fun hcon => hK (hcon ▸ hj)
    rw [dotp_single]
    show (if j = jstar then (1 : ZMod 2) else 0) = 0
    rw [if_neg hjs]
  refine ⟨single v jstar, a₀, ?_, hker, hsker, ?_, ?_, hpins₀, ?_⟩
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
          have h2 : dotp (single v j + single v j'') a
              = bval j + 1 + z j'' := h1
          rw [dotp_add_left, dotp_single, dotp_single] at h2
          have h3 : ¬ dotp (single v j'') a = z j'' + 1 :=
            hscaf j'' hj''K hj''s
          rw [dotp_single] at h3
          have h4 : a j'' = z j'' := hz2 _ _ h3
          rw [h4] at h2
          have h5 : a j = bval j + 1 := add_right_cancel h2
          rw [h5, ha₀K j hj]
      have hoffO : ∀ j : Fin v, j ∉ K → j ≠ jstar → a j = a₀ j := by
        intro j hjK hjs
        have h1 : ¬ dotp (single v j) a = z j + 1 := hscaf j hjK hjs
        rw [dotp_single] at h1
        rw [hz2 _ _ h1, ha₀off j hjK hjs]
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
        show ¬ dotp (single v j) a₀ = z j + 1
        rw [dotp_single, ha₀off j hjK hjs]
        exact hy3 (z j)
      · constructor
        · intro j hj
          show dotp (r j).1 (a₀ + single v jstar) = (r j).2
          rw [dotp_add_right, hker j hj, add_zero]
          exact hpins₀ j hj
        · intro j hjK hjs
          show ¬ dotp (single v j) (a₀ + single v jstar) = z j + 1
          rw [dotp_add_right, dotp_single, dotp_single,
            ha₀off j hjK hjs]
          show ¬ z j + (if j = jstar then (1 : ZMod 2) else 0) = z j + 1
          rw [if_neg hjs, add_zero]
          exact hy3 (z j)

end PallLean.Paper93.DeepMath.PathB.NFrameRouteSupplyZ

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRouteSupplyZ.routeAssignment_z_zero
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRouteSupplyZ.route_supply_z
