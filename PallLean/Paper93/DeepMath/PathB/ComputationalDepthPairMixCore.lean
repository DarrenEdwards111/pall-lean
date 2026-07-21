import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMediatedDichotomy

/-!
# The pair-mix kill, part 1: the decidable core and the singleton-swap machinery

Route-3 repair of the ∀m gap.  The two-slice contradiction is Boolean-specific,
but it localizes: a variable's influence is bottlenecked at its *first branch
point*, one wire.  A wire that bottlenecks chosen variables of two different
gadgets (partners outside) faces four completions demanding that a single
binary Boolean function separate all four input points — impossible:

* **`pair_mix_contra` (proved, decidable)** — no `op : Bool → Bool → Bool`
  admits unary factorizations of all four of `a∧b, ¬a∧b, a∧¬b, ¬a∧¬b`;
* `swapG_cone_clean` / **`swapG_blind_clean` (proved)** — the singleton-swap
  blindness: if every `{u}`-clean path misses a variable's gates off `u`, the
  `u`-swapped circuit is blind to it;
* `output_swapG` — the single swap at the true wire value preserves the output;
* general-width `getD_take_eq_g` / `inCone_take_reach_g` / `wire_take_output_g`
  / **`wire_blind_of_no_gate_below` (proved)** — the wire at `u` is blind to
  variables with no gate below `u`.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- **THE FOUR-COMPLETION CONTRADICTION (proved by decision)**: one binary
Boolean function cannot mediate all four sign patterns of a conjunction. -/
theorem pair_mix_contra (op : Bool → Bool → Bool) (U₁ U₂ U₃ U₄ : Bool → Bool) :
    ¬ ((∀ a b, (a && b) = U₁ (op a b)) ∧ (∀ a b, (!a && b) = U₂ (op a b))
      ∧ (∀ a b, (a && !b) = U₃ (op a b)) ∧ (∀ a b, (!a && !b) = U₄ (op a b))) := by
  revert op U₁ U₂ U₃ U₄
  decide

/-! ### Singleton-swap blindness -/

/-- A cone derivation of the `u`-swapped circuit is a `{u}`-clean path. -/
theorem swapG_cone_clean {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length)
    {u : ℕ} (hu : u < c.length) (w : Bool) :
    ∀ q, InCone (swapG c u w) q → CleanIn c {u} q := by
  have hlen : (swapG c u w).length = c.length := swapG_length c u w hu
  intro q hq
  induction hq with
  | root =>
    rw [hlen]
    exact CleanIn.root
  | step hw' ht hlt ih =>
    rename_i w' t
    by_cases hwu : w' = u
    · subst hwu
      rw [swapG_getD_self hu w] at ht
      exact absurd ht (by simp [gateReads])
    · rw [swapG_getD_ne hu w hwu] at ht
      exact CleanIn.step ih (by simp [hwu]) ht hlt

/-- **Singleton-swap blindness (proved)**: if every `{u}`-clean path misses a
variable's gates off `u`, the `u`-swapped circuit cannot see it. -/
theorem swapG_blind_clean {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length)
    {u : ℕ} (hu : u < c.length) (w : Bool) (i : Fin n)
    (hnc : ∀ q, CleanIn c {u} q → q ≠ u →
      c.getD q (.cst false) ≠ CGate.var i)
    (x : Fin n → Bool) (b : Bool) :
    output (swapG c u w) (Function.update x i b) = output (swapG c u w) x := by
  have hlen : (swapG c u w).length = c.length := swapG_length c u w hu
  have hnv : ∀ w', InCone (swapG c u w) w' →
      (swapG c u w).getD w' (.cst false) ≠ CGate.var i := by
    intro w' hw' hg
    by_cases hwu : w' = u
    · subst hwu
      rw [swapG_getD_self hu w] at hg
      simp at hg
    · rw [swapG_getD_ne hu w hwu] at hg
      exact hnc w' (swapG_cone_clean c hs hu w w' hw') hwu hg
  rw [output_eq_wire, output_eq_wire]
  exact cone_wire_agree (swapG c u w) i x b (by omega) hnv _ InCone.root

/-- The single swap at the true wire value preserves the output. -/
theorem output_swapG {n : ℕ} (c : List (CGate n)) {u : ℕ} (hu : u < c.length)
    (x : Fin n → Bool) :
    output (swapG c u (wire c x u)) x = output c x := by
  show (runFrom x [] (swapG c u (wire c x u))).getD
    ((swapG c u (wire c x u)).length - 1) false = output c x
  rw [runFrom_swapG c hu x, swapG_length c u (wire c x u) hu]
  rfl

/-! ### General-width prefix blindness -/

theorem getD_take_eq_g {n : ℕ} {c : List (CGate n)} {k q : ℕ} (h : q < k) :
    (c.take k).getD q (.cst false) = c.getD q (.cst false) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt h]

theorem inCone_take_reach_g {n : ℕ} {c : List (CGate n)} {u : ℕ}
    (hu : u < c.length) :
    ∀ q, InCone (c.take (u + 1)) q → Reach c u q := by
  intro q hq
  induction hq with
  | root =>
    have hlt : (c.take (u + 1)).length - 1 = u := by
      rw [List.length_take]
      omega
    rw [hlt]
    exact Reach.refl u
  | step hw' ht hlt ih =>
    rename_i w' t
    have hw'lt : w' < (c.take (u + 1)).length :=
      inCone_lt (show 0 < (c.take (u + 1)).length by rw [List.length_take]; omega) hw'
    have hw'lt' : w' < u + 1 := by
      rw [List.length_take] at hw'lt
      omega
    rw [getD_take_eq_g hw'lt'] at ht
    exact Reach.step ih ht hlt

theorem wire_take_output_g {n : ℕ} (c : List (CGate n)) {u : ℕ}
    (hu : u < c.length) (x : Fin n → Bool) :
    output (c.take (u + 1)) x = wire c x u := by
  show (runFrom x [] (c.take (u + 1))).getD ((c.take (u + 1)).length - 1) false
    = wire c x u
  have hl : (c.take (u + 1)).length = u + 1 := by
    rw [List.length_take]
    omega
  rw [hl]
  show (runFrom x [] (c.take (u + 1))).getD u false = wire c x u
  exact wire_prefix c x (by omega) (by omega)

/-- **The wire at `u` is blind to variables with no gate below `u` (proved).** -/
theorem wire_blind_of_no_gate_below {n : ℕ} (c : List (CGate n)) {u : ℕ}
    (hu : u < c.length) (i : Fin n)
    (hno : ∀ q, Reach c u q → c.getD q (.cst false) ≠ CGate.var i)
    (x : Fin n → Bool) (b : Bool) :
    wire c (Function.update x i b) u = wire c x u := by
  rw [← wire_take_output_g c hu, ← wire_take_output_g c hu]
  have hnv : ∀ w', InCone (c.take (u + 1)) w' →
      (c.take (u + 1)).getD w' (.cst false) ≠ CGate.var i := by
    intro w' hw' hg
    have hr := inCone_take_reach_g hu w' hw'
    have hw'lt : w' < u + 1 := by
      have := inCone_lt
        (show 0 < (c.take (u + 1)).length by rw [List.length_take]; omega) hw'
      rw [List.length_take] at this
      omega
    rw [getD_take_eq_g hw'lt] at hg
    exact hno w' hr hg
  rw [output_eq_wire, output_eq_wire]
  exact cone_wire_agree (c.take (u + 1)) i x b
    (by rw [List.length_take]; omega) hnv _ InCone.root

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.pair_mix_contra
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.swapG_blind_clean
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.wire_blind_of_no_gate_below
