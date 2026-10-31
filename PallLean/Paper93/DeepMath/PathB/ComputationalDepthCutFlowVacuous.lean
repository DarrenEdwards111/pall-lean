import PallLean.Paper93.DeepMath.PathB.ComputationalDepthChargedGateLanguage

/-!
# Step (4), item 6: cut-flow candidates tested — the unpinned version is VACUOUS

The audit left cut-communication / congestion / layout-movement measures as the open corner of the invariant
design space.  This file runs the first test and it is decisive for the **unpinned** family: define the cut flow
of a program as the number of gates straddling a wire bipartition; then **every** program has a semantics- and
cost-preserving equivalent together with a perfectly balanced cut of flow ZERO (`cutflow_vacuous`) — embed the
program in the low half of `w + w` wires and cut between the halves.  A measure minimized over equivalent
programs/layouts (as gauge/layout invariance demands) is therefore identically zero: **unpinned cut-flow cannot
be a hardness measure.**

The structural reason, and what remains: unlike VLSI lower bounds, nothing pins input ports to locations — inputs
are re-readable on any wire, so computation localizes to one side.  The surviving candidates are **pinned-port**
models: (a) pinned ports + a single cut caps at `n` (one crossing can carry at most... the information across the
cut is bounded by log-rank `≤ n` — the static cap again); (b) pinned ports + **bounded width** forces repeated
crossings and leads into time–space tradeoff theory (Borodin–Cook style `T·S` bounds) — genuine, *restricted*,
known territory, not a separation route.  Tests against the calibrations: `qfProg A` trivially passes (flow `0`
after localization — polynomial ✓) and the measure is not clock-equivalent (it is zero) — it passes every law by
being dead, the `Inv ≡ 0` phenomenon made concrete.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CutFlow

open PallLean.Paper93.DeepMath.PathB.ChargedGate

variable {n w : ℕ}

/-- A gate straddles a wire bipartition if its target is on a different side from an operand.  (Input gates read
no wire, so they never straddle.) -/
def crossing (side : Fin w → Bool) : Gate n w → Bool
  | .input _ _ => false
  | .notg a t => side a != side t
  | .andg a b t => (side a != side t) || (side b != side t)
  | .xorg a b t => (side a != side t) || (side b != side t)

/-- Embed a gate into the low half of `w + w` wires. -/
def castGate : Gate n w → Gate n (w + w)
  | .input i t => .input i (Fin.castAdd w t)
  | .notg a t => .notg (Fin.castAdd w a) (Fin.castAdd w t)
  | .andg a b t => .andg (Fin.castAdd w a) (Fin.castAdd w b) (Fin.castAdd w t)
  | .xorg a b t => .xorg (Fin.castAdd w a) (Fin.castAdd w b) (Fin.castAdd w t)

/-- The localized program: same gates, low half of a doubled wire set. -/
def embProg (P : Prog n w) : Prog n (w + w) := ⟨P.gates.map castGate, Fin.castAdd w P.out⟩

/-- The low half mirrors the original state. -/
def Rel2 (S : Fin (w + w) → Bool) (s : Fin w → Bool) : Prop :=
  ∀ j : Fin w, S (Fin.castAdd w j) = s j

theorem castAdd_inj : Function.Injective (Fin.castAdd (n := w) w) := by
  intro a b hab
  exact Fin.ext (by simpa [Fin.castAdd] using congrArg Fin.val hab)

theorem rel2_step (z : Fin n → Bool) (S : Fin (w + w) → Bool) (s : Fin w → Bool) (g : Gate n w)
    (hRel : Rel2 S s) : Rel2 (step z S (castGate g)) (step z s g) := by
  cases g with
  | input i t =>
    intro j
    show (Function.update S (Fin.castAdd w t) (z i)) (Fin.castAdd w j)
        = (Function.update s t (z i)) j
    by_cases hjt : j = t
    · subst hjt; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun hc => hjt (castAdd_inj hc)), Function.update_of_ne hjt,
        hRel j]
  | notg a t =>
    intro j
    show (Function.update S (Fin.castAdd w t) (! S (Fin.castAdd w a))) (Fin.castAdd w j)
        = (Function.update s t (! s a)) j
    by_cases hjt : j = t
    · subst hjt; rw [Function.update_self, Function.update_self, hRel a]
    · rw [Function.update_of_ne (fun hc => hjt (castAdd_inj hc)), Function.update_of_ne hjt,
        hRel j]
  | andg a b t =>
    intro j
    show (Function.update S (Fin.castAdd w t) (S (Fin.castAdd w a) && S (Fin.castAdd w b)))
        (Fin.castAdd w j) = (Function.update s t (s a && s b)) j
    by_cases hjt : j = t
    · subst hjt; rw [Function.update_self, Function.update_self, hRel a, hRel b]
    · rw [Function.update_of_ne (fun hc => hjt (castAdd_inj hc)), Function.update_of_ne hjt,
        hRel j]
  | xorg a b t =>
    intro j
    show (Function.update S (Fin.castAdd w t) (xor (S (Fin.castAdd w a)) (S (Fin.castAdd w b))))
        (Fin.castAdd w j) = (Function.update s t (xor (s a) (s b))) j
    by_cases hjt : j = t
    · subst hjt; rw [Function.update_self, Function.update_self, hRel a, hRel b]
    · rw [Function.update_of_ne (fun hc => hjt (castAdd_inj hc)), Function.update_of_ne hjt,
        hRel j]

theorem rel2_fold (z : Fin n → Bool) (gs : List (Gate n w)) :
    ∀ (S : Fin (w + w) → Bool) (s : Fin w → Bool), Rel2 S s →
      Rel2 (runGates z (gs.map castGate) S) (runGates z gs s) := by
  induction gs with
  | nil => intro S s h; exact h
  | cons g gs ih =>
    intro S s h
    exact ih _ _ (rel2_step z S s g h)

/-- **Localization preserves semantics** (and, definitionally, cost). -/
theorem embProg_run (P : Prog n w) (z : Fin n → Bool) : (embProg P).run z = P.run z :=
  rel2_fold z P.gates (fun _ => false) (fun _ => false) (fun _ => rfl) P.out

theorem embProg_cost (P : Prog n w) : (embProg P).cost = P.cost := List.length_map ..

/-- The balanced cut between the halves. -/
def halfSide : Fin (w + w) → Bool := fun j => decide (j.val < w)

theorem halfSide_low (j : Fin w) : halfSide (Fin.castAdd (n := w) w j) = true :=
  decide_eq_true j.isLt

/-- **No gate of the localized program crosses the half cut.** -/
theorem embProg_no_crossing (P : Prog n w) :
    ∀ g ∈ (embProg P).gates, crossing halfSide g = false := by
  intro g hg
  obtain ⟨g0, _, rfl⟩ := List.mem_map.mp hg
  cases g0 with
  | input i t => rfl
  | notg a t =>
    show (halfSide (Fin.castAdd w a) != halfSide (Fin.castAdd w t)) = false
    rw [halfSide_low, halfSide_low]
    rfl
  | andg a b t =>
    show ((halfSide (Fin.castAdd w a) != halfSide (Fin.castAdd w t))
        || (halfSide (Fin.castAdd w b) != halfSide (Fin.castAdd w t))) = false
    rw [halfSide_low, halfSide_low, halfSide_low]
    rfl
  | xorg a b t =>
    show ((halfSide (Fin.castAdd w a) != halfSide (Fin.castAdd w t))
        || (halfSide (Fin.castAdd w b) != halfSide (Fin.castAdd w t))) = false
    rw [halfSide_low, halfSide_low, halfSide_low]
    rfl

/-- The cut is perfectly balanced. -/
theorem halfSide_balanced :
    (Finset.univ.filter (fun j : Fin (w + w) => halfSide j = true)).card = w := by
  classical
  have himg : (Finset.univ.filter (fun j : Fin (w + w) => halfSide j = true))
      = Finset.univ.image (Fin.castAdd (n := w) w) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hj
      have hlt : j.val < w := of_decide_eq_true hj
      exact ⟨⟨j.val, hlt⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact halfSide_low a
  rw [himg, Finset.card_image_of_injective _ castAdd_inj, Finset.card_univ, Fintype.card_fin]

/-- **Unpinned cut-flow is vacuous.**  Every charged program has a semantics- and cost-preserving equivalent with
a perfectly balanced wire cut that NO gate crosses.  Any layout-minimized cut-flow measure is identically zero. -/
theorem cutflow_vacuous (P : Prog n w) :
    ∃ (P' : Prog n (w + w)) (side : Fin (w + w) → Bool),
      (∀ z, P'.run z = P.run z)
      ∧ P'.cost = P.cost
      ∧ (Finset.univ.filter (fun j => side j = true)).card = w
      ∧ ∀ g ∈ P'.gates, crossing side g = false :=
  ⟨embProg P, halfSide, embProg_run P, embProg_cost P, halfSide_balanced,
    embProg_no_crossing P⟩

end PallLean.Paper93.DeepMath.PathB.CutFlow

#print axioms PallLean.Paper93.DeepMath.PathB.CutFlow.cutflow_vacuous
