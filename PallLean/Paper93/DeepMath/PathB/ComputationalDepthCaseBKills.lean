import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPairKill

/-!
# Case (B) kills: the one-sided pair kill

Attacking case (B) of the ∀m gap.  The four-completion pair kill needed both
gadgets' partners outside the shared bottleneck.  Two completions on a *single*
side already force three distinct values of a Boolean function:

* **`pin2_contra` (proved, decidable)** — no `op : Bool → Bool → Bool` admits
  unary factorizations of both `a∧b` and `a∧¬b`: `op` would have to separate
  `(1,1)` and `(1,0)` from everything, three distinct Booleans;
* **`one_side_pair_kill` (proved)** — a wire `u` that carries all the influence
  of chosen variables from two different gadgets is contradictory as soon as
  *one* of the two gadgets has both partners without gates below `u`.  The
  other gadget's partners may be arbitrarily entangled with `u`: their pins are
  frozen across the two completions, so they never move the mediator.

This strictly subsumes `first_branch_pair_kill` and shrinks case (B) to: *both*
gadgets have a partner below the shared wire.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- **The two-completion contradiction (proved by decision).** -/
theorem pin2_contra (op : Bool → Bool → Bool) (U₁ U₂ : Bool → Bool) :
    ¬ ((∀ a b, (a && b) = U₁ (op a b)) ∧ (∀ a b, (a && !b) = U₂ (op a b))) := by
  revert op U₁ U₂
  decide

/-- The intra-gadget variant: `a∧b` and `¬a∧¬b` cannot share a mediator. -/
theorem pin2_contra' (op : Bool → Bool → Bool) (U₁ U₂ : Bool → Bool) :
    ¬ ((∀ a b, (a && b) = U₁ (op a b)) ∧ (∀ a b, (!a && !b) = U₂ (op a b))) := by
  revert op U₁ U₂
  decide

/-- **THE ONE-SIDED PAIR KILL (proved)**: a wire bottlenecking chosen variables
of two gadgets dies as soon as one gadget's partners are free of it. -/
theorem one_side_pair_kill (m : ℕ) (c : List (CGate (3 * m)))
    (hcomp : computes c (AEm m)) (hs : 0 < c.length)
    (u : ℕ) (hu : u < c.length)
    (pg ph : ℕ) (hpg : pg < 3 * m) (hph : ph < 3 * m) (hgh : pg / 3 ≠ ph / 3)
    (hsoleg : ∀ q, CleanIn c {u} q → q ≠ u →
      c.getD q (.cst false) ≠ CGate.var ⟨pg, hpg⟩)
    (hsoleh : ∀ q, CleanIn c {u} q → q ≠ u →
      c.getD q (.cst false) ≠ CGate.var ⟨ph, hph⟩)
    (hpartH : ∀ (t : ℕ) (ht : t < 3 * m), t / 3 = ph / 3 → t ≠ ph →
      ∀ q, Reach c u q → c.getD q (.cst false) ≠ CGate.var ⟨t, ht⟩) : False := by
  classical
  have hpgh : pg ≠ ph := fun he => hgh (by rw [he])
  have hpghF : (⟨pg, hpg⟩ : Fin (3 * m)) ≠ ⟨ph, hph⟩ :=
    fun he => hpgh (congrArg Fin.val he)
  have hfact : ∀ (εh a b : Bool),
      ((if true then a else !a) && (if εh then b else !b))
        = output (swapG c u (wire c (Function.update (Function.update
            (pairBase m pg ph true true) ⟨pg, hpg⟩ a) ⟨ph, hph⟩ b) u))
            (pairBase m pg ph true εh) := by
    intro εh a b
    rw [← AEm_pair_eval m pg ph hpg hph hgh true εh a b,
      ← hcomp (Function.update (Function.update (pairBase m pg ph true εh)
        ⟨pg, hpg⟩ a) ⟨ph, hph⟩ b),
      ← output_swapG c hu (Function.update (Function.update
        (pairBase m pg ph true εh) ⟨pg, hpg⟩ a) ⟨ph, hph⟩ b)]
    have hGeq : wire c (Function.update (Function.update
        (pairBase m pg ph true εh) ⟨pg, hpg⟩ a) ⟨ph, hph⟩ b) u
        = wire c (Function.update (Function.update
        (pairBase m pg ph true true) ⟨pg, hpg⟩ a) ⟨ph, hph⟩ b) u := by
      refine eval_agree_of_blind (fun z => wire c z u)
        (fun j => ¬(j.val / 3 = ph / 3 ∧ j.val ≠ ph)) ?_ _ _ ?_
      · intro j hj z b'
        rw [not_not] at hj
        obtain ⟨hd, hnp⟩ := hj
        refine wire_blind_of_no_gate_below c hu j ?_ z b'
        intro q hq
        exact hpartH j.val j.isLt hd hnp q hq
      · intro j hj
        by_cases hjp : j = (⟨pg, hpg⟩ : Fin (3 * m))
        · subst hjp
          rw [Function.update_of_ne hpghF b (Function.update
              (pairBase m pg ph true εh) ⟨pg, hpg⟩ a),
            Function.update_of_ne hpghF b (Function.update
              (pairBase m pg ph true true) ⟨pg, hpg⟩ a),
            Function.update_self, Function.update_self]
        · by_cases hjq : j = (⟨ph, hph⟩ : Fin (3 * m))
          · subst hjq
            rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hjq b (Function.update
                (pairBase m pg ph true εh) ⟨pg, hpg⟩ a),
              Function.update_of_ne hjq b (Function.update
                (pairBase m pg ph true true) ⟨pg, hpg⟩ a),
              Function.update_of_ne hjp a (pairBase m pg ph true εh),
              Function.update_of_ne hjp a (pairBase m pg ph true true)]
            show (if j.val / 3 = pg / 3 ∧ j.val ≠ pg then true
              else if j.val / 3 = ph / 3 ∧ j.val ≠ ph then εh else true)
              = (if j.val / 3 = pg / 3 ∧ j.val ≠ pg then true
              else if j.val / 3 = ph / 3 ∧ j.val ≠ ph then true else true)
            by_cases hA : (j.val / 3 = pg / 3 ∧ j.val ≠ pg)
            · rw [if_pos hA, if_pos hA]
            · rw [if_neg hA, if_neg hA, if_neg hj, if_neg hj]
    rw [hGeq]
    exact eval_agree_of_blind
      (output (swapG c u (wire c (Function.update (Function.update
        (pairBase m pg ph true true) ⟨pg, hpg⟩ a) ⟨ph, hph⟩ b) u)))
      (fun j => j ≠ (⟨pg, hpg⟩ : Fin (3 * m)) ∧ j ≠ (⟨ph, hph⟩ : Fin (3 * m)))
      (fun j hj z b' => by
        rw [not_and_or, not_not, not_not] at hj
        rcases hj with hj | hj
        · subst hj
          exact swapG_blind_clean c hs hu _ _ hsoleg z b'
        · subst hj
          exact swapG_blind_clean c hs hu _ _ hsoleh z b')
      _ _ (fun j hj => by
        obtain ⟨hj1, hj2⟩ := hj
        rw [Function.update_of_ne hj2 b (Function.update
            (pairBase m pg ph true εh) ⟨pg, hpg⟩ a),
          Function.update_of_ne hj1 a (pairBase m pg ph true εh)])
  exact pin2_contra
    (fun a b => wire c (Function.update (Function.update
      (pairBase m pg ph true true) ⟨pg, hpg⟩ a) ⟨ph, hph⟩ b) u)
    (fun w => output (swapG c u w) (pairBase m pg ph true true))
    (fun w => output (swapG c u w) (pairBase m pg ph true false))
    ⟨fun a b => hfact true a b, fun a b => hfact false a b⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.pin2_contra
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.one_side_pair_kill
