import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPairMixCore

/-!
# The pair-mix kill, part 2: no wire bottlenecks two gadgets

The circuit-level four-completion kill:

* `pairBase` / **`AEm_pair_eval` (proved)** — the two-gadget slice values: with
  gadget `pg/3` pinned to `εg` off `pg` and gadget `ph/3` pinned to `εh` off
  `ph` (everything else true), `AEm m` evaluates to the signed conjunction;
* **`first_branch_pair_kill` (proved)** — a wire `u` that carries *all* the
  influence of chosen variables from two different gadgets (every `{u}`-clean
  path misses their gates off `u`), with all four partner variables having no
  gates below `u`, is contradictory: the four sign completions share the same
  one-bit mediator `wire u`, and `pair_mix_contra` closes.

This is the (A)-case of the missing ∀m lemma (`φ`-injectivity for first-branch
bottlenecks).  The (B)-case — a partner variable with a gate below the shared
bottleneck — remains open.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- Both gadgets pinned to their signs off the chosen positions, rest true. -/
def pairBase (m pg ph : ℕ) (εg εh : Bool) : Fin (3 * m) → Bool := fun j =>
  if j.val / 3 = pg / 3 ∧ j.val ≠ pg then εg
  else if j.val / 3 = ph / 3 ∧ j.val ≠ ph then εh
  else true

theorem allEq3_pin2_a (v ε : Bool) : allEq3 v ε ε = (if ε then v else !v) := by
  cases v <;> cases ε <;> rfl

theorem allEq3_pin2_b (v ε : Bool) : allEq3 ε v ε = (if ε then v else !v) := by
  cases v <;> cases ε <;> rfl

theorem allEq3_pin2_c (v ε : Bool) : allEq3 ε ε v = (if ε then v else !v) := by
  cases v <;> cases ε <;> rfl

/-- **The two-gadget slice evaluation (proved).** -/
theorem AEm_pair_eval (m pg ph : ℕ) (hpg : pg < 3 * m) (hph : ph < 3 * m)
    (hgh : pg / 3 ≠ ph / 3) (εg εh a b : Bool) :
    AEm m (Function.update (Function.update (pairBase m pg ph εg εh)
      ⟨pg, hpg⟩ a) ⟨ph, hph⟩ b)
      = ((if εg then a else !a) && (if εh then b else !b)) := by
  have hpgh : pg ≠ ph := fun he => hgh (by rw [he])
  have hval : ∀ (t : ℕ) (ht : t < 3 * m),
      (Function.update (Function.update (pairBase m pg ph εg εh)
        ⟨pg, hpg⟩ a) ⟨ph, hph⟩ b) ⟨t, ht⟩
      = if t = ph then b else if t = pg then a
        else if t / 3 = pg / 3 ∧ t ≠ pg then εg
        else if t / 3 = ph / 3 ∧ t ≠ ph then εh else true := by
    intro t ht
    by_cases h1 : t = ph
    · rw [if_pos h1]
      have he : (⟨t, ht⟩ : Fin (3 * m)) = ⟨ph, hph⟩ := Fin.ext h1
      rw [he, Function.update_self]
    · have hne1 : (⟨t, ht⟩ : Fin (3 * m)) ≠ ⟨ph, hph⟩ :=
        fun he => h1 (congrArg Fin.val he)
      have e1 : (Function.update (Function.update (pairBase m pg ph εg εh)
          ⟨pg, hpg⟩ a) ⟨ph, hph⟩ b) ⟨t, ht⟩
          = (Function.update (pairBase m pg ph εg εh) ⟨pg, hpg⟩ a) ⟨t, ht⟩ :=
        Function.update_of_ne hne1 b
          (Function.update (pairBase m pg ph εg εh) ⟨pg, hpg⟩ a)
      rw [if_neg h1, e1]
      by_cases h2 : t = pg
      · rw [if_pos h2]
        have he : (⟨t, ht⟩ : Fin (3 * m)) = ⟨pg, hpg⟩ := Fin.ext h2
        rw [he, Function.update_self]
      · have hne2 : (⟨t, ht⟩ : Fin (3 * m)) ≠ ⟨pg, hpg⟩ :=
          fun he => h2 (congrArg Fin.val he)
        have e2 : (Function.update (pairBase m pg ph εg εh) ⟨pg, hpg⟩ a) ⟨t, ht⟩
            = pairBase m pg ph εg εh ⟨t, ht⟩ :=
          Function.update_of_ne hne2 a (pairBase m pg ph εg εh)
        rw [if_neg h2, e2]
        rfl
  rw [AEm]
  cases hRHS : ((if εg then a else !a) && (if εh then b else !b))
  · refine Bool.eq_false_iff.mpr ?_
    intro hall
    rw [List.all_eq_true] at hall
    rcases Bool.eq_false_or_eq_true (if εg then a else !a) with htg | hfg
    · have hfh : (if εh then b else !b) = false := by
        rw [htg, Bool.true_and] at hRHS
        exact hRHS
      have hHm : ph / 3 < m := by omega
      have hgd := hall ⟨ph / 3, hHm⟩ (List.mem_finRange _)
      rw [hval, hval, hval] at hgd
      rw [show ((⟨ph / 3, hHm⟩ : Fin m) : ℕ) = ph / 3 from rfl] at hgd
      have hr3 : ph % 3 = 0 ∨ ph % 3 = 1 ∨ ph % 3 = 2 := by omega
      rcases hr3 with hr | hr | hr
      · rw [if_pos (by omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_pos ⟨by omega, by omega⟩,
          if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_pos ⟨by omega, by omega⟩] at hgd
        rw [allEq3_pin2_a, hfh] at hgd
        exact absurd hgd (by decide)
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_pos ⟨by omega, by omega⟩,
          if_pos (by omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_pos ⟨by omega, by omega⟩] at hgd
        rw [allEq3_pin2_b, hfh] at hgd
        exact absurd hgd (by decide)
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_pos ⟨by omega, by omega⟩,
          if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_pos ⟨by omega, by omega⟩,
          if_pos (by omega)] at hgd
        rw [allEq3_pin2_c, hfh] at hgd
        exact absurd hgd (by decide)
    · have hGm : pg / 3 < m := by omega
      have hgd := hall ⟨pg / 3, hGm⟩ (List.mem_finRange _)
      rw [hval, hval, hval] at hgd
      rw [show ((⟨pg / 3, hGm⟩ : Fin m) : ℕ) = pg / 3 from rfl] at hgd
      have hr3 : pg % 3 = 0 ∨ pg % 3 = 1 ∨ pg % 3 = 2 := by omega
      rcases hr3 with hr | hr | hr
      · rw [if_neg (by omega), if_pos (by omega),
          if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩,
          if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩] at hgd
        rw [allEq3_pin2_a, hfg] at hgd
        exact absurd hgd (by decide)
      · rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩,
          if_neg (by omega), if_pos (by omega),
          if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩] at hgd
        rw [allEq3_pin2_b, hfg] at hgd
        exact absurd hgd (by decide)
      · rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩,
          if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩,
          if_neg (by omega), if_pos (by omega)] at hgd
        rw [allEq3_pin2_c, hfg] at hgd
        exact absurd hgd (by decide)
  · rw [List.all_eq_true]
    intro j _
    have hg1 : (if εg then a else !a) = true := by
      cases hgv : (if εg then a else !a)
      · rw [hgv, Bool.false_and] at hRHS
        exact absurd hRHS (by decide)
      · rfl
    have hh1 : (if εh then b else !b) = true := by
      cases hhv : (if εh then b else !b)
      · rw [hhv, Bool.and_false] at hRHS
        exact absurd hRHS (by decide)
      · rfl
    by_cases hjG : (j : ℕ) = pg / 3
    · rw [hval, hval, hval]
      have hr3 : pg % 3 = 0 ∨ pg % 3 = 1 ∨ pg % 3 = 2 := by omega
      rcases hr3 with hr | hr | hr
      · rw [if_neg (by omega), if_pos (by omega),
          if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩,
          if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩]
        rw [allEq3_pin2_a]
        exact hg1
      · rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩,
          if_neg (by omega), if_pos (by omega),
          if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩]
        rw [allEq3_pin2_b]
        exact hg1
      · rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩,
          if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩,
          if_neg (by omega), if_pos (by omega)]
        rw [allEq3_pin2_c]
        exact hg1
    · by_cases hjH : (j : ℕ) = ph / 3
      · rw [hval, hval, hval]
        have hr3 : ph % 3 = 0 ∨ ph % 3 = 1 ∨ ph % 3 = 2 := by omega
        rcases hr3 with hr | hr | hr
        · rw [if_pos (by omega),
            if_neg (by omega), if_neg (by omega), if_neg (by omega),
              if_pos ⟨by omega, by omega⟩,
            if_neg (by omega), if_neg (by omega), if_neg (by omega),
              if_pos ⟨by omega, by omega⟩]
          rw [allEq3_pin2_a]
          exact hh1
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
              if_pos ⟨by omega, by omega⟩,
            if_pos (by omega),
            if_neg (by omega), if_neg (by omega), if_neg (by omega),
              if_pos ⟨by omega, by omega⟩]
          rw [allEq3_pin2_b]
          exact hh1
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
              if_pos ⟨by omega, by omega⟩,
            if_neg (by omega), if_neg (by omega), if_neg (by omega),
              if_pos ⟨by omega, by omega⟩,
            if_pos (by omega)]
          rw [allEq3_pin2_c]
          exact hh1
      · rw [hval, hval, hval,
          if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_neg (by omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_neg (by omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_neg (by omega)]
        rfl

/-- **THE FIRST-BRANCH PAIR-KILL (proved)**: no wire can carry all the influence
of chosen variables from two different gadgets while their partner variables
stay outside its cone. -/
theorem first_branch_pair_kill (m : ℕ) (c : List (CGate (3 * m)))
    (hcomp : computes c (AEm m)) (hs : 0 < c.length)
    (u : ℕ) (hu : u < c.length)
    (pg ph : ℕ) (hpg : pg < 3 * m) (hph : ph < 3 * m) (hgh : pg / 3 ≠ ph / 3)
    (hsoleg : ∀ q, CleanIn c {u} q → q ≠ u →
      c.getD q (.cst false) ≠ CGate.var ⟨pg, hpg⟩)
    (hsoleh : ∀ q, CleanIn c {u} q → q ≠ u →
      c.getD q (.cst false) ≠ CGate.var ⟨ph, hph⟩)
    (hpart : ∀ (t : ℕ) (ht : t < 3 * m),
      (t / 3 = pg / 3 ∨ t / 3 = ph / 3) → t ≠ pg → t ≠ ph →
      ∀ q, Reach c u q → c.getD q (.cst false) ≠ CGate.var ⟨t, ht⟩) : False := by
  classical
  have hpgh : pg ≠ ph := fun he => hgh (by rw [he])
  have hpghF : (⟨pg, hpg⟩ : Fin (3 * m)) ≠ ⟨ph, hph⟩ :=
    fun he => hpgh (congrArg Fin.val he)
  have hfact : ∀ (εg εh a b : Bool),
      ((if εg then a else !a) && (if εh then b else !b))
        = output (swapG c u (wire c (Function.update (Function.update
            (pairBase m pg ph true true) ⟨pg, hpg⟩ a) ⟨ph, hph⟩ b) u))
            (pairBase m pg ph εg εh) := by
    intro εg εh a b
    rw [← AEm_pair_eval m pg ph hpg hph hgh εg εh a b,
      ← hcomp (Function.update (Function.update (pairBase m pg ph εg εh)
        ⟨pg, hpg⟩ a) ⟨ph, hph⟩ b),
      ← output_swapG c hu (Function.update (Function.update
        (pairBase m pg ph εg εh) ⟨pg, hpg⟩ a) ⟨ph, hph⟩ b)]
    have hGeq : wire c (Function.update (Function.update
        (pairBase m pg ph εg εh) ⟨pg, hpg⟩ a) ⟨ph, hph⟩ b) u
        = wire c (Function.update (Function.update
        (pairBase m pg ph true true) ⟨pg, hpg⟩ a) ⟨ph, hph⟩ b) u := by
      refine eval_agree_of_blind (fun z => wire c z u)
        (fun j => ¬((j.val / 3 = pg / 3 ∨ j.val / 3 = ph / 3)
          ∧ j.val ≠ pg ∧ j.val ≠ ph)) ?_ _ _ ?_
      · intro j hj z b'
        rw [not_not] at hj
        obtain ⟨hor, hnp, hnq⟩ := hj
        refine wire_blind_of_no_gate_below c hu j ?_ z b'
        intro q hq
        exact hpart j.val j.isLt hor hnp hnq q hq
      · intro j hj
        by_cases hjp : j = (⟨pg, hpg⟩ : Fin (3 * m))
        · subst hjp
          rw [Function.update_of_ne hpghF b (Function.update
              (pairBase m pg ph εg εh) ⟨pg, hpg⟩ a),
            Function.update_of_ne hpghF b (Function.update
              (pairBase m pg ph true true) ⟨pg, hpg⟩ a),
            Function.update_self, Function.update_self]
        · by_cases hjq : j = (⟨ph, hph⟩ : Fin (3 * m))
          · subst hjq
            rw [Function.update_self, Function.update_self]
          · have hvp : j.val ≠ pg := fun he => hjp (Fin.ext he)
            have hvq : j.val ≠ ph := fun he => hjq (Fin.ext he)
            have hnor : ¬(j.val / 3 = pg / 3 ∨ j.val / 3 = ph / 3) := by
              intro hor
              exact hj ⟨hor, hvp, hvq⟩
            rw [Function.update_of_ne hjq b (Function.update
                (pairBase m pg ph εg εh) ⟨pg, hpg⟩ a),
              Function.update_of_ne hjq b (Function.update
                (pairBase m pg ph true true) ⟨pg, hpg⟩ a),
              Function.update_of_ne hjp a (pairBase m pg ph εg εh),
              Function.update_of_ne hjp a (pairBase m pg ph true true)]
            show (if j.val / 3 = pg / 3 ∧ j.val ≠ pg then εg
              else if j.val / 3 = ph / 3 ∧ j.val ≠ ph then εh else true)
              = (if j.val / 3 = pg / 3 ∧ j.val ≠ pg then true
              else if j.val / 3 = ph / 3 ∧ j.val ≠ ph then true else true)
            rw [if_neg (fun hc => hnor (Or.inl hc.1)),
              if_neg (fun hc => hnor (Or.inr hc.1)),
              if_neg (fun hc => hnor (Or.inl hc.1)),
              if_neg (fun hc => hnor (Or.inr hc.1))]
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
            (pairBase m pg ph εg εh) ⟨pg, hpg⟩ a),
          Function.update_of_ne hj1 a (pairBase m pg ph εg εh)])
  exact pair_mix_contra
    (fun a b => wire c (Function.update (Function.update
      (pairBase m pg ph true true) ⟨pg, hpg⟩ a) ⟨ph, hph⟩ b) u)
    (fun w => output (swapG c u w) (pairBase m pg ph true true))
    (fun w => output (swapG c u w) (pairBase m pg ph false true))
    (fun w => output (swapG c u w) (pairBase m pg ph true false))
    (fun w => output (swapG c u w) (pairBase m pg ph false false))
    ⟨fun a b => hfact true true a b,
     fun a b => hfact false true a b,
     fun a b => hfact true false a b,
     fun a b => hfact false false a b⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.AEm_pair_eval
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.first_branch_pair_kill
