import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCaseBKills

/-!
# Case (B) kills, part 2: the intra-gadget kill

If two variables of the *same* gadget are both bottlenecked at one wire and the
third variable has no gates below it, the third variable's two pins demand that
`a∧b` and `¬a∧¬b` share the one-bit mediator — impossible (`pin2_contra'`):

* `intraBase` / **`AEm_intra_eval` (proved)** — the same-gadget slice values;
* **`intra_gadget_kill` (proved)** — the kill.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- All-true except the third gadget variable pinned to `ε`. -/
def intraBase (m pth : ℕ) (ε : Bool) : Fin (3 * m) → Bool := fun j =>
  if j.val = pth then ε else true

theorem allEq3_ib1 (a b ε : Bool) :
    allEq3 a b ε = (if ε then a && b else (!a && !b)) := by
  cases a <;> cases b <;> cases ε <;> rfl

theorem allEq3_ib2 (a b ε : Bool) :
    allEq3 a ε b = (if ε then a && b else (!a && !b)) := by
  cases a <;> cases b <;> cases ε <;> rfl

theorem allEq3_ib3 (a b ε : Bool) :
    allEq3 ε a b = (if ε then a && b else (!a && !b)) := by
  cases a <;> cases b <;> cases ε <;> rfl

theorem allEq3_ib4 (a b ε : Bool) :
    allEq3 b a ε = (if ε then a && b else (!a && !b)) := by
  cases a <;> cases b <;> cases ε <;> rfl

theorem allEq3_ib5 (a b ε : Bool) :
    allEq3 b ε a = (if ε then a && b else (!a && !b)) := by
  cases a <;> cases b <;> cases ε <;> rfl

theorem allEq3_ib6 (a b ε : Bool) :
    allEq3 ε b a = (if ε then a && b else (!a && !b)) := by
  cases a <;> cases b <;> cases ε <;> rfl

/-- **The same-gadget slice evaluation (proved).** -/
theorem AEm_intra_eval (m pg pt pth : ℕ) (hpg : pg < 3 * m) (hpt : pt < 3 * m)
    (hpth : pth < 3 * m) (hg1 : pt / 3 = pg / 3) (hg2 : pth / 3 = pg / 3)
    (hne1 : pg ≠ pt) (hne2 : pg ≠ pth) (hne3 : pt ≠ pth) (ε a b : Bool) :
    AEm m (Function.update (Function.update (intraBase m pth ε)
      ⟨pg, hpg⟩ a) ⟨pt, hpt⟩ b)
      = (if ε then a && b else (!a && !b)) := by
  have hval : ∀ (t : ℕ) (ht : t < 3 * m),
      (Function.update (Function.update (intraBase m pth ε)
        ⟨pg, hpg⟩ a) ⟨pt, hpt⟩ b) ⟨t, ht⟩
      = if t = pt then b else if t = pg then a
        else if t = pth then ε else true := by
    intro t ht
    by_cases h1 : t = pt
    · rw [if_pos h1]
      have he : (⟨t, ht⟩ : Fin (3 * m)) = ⟨pt, hpt⟩ := Fin.ext h1
      rw [he, Function.update_self]
    · have hne1' : (⟨t, ht⟩ : Fin (3 * m)) ≠ ⟨pt, hpt⟩ :=
        fun he => h1 (congrArg Fin.val he)
      have e1 : (Function.update (Function.update (intraBase m pth ε)
          ⟨pg, hpg⟩ a) ⟨pt, hpt⟩ b) ⟨t, ht⟩
          = (Function.update (intraBase m pth ε) ⟨pg, hpg⟩ a) ⟨t, ht⟩ :=
        Function.update_of_ne hne1' b
          (Function.update (intraBase m pth ε) ⟨pg, hpg⟩ a)
      rw [if_neg h1, e1]
      by_cases h2 : t = pg
      · rw [if_pos h2]
        have he : (⟨t, ht⟩ : Fin (3 * m)) = ⟨pg, hpg⟩ := Fin.ext h2
        rw [he, Function.update_self]
      · have hne2' : (⟨t, ht⟩ : Fin (3 * m)) ≠ ⟨pg, hpg⟩ :=
          fun he => h2 (congrArg Fin.val he)
        have e2 : (Function.update (intraBase m pth ε) ⟨pg, hpg⟩ a) ⟨t, ht⟩
            = intraBase m pth ε ⟨t, ht⟩ :=
          Function.update_of_ne hne2' a (intraBase m pth ε)
        rw [if_neg h2, e2]
        rfl
  rw [AEm]
  have h3g : pg % 3 = 0 ∨ pg % 3 = 1 ∨ pg % 3 = 2 := by omega
  have h3t : pt % 3 = 0 ∨ pt % 3 = 1 ∨ pt % 3 = 2 := by omega
  cases hRHS : (if ε then a && b else (!a && !b))
  · refine Bool.eq_false_iff.mpr ?_
    intro hall
    rw [List.all_eq_true] at hall
    have hGm : pg / 3 < m := by omega
    have hgd := hall ⟨pg / 3, hGm⟩ (List.mem_finRange _)
    rw [hval, hval, hval] at hgd
    rw [show ((⟨pg / 3, hGm⟩ : Fin m) : ℕ) = pg / 3 from rfl] at hgd
    rcases h3g with hr1 | hr1 | hr1 <;> rcases h3t with hr2 | hr2 | hr2
    · exact absurd (show pg = pt by omega) hne1
    · rw [if_neg (by omega),
        if_pos (by omega),
        if_pos (by omega),
        if_neg (by omega),
        if_neg (by omega),
        if_pos (by omega)] at hgd
      rw [allEq3_ib1] at hgd
      rw [hRHS] at hgd
      exact absurd hgd (by decide)
    · rw [if_neg (by omega),
        if_pos (by omega),
        if_neg (by omega),
        if_neg (by omega),
        if_pos (by omega),
        if_pos (by omega)] at hgd
      rw [allEq3_ib2] at hgd
      rw [hRHS] at hgd
      exact absurd hgd (by decide)
    · rw [if_pos (by omega),
        if_neg (by omega),
        if_pos (by omega),
        if_neg (by omega),
        if_neg (by omega),
        if_pos (by omega)] at hgd
      rw [allEq3_ib4] at hgd
      rw [hRHS] at hgd
      exact absurd hgd (by decide)
    · exact absurd (show pg = pt by omega) hne1
    · rw [if_neg (by omega),
        if_neg (by omega),
        if_pos (by omega),
        if_neg (by omega),
        if_pos (by omega),
        if_pos (by omega)] at hgd
      rw [allEq3_ib3] at hgd
      rw [hRHS] at hgd
      exact absurd hgd (by decide)
    · rw [if_pos (by omega),
        if_neg (by omega),
        if_neg (by omega),
        if_pos (by omega),
        if_neg (by omega),
        if_pos (by omega)] at hgd
      rw [allEq3_ib5] at hgd
      rw [hRHS] at hgd
      exact absurd hgd (by decide)
    · rw [if_neg (by omega),
        if_neg (by omega),
        if_pos (by omega),
        if_pos (by omega),
        if_neg (by omega),
        if_pos (by omega)] at hgd
      rw [allEq3_ib6] at hgd
      rw [hRHS] at hgd
      exact absurd hgd (by decide)
    · exact absurd (show pg = pt by omega) hne1
  · rw [List.all_eq_true]
    intro j _
    by_cases hjG : (j : ℕ) = pg / 3
    · rw [hval, hval, hval]
      rcases h3g with hr1 | hr1 | hr1 <;> rcases h3t with hr2 | hr2 | hr2
      · exact absurd (show pg = pt by omega) hne1
      · rw [if_neg (by omega),
          if_pos (by omega),
          if_pos (by omega),
          if_neg (by omega),
          if_neg (by omega),
          if_pos (by omega)]
        rw [allEq3_ib1]
        exact hRHS
      · rw [if_neg (by omega),
          if_pos (by omega),
          if_neg (by omega),
          if_neg (by omega),
          if_pos (by omega),
          if_pos (by omega)]
        rw [allEq3_ib2]
        exact hRHS
      · rw [if_pos (by omega),
          if_neg (by omega),
          if_pos (by omega),
          if_neg (by omega),
          if_neg (by omega),
          if_pos (by omega)]
        rw [allEq3_ib4]
        exact hRHS
      · exact absurd (show pg = pt by omega) hne1
      · rw [if_neg (by omega),
          if_neg (by omega),
          if_pos (by omega),
          if_neg (by omega),
          if_pos (by omega),
          if_pos (by omega)]
        rw [allEq3_ib3]
        exact hRHS
      · rw [if_pos (by omega),
          if_neg (by omega),
          if_neg (by omega),
          if_pos (by omega),
          if_neg (by omega),
          if_pos (by omega)]
        rw [allEq3_ib5]
        exact hRHS
      · rw [if_neg (by omega),
          if_neg (by omega),
          if_pos (by omega),
          if_pos (by omega),
          if_neg (by omega),
          if_pos (by omega)]
        rw [allEq3_ib6]
        exact hRHS
      · exact absurd (show pg = pt by omega) hne1
    · rw [hval, hval, hval,
        if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rfl

/-- **THE INTRA-GADGET KILL (proved)**: two same-gadget variables bottlenecked at
one wire, third variable free of it — contradictory. -/
theorem intra_gadget_kill (m : ℕ) (c : List (CGate (3 * m)))
    (hcomp : computes c (AEm m)) (hs : 0 < c.length)
    (u : ℕ) (hu : u < c.length)
    (pg pt pth : ℕ) (hpg : pg < 3 * m) (hpt : pt < 3 * m) (hpth : pth < 3 * m)
    (hg1 : pt / 3 = pg / 3) (hg2 : pth / 3 = pg / 3)
    (hne1 : pg ≠ pt) (hne2 : pg ≠ pth) (hne3 : pt ≠ pth)
    (hsoleg : ∀ q, CleanIn c {u} q → q ≠ u →
      c.getD q (.cst false) ≠ CGate.var ⟨pg, hpg⟩)
    (hsolet : ∀ q, CleanIn c {u} q → q ≠ u →
      c.getD q (.cst false) ≠ CGate.var ⟨pt, hpt⟩)
    (hthird : ∀ q, Reach c u q →
      c.getD q (.cst false) ≠ CGate.var ⟨pth, hpth⟩) : False := by
  classical
  have hptF : (⟨pg, hpg⟩ : Fin (3 * m)) ≠ ⟨pt, hpt⟩ :=
    fun he => hne1 (congrArg Fin.val he)
  have hfact : ∀ (ε a b : Bool),
      (if ε then a && b else (!a && !b))
        = output (swapG c u (wire c (Function.update (Function.update
            (intraBase m pth true) ⟨pg, hpg⟩ a) ⟨pt, hpt⟩ b) u))
            (intraBase m pth ε) := by
    intro ε a b
    rw [← AEm_intra_eval m pg pt pth hpg hpt hpth hg1 hg2 hne1 hne2 hne3 ε a b,
      ← hcomp (Function.update (Function.update (intraBase m pth ε)
        ⟨pg, hpg⟩ a) ⟨pt, hpt⟩ b),
      ← output_swapG c hu (Function.update (Function.update
        (intraBase m pth ε) ⟨pg, hpg⟩ a) ⟨pt, hpt⟩ b)]
    have hGeq : wire c (Function.update (Function.update
        (intraBase m pth ε) ⟨pg, hpg⟩ a) ⟨pt, hpt⟩ b) u
        = wire c (Function.update (Function.update
        (intraBase m pth true) ⟨pg, hpg⟩ a) ⟨pt, hpt⟩ b) u := by
      refine eval_agree_of_blind (fun z => wire c z u)
        (fun j => j.val ≠ pth) ?_ _ _ ?_
      · intro j hj z b'
        rw [not_not] at hj
        refine wire_blind_of_no_gate_below c hu j ?_ z b'
        intro q hq
        have hjF : j = (⟨pth, hpth⟩ : Fin (3 * m)) := Fin.ext hj
        rw [hjF]
        exact hthird q hq
      · intro j hj
        by_cases hjp : j = (⟨pg, hpg⟩ : Fin (3 * m))
        · subst hjp
          rw [Function.update_of_ne hptF b (Function.update
              (intraBase m pth ε) ⟨pg, hpg⟩ a),
            Function.update_of_ne hptF b (Function.update
              (intraBase m pth true) ⟨pg, hpg⟩ a),
            Function.update_self, Function.update_self]
        · by_cases hjq : j = (⟨pt, hpt⟩ : Fin (3 * m))
          · subst hjq
            rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hjq b (Function.update
                (intraBase m pth ε) ⟨pg, hpg⟩ a),
              Function.update_of_ne hjq b (Function.update
                (intraBase m pth true) ⟨pg, hpg⟩ a),
              Function.update_of_ne hjp a (intraBase m pth ε),
              Function.update_of_ne hjp a (intraBase m pth true)]
            show (if j.val = pth then ε else true)
              = (if j.val = pth then true else true)
            rw [if_neg hj, if_neg hj]
    rw [hGeq]
    exact eval_agree_of_blind
      (output (swapG c u (wire c (Function.update (Function.update
        (intraBase m pth true) ⟨pg, hpg⟩ a) ⟨pt, hpt⟩ b) u)))
      (fun j => j ≠ (⟨pg, hpg⟩ : Fin (3 * m)) ∧ j ≠ (⟨pt, hpt⟩ : Fin (3 * m)))
      (fun j hj z b' => by
        rw [not_and_or, not_not, not_not] at hj
        rcases hj with hj | hj
        · subst hj
          exact swapG_blind_clean c hs hu _ _ hsoleg z b'
        · subst hj
          exact swapG_blind_clean c hs hu _ _ hsolet z b')
      _ _ (fun j hj => by
        obtain ⟨hj1, hj2⟩ := hj
        rw [Function.update_of_ne hj2 b (Function.update
            (intraBase m pth ε) ⟨pg, hpg⟩ a),
          Function.update_of_ne hj1 a (intraBase m pth ε)])
  exact pin2_contra'
    (fun a b => wire c (Function.update (Function.update
      (intraBase m pth true) ⟨pg, hpg⟩ a) ⟨pt, hpt⟩ b) u)
    (fun w => output (swapG c u w) (intraBase m pth true))
    (fun w => output (swapG c u w) (intraBase m pth false))
    ⟨fun a b => hfact true a b, fun a b => hfact false a b⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.AEm_intra_eval
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.intra_gadget_kill
