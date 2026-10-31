import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMTwoGadgetKill

/-!
# Brick 4b of the `SlackComposes` m = 2 attack: the shared-wire mediation

The one-bit mediation: swapping the shared wire `s` for the constant it carries
leaves the output unchanged (`output_swapC`), the swapped circuit is blind to
every variable inside the shared subtree (`swapC_blind`), and the shared wire
itself is blind to every variable outside it (`wire_s_blind`).  A generic
agreement lemma (`eval_agree_of_blind`) turns pointwise blindness into
agreement on whole assignments.  Together: `AEm 2` depends on the shared
subtree's variables only through the single bit `wire s`.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-! ### The swap -/

/-- The circuit with the shared wire replaced by a constant. -/
def swapC (c : List (CGate (3 * 2))) (s : ℕ) (w : Bool) : List (CGate (3 * 2)) :=
  c.take s ++ CGate.cst w :: c.drop (s + 1)

theorem swapC_length (c : List (CGate (3 * 2))) (s : ℕ) (w : Bool)
    (hs : s < c.length) : (swapC c s w).length = c.length := by
  rw [swapC]
  simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]
  omega

theorem swapC_getD_self {c : List (CGate (3 * 2))} {s : ℕ} (hs : s < c.length)
    (w : Bool) : (swapC c s w).getD s (.cst false) = CGate.cst w := by
  rw [swapC, List.getD_append_right _ _ (CGate.cst false) s
    (by rw [List.length_take]; omega),
    show s - (c.take s).length = 0 from by rw [List.length_take]; omega]
  rfl

theorem swapC_getD_ne {c : List (CGate (3 * 2))} {s : ℕ} (hs : s < c.length)
    (w : Bool) {q : ℕ} (hq : q ≠ s) :
    (swapC c s w).getD q (.cst false) = c.getD q (.cst false) := by
  rcases Nat.lt_or_ge q s with h | h
  · rw [swapC, List.getD_append _ _ (CGate.cst false) q
      (by rw [List.length_take]; omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt h]
  · have h' : s < q := by omega
    rw [swapC, List.getD_append_right _ _ (CGate.cst false) q
      (by rw [List.length_take]; omega),
      show q - (c.take s).length = (q - s - 1) + 1 from by rw [List.length_take]; omega]
    show (c.drop (s + 1)).getD (q - s - 1) (.cst false) = c.getD q (.cst false)
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
      show s + 1 + (q - s - 1) = q from by omega]

/-- **The mediation identity (proved)**: swapping the shared wire for the value it
carries leaves the output unchanged. -/
theorem output_swapC (c : List (CGate (3 * 2))) {s : ℕ} (hs : s < c.length)
    (x : Fin (3 * 2) → Bool) :
    output (swapC c s (wire c x s)) x = output c x := by
  have hsplit := split_at_getD c hs
  have hwire : wire c x s
      = evalGate x (runFrom x [] (c.take s)) (c.getD s (.cst false)) :=
    wire_eq c x hs
  show (runFrom x [] (c.take s ++ CGate.cst (wire c x s) :: c.drop (s + 1))).getD
    ((swapC c s (wire c x s)).length - 1) false = output c x
  rw [runFrom_append]
  show (runFrom x (runFrom x [] (c.take s)
      ++ [evalGate x (runFrom x [] (c.take s)) (CGate.cst (wire c x s))])
      (c.drop (s + 1))).getD ((swapC c s (wire c x s)).length - 1) false = output c x
  have hval : evalGate x (runFrom x [] (c.take s)) (CGate.cst (wire c x s))
      = evalGate x (runFrom x [] (c.take s)) (c.getD s (.cst false)) := hwire
  rw [hval, swapC_length c s (wire c x s) hs]
  conv_rhs => rw [hsplit]
  show _ = (runFrom x [] (c.take s ++ c.getD s (.cst false) :: c.drop (s + 1))).getD
    ((c.take s ++ c.getD s (.cst false) :: c.drop (s + 1)).length - 1) false
  rw [runFrom_append]
  show (runFrom x (runFrom x [] (c.take s)
      ++ [evalGate x (runFrom x [] (c.take s)) (c.getD s (.cst false))])
      (c.drop (s + 1))).getD (c.length - 1) false
    = (runFrom x (runFrom x [] (c.take s)
      ++ [evalGate x (runFrom x [] (c.take s)) (c.getD s (.cst false))])
      (c.drop (s + 1))).getD
      ((c.take s ++ c.getD s (.cst false) :: c.drop (s + 1)).length - 1) false
  rw [← hsplit]

/-! ### Blindness of the swapped circuit inside the shared subtree -/

/-- The swapped cone avoids the shared subtree's interior. -/
theorem swapC_cone_avoids (c : List (CGate (3 * 2))) {s r₁ r₂ : ℕ}
    (hsh : TwelveShape c s r₁ r₂) (hlen : c.length = 12) (w : Bool) :
    ∀ q, InCone (swapC c s w) q → ¬(Reach c s q ∧ q ≠ s) := by
  have hsl := hsh.s_lt
  have hs : s < c.length := by omega
  have hswlen : (swapC c s w).length = c.length := swapC_length c s w hs
  intro q hq
  induction hq with
  | root =>
    rintro ⟨hr, -⟩
    have := reach_le hr
    omega
  | step hw' ht hlt ih =>
    rename_i w' t
    rintro ⟨hrt, hts⟩
    by_cases hw's : w' = s
    · subst hw's
      rw [swapC_getD_self hs w] at ht
      simp [gateReads] at ht
    · rw [swapC_getD_ne hs w hw's] at ht
      obtain ⟨p, hps, hqp, hqlt⟩ := reach_last hrt hts
      have hw'lt : w' < c.length := by
        have := inCone_lt (show 0 < (swapC c s w).length by omega) hw'
        omega
      have hple := reach_le hps
      have hpw : w' = p :=
        hsh.others_one t (by omega) hts w' p (by omega) (by omega) ht hqp
      rw [← hpw] at hps
      exact ih ⟨hps, hw's⟩

/-- **The swapped circuit is blind inside the shared subtree (proved).** -/
theorem swapC_blind (c : List (CGate (3 * 2))) {s r₁ r₂ : ℕ}
    (hsh : TwelveShape c s r₁ r₂) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) (w : Bool) (i : Fin (3 * 2))
    (hi : Reach c s (varPos c i)) (x : Fin (3 * 2) → Bool) (b : Bool) :
    output (swapC c s w) (Function.update x i b) = output (swapC c s w) x := by
  have hsl := hsh.s_lt
  have hs : s < c.length := by omega
  have hswlen : (swapC c s w).length = c.length := swapC_length c s w hs
  have hnv : ∀ w', InCone (swapC c s w) w' →
      (swapC c s w).getD w' (.cst false) ≠ CGate.var i := by
    intro w' hw' hg
    by_cases hw's : w' = s
    · subst hw's
      rw [swapC_getD_self hs w] at hg
      simp at hg
    · rw [swapC_getD_ne hs w hw's] at hg
      have hw'lt : w' < 12 := by
        have := inCone_lt (show 0 < (swapC c s w).length by omega) hw'
        omega
      have hvp : w' = varPos c i :=
        hsh.var_inj w' (varPos c i) i hw'lt (varPos_lt c hcomp hlen i) hg
          (varPos_gate c hcomp hlen i)
      exact swapC_cone_avoids c hsh hlen w w' hw' ⟨by rw [hvp]; exact hi, hw's⟩
  rw [output_eq_wire, output_eq_wire]
  exact cone_wire_agree (swapC c s w) i x b (by omega) hnv _ InCone.root

/-! ### Blindness of the shared wire outside its subtree -/

theorem getD_take_eq' {c : List (CGate (3 * 2))} {k q : ℕ} (h : q < k) :
    (c.take k).getD q (.cst false) = c.getD q (.cst false) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt h]

theorem inCone_take_reach {c : List (CGate (3 * 2))} {s : ℕ} (hs : s < c.length) :
    ∀ q, InCone (c.take (s + 1)) q → Reach c s q := by
  intro q hq
  induction hq with
  | root =>
    have hlt : (c.take (s + 1)).length - 1 = s := by
      rw [List.length_take]
      omega
    rw [hlt]
    exact Reach.refl s
  | step hw' ht hlt ih =>
    rename_i w' t
    have hw'lt : w' < (c.take (s + 1)).length :=
      inCone_lt (show 0 < (c.take (s + 1)).length by rw [List.length_take]; omega) hw'
    have hw'lt' : w' < s + 1 := by
      rw [List.length_take] at hw'lt
      omega
    rw [getD_take_eq' hw'lt'] at ht
    exact Reach.step ih ht hlt

theorem wire_take_output (c : List (CGate (3 * 2))) {s : ℕ} (hs : s < c.length)
    (x : Fin (3 * 2) → Bool) : output (c.take (s + 1)) x = wire c x s := by
  show (runFrom x [] (c.take (s + 1))).getD ((c.take (s + 1)).length - 1) false
    = wire c x s
  have hl : (c.take (s + 1)).length = s + 1 := by
    rw [List.length_take]
    omega
  rw [hl]
  show (runFrom x [] (c.take (s + 1))).getD s false = wire c x s
  exact wire_prefix c x (by omega) (by omega)

/-- **The shared wire is blind outside its subtree (proved).** -/
theorem wire_s_blind (c : List (CGate (3 * 2))) {s r₁ r₂ : ℕ}
    (hsh : TwelveShape c s r₁ r₂) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) (i : Fin (3 * 2)) (hi : ¬ Reach c s (varPos c i))
    (x : Fin (3 * 2) → Bool) (b : Bool) :
    wire c (Function.update x i b) s = wire c x s := by
  have hsl := hsh.s_lt
  have hs : s < c.length := by omega
  rw [← wire_take_output c hs, ← wire_take_output c hs]
  have hnv : ∀ w', InCone (c.take (s + 1)) w' →
      (c.take (s + 1)).getD w' (.cst false) ≠ CGate.var i := by
    intro w' hw' hg
    have hr := inCone_take_reach hs w' hw'
    have hw'lt : w' < s + 1 := by
      have := inCone_lt
        (show 0 < (c.take (s + 1)).length by rw [List.length_take]; omega) hw'
      rw [List.length_take] at this
      omega
    rw [getD_take_eq' hw'lt] at hg
    have hvp : w' = varPos c i :=
      hsh.var_inj w' (varPos c i) i (by omega) (varPos_lt c hcomp hlen i) hg
        (varPos_gate c hcomp hlen i)
    rw [hvp] at hr
    exact hi hr
  rw [output_eq_wire, output_eq_wire]
  exact cone_wire_agree (c.take (s + 1)) i x b
    (by rw [List.length_take]; omega) hnv _ InCone.root

/-! ### Generic agreement from pointwise blindness -/

theorem output_agree_of_blind {n : ℕ} (F : (Fin n → Bool) → Bool) (P : Fin n → Prop)
    (hblind : ∀ j, ¬ P j → ∀ x b, F (Function.update x j b) = F x) :
    ∀ (l : List (Fin n)) (x y : Fin n → Bool),
      (∀ j, P j → x j = y j) → (∀ j, j ∉ l → x j = y j) → F x = F y := by
  intro l
  induction l with
  | nil =>
    intro x y hS hoff
    have hxy : x = y := funext (fun j => hoff j (by simp))
    rw [hxy]
  | cons j l' ih =>
    intro x y hS hoff
    have hstep : F x = F (Function.update x j (y j)) := by
      by_cases hjP : P j
      · have hxy := hS j hjP
        rw [← hxy, Function.update_eq_self]
      · exact (hblind j hjP x (y j)).symm
    rw [hstep]
    refine ih (Function.update x j (y j)) y ?_ ?_
    · intro j' hj'
      by_cases hjj : j' = j
      · subst hjj
        rw [Function.update_self]
      · rw [Function.update_of_ne hjj (y j) x]
        exact hS j' hj'
    · intro j' hj'
      by_cases hjj : j' = j
      · subst hjj
        rw [Function.update_self]
      · rw [Function.update_of_ne hjj (y j) x]
        exact hoff j' (by
          intro hmem
          rcases List.mem_cons.mp hmem with h | h
          · exact hjj h
          · exact hj' h)

theorem eval_agree_of_blind {n : ℕ} (F : (Fin n → Bool) → Bool) (P : Fin n → Prop)
    (hblind : ∀ j, ¬ P j → ∀ x b, F (Function.update x j b) = F x)
    (x y : Fin n → Bool) (h : ∀ j, P j → x j = y j) : F x = F y :=
  output_agree_of_blind F P hblind (List.finRange n) x y h
    (fun j hj => absurd (List.mem_finRange j) hj)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.output_swapC
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.swapC_blind
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.wire_s_blind
