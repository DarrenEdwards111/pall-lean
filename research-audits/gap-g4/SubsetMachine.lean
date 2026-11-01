import G4SATLink

/-!
# G4.4 item 4: is `subsetPoly` the characteristic of a `ComposableMachine`-decided language?

Against codex/godmove-gap-repairs @ 21921958 (`PallLean.Paper93.DeepMath.PathB.ComposableMachine`:
`Machine`, `step`, `run`, `Decides M L T := ∀ x, HaltsBy M x (T |x|) ∧ decideOut M x (T |x|) = L x`, `InP`),
the branch's `GodMoveSATSourceCanonicity.languageCharacteristic`, and `G4SATLink.easyEven`
(= `subsetPoly m κ` on `m+m` coordinates, the comparison polynomial of `satChar_def12_le_easy_paper`).

Results (all kernel-checked, axioms ⊆ {propext, Classical.choice, Quot.sound}):

* **Model fact** `decides_append_false`: every language decided by a `ComposableMachine` (any clock)
  satisfies `L (x ++ [false]) = L x`. The machine has no end-of-input marker (blank cells read `false`,
  `init` puts no delimiter), so it cannot observe `|x|`. E.g. `evenLength_not_decided`.
* **Negative** `no_decider_has_easyEven_char_family` / `_log` / `no_decider_has_easyEven_char`:
  no `ComposableMachine` (any clock, polynomial or not) decides a language whose characteristic is
  `easyEven` at lengths `2m₁` and `4m₁` — for every parameter schedule κ(m) with some `κ(m₁) ≤ m₁`, `m₁ ≥ 1`
  (fixed κ; κ = ⌊log₂ m⌋). So the G4.3 item-7 claim "f(x,y) = [|y| = κ ∧ y ⊆ x] (block layout) is a
  linear-time language" is FALSE in the branch's machine model. Non-vacuity: `easyEven_char_exists`.
* **Positive** `cont_decides` / `contLang_inP`: a 6-state self-delimiting scanner `contMachine` decides
  `contLang` (triples (c, x, y): stop & accept at the first c = 0; reject if y ∧ ¬x) within `|w| + 3` steps.
  Its characteristic's Def. 12 lower bound is NOT proved here (next step; [C] for N ≤ 12).
-/

set_option autoImplicit false

namespace SubsetMachine

open MvPolynomial
open GodMoveBooleanInterpolation GodMoveSATSourceCanonicity
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge (wordOfFin)
open Def12Measure (subsetPoly xMon yEval xExp yEval_xMon yEval_delta xExp_apply_castAdd xExp_apply_natAdd)

section Model

def TapeEq (a b : List Bool) : Prop := ∀ i, a.getD i false = b.getD i false

theorem getD_append_replicate_false (tape : List Bool) (k i : ℕ) :
    (tape ++ List.replicate k false).getD i false = tape.getD i false := by
  by_cases h : i < tape.length
  · rw [List.getD_append _ _ _ _ h]
  · push_neg at h
    rw [List.getD_append_right _ _ _ _ h, List.getD_eq_default _ _ h]
    simp

theorem writeAt_getD (tape : List Bool) (p : ℕ) (w : Bool) (i : ℕ) :
    (writeAt tape p w).getD i false = if i = p then w else tape.getD i false := by
  unfold writeAt
  have hlen : p < (tape ++ List.replicate (p + 1 - tape.length) false).length := by
    simp; omega
  by_cases h : i = p
  · subst h
    rw [if_pos rfl, List.getD_eq_getElem?_getD, List.getElem?_set_self hlen]
    rfl
  · rw [if_neg h, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h),
      ← List.getD_eq_getElem?_getD, getD_append_replicate_false]

def CfgRel {M : Machine} (c d : Cfg M) : Prop := c.st = d.st ∧ c.hd = d.hd ∧ TapeEq c.tp d.tp

theorem step_rel (M : Machine) (c d : Cfg M) (h : CfgRel c d) : CfgRel (step M c) (step M d) := by
  obtain ⟨s, p, a⟩ := c
  obtain ⟨s', p', b⟩ := d
  obtain ⟨hs, hp, ht⟩ := h
  simp only at hs hp
  subst hs hp
  have hr : a.getD p false = b.getD p false := ht p
  unfold step
  by_cases hh : M.halt s = true
  · simp only [hh, ↓reduceIte]; exact ⟨rfl, rfl, ht⟩
  · simp only [hh, Bool.false_eq_true, ↓reduceIte]
    rw [hr]
    refine ⟨rfl, rfl, ?_⟩
    cases hw : (M.δ s (b.getD p false)).2.1 with
    | none => exact ht
    | some w =>
      intro i
      simp only [writeAt_getD]
      split_ifs
      · rfl
      · exact ht i

theorem run_rel (M : Machine) (t : ℕ) (c d : Cfg M) (h : CfgRel c d) :
    CfgRel (run M t c) (run M t d) := by
  induction t with
  | zero => exact h
  | succ t ih => rw [run_succ, run_succ]; exact step_rel M _ _ ih

theorem init_rel_append_false (M : Machine) (x : List Bool) :
    CfgRel (init M x) (init M (x ++ [false])) :=
  ⟨rfl, rfl, fun i => (getD_append_replicate_false x 1 i).symm⟩

/-- **Model fact (kernel-checked).** Every language decided by a `ComposableMachine` (with any clock)
is invariant under appending a `false` bit: the machine reads blank cells as `false` and has no
end-of-input marker, so it cannot see the input length. -/
theorem decides_append_false (M : Machine) (lang : List Bool → Bool) (T : ℕ → ℕ)
    (hD : Decides M lang T) (x : List Bool) : lang (x ++ [false]) = lang x := by
  obtain ⟨h1, e1⟩ := hD x
  obtain ⟨h2, e2⟩ := hD (x ++ [false])
  have s1 := run_stable M x (le_max_left (T x.length) (T (x ++ [false]).length)) h1
  have s2 := run_stable M (x ++ [false]) (le_max_right (T x.length) (T (x ++ [false]).length)) h2
  have hR := run_rel M (max (T x.length) (T (x ++ [false]).length)) _ _ (init_rel_append_false M x)
  unfold decideOut at e1 e2
  rw [← e1, ← e2, ← s1, ← s2, hR.1]

theorem decides_append_replicate_false (M : Machine) (lang : List Bool → Bool) (T : ℕ → ℕ)
    (hD : Decides M lang T) (x : List Bool) (k : ℕ) :
    lang (x ++ List.replicate k false) = lang x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ', ← List.append_assoc, decides_append_false M lang T hD, ih]

/-- Consequence: "even length" is not decided by any `ComposableMachine`, at any clock. -/
theorem evenLength_not_decided :
    ¬ ∃ (M : Machine) (T : ℕ → ℕ), Decides M (fun w => decide (w.length % 2 = 0)) T := by
  rintro ⟨M, T, hD⟩
  have := decides_append_false M _ T hD []
  simp at this

/-! ## A self-delimiting subset scanner -/

inductive CState | readC | readX | readY (x : Bool) | done (ans : Bool)
  deriving DecidableEq, Fintype

def contMachine : Machine where
  State := CState
  fin := inferInstance
  dec := inferInstance
  start := .readC
  halt := fun s => match s with | .done _ => true | _ => false
  δ := fun s b => match s with
    | .readC => if b then (.readX, none, 1) else (.done true, none, 2)
    | .readX => (.readY b, none, 1)
    | .readY x => if b && !x then (.done false, none, 2) else (.readC, none, 1)
    | .done a => (.done a, none, 2)
  accept := fun s => match s with | .done a => a | _ => false

def contLang : List Bool → Bool
  | [] => true
  | false :: _ => true
  | [true] => true
  | [true, _] => true
  | true :: x :: y :: rest => if y && !x then false else contLang rest

def contSteps : List Bool → ℕ
  | [] => 1
  | false :: _ => 1
  | [true] => 4
  | [true, _] => 4
  | true :: x :: y :: rest => if y && !x then 3 else 3 + contSteps rest

theorem contSteps_le (xs : List Bool) : contSteps xs ≤ xs.length + 3 := by
  induction xs using contSteps.induct with
  | case1 => simp [contSteps]
  | case2 _ => simp [contSteps]
  | case3 => simp [contSteps]
  | case4 _ => simp [contSteps]
  | case5 x y rest hxy => simp [contSteps, hxy]
  | case6 x y rest hxy ih =>
    simp only [contSteps, hxy, List.length_cons]
    simp only [Bool.false_eq_true, if_false]
    omega

theorem run_succ' (M : Machine) (t : ℕ) (c : Cfg M) : run M (t + 1) c = run M t (step M c) :=
  Function.iterate_succ_apply (step M) t c


section Steps
variable (h : ℕ) (tp : List Bool)

theorem step_readC_true (hb : tp.getD h false = true) :
    step contMachine ⟨.readC, h, tp⟩ = ⟨.readX, h + 1, tp⟩ := by
  change tp[h]?.getD false = true at hb
  simp [step, contMachine, hb, moveHead]

theorem step_readC_false (hb : tp.getD h false = false) :
    step contMachine ⟨.readC, h, tp⟩ = ⟨.done true, h, tp⟩ := by
  change tp[h]?.getD false = false at hb
  simp [step, contMachine, hb, moveHead]

theorem step_readX (b : Bool) (hb : tp.getD h false = b) :
    step contMachine ⟨.readX, h, tp⟩ = ⟨.readY b, h + 1, tp⟩ := by
  change tp[h]?.getD false = b at hb
  simp [step, contMachine, hb, moveHead]

theorem step_readY_rej (x b : Bool) (hb : tp.getD h false = b) (hxy : (b && !x) = true) :
    step contMachine ⟨.readY x, h, tp⟩ = ⟨.done false, h, tp⟩ := by
  change tp[h]?.getD false = b at hb
  simp [step, contMachine, hb, moveHead, hxy]

theorem step_readY_ok (x b : Bool) (hb : tp.getD h false = b) (hxy : ¬ (b && !x) = true) :
    step contMachine ⟨.readY x, h, tp⟩ = ⟨.readC, h + 1, tp⟩ := by
  change tp[h]?.getD false = b at hb
  simp only [Bool.not_eq_true] at hxy
  simp [step, contMachine, hb, moveHead, hxy]

end Steps

/-- Run invariant at any head offset over any tape whose suffix from the head reads `xs`. -/
theorem cont_run_state (xs : List Bool) : ∀ (h : ℕ) (tp : List Bool),
    (∀ j, tp.getD (h + j) false = xs.getD j false) →
    (run contMachine (contSteps xs) ⟨.readC, h, tp⟩).st = .done (contLang xs) := by
  induction xs using contSteps.induct with
  | case1 =>
    intro h tp hr
    have r0 : tp.getD h false = false := by simpa using hr 0
    show (step contMachine ⟨.readC, h, tp⟩).st = _
    rw [step_readC_false h tp r0]; rfl
  | case2 tail =>
    intro h tp hr
    have r0 : tp.getD h false = false := by simpa using hr 0
    show (step contMachine ⟨.readC, h, tp⟩).st = _
    rw [step_readC_false h tp r0]; rfl
  | case3 =>
    intro h tp hr
    have r0 : tp.getD h false = true := by simpa using hr 0
    have r1 : tp.getD (h + 1) false = false := by simpa using hr 1
    have r2 : tp.getD (h + 1 + 1) false = false := by simpa [Nat.add_assoc] using hr 2
    have r3 : tp.getD (h + 1 + 1 + 1) false = false := by simpa [Nat.add_assoc] using hr 3
    show (step contMachine (step contMachine (step contMachine (step contMachine ⟨.readC, h, tp⟩)))).st = _
    rw [step_readC_true h tp r0, step_readX _ tp false r1,
      step_readY_ok _ tp false false r2 (by decide), step_readC_false _ tp r3]; rfl
  | case4 b =>
    intro h tp hr
    have r0 : tp.getD h false = true := by simpa using hr 0
    have r1 : tp.getD (h + 1) false = b := by simpa using hr 1
    have r2 : tp.getD (h + 1 + 1) false = false := by simpa [Nat.add_assoc] using hr 2
    have r3 : tp.getD (h + 1 + 1 + 1) false = false := by simpa [Nat.add_assoc] using hr 3
    show (step contMachine (step contMachine (step contMachine (step contMachine ⟨.readC, h, tp⟩)))).st = _
    rw [step_readC_true h tp r0, step_readX _ tp b r1,
      step_readY_ok _ tp b false r2 (by simp), step_readC_false _ tp r3]; rfl
  | case5 x y rest hxy =>
    intro h tp hr
    have r0 : tp.getD h false = true := by simpa using hr 0
    have r1 : tp.getD (h + 1) false = x := by simpa using hr 1
    have r2 : tp.getD (h + 1 + 1) false = y := by simpa [Nat.add_assoc] using hr 2
    have e : contSteps (true :: x :: y :: rest) = 3 := by simp [contSteps, hxy]
    rw [e]
    show (step contMachine (step contMachine (step contMachine ⟨.readC, h, tp⟩))).st = _
    rw [step_readC_true h tp r0, step_readX _ tp x r1, step_readY_rej _ tp x y r2 hxy]
    simp [contLang, hxy]
  | case6 x y rest hxy ih =>
    intro h tp hr
    have r0 : tp.getD h false = true := by simpa using hr 0
    have r1 : tp.getD (h + 1) false = x := by simpa using hr 1
    have r2 : tp.getD (h + 1 + 1) false = y := by simpa [Nat.add_assoc] using hr 2
    have e : contSteps (true :: x :: y :: rest) = 3 + contSteps rest := by simp [contSteps, hxy]
    have e2 : contLang (true :: x :: y :: rest) = contLang rest := by simp [contLang, hxy]
    rw [e, e2, run_add]
    have e3 : run contMachine 3 ⟨.readC, h, tp⟩ = ⟨.readC, h + 1 + 1 + 1, tp⟩ := by
      show step contMachine (step contMachine (step contMachine ⟨.readC, h, tp⟩)) = _
      rw [step_readC_true h tp r0, step_readX _ tp x r1, step_readY_ok _ tp x y r2 hxy]
    rw [e3]
    exact ih _ tp (fun j => by
      have := hr (j + 3)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this)

/-- **The machine decides `contLang` within `L + 3` steps on every input of length `L`.** -/
theorem cont_decides : Decides contMachine contLang (fun L => L + 3) := by
  intro xs
  have hs := cont_run_state xs 0 xs (by intro j; simp)
  have hh : contMachine.halt (run contMachine (contSteps xs) (init contMachine xs)).st = true := by
    change contMachine.halt (run contMachine (contSteps xs) ⟨.readC, 0, xs⟩).st = true
    rw [hs]; rfl
  have hst := run_stable contMachine xs (contSteps_le xs) hh
  constructor
  · unfold HaltsBy; rw [hst]; exact hh
  · unfold decideOut; rw [hst]
    change contMachine.accept (run contMachine (contSteps xs) ⟨.readC, 0, xs⟩).st = _
    rw [hs]; rfl

theorem cont_clock_polynomial :
    PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant.PolyBounded (fun L => L + 3) :=
  ⟨3, 1, fun L => by simp; omega⟩

theorem contLang_inP : InP contLang := ⟨contMachine, fun L => L + 3, cont_clock_polynomial, cont_decides⟩

/-! Boundary tests (kernel `decide`). -/
example : contLang [] = true := rfl
example : contLang [true, false, true] = false := rfl
example : contLang [true, true, true, true, false, true] = false := rfl
example : contLang [true, true, true, false, false, true] = true := rfl
example : decideOut contMachine [true, false, true] (3 + 3) = false := by decide
example : decideOut contMachine [true, true, true, true, false] (5 + 3) = true := by decide
example : decideOut contMachine [] (0 + 3) = true := by decide

end Model

section Block

variable {m : ℕ}

/-- the y-support of a Boolean point -/
def ySet (a : Fin (m + m) → Bool) : Finset (Fin m) := Finset.univ.filter (fun j => a (Fin.natAdd m j) = true)

theorem eval_yEval (a : Fin (m + m) → Bool) (q : MvPolynomial (Fin (m + m)) ℚ) :
    eval (booleanPoint a) (yEval (F := ℚ) (ySet a) q) = eval (booleanPoint a) q := by
  have h : (aeval (booleanPoint a) : MvPolynomial (Fin (m + m)) ℚ →ₐ[ℚ] ℚ).comp (yEval (ySet a))
      = aeval (booleanPoint a) := by
    apply MvPolynomial.algHom_ext
    intro v
    refine Fin.addCases (fun i => ?_) (fun j => ?_) v
    · simp [yEval]
    · simp only [AlgHom.comp_apply, yEval, aeval_X, Fin.addCases_right]
      simp [ySet, booleanPoint, bit]
  have := congrArg (fun f => f q) h
  simpa [MvPolynomial.coe_aeval_eq_eval] using this

theorem eval_subsetPoly (a : Fin (m + m) → Bool) (κ : ℕ) :
    eval (booleanPoint a) (subsetPoly (F := ℚ) m κ) =
      if (ySet a).card = κ then eval (booleanPoint a) (xMon (F := ℚ) (ySet a)) else 0 := by
  rw [← eval_yEval, subsetPoly, map_sum]
  simp only [map_mul, yEval_xMon, yEval_delta, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
  split_ifs <;> simp

theorem eval_xMon_of_true (a : Fin (m + m) → Bool) (A : Finset (Fin m))
    (hA : ∀ i ∈ A, a (Fin.castAdd m i) = true) :
    eval (booleanPoint a) (xMon (F := ℚ) A) = 1 := by
  rw [xMon, eval_monomial, one_mul]
  apply Finset.prod_eq_one
  intro v hv
  revert hv
  refine Fin.addCases (fun i hi => ?_) (fun j hj => ?_) v
  · rw [Finsupp.mem_support_iff, xExp_apply_castAdd] at hi
    have hiA : i ∈ A := by by_contra h; simp [h] at hi
    simp [booleanPoint, bit, hA i hiA]
  · exact absurd (xExp_apply_natAdd A j) (Finsupp.mem_support_iff.mp hj)

theorem eval_easyEven (a : Fin (m + m) → Bool) (κ : ℕ) :
    eval (booleanPoint a) (G4SATLink.easyEven (m + m) m κ rfl) =
      eval (booleanPoint a) (subsetPoly (F := ℚ) m κ) := by
  simp [G4SATLink.easyEven]



theorem bit_lang_of_char (lang : List Bool → Bool) (κ : ℕ)
    (hc : languageCharacteristic lang (m + m) = G4SATLink.easyEven (m + m) m κ rfl)
    (a : Fin (m + m) → Bool) :
    bit (lang (wordOfFin a)) = eval (booleanPoint a) (subsetPoly (F := ℚ) m κ) := by
  have := congrArg (eval (booleanPoint a)) hc
  rw [languageCharacteristic, eval_interpolate, eval_easyEven] at this
  exact this

theorem wordOfFin_const (n : ℕ) : wordOfFin (fun _ : Fin n => true) = List.replicate n true := by
  simp [wordOfFin]

theorem wordOfFin_prefix (k : ℕ) :
    wordOfFin (fun i : Fin ((k + k + 1) + (k + k + 1)) => decide (i.val < k + k)) =
      List.replicate (k + k) true ++ List.replicate (k + k + 2) false := by
  apply List.ext_getElem
  · simp [wordOfFin]; omega
  · intro i h1 h2
    simp only [wordOfFin, List.getElem_map, List.getElem_finRange, List.getElem_append,
      List.getElem_replicate]
    split_ifs with h
    · simpa using h
    · simp only [List.length_replicate] at h; simpa using h


/-- **No `ComposableMachine` decides a language whose characteristic at every even length `m+m`
is the embedded `subsetPoly m κ` of G4SATLink (`easyEven`)** — for every κ, any clock. -/
theorem no_decider_has_easyEven_char (κ : ℕ) :
    ¬ ∃ (M : Machine) (T : ℕ → ℕ) (lang : List Bool → Bool), Decides M lang T ∧
      ∀ m : ℕ, languageCharacteristic lang (m + m) = G4SATLink.easyEven (m + m) m κ rfl := by
  rintro ⟨M, T, lang, hD, hc⟩
  rcases Nat.eq_zero_or_pos κ with rfl | hκ
  · have e1 := bit_lang_of_char lang 0 (hc 1) ![false, true]
    have e2 := bit_lang_of_char lang 0 (hc 2) ![false, true, false, false]
    have w1 : wordOfFin (![false, true] : Fin (1 + 1) → Bool) = [false, true] := rfl
    have w2 : wordOfFin (![false, true, false, false] : Fin (2 + 2) → Bool) =
        [false, true] ++ List.replicate 2 false := rfl
    rw [w1] at e1
    rw [w2, decides_append_replicate_false M lang T hD, e1] at e2
    have v1 : (ySet (m := 1) ![false, true]).card ≠ 0 := by decide
    have v2 : (ySet (m := 2) ![false, true, false, false]).card = 0 := by decide
    have u1 : eval (booleanPoint (![false, true] : Fin (1 + 1) → Bool)) (subsetPoly (F := ℚ) 1 0) = 0 := by
      exact (eval_subsetPoly (m := 1) _ 0).trans (if_neg v1)
    have u2 : eval (booleanPoint (![false, true, false, false] : Fin (2 + 2) → Bool))
        (subsetPoly (F := ℚ) 2 0) = 1 := by
      refine (eval_subsetPoly (m := 2) _ 0).trans ?_
      rw [if_pos v2]
      have v3 : ySet (m := 2) ![false, true, false, false] = ∅ := Finset.card_eq_zero.mp v2
      rw [v3]
      exact eval_xMon_of_true (m := 2) _ ∅ (by simp)
    rw [u1, u2] at e2
    norm_num at e2
  · have e1 := bit_lang_of_char lang κ (hc κ) (fun _ => true)
    have e2 := bit_lang_of_char lang κ (hc (κ + κ + 1)) (fun i => decide (i.val < κ + κ))
    rw [wordOfFin_const] at e1
    rw [wordOfFin_prefix, decides_append_replicate_false M lang T hD, e1] at e2
    have y1 : ySet (m := κ) (fun _ => true) = Finset.univ := by ext j; simp [ySet]
    have y2 : ySet (m := κ + κ + 1) (fun i => decide (i.val < κ + κ)) = ∅ := by
      ext j; simp [ySet]; omega
    have u1 : eval (booleanPoint (fun _ : Fin (κ + κ) => true)) (subsetPoly (F := ℚ) κ κ) = 1 := by
      rw [eval_subsetPoly, y1, Finset.card_univ, Fintype.card_fin, if_pos rfl,
        eval_xMon_of_true _ _ (fun _ _ => rfl)]
    have u2 : eval (booleanPoint (fun i : Fin ((κ + κ + 1) + (κ + κ + 1)) => decide (i.val < κ + κ)))
        (subsetPoly (F := ℚ) (κ + κ + 1) κ) = 0 := by
      rw [eval_subsetPoly, y2, Finset.card_empty, if_neg (by omega)]
    rw [u1, u2] at e2
    norm_num at e2

/-- Pad a point on `m+m` coordinates with `m+m` trailing `false` bits. -/
def padPoint (a : Fin (m + m) → Bool) : Fin ((m + m) + (m + m)) → Bool :=
  fun i => if h : i.val < m + m then a ⟨i.val, h⟩ else false

theorem wordOfFin_padPoint (a : Fin (m + m) → Bool) :
    wordOfFin (padPoint a) = wordOfFin a ++ List.replicate (m + m) false := by
  apply List.ext_getElem
  · simp [wordOfFin]
  · intro i h1 h2
    simp only [wordOfFin, List.getElem_map, List.getElem_finRange, List.getElem_append,
      List.getElem_replicate, padPoint, Fin.val_cast, List.length_map, List.length_finRange]
    split_ifs <;> rfl

theorem ySet_padPoint (a : Fin (m + m) → Bool) : ySet (m := m + m) (padPoint a) = ∅ := by
  ext j; simp [ySet, padPoint]

theorem eval_pad (a : Fin (m + m) → Bool) (κ : ℕ) :
    eval (booleanPoint (padPoint a)) (subsetPoly (F := ℚ) (m + m) κ) = if κ = 0 then 1 else 0 := by
  rw [eval_subsetPoly, ySet_padPoint, Finset.card_empty]
  by_cases h : κ = 0
  · subst h; rw [if_pos rfl, if_pos rfl]; exact eval_xMon_of_true _ ∅ (by simp)
  · rw [if_neg (Ne.symm h), if_neg h]

/-- **Uniform-κ version.** Let `κf : ℕ → ℕ` be ANY parameter schedule (e.g. `κ = ⌊log₂ m⌋`).
If some `m₁ ≥ 1` has `κf m₁ ≤ m₁`, no `ComposableMachine` (any clock) decides a language whose
characteristic is `easyEven` both at length `m₁+m₁` (parameter `κf m₁`) and at length
`2m₁+2m₁` (parameter `κf (2m₁)`). Only these two lengths are used. -/
theorem no_decider_has_easyEven_char_family (κf : ℕ → ℕ) (m₁ : ℕ) (hm : 1 ≤ m₁) (hκ : κf m₁ ≤ m₁) :
    ¬ ∃ (M : Machine) (T : ℕ → ℕ) (lang : List Bool → Bool), Decides M lang T ∧
      languageCharacteristic lang (m₁ + m₁) = G4SATLink.easyEven (m₁ + m₁) m₁ (κf m₁) rfl ∧
      languageCharacteristic lang ((m₁ + m₁) + (m₁ + m₁)) =
        G4SATLink.easyEven ((m₁ + m₁) + (m₁ + m₁)) (m₁ + m₁) (κf (m₁ + m₁)) rfl := by
  rintro ⟨M, T, lang, hD, h1, h2⟩
  have key : ∀ a : Fin (m₁ + m₁) → Bool,
      bit (lang (wordOfFin a)) = if κf (m₁ + m₁) = 0 then 1 else 0 := by
    intro a
    have := bit_lang_of_char lang _ h2 (padPoint a)
    rwa [wordOfFin_padPoint, decides_append_replicate_false M lang T hD, eval_pad] at this
  -- a point with value 1: x all true, y = the first κf m₁ coordinates
  let S0 : Finset (Fin m₁) := (Finset.univ : Finset (Fin (κf m₁))).map (Fin.castLEEmb hκ)
  let a1 : Fin (m₁ + m₁) → Bool := Fin.addCases (fun _ => true) (fun j => decide (j ∈ S0))
  -- a point with value 0: x all true, y = all ones if κf m₁ = 0, else empty
  let a0 : Fin (m₁ + m₁) → Bool := Fin.addCases (fun _ => true) (fun _ => decide (κf m₁ = 0))
  have ys1 : ySet a1 = S0 := by ext j; simp only [ySet, Finset.mem_filter, Finset.mem_univ, true_and, Fin.addCases_right, a1, decide_eq_true_eq]
  have hS0 : S0.card = κf m₁ := by simp [S0]
  have v1 : eval (booleanPoint a1) (subsetPoly (F := ℚ) m₁ (κf m₁)) = 1 := by
    rw [eval_subsetPoly, ys1, if_pos hS0]
    exact eval_xMon_of_true _ _ (fun i _ => by simp [a1])
  have v0 : eval (booleanPoint a0) (subsetPoly (F := ℚ) m₁ (κf m₁)) = 0 := by
    rw [eval_subsetPoly, if_neg]
    by_cases hz : κf m₁ = 0
    · have : ySet a0 = Finset.univ := by ext j; simp only [ySet, Finset.mem_filter, Finset.mem_univ, true_and, Fin.addCases_right, a0, hz]; simp
      rw [this, Finset.card_univ, Fintype.card_fin, hz]; omega
    · have : ySet a0 = ∅ := by ext j; simp only [ySet, Finset.mem_filter, Finset.mem_univ, true_and, Fin.addCases_right, a0, hz]; simp
      rw [this, Finset.card_empty]; exact Ne.symm hz
  have e1 := (bit_lang_of_char lang _ h1 a1).trans v1
  have e0 := (bit_lang_of_char lang _ h1 a0).trans v0
  rw [key] at e1 e0
  rw [e1] at e0
  exact one_ne_zero e0

/-- Paper schedule `κ = ⌊log₂ m⌋` (any fixed κ also works, via `m₁ = max κ 1`). -/
theorem no_decider_has_easyEven_char_log :
    ¬ ∃ (M : Machine) (T : ℕ → ℕ) (lang : List Bool → Bool), Decides M lang T ∧
      ∀ m : ℕ, languageCharacteristic lang (m + m) = G4SATLink.easyEven (m + m) m (Nat.log 2 m) rfl := by
  rintro ⟨M, T, lang, hD, hc⟩
  exact no_decider_has_easyEven_char_family (fun m => Nat.log 2 m) 1 le_rfl (by simp)
    ⟨M, T, lang, hD, hc 1, hc 2⟩

/-! ### Non-vacuity: the hypotheses above are satisfiable by an (undecidable-in-the-model) language -/

theorem eval_xMon_of_false (a : Fin (m + m) → Bool) (A : Finset (Fin m)) (i : Fin m) (hi : i ∈ A)
    (hf : a (Fin.castAdd m i) = false) : eval (booleanPoint a) (xMon (F := ℚ) A) = 0 := by
  rw [xMon, eval_monomial, one_mul]
  apply Finset.prod_eq_zero (i := Fin.castAdd m i)
  · rw [Finsupp.mem_support_iff, xExp_apply_castAdd, if_pos hi]; exact one_ne_zero
  · rw [xExp_apply_castAdd, if_pos hi]; simp [booleanPoint, bit, hf]

theorem eval_subsetPoly_01 (a : Fin (m + m) → Bool) (κ : ℕ) :
    eval (booleanPoint a) (subsetPoly (F := ℚ) m κ) = 0 ∨
      eval (booleanPoint a) (subsetPoly (F := ℚ) m κ) = 1 := by
  rw [eval_subsetPoly]
  split_ifs
  · by_cases h : ∀ i ∈ ySet a, a (Fin.castAdd m i) = true
    · exact Or.inr (eval_xMon_of_true _ _ h)
    · push_neg at h
      obtain ⟨i, hi, hf⟩ := h
      exact Or.inl (eval_xMon_of_false _ _ i hi (by simpa using hf))
  · exact Or.inl rfl

theorem subsetPoly_isMultilinear (κ : ℕ) :
    MultilinearSPDP.IsMultilinear (subsetPoly (F := ℚ) m κ) := by
  intro s hs i
  obtain ⟨S, -, hS⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hs)
  exact Def12Measure.row_MLSupp S S s hS i

theorem wordOfFin_injective {n : ℕ} {a b : Fin n → Bool} (h : wordOfFin a = wordOfFin b) : a = b := by
  funext i
  have := congrArg (fun l : List Bool => l[i.val]?) h
  simpa [wordOfFin] using this

open Classical in
/-- The block-layout language: accept `w` iff `w = wordOfFin a` for some `a : Fin (m+m) → Bool`
with `subsetPoly m κ (a) = 1`. Classical; it is NOT decided by any `ComposableMachine`. -/
noncomputable def easyLangEven (κ : ℕ) (w : List Bool) : Bool :=
  decide (∃ (m : ℕ) (a : Fin (m + m) → Bool), wordOfFin a = w ∧
    eval (booleanPoint a) (subsetPoly (F := ℚ) m κ) = 1)

theorem easyLangEven_wordOfFin (κ : ℕ) (a : Fin (m + m) → Bool) :
    easyLangEven κ (wordOfFin a) = true ↔ eval (booleanPoint a) (subsetPoly (F := ℚ) m κ) = 1 := by
  simp only [easyLangEven, decide_eq_true_eq]
  constructor
  · rintro ⟨m', a', h, hv⟩
    have hl := congrArg List.length h
    simp only [wordOfFin, List.length_map, List.length_finRange] at hl
    obtain rfl : m' = m := by omega
    rwa [wordOfFin_injective h] at hv
  · intro hv; exact ⟨m, a, rfl, hv⟩

/-- **Non-vacuity of `no_decider_has_easyEven_char_*`:** for every κ some language has
characteristic exactly `easyEven (m+m) m κ` at EVERY even length. -/
theorem easyEven_char_exists (κ : ℕ) :
    ∃ lang : List Bool → Bool, ∀ m : ℕ,
      languageCharacteristic lang (m + m) = G4SATLink.easyEven (m + m) m κ rfl := by
  refine ⟨easyLangEven κ, fun m => ?_⟩
  have he : G4SATLink.easyEven (m + m) m κ rfl = subsetPoly (F := ℚ) m κ := by
    simp [G4SATLink.easyEven]
  rw [he]
  apply GodMoveCircuitNormalization.multilinear_eq_of_boolean_eval
  · intro α hα i; exact interpolate_isMultilinear _ α hα i
  · exact subsetPoly_isMultilinear κ
  · intro a
    rw [languageCharacteristic, eval_interpolate]
    rcases eval_subsetPoly_01 a κ with h | h
    · have hf : easyLangEven κ (wordOfFin a) = false := by
        cases hb : easyLangEven κ (wordOfFin a)
        · rfl
        · rw [easyLangEven_wordOfFin] at hb; rw [hb] at h; norm_num at h
      rw [hf, h]; rfl
    · rw [(easyLangEven_wordOfFin κ a).mpr h, h]; rfl

end Block

end SubsetMachine

#print axioms SubsetMachine.getD_append_replicate_false
#print axioms SubsetMachine.writeAt_getD
#print axioms SubsetMachine.step_rel
#print axioms SubsetMachine.run_rel
#print axioms SubsetMachine.decides_append_false
#print axioms SubsetMachine.decides_append_replicate_false
#print axioms SubsetMachine.evenLength_not_decided
#print axioms SubsetMachine.contSteps_le
#print axioms SubsetMachine.cont_run_state
#print axioms SubsetMachine.cont_decides
#print axioms SubsetMachine.cont_clock_polynomial
#print axioms SubsetMachine.contLang_inP
#print axioms SubsetMachine.eval_yEval
#print axioms SubsetMachine.eval_subsetPoly
#print axioms SubsetMachine.eval_xMon_of_true
#print axioms SubsetMachine.eval_easyEven
#print axioms SubsetMachine.bit_lang_of_char
#print axioms SubsetMachine.wordOfFin_padPoint
#print axioms SubsetMachine.no_decider_has_easyEven_char
#print axioms SubsetMachine.no_decider_has_easyEven_char_family
#print axioms SubsetMachine.no_decider_has_easyEven_char_log
#print axioms SubsetMachine.eval_subsetPoly_01
#print axioms SubsetMachine.subsetPoly_isMultilinear
#print axioms SubsetMachine.easyEven_char_exists
set_option pp.fullNames true in
#check @SubsetMachine.decides_append_false
set_option pp.fullNames true in
#check @SubsetMachine.cont_decides
set_option pp.fullNames true in
#check @SubsetMachine.contLang_inP
set_option pp.fullNames true in
#check @SubsetMachine.no_decider_has_easyEven_char
set_option pp.fullNames true in
#check @SubsetMachine.no_decider_has_easyEven_char_family
set_option pp.fullNames true in
#check @SubsetMachine.no_decider_has_easyEven_char_log
set_option pp.fullNames true in
#check @SubsetMachine.easyEven_char_exists
set_option pp.fullNames true in
#print SubsetMachine.contMachine
set_option pp.fullNames true in
#print SubsetMachine.contLang
