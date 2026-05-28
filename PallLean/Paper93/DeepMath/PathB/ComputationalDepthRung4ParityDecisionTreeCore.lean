import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4CircuitSubstrates

/-!
# Rung 4 parity decision-tree core

**STATUS: REAL LOWER-BOUND CORE, NOT THE FULL HÅSTAD SWITCHING LEMMA.**

Håstad's AC⁰ lower bound for parity has two logically separate pieces:

1. random restrictions simplify small AC⁰ circuits into shallow decision trees;
2. parity still requires large decision-tree depth after enough variables remain.

This file formalizes the second piece in Lean.  It proves that any Boolean
decision tree computing parity on `n` variables has depth at least `n`.

This is a genuine rung-4 theorem, but it is not the full switching lemma and it
does not formalize the Razborov--Smolensky polynomial method.  It supplies a
checked endpoint that those deeper engines can target later.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Finset

/-! ## Inputs used by the parity lower bound -/

/-- The all-false Boolean input. -/
def falseInput (n : Nat) : Fin n -> Bool :=
  fun _ => false

/-- The Boolean input that is true at exactly one coordinate. -/
def oneHotInput {n : Nat} (i : Fin n) : Fin n -> Bool :=
  fun j => decide (j = i)

theorem boolParity_falseInput (n : Nat) :
    boolParity (falseInput n) = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have htail : boolParity (fun _ : Fin n => false) = false := by
        simpa [falseInput] using ih
      simp [falseInput, boolParity, htail]

theorem boolParity_oneHotInput {n : Nat} (i : Fin n) :
    boolParity (oneHotInput i) = true := by
  induction n with
  | zero =>
      exact Fin.elim0 i
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          have htail : boolParity (fun _ : Fin n => false) = false := by
            simpa [falseInput] using boolParity_falseInput n
          simp [oneHotInput, boolParity, htail]
      | succ i =>
          have hzero : (0 : Fin (n + 1)) ≠ i.succ := by
            intro h
            have hval : (0 : Nat) = i.val.succ := by
              simpa using congrArg Fin.val h
            omega
          have htail :
              boolParity (fun j : Fin n => decide (j = i)) = true := by
            simpa [oneHotInput] using ih i
          simp [oneHotInput, boolParity, hzero, htail]

theorem parityFunction_falseInput_ne_oneHotInput {n : Nat} (i : Fin n) :
    parityFunction n (falseInput n) ≠ parityFunction n (oneHotInput i) := by
  rw [parityFunction, boolParity_falseInput, boolParity_oneHotInput]
  decide

/-! ## Decision trees -/

/-- Boolean decision trees over `n` input bits.  The model is deliberately simple:
internal nodes query one input coordinate and choose a branch by its Boolean
value; leaves output a Boolean. -/
inductive BoolDecisionTree (n : Nat) : Type where
  | leaf : Bool -> BoolDecisionTree n
  | query : Fin n -> BoolDecisionTree n -> BoolDecisionTree n -> BoolDecisionTree n

namespace BoolDecisionTree

/-- Evaluate a decision tree on an input. -/
def eval {n : Nat} : BoolDecisionTree n -> (Fin n -> Bool) -> Bool
  | leaf b, _ => b
  | query i low high, x =>
      if x i then eval high x else eval low x

/-- Decision-tree depth. -/
def depth {n : Nat} : BoolDecisionTree n -> Nat
  | leaf _ => 0
  | query _ low high => max low.depth high.depth + 1

/-- The set of variables queried along the all-false execution path. -/
def falsePathVars {n : Nat} : BoolDecisionTree n -> Finset (Fin n)
  | leaf _ => ∅
  | query i low _ => insert i low.falsePathVars

/-- A decision tree computes a Boolean function. -/
def Computes {n : Nat} (T : BoolDecisionTree n) (F : BoolFunction n) : Prop :=
  forall x : Fin n -> Bool, T.eval x = F x

@[simp] theorem eval_leaf {n : Nat} (b : Bool) (x : Fin n -> Bool) :
    eval (leaf b) x = b :=
  rfl

@[simp] theorem depth_leaf {n : Nat} (b : Bool) :
    depth (leaf (n := n) b) = 0 :=
  rfl

@[simp] theorem falsePathVars_leaf {n : Nat} (b : Bool) :
    falsePathVars (leaf (n := n) b) = ∅ :=
  rfl

theorem falsePathVars_card_le_depth {n : Nat} (T : BoolDecisionTree n) :
    T.falsePathVars.card <= T.depth := by
  induction T with
  | leaf b =>
      simp [falsePathVars, depth]
  | query i low high ihLow ihHigh =>
      calc
        (insert i low.falsePathVars).card <= low.falsePathVars.card + 1 :=
          Finset.card_insert_le _ _
        _ <= low.depth + 1 := by omega
        _ <= max low.depth high.depth + 1 := by
          exact Nat.succ_le_succ (le_max_left _ _)

/-- If a coordinate is not queried on the all-false path, then the tree evaluates
the all-false input and the one-hot input at that coordinate identically. -/
theorem eval_falseInput_eq_eval_oneHotInput_of_not_mem_falsePathVars
    {n : Nat} (T : BoolDecisionTree n) {i : Fin n}
    (hi : i ∉ T.falsePathVars) :
    T.eval (falseInput n) = T.eval (oneHotInput i) := by
  induction T with
  | leaf b =>
      rfl
  | query q low high ihLow ihHigh =>
      have hiq : i ≠ q := by
        intro h
        exact hi (by simp [falsePathVars, h])
      have hlow : i ∉ low.falsePathVars := by
        intro hmem
        exact hi (by simp [falsePathVars, hmem])
      have hq : oneHotInput i q = false := by
        simp [oneHotInput, hiq.symm]
      simp [eval, falseInput, hq, ihLow hlow]

/-- If a Boolean function flips value between the all-false input and every
one-hot input, then any decision tree computing it has depth at least `n`. -/
theorem depth_ge_of_falseInput_oneHot_sensitive
    {n : Nat} {F : BoolFunction n} (T : BoolDecisionTree n)
    (hsensitive : forall i : Fin n, F (falseInput n) ≠ F (oneHotInput i))
    (hcomputes : T.Computes F) :
    n <= T.depth := by
  by_contra hnot
  have hdepth_lt : T.depth < n := Nat.lt_of_not_ge hnot
  have hcard_lt : T.falsePathVars.card < Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    exact lt_of_le_of_lt (falsePathVars_card_le_depth T) hdepth_lt
  have hcompl_pos : 0 < ((Finset.univ : Finset (Fin n)) \ T.falsePathVars).card := by
    rw [Finset.card_sdiff_of_subset]
    · have hproper : T.falsePathVars.card < (Finset.univ : Finset (Fin n)).card := by
        simpa using hcard_lt
      exact Nat.sub_pos_of_lt hproper
    · intro x hx
      simp
  obtain ⟨i, hiuniv⟩ := Finset.card_pos.mp hcompl_pos
  have hinot : i ∉ T.falsePathVars := (Finset.mem_sdiff.mp hiuniv).2
  have heval : T.eval (falseInput n) = T.eval (oneHotInput i) :=
    eval_falseInput_eq_eval_oneHotInput_of_not_mem_falsePathVars T hinot
  have hF : F (falseInput n) = F (oneHotInput i) := by
    rw [← hcomputes (falseInput n), ← hcomputes (oneHotInput i)]
    exact heval
  exact hsensitive i hF

/-- Parity requires decision-tree depth at least the number of input bits.  This
is the endpoint lower-bound core used after switching-lemma simplification. -/
theorem depth_ge_of_computes_parity
    {n : Nat} (T : BoolDecisionTree n)
    (hcomputes : T.Computes (parityFunction n)) :
    n <= T.depth :=
  depth_ge_of_falseInput_oneHot_sensitive T
    (fun i => parityFunction_falseInput_ne_oneHotInput i)
    hcomputes

end BoolDecisionTree

/-! ## Kernel-only axiom trace -/

#print axioms boolParity_falseInput
#print axioms boolParity_oneHotInput
#print axioms parityFunction_falseInput_ne_oneHotInput
#print axioms BoolDecisionTree.falsePathVars_card_le_depth
#print axioms BoolDecisionTree.eval_falseInput_eq_eval_oneHotInput_of_not_mem_falsePathVars
#print axioms BoolDecisionTree.depth_ge_of_falseInput_oneHot_sensitive
#print axioms BoolDecisionTree.depth_ge_of_computes_parity

end PallLean.Paper93.DeepMath.PathB
