import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameW2YaoBrick1

/-!
# N-Frame: Yao bricks 2 — per-step classification and the activation dichotomy

Brick 1 gave the chain normal form.  This brick classifies **steps** on a given input and proves the dichotomy the
counting argument (Y3) will consume:

  `stepActive` — step `(op, v)` is *active* on input `x` when its induced register map `r ↦ op r (x v)` is constant
        (the register is erased); otherwise *passive* (a permutation).
  `w2run_allPassive` — **PROVED, regime A**: on an input activating no step, the run is **affine** —
        `r₀ ⊕ (⊕ₖ uₖ(x vₖ))`, an XOR of the initial register with unary reads.
  `w2run_active_r0_indep` — **PROVED, regime B**: on an input activating *some* step, the output is independent of the
        initial register — the constant regime erases history.
  `and2_forces_activation` — **PROVED, the payoff**: any program computing `x₀ ∧ x₁` must have an activating input —
        non-affine functions **force** the constant regime (the second-difference test: affine functions vanish on the
        4-point square, AND does not).

This is the entry point of the threshold argument: majority is non-affine on every relevant subcube, so it forces
activations *throughout* the input space; Y3's (open) content is counting how many — Yao's combinatorics shows
super-polynomially many regime switches are needed, and Y4 transfers that count into length.  Neither is here.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {n : ℕ}

/-! ### Step classification -/

/-- A step is **active** on `x` when its induced register map is constant — the register is erased. -/
def stepActive (s : (Bool → Bool → Bool) × Fin n) (x : Fin n → Bool) : Prop :=
  s.1 false (x s.2) = s.1 true (x s.2)

instance (s : (Bool → Bool → Bool) × Fin n) (x : Fin n → Bool) :
    Decidable (stepActive s x) := by unfold stepActive; infer_instance

/-- A passive step's map is the XOR with its `false`-row value. -/
theorem passive_step_map (s : (Bool → Bool → Bool) × Fin n) (x : Fin n → Bool)
    (h : ¬ stepActive s x) (r : Bool) :
    s.1 r (x s.2) = xor r (s.1 false (x s.2)) := by
  unfold stepActive at h
  cases r
  · cases hb : s.1 false (x s.2) <;> rfl
  · cases hf : s.1 false (x s.2) <;> cases ht : s.1 true (x s.2)
    · exact absurd (hf.trans ht.symm) h
    · rfl
    · rfl
    · exact absurd (hf.trans ht.symm) h

/-- The affine parity accumulated by a run: the XOR of every step's `false`-row read. -/
def progPar (p : W2Prog n) (x : Fin n → Bool) : Bool :=
  p.foldr (fun s q => xor (s.1 false (x s.2)) q) false

/-! ### The dichotomy -/

/-- **Regime A (proved)**: with no active step, the run is affine — `r₀ ⊕ progPar`. -/
theorem w2run_allPassive (p : W2Prog n) (x : Fin n → Bool)
    (h : ∀ s ∈ p, ¬ stepActive s x) (r0 : Bool) :
    w2run p r0 x = xor r0 (progPar p x) := by
  induction p generalizing r0 with
  | nil => cases r0 <;> rfl
  | cons s p ih =>
    show w2run p (s.1 r0 (x s.2)) x = _
    rw [ih (fun s' hs' => h s' (List.mem_cons_of_mem _ hs')),
      passive_step_map s x (h s List.mem_cons_self) r0]
    show xor (xor r0 (s.1 false (x s.2))) (progPar p x)
      = xor r0 (xor (s.1 false (x s.2)) (progPar p x))
    cases r0 <;> cases s.1 false (x s.2) <;> cases progPar p x <;> rfl

/-- **Regime B (proved)**: with an active step, the output is independent of the initial register. -/
theorem w2run_active_r0_indep (p : W2Prog n) (x : Fin n → Bool)
    (h : ∃ s ∈ p, stepActive s x) (r0 r0' : Bool) :
    w2run p r0 x = w2run p r0' x := by
  induction p generalizing r0 r0' with
  | nil =>
    obtain ⟨s, hs, -⟩ := h
    exact absurd hs List.not_mem_nil
  | cons s p ih =>
    show w2run p (s.1 r0 (x s.2)) x = w2run p (s.1 r0' (x s.2)) x
    by_cases hact : stepActive s x
    · unfold stepActive at hact
      cases r0 <;> cases r0' <;> first | rfl | (rw [hact]) | (rw [← hact])
    · obtain ⟨s', hs', hact'⟩ := h
      rcases List.mem_cons.mp hs' with h' | h'
      · exact absurd (h' ▸ hact') hact
      · exact ih ⟨s', h', hact'⟩ _ _

/-! ### The payoff: non-affine functions force activation -/

/-- The four corners of the `(x₀, x₁)` square. -/
def sq00 (n : ℕ) : Fin n → Bool := fun _ => false

def sq10 (hn : 2 ≤ n) : Fin n → Bool := Function.update (sq00 n) ⟨0, by omega⟩ true

def sq01 (hn : 2 ≤ n) : Fin n → Bool := Function.update (sq00 n) ⟨1, by omega⟩ true

def sq11 (hn : 2 ≤ n) : Fin n → Bool :=
  Function.update (Function.update (sq00 n) ⟨0, by omega⟩ true) ⟨1, by omega⟩ true

/-- **The second difference of the affine part vanishes (proved)**: each step reads one variable, so its contributions
pair up across the square. -/
theorem progPar_second_difference (hn : 2 ≤ n) (p : W2Prog n) :
    xor (xor (progPar p (sq00 n)) (progPar p (sq10 hn)))
      (xor (progPar p (sq01 hn)) (progPar p (sq11 hn))) = false := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    show xor (xor (xor (s.1 false (sq00 n s.2)) (progPar p (sq00 n)))
        (xor (s.1 false (sq10 hn s.2)) (progPar p (sq10 hn))))
      (xor (xor (s.1 false (sq01 hn s.2)) (progPar p (sq01 hn)))
        (xor (s.1 false (sq11 hn s.2)) (progPar p (sq11 hn)))) = false
    -- the step's four reads pair up equal
    have hpair : xor (xor (s.1 false (sq00 n s.2)) (s.1 false (sq10 hn s.2)))
        (xor (s.1 false (sq01 hn s.2)) (s.1 false (sq11 hn s.2))) = false := by
      by_cases h0 : s.2 = (⟨0, by omega⟩ : Fin n)
      · have e00 : sq00 n s.2 = false := rfl
        have e10 : sq10 hn s.2 = true := by rw [sq10, h0, Function.update_self]
        have e01 : sq01 hn s.2 = false := by
          rw [sq01, h0, Function.update_of_ne (by
            intro hc
            have := congrArg Fin.val hc
            simp at this)]
          rfl
        have e11 : sq11 hn s.2 = true := by
          rw [sq11, h0, Function.update_of_ne (by
            intro hc
            have := congrArg Fin.val hc
            simp at this), Function.update_self]
        rw [e00, e10, e01, e11]
        cases s.1 false false <;> cases s.1 false true <;> rfl
      · by_cases h1 : s.2 = (⟨1, by omega⟩ : Fin n)
        · have e00 : sq00 n s.2 = false := rfl
          have e10 : sq10 hn s.2 = false := by
            rw [sq10, h1, Function.update_of_ne (by
              intro hc
              have := congrArg Fin.val hc
              simp at this)]
            rfl
          have e01 : sq01 hn s.2 = true := by rw [sq01, h1, Function.update_self]
          have e11 : sq11 hn s.2 = true := by rw [sq11, h1, Function.update_self]
          rw [e00, e10, e01, e11]
          cases s.1 false false <;> cases s.1 false true <;> rfl
        · have e10 : sq10 hn s.2 = false := by
            rw [sq10, Function.update_of_ne h0]
            rfl
          have e01 : sq01 hn s.2 = false := by
            rw [sq01, Function.update_of_ne h1]
            rfl
          have e11 : sq11 hn s.2 = false := by
            rw [sq11, Function.update_of_ne h1, Function.update_of_ne h0]
            rfl
          rw [show sq00 n s.2 = false from rfl, e10, e01, e11]
          cases s.1 false false <;> rfl
    -- reassociate: (step-terms) ⊕ (tail-terms)
    generalize s.1 false (sq00 n s.2) = a1 at hpair ⊢
    generalize s.1 false (sq10 hn s.2) = a2 at hpair ⊢
    generalize s.1 false (sq01 hn s.2) = a3 at hpair ⊢
    generalize s.1 false (sq11 hn s.2) = a4 at hpair ⊢
    generalize progPar p (sq00 n) = b1 at ih ⊢
    generalize progPar p (sq10 hn) = b2 at ih ⊢
    generalize progPar p (sq01 hn) = b3 at ih ⊢
    generalize progPar p (sq11 hn) = b4 at ih ⊢
    cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;>
      cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
      simp_all

/-- **The payoff (proved)**: any program computing `x₀ ∧ x₁` has an activating input — non-affine functions force the
constant regime.  (The affine second difference vanishes; AND's equals `true` on the square.) -/
theorem and2_forces_activation (hn : 2 ≤ n) (r0 : Bool) (p : W2Prog n)
    (hcomp : ∀ x, w2run p r0 x = (x ⟨0, by omega⟩ && x ⟨1, by omega⟩)) :
    ∃ x, ∃ s ∈ p, stepActive s x := by
  by_contra hcon
  push_neg at hcon
  -- all four corners run in the affine regime
  have h00 := (hcomp (sq00 n)).symm.trans (w2run_allPassive p (sq00 n) (hcon _) r0)
  have h10 := (hcomp (sq10 hn)).symm.trans (w2run_allPassive p (sq10 hn) (hcon _) r0)
  have h01 := (hcomp (sq01 hn)).symm.trans (w2run_allPassive p (sq01 hn) (hcon _) r0)
  have h11 := (hcomp (sq11 hn)).symm.trans (w2run_allPassive p (sq11 hn) (hcon _) r0)
  have hsecond := progPar_second_difference hn p
  -- AND's values on the square: 0,0,0,1 — second difference `true`; affine gives `false`
  have v00 : (sq00 n ⟨0, by omega⟩ && sq00 n ⟨1, by omega⟩) = false := rfl
  have v10 : (sq10 hn ⟨0, by omega⟩ && sq10 hn ⟨1, by omega⟩) = false := by
    show (Function.update (sq00 n) ⟨0, by omega⟩ true ⟨0, by omega⟩ && _) = false
    rw [Function.update_self, sq10, Function.update_of_ne (by
      intro hc
      have := congrArg Fin.val hc
      simp at this)]
    rfl
  have v01 : (sq01 hn ⟨0, by omega⟩ && sq01 hn ⟨1, by omega⟩) = false := by
    show (Function.update (sq00 n) ⟨1, by omega⟩ true ⟨0, by omega⟩ && _) = false
    rw [Function.update_of_ne (by
      intro hc
      have := congrArg Fin.val hc
      simp at this)]
    rfl
  have v11 : (sq11 hn ⟨0, by omega⟩ && sq11 hn ⟨1, by omega⟩) = true := by
    have hA : sq11 hn (⟨0, by omega⟩ : Fin n) = true := by
      rw [sq11, Function.update_of_ne (by
        intro hc
        have := congrArg Fin.val hc
        simp at this), Function.update_self]
    have hB : sq11 hn (⟨1, by omega⟩ : Fin n) = true := by
      rw [sq11, Function.update_self]
    rw [hA, hB]
    rfl
  rw [v00] at h00
  rw [v10] at h10
  rw [v01] at h01
  rw [v11] at h11
  -- combine: r0 cancels four times, leaving second-difference true = false
  generalize progPar p (sq00 n) = b1 at h00 hsecond
  generalize progPar p (sq10 hn) = b2 at h10 hsecond
  generalize progPar p (sq01 hn) = b3 at h01 hsecond
  generalize progPar p (sq11 hn) = b4 at h11 hsecond
  cases r0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    first
      | exact Bool.noConfusion h00
      | exact Bool.noConfusion h10
      | exact Bool.noConfusion h01
      | exact Bool.noConfusion h11
      | exact Bool.noConfusion hsecond

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.w2run_allPassive
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.w2run_active_r0_indep
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.and2_forces_activation
