import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkObserverBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTreeDAGWall
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposablePpolyDischarge

/-!
# Shrinkage to general DAG circuits: the strongest unconditional bridge

This file discharges the *honest* part of the formula-to-circuit seam.  Every
general binary-gate circuit is expanded directly into a constant-extended
De Morgan formula.  A truth-table implementation of each unary/binary gate
multiplies the current formula-size bound by at most eight, so

  `dmsizeC f <= 8 ^ cbudget f`.

Consequently a shrinkage lower bound `q` gives the genuine general-circuit
lower bound certificate `q n <= 8 ^ cbudget (F n)`.  This is representation
independent: it applies to the minimum over every DAG circuit computing the
function.

The same file proves the exact obstruction.  Every `n`-bit Boolean function
has a DNF with at most `n * 2^n` variable leaves.  Hence no De Morgan formula
lower bound can cross `8^(n+1)`, and the generic unfolding certificate cannot
prove even `cbudget > n+1`.  Formula shrinkage therefore reaches general
circuits only logarithmically.  A separation-strength bridge must exploit
additional semantics (hardness magnification, sharing-sensitive structure,
or another non-generic invariant); it cannot be obtained from formula size
alone.

Nothing here proves `P != NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ShrinkDAGBridge

open PallLean.Paper93.DeepMath.PathB.Khrapchenko
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.ShrinkObserverBridge

/-! ## A constant-cost De Morgan implementation of the full binary basis -/

/-- De Morgan negation.  Literal polarity flips; constants and connectives
are dualized. -/
def notC {n : ℕ} : DMTreeC n → DMTreeC n
  | .lit i b => .lit i (!b)
  | .cst b => .cst (!b)
  | .and l r => .or (notC l) (notC r)
  | .or l r => .and (notC l) (notC r)

theorem notC_eval {n : ℕ} (t : DMTreeC n) (x : Fin n → Bool) :
    (notC t).eval x = !(t.eval x) := by
  induction t with
  | lit i b => cases x i <;> cases b <;> simp [notC, DMTreeC.eval]
  | cst b => rfl
  | and l r ihl ihr => simp only [notC, DMTreeC.eval, ihl, ihr]; cases l.eval x <;> cases r.eval x <;> rfl
  | or l r ihl ihr => simp only [notC, DMTreeC.eval, ihl, ihr]; cases l.eval x <;> cases r.eval x <;> rfl

theorem notC_lsize0 {n : ℕ} (t : DMTreeC n) : (notC t).lsize0 = t.lsize0 := by
  induction t with
  | lit i b => rfl
  | cst b => rfl
  | and l r ihl ihr => simp only [notC, DMTreeC.lsize0, ihl, ihr]
  | or l r ihl ihr => simp only [notC, DMTreeC.lsize0, ihl, ihr]

/-- Formula-level if-then-else: `if c then t else e`. -/
def iteC {n : ℕ} (c t e : DMTreeC n) : DMTreeC n :=
  .or (.and c t) (.and (notC c) e)

theorem iteC_eval {n : ℕ} (c t e : DMTreeC n) (x : Fin n → Bool) :
    (iteC c t e).eval x = if c.eval x then t.eval x else e.eval x := by
  simp only [iteC, DMTreeC.eval, notC_eval]
  cases c.eval x <;> simp

theorem iteC_lsize0 {n : ℕ} (c t e : DMTreeC n) :
    (iteC c t e).lsize0 = 2 * c.lsize0 + t.lsize0 + e.lsize0 := by
  simp only [iteC, DMTreeC.lsize0, notC_lsize0]
  omega

/-- Any unary Boolean gate, implemented by its two-entry truth table. -/
def unaryC {n : ℕ} (op : Bool → Bool) (a : DMTreeC n) : DMTreeC n :=
  iteC a (.cst (op true)) (.cst (op false))

theorem unaryC_eval {n : ℕ} (op : Bool → Bool) (a : DMTreeC n)
    (x : Fin n → Bool) :
    (unaryC op a).eval x = op (a.eval x) := by
  rw [unaryC, iteC_eval]
  cases a.eval x <;> rfl

theorem unaryC_lsize0 {n : ℕ} (op : Bool → Bool) (a : DMTreeC n) :
    (unaryC op a).lsize0 = 2 * a.lsize0 := by
  simp [unaryC, iteC_lsize0, DMTreeC.lsize0]

/-- Any binary Boolean gate, implemented by its four-entry truth table. -/
def binaryC {n : ℕ} (op : Bool → Bool → Bool)
    (a b : DMTreeC n) : DMTreeC n :=
  iteC a
    (iteC b (.cst (op true true)) (.cst (op true false)))
    (iteC b (.cst (op false true)) (.cst (op false false)))

theorem binaryC_eval {n : ℕ} (op : Bool → Bool → Bool)
    (a b : DMTreeC n) (x : Fin n → Bool) :
    (binaryC op a b).eval x = op (a.eval x) (b.eval x) := by
  simp only [binaryC, iteC_eval, DMTreeC.eval]
  cases a.eval x <;> cases b.eval x <;> rfl

theorem binaryC_lsize0 {n : ℕ} (op : Bool → Bool → Bool)
    (a b : DMTreeC n) :
    (binaryC op a b).lsize0 = 2 * a.lsize0 + 4 * b.lsize0 := by
  simp only [binaryC, iteC_lsize0, DMTreeC.lsize0]
  omega

/-! ## Direct circuit expansion -/

/-- Expand one circuit gate using formulas for the earlier wires.  Out-of-range
reads match circuit semantics by defaulting to `false`. -/
def gateC {n : ℕ} (acc : List (DMTreeC n)) : CGate n → DMTreeC n
  | .var i => .lit i true
  | .cst b => .cst b
  | .un op j => unaryC op (acc.getD j (.cst false))
  | .bin op i j => binaryC op (acc.getD i (.cst false)) (acc.getD j (.cst false))

/-- Expand all circuit wires, retaining the formula for each wire. -/
def unfoldC {n : ℕ} (acc : List (DMTreeC n)) : List (CGate n) → List (DMTreeC n)
  | [] => acc
  | g :: gs => unfoldC (acc ++ [gateC acc g]) gs

theorem map_getD_evalC {n : ℕ} (x : Fin n → Bool)
    (l : List (DMTreeC n)) (j : ℕ) :
    (l.map (fun t => t.eval x)).getD j false =
      (l.getD j (.cst false)).eval x := by
  induction l generalizing j with
  | nil => cases j <;> rfl
  | cons t ts ih =>
    cases j with
    | zero => rfl
    | succ jj => exact ih jj

theorem gateC_eval {n : ℕ} (x : Fin n → Bool)
    (acc : List (DMTreeC n)) (g : CGate n) :
    (gateC acc g).eval x = evalGate x (acc.map (fun t => t.eval x)) g := by
  cases g with
  | var i => simp only [gateC, DMTreeC.eval, evalGate]; cases x i <;> rfl
  | cst b => rfl
  | un op j => simp only [gateC, unaryC_eval, evalGate, map_getD_evalC]
  | bin op i j => simp only [gateC, binaryC_eval, evalGate, map_getD_evalC]

theorem unfoldC_evals {n : ℕ} (x : Fin n → Bool) :
    ∀ (gs : List (CGate n)) (acc : List (DMTreeC n)),
      (unfoldC acc gs).map (fun t => t.eval x) =
        runFrom x (acc.map (fun t => t.eval x)) gs := by
  intro gs
  induction gs with
  | nil => intro acc; rfl
  | cons g rest ih =>
    intro acc
    show (unfoldC (acc ++ [gateC acc g]) rest).map _ =
      runFrom x ((acc.map fun t => t.eval x) ++
        [evalGate x (acc.map fun t => t.eval x) g]) rest
    rw [ih (acc ++ [gateC acc g]), List.map_append]
    congr 2
    simp only [List.map_singleton]
    rw [gateC_eval]

theorem getD_lsize0_le {n : ℕ} (acc : List (DMTreeC n)) (B : ℕ)
    (hB : ∀ t ∈ acc, t.lsize0 ≤ B) (j : ℕ) :
    (acc.getD j (.cst false)).lsize0 ≤ B := by
  induction acc generalizing j with
  | nil => cases j <;> simp [DMTreeC.lsize0]
  | cons t ts ih =>
    cases j with
    | zero => exact hB t List.mem_cons_self
    | succ jj => exact ih (fun t' ht' => hB t' (List.mem_cons_of_mem t ht')) jj

theorem gateC_lsize0_le {n : ℕ} (acc : List (DMTreeC n)) (B : ℕ)
    (hB1 : 1 ≤ B) (hB : ∀ t ∈ acc, t.lsize0 ≤ B) (g : CGate n) :
    (gateC acc g).lsize0 ≤ 8 * B := by
  cases g with
  | var i => simp [gateC, DMTreeC.lsize0]; omega
  | cst b => simp [gateC, DMTreeC.lsize0]
  | un op j =>
    rw [gateC, unaryC_lsize0]
    have hj := getD_lsize0_le acc B hB j
    omega
  | bin op i j =>
    rw [gateC, binaryC_lsize0]
    have hi := getD_lsize0_le acc B hB i
    have hj := getD_lsize0_le acc B hB j
    omega

/-- Each circuit gate costs at most one factor eight in the direct expansion. -/
theorem unfoldC_lsize0 {n : ℕ} :
    ∀ (gs : List (CGate n)) (acc : List (DMTreeC n)) (B : ℕ), 1 ≤ B →
      (∀ t ∈ acc, t.lsize0 ≤ B) →
      ∀ t ∈ unfoldC acc gs, t.lsize0 ≤ B * 8 ^ gs.length := by
  intro gs
  induction gs with
  | nil =>
    intro acc B hB1 hB t ht
    simpa using hB t ht
  | cons g rest ih =>
    intro acc B hB1 hB t ht
    have hnew := gateC_lsize0_le acc B hB1 hB g
    have hacc' : ∀ t' ∈ acc ++ [gateC acc g], t'.lsize0 ≤ 8 * B := by
      intro t' ht'
      rcases List.mem_append.mp ht' with h | h
      · have := hB t' h
        omega
      · rw [List.mem_singleton] at h
        subst t'
        exact hnew
    have hres := ih (acc ++ [gateC acc g]) (8 * B) (by omega) hacc' t ht
    calc
      t.lsize0 ≤ (8 * B) * 8 ^ rest.length := hres
      _ = B * 8 ^ (g :: rest).length := by
        simp only [List.length_cons, pow_succ]
        ring

theorem getD_mem_orC {α : Type} (l : List α) (k : ℕ) (d : α) :
    l.getD k d ∈ l ∨ l.getD k d = d := by
  induction l generalizing k with
  | nil => right; cases k <;> rfl
  | cons a l ih =>
    cases k with
    | zero => left; exact List.mem_cons_self
    | succ kk =>
      rcases ih kk with h | h
      · left; exact List.mem_cons_of_mem a h
      · right; exact h

/-- A circuit of `s` gates has an equivalent De Morgan formula with at most
`8^s` variable leaves. -/
theorem dmFormula_of_circuit {n : ℕ} (c : List (CGate n))
    (f : (Fin n → Bool) → Bool) (hc : computes c f) :
    ∃ t : DMTreeC n, t.eval = f ∧ t.lsize0 ≤ 8 ^ c.length := by
  let t : DMTreeC n := (unfoldC [] c).getD (c.length - 1) (.cst false)
  refine ⟨t, ?_, ?_⟩
  · funext x
    rw [show t.eval x = ((unfoldC [] c).map (fun u => u.eval x)).getD
        (c.length - 1) false by
      simp only [t, map_getD_evalC]]
    rw [unfoldC_evals]
    exact hc x
  · rcases getD_mem_orC (unfoldC [] c) (c.length - 1) (.cst false) with h | h
    · simpa using (unfoldC_lsize0 c [] 1 (le_refl 1)
        (fun u hu => absurd hu List.not_mem_nil) t (by simpa [t] using h))
    · simp only [t, h, DMTreeC.lsize0]
      exact Nat.zero_le _

/-! ## The genuine logarithmic transport -/

/-- The minimum De Morgan formula size is at most exponential in minimum DAG
circuit size. -/
theorem dmsizeC_le_eight_pow_cbudget {n : ℕ}
    (f : (Fin n → Bool) → Bool) :
    dmsizeC f ≤ 8 ^ cbudget f := by
  have hne : {s | ∃ c : List (CGate n), computes c f ∧ c.length = s}.Nonempty := by
    refine ⟨(compile 0 (PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.dnfFor f)).length,
      compile 0 (PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.dnfFor f), ?_, rfl⟩
    have h := compile_computes
      (PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.dnfFor f)
    rwa [show (fun x =>
      PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.eval
        (PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.dnfFor f) x) = f from
      PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.eval_dnfFor f] at h
  obtain ⟨c, hc, hlen⟩ := Nat.sInf_mem hne
  obtain ⟨t, ht, hs⟩ := dmFormula_of_circuit c f hc
  have hmin : dmsizeC f ≤ t.lsize0 := Nat.sInf_le ⟨t, fun x => congrFun ht x, rfl⟩
  change dmsizeC f ≤ 8 ^ sInf {s | ∃ c : List (CGate n), computes c f ∧ c.length = s}
  rw [← hlen]
  exact hmin.trans hs

/-- **Unconditional formula-to-DAG bridge.**  Any shrinkage theorem gives an
exponential certificate against the minimum general circuit. -/
theorem shrinkage_to_general_circuit
    (F : BoolFamily) (q : ℕ → ℕ) (h : ShrinkageLowerBound F q) :
    ∀ n, q n ≤ 8 ^ cbudget (F n) := by
  intro n
  have hq : q n ≤ dmsizeC (F n) := by
    have hne : {L | ∃ t : DMTreeC n,
        (∀ x, t.eval x = F n x) ∧ t.lsize0 = L}.Nonempty :=
      ⟨(dnfForC (F n)).lsize0, dnfForC (F n),
        fun x => congrFun (eval_dnfForC (F n)) x, rfl⟩
    obtain ⟨t, ht, hs⟩ := Nat.sInf_mem hne
    change q n ≤ sInf {L | ∃ t : DMTreeC n,
      (∀ x, t.eval x = F n x) ∧ t.lsize0 = L}
    rw [← hs]
    exact h n t (funext ht)
  exact hq.trans (dmsizeC_le_eight_pow_cbudget (F n))

/-- A strict formula lower bound above `8^s` certifies circuit size above `s`. -/
theorem cbudget_gt_of_eight_pow_lt_shrinkage
    (F : BoolFamily) (q : ℕ → ℕ) (h : ShrinkageLowerBound F q)
    (n s : ℕ) (hgap : 8 ^ s < q n) :
    s < cbudget (F n) := by
  have hp : 8 ^ s < 8 ^ cbudget (F n) :=
    hgap.trans_le (shrinkage_to_general_circuit F q h n)
  exact (Nat.pow_lt_pow_iff_right (by omega : 1 < (8 : ℕ))).mp hp

/-! ## The ceiling: generic formula shrinkage cannot supply separation -/

theorem mintermC_lsize0 {n : ℕ} (a : Fin n → Bool) (is : List (Fin n)) :
    (mintermC a is).lsize0 = is.length := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [mintermC, DMTreeC.lsize0, ih, Nat.add_comm]

theorem dnfOnC_lsize0 {n : ℕ} (as : List (Fin n → Bool)) :
    (dnfOnC as).lsize0 = as.length * n := by
  induction as with
  | nil => simp [dnfOnC, DMTreeC.lsize0]
  | cons a as ih =>
    simp only [dnfOnC, DMTreeC.lsize0, mintermC_lsize0, List.length_finRange,
      List.length_cons, ih]
    ring

/-- Universal DNF ceiling for the concrete formula model. -/
theorem dnfForC_lsize0_le {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (dnfForC f).lsize0 ≤ n * 2 ^ n := by
  rw [dnfForC, dnfOnC_lsize0]
  have hlen :
      (((Finset.univ : Finset (Fin n → Bool)).toList.filter f).length) ≤ 2 ^ n := by
    calc
      (((Finset.univ : Finset (Fin n → Bool)).toList.filter f).length)
          ≤ (Finset.univ : Finset (Fin n → Bool)).toList.length := List.length_filter_le _ _
      _ = Fintype.card (Fin n → Bool) := by simp
      _ = 2 ^ n := by rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  simpa [Nat.mul_comm] using Nat.mul_le_mul_right n hlen

/-- Every valid shrinkage lower bound is capped by the universal DNF. -/
theorem shrinkageLowerBound_le_dnf
    (F : BoolFamily) (q : ℕ → ℕ) (h : ShrinkageLowerBound F q) (n : ℕ) :
    q n ≤ n * 2 ^ n := by
  exact (h n (dnfForC (F n)) (eval_dnfForC (F n))).trans
    (dnfForC_lsize0_le (F n))

theorem n_mul_two_pow_le_eight_pow_succ (n : ℕ) :
    n * 2 ^ n ≤ 8 ^ (n + 1) := by
  have hn : n ≤ 4 ^ n := by
    induction n with
    | zero => simp
    | succ k ih =>
      have hpos : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by omega)
      rw [pow_succ]
      omega
  calc
    n * 2 ^ n ≤ 4 ^ n * 2 ^ n := Nat.mul_le_mul_right (2 ^ n) hn
    _ = 8 ^ n := by rw [← Nat.mul_pow]
    _ ≤ 8 ^ (n + 1) := by exact Nat.pow_le_pow_right (by omega) (by omega)

/-- The formula lower-bound premise itself never exceeds the linear-exponent
threshold `8^(n+1)`. -/
theorem shrinkageLowerBound_le_eight_pow_succ
    (F : BoolFamily) (q : ℕ → ℕ) (h : ShrinkageLowerBound F q) (n : ℕ) :
    q n ≤ 8 ^ (n + 1) :=
  (shrinkageLowerBound_le_dnf F q h n).trans (n_mul_two_pow_le_eight_pow_succ n)

/-- **Linear ceiling for the generic bridge.**  No formula-size lower bound can
meet the strict threshold required by the unfolding transport to prove
`cbudget (F n) > n+1`. -/
theorem no_shrinkage_unfolding_certificate_above_linear
    (F : BoolFamily) (q : ℕ → ℕ) (h : ShrinkageLowerBound F q) (n : ℕ) :
    ¬ (8 ^ (n + 1) < q n) :=
  not_lt_of_ge (shrinkageLowerBound_le_eight_pow_succ F q h n)

/-! ## Connection to the faithful SAT separation capstone -/

open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.ComposablePpolyDischarge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget

/-- The quantitative shrinkage premise that the generic expansion bridge
would need in order to prove super-polynomial general-circuit complexity. -/
def ShrinkageCircuitSeparationTarget (F : BoolFamily) (q : ℕ → ℕ) : Prop :=
  ShrinkageLowerBound F q ∧ ∀ k, ∃ n, 8 ^ (n ^ k + k) < q n

/-- If the required exponential-threshold shrinkage premise held, it would
indeed discharge the repository's general-circuit lower-bound target. -/
theorem circuitLowerBoundTarget_of_shrinkage
    (F : BoolFamily) (q : ℕ → ℕ)
    (h : ShrinkageCircuitSeparationTarget F q) :
    NFrameCircuitLowerBoundTarget F := by
  intro k
  obtain ⟨n, hn⟩ := h.2 k
  exact ⟨n, cbudget_gt_of_eight_pow_lt_shrinkage F q h.1 n (n ^ k + k) hn⟩

/-- The resulting route reaches the faithful SAT target, using the already
proved `P ⊆ P/poly` compiler.  This implication is valid but its shrinkage
premise is refuted below. -/
theorem SAT_not_in_P_of_shrinkageCircuitTarget
    (q : ℕ → ℕ) (h : ShrinkageCircuitSeparationTarget SATFamily q) :
    SAT_not_in_P :=
  sat_circuit_lower_bound_implies_target
    (circuitLowerBoundTarget_of_shrinkage SATFamily q h)

theorem linear_exp_le_separation_exp (n : ℕ) : n + 1 ≤ n ^ 2 + 2 := by
  cases n with
  | zero => norm_num
  | succ k =>
    have hk : 0 ≤ k ^ 2 := Nat.zero_le _
    nlinarith

/-- **The decisive no-go.**  The shrinkage premise required by the generic
formula-to-DAG bridge is inconsistent with the universal DNF upper bound.
Thus the bridge is real, but it cannot be the missing separation-strength
transport. -/
theorem no_shrinkageCircuitSeparationTarget
    (F : BoolFamily) (q : ℕ → ℕ) :
    ¬ ShrinkageCircuitSeparationTarget F q := by
  rintro ⟨hLower, hGrowth⟩
  obtain ⟨n, hn⟩ := hGrowth 2
  have hceil := shrinkageLowerBound_le_eight_pow_succ F q hLower n
  have hp : 8 ^ (n + 1) ≤ 8 ^ (n ^ 2 + 2) :=
    Nat.pow_le_pow_right (by omega) (linear_exp_le_separation_exp n)
  omega

end PallLean.Paper93.DeepMath.PathB.ShrinkDAGBridge

#print axioms PallLean.Paper93.DeepMath.PathB.ShrinkDAGBridge.dmFormula_of_circuit
#print axioms PallLean.Paper93.DeepMath.PathB.ShrinkDAGBridge.dmsizeC_le_eight_pow_cbudget
#print axioms PallLean.Paper93.DeepMath.PathB.ShrinkDAGBridge.shrinkage_to_general_circuit
#print axioms PallLean.Paper93.DeepMath.PathB.ShrinkDAGBridge.no_shrinkage_unfolding_certificate_above_linear
#print axioms PallLean.Paper93.DeepMath.PathB.ShrinkDAGBridge.SAT_not_in_P_of_shrinkageCircuitTarget
#print axioms PallLean.Paper93.DeepMath.PathB.ShrinkDAGBridge.no_shrinkageCircuitSeparationTarget
