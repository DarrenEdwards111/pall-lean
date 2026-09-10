import GodMoveCircuitConnection
import GodMoveUnitCharacteristic
import GodMoveBooleanFace
import GodMoveTopCoefficientMinor

/-!
# A uniform linear-time machine with large normalized SPDP rank

The machine scans right until the first false bit (blank cells read false),
accepting precisely when its position is even. Four finite control states,
no tape writes, and an explicit length-plus-one clock suffice on every input.
This is an actual machine example, not a family of postulated circuits.

Its normalized source has a nonzero full-degree coefficient, which yields
the binomial complementary-column minor at every derivative order. At
logarithmic order the rank exceeds every polynomial in input length and
the actual halting time. Thus local machine operations and runtime alone
cannot give the proposed universal polynomial rank bound. A theorem that
essentially uses correctness for SAT is a separate, unresolved obligation.
-/

namespace GodMoveLinearTimeRankObstruction

open MvPolynomial MultilinearSPDP SPDP
open GodMoveBooleanInterpolation GodMoveCircuitConnection
open PallLean.Paper93.DeepMath.PathB
open ComposableMachine ComposableStepCircuit ComposablePpolyDischarge
open NFrameBoundaryTransducer
open SATCircuitSeparationBridge GodMoveBooleanFace GodMoveCircuitNormalization
open GodMoveMonomialMinor (discreteBlocks)

/-- Running states carry the answer appropriate if the current cell is false;
halted states carry the final answer. -/
def scanner : Machine where
  State := Bool ⊕ Bool
  fin := inferInstance
  dec := inferInstance
  start := .inl true
  halt := fun s => match s with | .inl _ => false | .inr _ => true
  δ := fun s b => match s with
    | .inl parity => if b then (.inl (!parity), none, 1) else (.inr parity, none, 2)
    | .inr answer => (.inr answer, none, 2)
  accept := fun s => match s with | .inl _ => false | .inr answer => answer

/-- Accept exactly when the first false bit has even index. The implicit
false cell following the finite input guarantees that such an index exists. -/
def easyLanguage : List Bool → Bool
  | [] => true
  | b :: xs => if b then !easyLanguage xs else true

theorem scanner_step_false (parity : Bool) (h : ℕ) (tp : List Bool)
    (hb : tp.getD h false = false) :
    step scanner ⟨.inl parity, h, tp⟩ = ⟨.inr parity, h, tp⟩ := by
  change tp[h]?.getD false = false at hb
  simp [step, scanner, hb, moveHead]

theorem scanner_step_true (parity : Bool) (h : ℕ) (tp : List Bool)
    (hb : tp.getD h false = true) :
    step scanner ⟨.inl parity, h, tp⟩ = ⟨.inl (!parity), h + 1, tp⟩ := by
  change tp[h]?.getD false = true at hb
  simp [step, scanner, hb, moveHead]

/-- The run invariant works at any head offset with any unchanged tape
having the specified remaining suffix. -/
theorem scanner_run_state (xs tp : List Bool) (h : ℕ) (parity : Bool)
    (hread : ∀ j, tp.getD (h + j) false = xs.getD j false) :
    (run scanner (xs.length + 1) ⟨.inl parity, h, tp⟩).st =
      .inr (if parity then easyLanguage xs else !easyLanguage xs) := by
  induction xs generalizing h parity with
  | nil =>
    have hb : tp.getD h false = false := by simpa using hread 0
    simp only [List.length_nil, Nat.zero_add, run_succ, run_zero]
    rw [scanner_step_false parity h tp hb]
    cases parity <;> rfl
  | cons b xs ih =>
    have hb : tp.getD h false = b := by simpa using hread 0
    have hnext : ∀ j, tp.getD (h + 1 + j) false = xs.getD j false := by
      intro j
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hread (j + 1)
    rw [show (b :: xs).length + 1 = 1 + (xs.length + 1) by simp; omega,
      run_add, show run scanner 1 ⟨.inl parity, h, tp⟩ =
        step scanner ⟨.inl parity, h, tp⟩ from rfl]
    cases b with
    | false =>
      rw [scanner_step_false parity h tp hb,
        run_of_halted scanner (by rfl)]
      cases parity <;> rfl
    | true =>
      rw [scanner_step_true parity h tp hb, ih (h + 1) (!parity) hnext]
      cases parity <;> simp [easyLanguage]

/-- This fixed machine halts and decides the language within L+1 steps. -/
theorem scanner_decides : Decides scanner easyLanguage (fun L => L + 1) := by
  intro xs
  have hs := scanner_run_state xs xs 0 true (by intro j; simp)
  simp only [↓reduceIte] at hs
  constructor
  · change scanner.halt (run scanner (xs.length + 1) ⟨.inl true, 0, xs⟩).st = true
    rw [hs]
    rfl
  · change scanner.accept (run scanner (xs.length + 1) ⟨.inl true, 0, xs⟩).st = _
    rw [hs]
    rfl

theorem scanner_clock_polynomial :
    PvsNPSeparatingInvariant.PolyBounded (fun L => L + 1) := by
  exact ⟨1, 1, fun L => by simp⟩

theorem easyLanguage_inP : InP easyLanguage :=
  ⟨scanner, (fun L => L + 1), scanner_clock_polynomial, scanner_decides⟩

/-- The alternating prefix polynomial: 1 - X₀ + X₀X₁ - ... . -/
noncomputable def prefixPolynomial : (L : ℕ) → Poly L
  | 0 => 1
  | L + 1 => 1 - X 0 * rename Fin.succ (prefixPolynomial L)

theorem prefixPolynomial_eval (L : ℕ) (a : Assignment L) :
    MvPolynomial.eval (booleanPoint a) (prefixPolynomial L) =
      bit (easyLanguage (wordOfFin a)) := by
  induction L with
  | zero => simp [prefixPolynomial, wordOfFin, easyLanguage, bit]
  | succ L ih =>
    rw [prefixPolynomial, map_sub, map_one, map_mul, eval_X,
      eval_rename_boolean, ih]
    simp only [wordOfFin, List.finRange_succ, List.map_cons, List.map_map,
      Function.comp_def, easyLanguage]
    cases h0 : a 0 <;>
      cases easyLanguage ((List.finRange L).map (fun i => a i.succ)) <;>
      simp [booleanPoint, bit, h0]

private theorem multilinear_one_sub_head {L : ℕ} (p : Poly L)
    (hp : IsMultilinear p) :
    IsMultilinear (1 - X 0 * rename Fin.succ p) := by
  have hr : IsMultilinear (rename Fin.succ p) :=
    isMultilinear_rename _ (Fin.succ_injective L) p hp
  intro a ha i
  by_cases ha0 : a = 0
  · subst a
    simp
  have hone : coeff a (1 : MvPolynomial (Fin (L + 1)) ℚ) = 0 := by
    simp [coeff_one, Ne.symm ha0]
  have hmul : a ∈ (X 0 * rename Fin.succ p).support := by
    rw [mem_support_iff] at ha ⊢
    rw [coeff_sub, hone, zero_sub, neg_ne_zero] at ha
    exact ha
  obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hmul)
  have hb0 : b = Finsupp.single (0 : Fin (L + 1)) 1 := by
    exact Finset.mem_singleton.mp (support_monomial_subset hb)
  have hc0 : c 0 = 0 := by
    by_contra hn
    have hv : (0 : Fin (L + 1)) ∈ (rename Fin.succ p).vars :=
      (mem_vars _).mpr ⟨c, hc, Finsupp.mem_support_iff.mpr hn⟩
    obtain ⟨j, _, hj⟩ := mem_vars_rename Fin.succ p hv
    exact Fin.succ_ne_zero j hj
  rw [hb0, Finsupp.add_apply]
  by_cases hi : i = 0
  · subst i
    simp [hc0]
  · simpa [Finsupp.single_apply, hi] using hr c hc i

theorem prefixPolynomial_multilinear (L : ℕ) : IsMultilinear (prefixPolynomial L) := by
  induction L with
  | zero =>
    intro a ha i
    exact Fin.elim0 i
  | succ L ih => exact multilinear_one_sub_head _ ih

/-- The same normalized output source used by machine-face extraction, now
for a concrete fixed uniform scanner at its proved halting clock. -/
noncomputable def scannerSource (L : ℕ) : Poly L :=
  circuitTarget (circuitFor scanner L (L + 1))

theorem scannerSource_eq_prefixPolynomial (L : ℕ) :
    scannerSource L = prefixPolynomial L := by
  apply multilinear_eq_of_boolean_eval
  · exact normalize_isMultilinear _
  · exact prefixPolynomial_multilinear L
  · intro a
    rw [prefixPolynomial_eval, scannerSource, circuitTarget_eq_interpolate,
      eval_interpolate, circuitFor_output]
    have h := (scanner_decides (wordOfFin a)).2
    simpa only [wordOfFin_length] using congrArg bit h

/-- The square-free exponent containing every input coordinate. -/
noncomputable def topExponent (L : ℕ) : Fin L →₀ ℕ :=
  SymmetricPower.tagMonomial Finset.univ

theorem topExponent_apply {L : ℕ} (i : Fin L) : topExponent L i = 1 := by
  simp [topExponent, SymmetricPower.tagMonomial_apply]

theorem topExponent_succ (L : ℕ) :
    topExponent (L + 1) = Finsupp.single 0 1 +
      Finsupp.mapDomain Fin.succ (topExponent L) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have hz : Finsupp.mapDomain Fin.succ (topExponent L) 0 = 0 :=
      Finsupp.mapDomain_notin_range _ _ (by rintro ⟨j, hj⟩; exact Fin.succ_ne_zero j hj)
    simp [topExponent_apply, hz]
  · simp [topExponent_apply, Finsupp.mapDomain_apply (Fin.succ_injective L)]

theorem prefixPolynomial_top_coeff (L : ℕ) :
    coeff (topExponent L) (prefixPolynomial L) = (-1 : ℚ) ^ L := by
  induction L with
  | zero => simp [prefixPolynomial, topExponent, SymmetricPower.tagMonomial]
  | succ L ih =>
    have hz : (0 : Fin (L + 1) →₀ ℕ) ≠ topExponent (L + 1) := by
      intro h
      have h0 := congrArg (fun a : Fin (L + 1) →₀ ℕ => a 0) h
      simp [topExponent_apply] at h0
    rw [prefixPolynomial, coeff_sub, coeff_one, if_neg hz, zero_sub,
      topExponent_succ, coeff_X_mul, coeff_rename_mapDomain _ (Fin.succ_injective L), ih,
      pow_succ]
    ring

theorem scannerSource_top_coeff (L : ℕ) :
    coeff (topExponent L) (scannerSource L) = (-1 : ℚ) ^ L := by
  rw [scannerSource_eq_prefixPolynomial, prefixPolynomial_top_coeff]

theorem scannerSource_top_coeff_ne_zero (L : ℕ) :
    coeff (topExponent L) (scannerSource L) ≠ 0 := by
  rw [scannerSource_top_coeff]
  exact pow_ne_zero _ (by norm_num)

/-- The normalized output of this actual uniform machine contains the
binomial minor, with no SAT or rank-transport hypothesis. -/
theorem choose_le_scannerSource_rank (L k ell : ℕ) :
    Nat.choose L k ≤ mlBlockedSpdpRank (discreteBlocks L) k ell (scannerSource L) :=
  GodMoveTopCoefficientMinor.choose_le_strict_rank_of_top_coeff
    (scannerSource L) (normalize_isMultilinear _) (scannerSource_top_coeff_ne_zero L) k ell

theorem choose_le_scannerSource_inclusive_rank (L k ell : ℕ) :
    Nat.choose L k ≤ mlBlockedSpdpRankInc (discreteBlocks L) k ell (scannerSource L) :=
  GodMoveTopCoefficientMinor.choose_le_inclusive_rank_of_top_coeff
    (scannerSource L) (normalize_isMultilinear _) (scannerSource_top_coeff_ne_zero L) k ell

/-- The rank has no eventual polynomial bound even for this one fixed machine. -/
theorem no_eventual_polynomial_scanner_rank (ell : ℕ → ℕ) :
    ¬ ∃ C d L0 : ℕ, ∀ L ≥ L0,
      mlBlockedSpdpRank (discreteBlocks L) (Nat.log 2 L) (ell L) (scannerSource L) ≤ C * L ^ d := by
  rintro ⟨C, d, L0, hbound⟩
  let L := max (max C L0) (2 ^ (max 20 (4 * (d + 1 + 1))))
  have hL0 : L0 ≤ L := (le_max_right C L0).trans (le_max_left _ _)
  have hLC : C ≤ L := (le_max_left C L0).trans (le_max_left _ _)
  have hlarge : 2 ^ (max 20 (4 * (d + 1 + 1))) ≤ L := le_max_right _ _
  have hlow := (GodMoveMonomialMinor.npow_lt_choose_log L (d + 1) hlarge).trans_le
    (choose_le_scannerSource_rank L (Nat.log 2 L) (ell L))
  have hup : C * L ^ d ≤ L ^ (d + 1) := by
    rw [pow_succ, mul_comm (L ^ d) L]
    exact Nat.mul_le_mul_right _ hLC
  exact (not_le_of_gt hlow) ((hbound L hL0).trans hup)

/-- Allowing the machine's proved actual clock L+1 in the polynomial does
not repair the bound. Constants and degree may depend on this fixed machine. -/
theorem no_eventual_polynomial_scanner_runtime_bound (ell : ℕ → ℕ) :
    ¬ ∃ C d L0 : ℕ, ∀ L ≥ L0,
      mlBlockedSpdpRank (discreteBlocks L) (Nat.log 2 L) (ell L) (scannerSource L) ≤
        C * (L + (L + 1) + 1) ^ d := by
  rintro ⟨C, d, L0, hbound⟩
  apply no_eventual_polynomial_scanner_rank ell
  refine ⟨C * 4 ^ d, d, max L0 1, ?_⟩
  intro L hL
  have hL0 : L0 ≤ L := (le_max_left _ _).trans hL
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hsize : L + (L + 1) + 1 ≤ 4 * L := by omega
  calc
    _ ≤ C * (L + (L + 1) + 1) ^ d := hbound L hL0
    _ ≤ C * (4 * L) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize _)
    _ = (C * 4 ^ d) * L ^ d := by rw [mul_pow, mul_assoc]

theorem no_eventual_polynomial_scanner_inclusive_runtime_bound (ell : ℕ → ℕ) :
    ¬ ∃ C d L0 : ℕ, ∀ L ≥ L0,
      mlBlockedSpdpRankInc (discreteBlocks L) (Nat.log 2 L) (ell L) (scannerSource L) ≤
        C * (L + (L + 1) + 1) ^ d := by
  rintro ⟨C, d, L0, hbound⟩
  apply no_eventual_polynomial_scanner_runtime_bound ell
  refine ⟨C, d, L0, fun L hL => ?_⟩
  exact (Submodule.finrank_mono
    (mlBlockedSpdpSubspace_le_inc (discreteBlocks L) (Nat.log 2 L) (ell L) (scannerSource L))).trans
    (hbound L hL)

/-- Even allowing separate constants for every correct polynomial-time
decider, runtime alone does not uniformly bound normalized-source SPDP rank.
The quantified language here is arbitrary; this is not a SAT-specific claim. -/
theorem no_general_polynomial_machine_rank_bound (ell : ℕ → ℕ) :
    ¬ ∀ (M : Machine) (language : List Bool → Bool) (T : ℕ → ℕ),
      Decides M language T → PvsNPSeparatingInvariant.PolyBounded T →
        ∃ C d L0 : ℕ, ∀ L ≥ L0,
          mlBlockedSpdpRank (discreteBlocks L) (Nat.log 2 L) (ell L)
            (circuitTarget (circuitFor M L (T L))) ≤ C * (L + T L + 1) ^ d := by
  intro h
  exact no_eventual_polynomial_scanner_runtime_bound ell
    (h scanner easyLanguage (fun L => L + 1) scanner_decides scanner_clock_polynomial)

end GodMoveLinearTimeRankObstruction

#print axioms GodMoveLinearTimeRankObstruction.scanner_run_state
#print axioms GodMoveLinearTimeRankObstruction.scanner_decides
#print axioms GodMoveLinearTimeRankObstruction.easyLanguage_inP
#print axioms GodMoveLinearTimeRankObstruction.scannerSource_eq_prefixPolynomial
#print axioms GodMoveLinearTimeRankObstruction.scannerSource_top_coeff
#print axioms GodMoveLinearTimeRankObstruction.choose_le_scannerSource_rank
#print axioms GodMoveLinearTimeRankObstruction.choose_le_scannerSource_inclusive_rank
#print axioms GodMoveLinearTimeRankObstruction.no_eventual_polynomial_scanner_runtime_bound
#print axioms GodMoveLinearTimeRankObstruction.no_eventual_polynomial_scanner_inclusive_runtime_bound
#print axioms GodMoveLinearTimeRankObstruction.no_general_polynomial_machine_rank_bound
