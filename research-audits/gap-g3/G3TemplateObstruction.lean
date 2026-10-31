import PallLean.PaperFaithfulCompilation
import PallLean.GlobalGodMoveGauge
import PallLean.GodMoveReal

/-!
# Gap G3 (research/gap-g3): witness-free template extraction fails the always-accept sanity test

`PassesG3` is the necessary sanity condition for any God-Move architecture: with the SAME
extraction `T_Φ` that is used for a SAT solver, the always-accept machine's compiled polynomial
must have SPDP rank below the NP-side bound `C(n/3, log₂ n)`.  (Otherwise the P-side bound G1
already fails for a trivial machine, and G1 ∧ Item 2 ∧ Item 3 is refutable outright.)

We prove that every architecture of the shape used by the paper and by the Lean Path-A /
Route-B code FAILS `PassesG3`:
* additive form `P_{M,Φ} = Q×_Φ(u,z) + R_{M,Φ}(v)` (paper Lemma 222 + Lemma 123 + Thm 223(iii)),
* multiplicative form `P_{M,Φ} = Q×_Φ · F_{M,Φ}` with `Π_Φ F = 1` (Lean `templatePMn`),
* any "M-blind" extraction `Π_Φ(P_{M,Φ}) = embed(Q_Φ) + const` (general form),
* the Route-B interfaces `Theorem207Extraction` / `…RankMonotone` / `…NPSideLowerBound` /
  `…PSideUpperBound` with a witness-free sheet (same sheet for all machines).
In each case: if extraction gives the NP-side bound for a correct machine `Msol`, it gives the
same bound for every machine, in particular for `alwaysAccept`.

Non-vacuity: concrete instances (n ≥ 2^804) where all hypotheses hold with the repo's own kernel-
checked NP-side object (`cookLevinQ`, `compiled_np_lower_bound_any_dtm`).
Measure: Lean `mlBlockedSpdpRank`.  Def. 12 variant: see docs/RESEARCH_NOTES.md (informal).
-/

namespace GapG3
open MvPolynomial TuringMachine PaperFaithfulCompilation MultilinearSPDP

/-- The 3-state machine that accepts on its first step. -/
def alwaysAccept : DTM where
  numStates := 3
  hStates := by decide
  transition := fun _ bit => (1, bit, true)
  timeBound := 1
  hTimeBound := by decide

theorem alwaysAccept_accepts_everything (n : ℕ) (hn : 1 ≤ n) (input : Fin n → Bool) :
    accepts alwaysAccept n hn input := by
  refine ⟨1, ?_, ?_⟩
  · simpa [timeSteps, alwaysAccept] using hn
  · rfl

/-- The NP-side bound of Item 2. -/
def npBound (n : ℕ) : ℕ := Nat.choose (n / 3) (Nat.log 2 n)

section Defs
variable {σ : UVSplit}

/-- **G3 sanity condition (Lean measure).** The always-accept machine's compiled polynomial
`P_acc` has SPDP rank strictly below `bound` (intended: `bound = npBound n`, κ = ℓ = log₂ n). -/
def PassesG3 (B : SPDP.BlockPartition σ.total) (κ ℓ bound : ℕ) (P_acc : PMnPoly σ) : Prop :=
  mlBlockedSpdpRank B κ ℓ P_acc < bound

/-- **G3, extracted form.** With the same extraction `T` used for the SAT solver, the extracted
object of the always-accept machine has rank below `bound`. -/
def PassesG3Extracted (B : SPDP.BlockPartition σ.total) (κ ℓ bound : ℕ)
    (T : PMnPoly σ →ₗ[ℚ] PMnPoly σ) (P_acc : PMnPoly σ) : Prop :=
  mlBlockedSpdpRank B κ ℓ (T P_acc) < bound

/-- For a rank-monotone extraction, `PassesG3` implies the extracted form. -/
theorem passesG3Extracted_of_passesG3 (B : SPDP.BlockPartition σ.total) (κ ℓ bound : ℕ)
    (T : PMnPoly σ →ₗ[ℚ] PMnPoly σ) (hT : GaugeMonotonicity.IsRankMonotoneGauge B T)
    (P : PMnPoly σ) (h : PassesG3 B κ ℓ bound P) : PassesG3Extracted B κ ℓ bound T P :=
  lt_of_le_of_lt (hT κ ℓ P) h

end Defs

section Core
variable {σ : UVSplit}

/-- `Π_Φ` kills every non-constant monomial of a v-only polynomial (Lemma 123: `R(v) ↦ R(0)`). -/
theorem piPhi_rename_inlV (R : MvPolynomial (Fin σ.numV) ℚ) :
    piPhi σ (rename σ.inlV R) = C (constantCoeff R) := by
  unfold piPhi PiStarConcrete.piZero PiStarConcrete.piSubst PiStarConcrete.substAlgHom
  rw [AlgHom.toLinearMap_apply, aeval_rename]
  have h : (PiStarConcrete.substFn (keepU σ) 0 ∘ σ.inlV) = fun _ => 0 := by
    funext j
    simp [Function.comp, PiStarConcrete.substFn, not_keepU_inlV σ j]
  rw [h, aeval_zero', algebraMap_eq]

/-- Core: an extraction identity `Π_Φ P = embed Q + c` forces `rank(embed Q) ≤ rank P` and
`rank(Π_Φ P) = rank(embed Q)` (κ ≥ 1). -/
theorem rank_of_extraction (B : SPDP.BlockPartition σ.total) (κ ℓ : ℕ) (hκ : 1 ≤ κ)
    (P : PMnPoly σ) (Q : CoupledSheetPoly σ) (c : ℚ)
    (hExt : piPhi σ P = CoupledSheetPoly.embed σ Q + C c) :
    mlBlockedSpdpRank B κ ℓ (piPhi σ P) = mlBlockedSpdpRank B κ ℓ (CoupledSheetPoly.embed σ Q) ∧
    mlBlockedSpdpRank B κ ℓ (CoupledSheetPoly.embed σ Q) ≤ mlBlockedSpdpRank B κ ℓ P := by
  have heq : mlBlockedSpdpRank B κ ℓ (piPhi σ P) =
      mlBlockedSpdpRank B κ ℓ (CoupledSheetPoly.embed σ Q) := by
    rw [hExt]; exact GodMoveReal.mlBlockedSpdpRank_add_const B κ ℓ hκ _ c
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact piPhi_isRankMonotoneGauge σ B κ ℓ P

/-- **G3 obstruction, general M-blind form.** Suppose the extraction `Π_Φ` produces, for every
machine, the same sheet `Q_Φ` up to an additive constant (witness-free, template-generated). If
the extracted object of ONE machine `Msol` meets `bound`, then EVERY machine's compiled polynomial
(and its extraction) meets `bound`. -/
theorem g3_fails_of_mblind_extraction {Inst : Type*}
    (sheet : Inst → CoupledSheetPoly σ) (compile : DTM → Inst → PMnPoly σ)
    (hBlind : ∀ M Φ, ∃ c : ℚ, piPhi σ (compile M Φ) = CoupledSheetPoly.embed σ (sheet Φ) + C c)
    (B : SPDP.BlockPartition σ.total) (κ ℓ : ℕ) (hκ : 1 ≤ κ)
    (Msol : DTM) (Φ : Inst) (bound : ℕ)
    (hNP : bound ≤ mlBlockedSpdpRank B κ ℓ (piPhi σ (compile Msol Φ))) (M : DTM) :
    bound ≤ mlBlockedSpdpRank B κ ℓ (piPhi σ (compile M Φ)) ∧
    bound ≤ mlBlockedSpdpRank B κ ℓ (compile M Φ) := by
  obtain ⟨c₁, h₁⟩ := hBlind Msol Φ
  obtain ⟨c₂, h₂⟩ := hBlind M Φ
  have hs := (rank_of_extraction B κ ℓ hκ _ _ c₁ h₁).1
  have hm := rank_of_extraction B κ ℓ hκ _ _ c₂ h₂
  rw [hs] at hNP
  exact ⟨hm.1 ▸ hNP, le_trans hNP hm.2⟩

/-- The always-accept instance: `PassesG3` and its extracted form both FAIL. -/
theorem not_passesG3_of_mblind_extraction {Inst : Type*}
    (sheet : Inst → CoupledSheetPoly σ) (compile : DTM → Inst → PMnPoly σ)
    (hBlind : ∀ M Φ, ∃ c : ℚ, piPhi σ (compile M Φ) = CoupledSheetPoly.embed σ (sheet Φ) + C c)
    (B : SPDP.BlockPartition σ.total) (κ ℓ : ℕ) (hκ : 1 ≤ κ)
    (Msol : DTM) (Φ : Inst) (bound : ℕ)
    (hNP : bound ≤ mlBlockedSpdpRank B κ ℓ (piPhi σ (compile Msol Φ))) :
    ¬ PassesG3 B κ ℓ bound (compile alwaysAccept Φ) ∧
    ¬ PassesG3Extracted B κ ℓ bound (piPhi σ) (compile alwaysAccept Φ) := by
  have h := g3_fails_of_mblind_extraction sheet compile hBlind B κ ℓ hκ Msol Φ bound hNP alwaysAccept
  unfold PassesG3 PassesG3Extracted
  omega

/-- **Additive form (paper Lemma 222 + Lemma 123 + Thm 223(iii)).**
`P_{M,Φ} = embed(Q×_Φ) + R_{M,Φ}(v)`: the clause sheet depends only on Φ, the machine only on the
v-variables. Then the extraction is M-blind. -/
theorem mblind_of_additive {Inst : Type*}
    (sheet : Inst → CoupledSheetPoly σ) (compile : DTM → Inst → PMnPoly σ)
    (hShape : ∀ M Φ, ∃ R : MvPolynomial (Fin σ.numV) ℚ,
      compile M Φ = CoupledSheetPoly.embed σ (sheet Φ) + rename σ.inlV R) :
    ∀ M Φ, ∃ c : ℚ, piPhi σ (compile M Φ) = CoupledSheetPoly.embed σ (sheet Φ) + C c := by
  intro M Φ
  obtain ⟨R, hR⟩ := hShape M Φ
  refine ⟨constantCoeff R, ?_⟩
  rw [hR, map_add, piPhi_embed_eq, piPhi_rename_inlV]

/-- **Multiplicative form (Lean `templatePMn`).** `P_{M,Φ} = embed(Q_Φ) · F_{M,Φ}` with
`Π_Φ F_{M,Φ} = 1`. Then the extraction is M-blind. -/
theorem mblind_of_multiplicative {Inst : Type*}
    (sheet : Inst → CoupledSheetPoly σ) (compile : DTM → Inst → PMnPoly σ)
    (hShape : ∀ M Φ, ∃ F : PMnPoly σ,
      compile M Φ = CoupledSheetPoly.embed σ (sheet Φ) * F ∧ piPhi σ F = 1) :
    ∀ M Φ, ∃ c : ℚ, piPhi σ (compile M Φ) = CoupledSheetPoly.embed σ (sheet Φ) + C c := by
  intro M Φ
  obtain ⟨F, hF, h1⟩ := hShape M Φ
  refine ⟨0, ?_⟩
  rw [hF, piPhi_embed_mul, h1, mul_one, C_0, add_zero]

/-- **Main G3 theorem, additive (Lemma 222/123) form.** -/
theorem g3_fails_additive {Inst : Type*}
    (sheet : Inst → CoupledSheetPoly σ) (compile : DTM → Inst → PMnPoly σ)
    (hShape : ∀ M Φ, ∃ R : MvPolynomial (Fin σ.numV) ℚ,
      compile M Φ = CoupledSheetPoly.embed σ (sheet Φ) + rename σ.inlV R)
    (B : SPDP.BlockPartition σ.total) (κ ℓ : ℕ) (hκ : 1 ≤ κ)
    (Msol : DTM) (Φ : Inst) (bound : ℕ)
    (hNP : bound ≤ mlBlockedSpdpRank B κ ℓ (piPhi σ (compile Msol Φ))) :
    ¬ PassesG3 B κ ℓ bound (compile alwaysAccept Φ) ∧
    ¬ PassesG3Extracted B κ ℓ bound (piPhi σ) (compile alwaysAccept Φ) :=
  not_passesG3_of_mblind_extraction sheet compile (mblind_of_additive sheet compile hShape)
    B κ ℓ hκ Msol Φ bound hNP

/-- **Main G3 theorem, multiplicative (`templatePMn`) form.** -/
theorem g3_fails_multiplicative {Inst : Type*}
    (sheet : Inst → CoupledSheetPoly σ) (compile : DTM → Inst → PMnPoly σ)
    (hShape : ∀ M Φ, ∃ F : PMnPoly σ,
      compile M Φ = CoupledSheetPoly.embed σ (sheet Φ) * F ∧ piPhi σ F = 1)
    (B : SPDP.BlockPartition σ.total) (κ ℓ : ℕ) (hκ : 1 ≤ κ)
    (Msol : DTM) (Φ : Inst) (bound : ℕ)
    (hNP : bound ≤ mlBlockedSpdpRank B κ ℓ (piPhi σ (compile Msol Φ))) :
    ¬ PassesG3 B κ ℓ bound (compile alwaysAccept Φ) ∧
    ¬ PassesG3Extracted B κ ℓ bound (piPhi σ) (compile alwaysAccept Φ) :=
  not_passesG3_of_mblind_extraction sheet compile (mblind_of_multiplicative sheet compile hShape)
    B κ ℓ hκ Msol Φ bound hNP

/-- `templatePMn` satisfies the multiplicative shape (with `F = 1 + tableauBoolProduct`). -/
theorem templatePMn_shape {Inst : Type*} (sheet : Inst → CoupledSheetPoly σ) (hV : 0 < σ.numV) :
    ∀ (M : DTM) (Φ : Inst), ∃ F : PMnPoly σ,
      (fun (_ : DTM) Φ => templatePMn σ (sheet Φ)) M Φ = CoupledSheetPoly.embed σ (sheet Φ) * F ∧
      piPhi σ F = 1 := by
  intro M Φ
  refine ⟨1 + tableauBoolProduct σ, rfl, ?_⟩
  have h := piPhi_embed_mul_one_plus_tableauBool σ (1 : CoupledSheetPoly σ) hV
  rw [piPhi_embed_mul] at h
  have he : CoupledSheetPoly.embed σ (1 : CoupledSheetPoly σ) = 1 := by
    unfold CoupledSheetPoly.embed; exact map_one _
  rw [he, one_mul] at h
  exact h

end Core

section RouteB
open GlobalGodMoveGauge PaperFaithfulSeparation

/-- **Route-B form (Theorem 207 interfaces), witness-free sheet.** If the always-accept machine's
extraction produces the same coupled sheet as a solver's (witness-free, Thm 223(iii)) and the
extraction is rank-monotone for it (Lemma 205/221 is a property of `T_Φ`, valid for every input
polynomial), then the solver's NP-side bound refutes the P-side bound for always-accept. -/
theorem routeB_witnessFree_not_PSide (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (hnsA : alwaysAccept.numStates ≤ n)
    (Msol : DTM) (htbS : Msol.timeBound ≤ 4) (hnsS : Msol.numStates ≤ n)
    (Eacc : Theorem207Extraction alwaysAccept n hn hn2 (by decide) hnsA)
    (Esol : Theorem207Extraction Msol n hn hn2 htbS hnsS)
    (hWF : Eacc.coupledSheet = Esol.coupledSheet)
    (hMono : Theorem207ExtractionRankMonotone alwaysAccept n hn hn2 (by decide) hnsA Eacc)
    (hNP : Theorem207NPSideLowerBound Msol n hn hn2 htbS hnsS Esol) :
    ¬ Theorem207PSideUpperBound alwaysAccept n hn hn2 (by decide) hnsA Eacc := by
  intro hP
  have h1 := hNP.sheet_np_side_lower_bound
  rw [← hWF] at h1
  have h2 : Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank (cook_levin_compilation alwaysAccept n hn2 (by decide) hnsA).partition
        (Nat.log 2 n) (Nat.log 2 n) Eacc.coupledSheet := h1
  have h3 := hMono.extraction_rank_monotone
  have h4 := hP.compiled_p_side_bound
  have h5 := arithmetic_gap_2pow804 n hn
  omega

end RouteB

section NonVacuity
open PaperFaithfulSeparation

variable (n : ℕ) (hn : n ≥ 2 ^ 804)

theorem two_le_of_big {n : ℕ} (hn : n ≥ 2 ^ 804) : n ≥ 2 := by
  have : (2 : ℕ) ≤ 2 ^ 804 := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- Concrete split, partition and sheet (the repo's kernel-checked NP-side object). -/
abbrev σ0 (n : ℕ) : UVSplit := cookLevinUVSplit alwaysAccept n

theorem σ0_numV_pos (n : ℕ) : 0 < (σ0 n).numV := by
  show 0 < (let S := tapeSize alwaysAccept n; S * S + S * alwaysAccept.numStates + S * S)
  simp only [tapeSize]
  positivity

noncomputable def Q0 : CoupledSheetPoly (σ0 n) :=
  cookLevinQ alwaysAccept n (two_le_of_big hn) (by decide) (by show 3 ≤ n; have := two_le_of_big hn; omega)

noncomputable def B0 : SPDP.BlockPartition (σ0 n).total :=
  extendedCookLevinPartition alwaysAccept n (two_le_of_big hn)

/-- A machine-DEPENDENT computation part in the v-variables (here: numStates · v₀ + #steps). -/
noncomputable def R0 (M : DTM) : MvPolynomial (Fin (σ0 n).numV) ℚ :=
  C (M.numStates : ℚ) * X ⟨0, σ0_numV_pos n⟩ + C (timeSteps M n : ℚ)

/-- Concrete additive architecture `P_M = embed(Q0) + R0_M(v)`. -/
noncomputable def compileAdd (M : DTM) (_ : Unit) : PMnPoly (σ0 n) :=
  CoupledSheetPoly.embed (σ0 n) (Q0 n hn) + rename (σ0 n).inlV (R0 n M)

/-- Hypothesis `hShape` of `g3_fails_additive` holds for the concrete architecture. -/
theorem concrete_shape : ∀ (M : DTM) (Φ : Unit), ∃ R : MvPolynomial (Fin (σ0 n).numV) ℚ,
    compileAdd n hn M Φ = CoupledSheetPoly.embed (σ0 n) ((fun _ => Q0 n hn) Φ) + rename (σ0 n).inlV R :=
  fun M _ => ⟨R0 n M, rfl⟩

/-- Hypothesis `hNP` holds for the concrete architecture, for ANY solver machine `Msol`
(kernel-checked NP-side bound of the repo, at κ = ℓ = log₂ n). -/
theorem concrete_hNP (Msol : DTM) :
    npBound n ≤ mlBlockedSpdpRank (B0 n hn) (Nat.log 2 n) (Nat.log 2 n)
      (piPhi (σ0 n) (compileAdd n hn Msol ())) := by
  have hκ : 1 ≤ Nat.log 2 n := by
    have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn; omega
  obtain ⟨c, hc⟩ := mblind_of_additive (fun _ => Q0 n hn) (compileAdd n hn) (concrete_shape n hn) Msol ()
  rw [(rank_of_extraction (B0 n hn) _ (Nat.log 2 n) hκ _ _ c hc).1]
  refine le_trans ?_ (embed_rank_preservation (σ0 n) (B0 n hn) _ _ (Q0 n hn))
  exact cookLevinQ_rank_ge alwaysAccept n hn (by decide) (by show 3 ≤ n; have := two_le_of_big hn; omega)

/-- Hence, concretely: the always-accept machine fails G3 in the concrete architecture. -/
theorem concrete_not_passesG3 :
    ¬ PassesG3 (B0 n hn) (Nat.log 2 n) (Nat.log 2 n) (npBound n) (compileAdd n hn alwaysAccept ()) ∧
    ¬ PassesG3Extracted (B0 n hn) (Nat.log 2 n) (Nat.log 2 n) (npBound n) (piPhi (σ0 n))
      (compileAdd n hn alwaysAccept ()) := by
  have hκ : 1 ≤ Nat.log 2 n := by
    have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn; omega
  exact g3_fails_additive (fun _ => Q0 n hn) (compileAdd n hn) (concrete_shape n hn) (B0 n hn)
    _ _ hκ alwaysAccept () (npBound n) (concrete_hNP n hn alwaysAccept)

/-- The concrete `templatePMn` architecture also satisfies the multiplicative hypotheses. -/
theorem concrete_template_not_passesG3 :
    ¬ PassesG3 (B0 n hn) (Nat.log 2 n) (Nat.log 2 n) (npBound n) (templatePMn (σ0 n) (Q0 n hn)) := by
  have hκ : 1 ≤ Nat.log 2 n := by
    have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn; omega
  have hNP : npBound n ≤ mlBlockedSpdpRank (B0 n hn) (Nat.log 2 n) (Nat.log 2 n)
      (piPhi (σ0 n) ((fun (_ : DTM) (_ : Unit) => templatePMn (σ0 n) (Q0 n hn)) alwaysAccept ())) := by
    show npBound n ≤ mlBlockedSpdpRank (B0 n hn) _ _ (piPhi (σ0 n) (templatePMn (σ0 n) (Q0 n hn)))
    rw [piPhi_templatePMn (σ0 n) (Q0 n hn) (σ0_numV_pos n)]
    refine le_trans ?_ (embed_rank_preservation (σ0 n) (B0 n hn) _ _ (Q0 n hn))
    exact cookLevinQ_rank_ge alwaysAccept n hn (by decide) (by show 3 ≤ n; have := two_le_of_big hn; omega)
  exact (g3_fails_multiplicative (fun (_ : Unit) => Q0 n hn)
    (fun (_ : DTM) (_ : Unit) => templatePMn (σ0 n) (Q0 n hn))
    (templatePMn_shape (fun _ => Q0 n hn) (σ0_numV_pos n)) (B0 n hn) _ _ hκ alwaysAccept () (npBound n)
    hNP).1

end NonVacuity

section AnswerView
variable {σ : UVSplit}

/-- The 3-state machine that rejects on its first step. -/
def alwaysReject : DTM where
  numStates := 3
  hStates := by decide
  transition := fun _ bit => (2, bit, true)
  timeBound := 1
  hTimeBound := by decide

/-- **Residual loophole, closed for answer-only dependence.** If the extracted object depends on
the machine only through some view `view M Φ` (e.g. M's accept/reject answer on Φ, or its run on Φ
reduced to its answer), then for each instance one of the two constant machines shares the solver's
view, hence the solver's extracted rank. (Elementary; recorded so that any repair has to make
`T_Φ(P_M)` depend on M through information that no constant-answer machine shares with a solver.) -/
theorem g3_fails_of_answer_view {Inst : Type*}
    (ext : DTM → Inst → PMnPoly σ) (ans : DTM → Inst → Bool)
    (hView : ∀ M M' Φ, ans M Φ = ans M' Φ → ext M Φ = ext M' Φ)
    (Φ : Inst) (hacc : ans alwaysAccept Φ = true) (hrej : ans alwaysReject Φ = false)
    (B : SPDP.BlockPartition σ.total) (κ ℓ bound : ℕ) (Msol : DTM)
    (hNP : bound ≤ mlBlockedSpdpRank B κ ℓ (ext Msol Φ)) :
    bound ≤ mlBlockedSpdpRank B κ ℓ (ext alwaysAccept Φ) ∨
    bound ≤ mlBlockedSpdpRank B κ ℓ (ext alwaysReject Φ) := by
  cases h : ans Msol Φ
  · right; rw [hView alwaysReject Msol Φ (by rw [hrej, h])]; exact hNP
  · left; rw [hView alwaysAccept Msol Φ (by rw [hacc, h])]; exact hNP

end AnswerView

section RouteBNonVacuity
open GlobalGodMoveGauge PaperFaithfulSeparation

/-- Route-B non-vacuity: at every n ≥ 2^804 there are extractions for always-accept and for a
DIFFERENT machine (always-reject) satisfying all hypotheses of `routeB_witnessFree_not_PSide`
(same sheet, rank-monotone, NP-side bound), using the repo's kernel-checked NP-side bound. -/
theorem routeB_hypotheses_satisfiable (n : ℕ) (hn : n ≥ 2 ^ 804) :
    ∃ (Eacc : Theorem207Extraction alwaysAccept n hn (two_le_of_big hn) (by decide)
        (by show 3 ≤ n; have := two_le_of_big hn; omega))
      (Erej : Theorem207Extraction alwaysReject n hn (two_le_of_big hn) (by decide)
        (by show 3 ≤ n; have := two_le_of_big hn; omega)),
      Eacc.coupledSheet = Erej.coupledSheet ∧
      Theorem207ExtractionRankMonotone alwaysAccept n hn (two_le_of_big hn) (by decide)
        (by show 3 ≤ n; have := two_le_of_big hn; omega) Eacc ∧
      Theorem207NPSideLowerBound alwaysReject n hn (two_le_of_big hn) (by decide)
        (by show 3 ≤ n; have := two_le_of_big hn; omega) Erej := by
  have h3 : alwaysAccept.numStates ≤ n := by show 3 ≤ n; have := two_le_of_big hn; omega
  have h3' : alwaysReject.numStates ≤ n := by show 3 ≤ n; have := two_le_of_big hn; omega
  let q := compiledPoly (cook_levin_compilation alwaysAccept n (two_le_of_big hn) (by decide) h3)
  refine ⟨⟨q, q⟩, ⟨q, q⟩, rfl, ⟨le_refl _⟩, ⟨?_⟩⟩
  exact GodMoveReal.compiled_np_lower_bound_any_dtm alwaysAccept n hn (by decide) h3

end RouteBNonVacuity
end GapG3

#print axioms GapG3.passesG3Extracted_of_passesG3
#print axioms GapG3.piPhi_rename_inlV
#print axioms GapG3.rank_of_extraction
#print axioms GapG3.g3_fails_of_mblind_extraction
#print axioms GapG3.not_passesG3_of_mblind_extraction
#print axioms GapG3.mblind_of_additive
#print axioms GapG3.mblind_of_multiplicative
#print axioms GapG3.g3_fails_additive
#print axioms GapG3.g3_fails_multiplicative
#print axioms GapG3.templatePMn_shape
#print axioms GapG3.routeB_witnessFree_not_PSide
#print axioms GapG3.concrete_hNP
#print axioms GapG3.concrete_not_passesG3
#print axioms GapG3.concrete_template_not_passesG3
#print axioms GapG3.g3_fails_of_answer_view
#print axioms GapG3.routeB_hypotheses_satisfiable
