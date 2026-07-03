import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTargetHarness

/-!
# N-Frame: the GodMove principle — specified, beamed, and its first candidate eliminated

HAL's cleaned form of the GodMove: *a new lower-bound principle — a boundary/pressure invariant with a proved transfer
into circuit energy — that certifies super-polynomial `cbudget` for SAT*.  Not an axiom.  This file makes that testable:
it specifies the principle precisely, proves the beam (a genuine GodMove principle closes the conditional theorem's open
premise), proves a **third admissibility constraint** beyond the harness's two, and formally **eliminates the first
candidate pressure** — the SPDP-degree proxy of the p-vs-np1 paper.

  `GodMovePressure Φ g F` — the specification: a pressure invariant `Φ`, a monotone certification scale `g`, a **proved
        transfer** `g (Φ f) ≤ cbudget f` (pressure lower-bounds energy, for *every* `f`), and high pressure on the family.
  `godmove_gives_target` — **PROVED, the beam**: any genuine GodMove principle yields `NFrameCircuitLowerBoundTarget F`,
        closing the conditional `P ≠ NP` theorem's sole open premise.
  `pressure_dominated_by_easy` — **PROVED, constraint #3**: if any *easy* function `e` pressure-dominates `f`, the
        certified bound at `f` is capped by `cbudget e`.  So an admissible pressure must strictly order the target above
        **every** easy function — the hardness information must live in the invariant itself, not the transfer.
  `boolPressure` / `boolPressure_fullAnd` / `degree_pressure_capped` — **PROVED, the elimination**: the SPDP-degree
        pressure (`NFrameComplexity` of the field lift) saturates at `n`, and the *easy* full-AND attains that maximum
        with `cbudget ≤ 2n+1`; hence **every** monotone transfer through the degree pressure certifies at most `2n+1` —
        linear — for every function.  `degree_pressure_not_godmove`: it cannot even certify a quadratic bound.

## Honest scope — a well-posed target, a dead first candidate, and the surviving window

Together with the harness, an admissible GodMove pressure must now survive **three proven constraints**: (1) non-circular
(not `cbudget` restated — `cbudget_gap_iff_not_sizeClass`), (2) anti-natural (not constructive-and-large, under RR —
`no_natural_method`), (3) **not dominated at the top by easy functions** (`pressure_dominated_by_easy`) — which the
SPDP-degree proxy fails at the full-AND, formally eliminating pillar-3's naive pressure as the GodMove.  The surviving
window is sharp: a pressure that is anti-natural, non-circular, and already orders SAT strictly above all easy functions,
with a proved transfer into `cbudget`.  **No such invariant is known**; constructing one *is* the breakthrough, and this
file supplies the test harness it would have to pass, not the invariant.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.Layer4 (sqfEval boolToField)
open PallLean.Paper93.DeepMath.PathB.NFrameACC0 (NFrameComplexity
  nframeComplexity_le_of_mem_span mem_sqfSpan_n nframeComplexity_sqfEval_univ_eq)

variable {n : ℕ}

/-! ### The specification and its beam -/

/-- **The GodMove principle, specified.**  A pressure invariant `Φ`, a monotone certification scale `g`, a proved
transfer (pressure lower-bounds circuit energy, for every function), and high pressure on the target family. -/
def GodMovePressure (Φ : ∀ n : ℕ, ((Fin n → Bool) → Bool) → ℕ) (g : ℕ → ℕ)
    (F : ∀ n : ℕ, (Fin n → Bool) → Bool) : Prop :=
  (∀ (n : ℕ) (f : (Fin n → Bool) → Bool), g (Φ n f) ≤ cbudget f) ∧
    (∀ k, ∃ n, n ^ k + k < g (Φ n (F n)))

/-- **The beam (proved)**: a genuine GodMove principle yields the circuit lower-bound target — closing the conditional
`P ≠ NP` theorem's sole open premise. -/
theorem godmove_gives_target {Φ : ∀ n : ℕ, ((Fin n → Bool) → Bool) → ℕ} {g : ℕ → ℕ}
    {F : ∀ n : ℕ, (Fin n → Bool) → Bool} (h : GodMovePressure Φ g F) :
    NFrameCircuitLowerBoundTarget F := by
  intro k
  obtain ⟨m, hm⟩ := h.2 k
  exact ⟨m, lt_of_lt_of_le hm (h.1 m (F m))⟩

/-- **Constraint #3 (proved)**: if an easy function `e` pressure-dominates `f`, the certified bound at `f` is capped by
`cbudget e`.  An admissible pressure must order the target strictly above every easy function. -/
theorem pressure_dominated_by_easy {Φ : ((Fin n → Bool) → Bool) → ℕ} {g : ℕ → ℕ}
    (hg : Monotone g) (transfer : ∀ f : (Fin n → Bool) → Bool, g (Φ f) ≤ cbudget f)
    {f e : (Fin n → Bool) → Bool} (hdom : Φ f ≤ Φ e) :
    g (Φ f) ≤ cbudget e :=
  le_trans (hg hdom) (transfer e)

/-! ### The first candidate, eliminated: the SPDP-degree pressure -/

variable (F : Type*) [Field F]

/-- The SPDP-degree pressure of a Boolean function: the `NFrameComplexity` (minimal monoAND-span degree — the repo's
SPDP-rank proxy) of its field lift.  This is pillar 3's pressure candidate, made precise. -/
noncomputable def boolPressure (f : (Fin n → Bool) → Bool) : ℕ :=
  NFrameComplexity F (fun x => boolToField F (f x))

/-- The field lift of the full-AND is the top monomial. -/
theorem boolToField_fullAnd [Fintype F] [DecidableEq F] (x : Fin n → Bool) :
    boolToField F (fullAndFn n x) = sqfEval F (Finset.univ : Finset (Fin n)) x := by
  have hbf : ∀ b : Bool, boolToField F b = if b = true then (1 : F) else 0 := fun b => by
    cases b <;> rfl
  have hfold : ∀ l : List (Fin n),
      (l.foldr (fun i acc => x i && acc) true = true) ↔ (∀ i ∈ l, x i = true) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp [Bool.and_eq_true, ih]
  have hrhs : sqfEval F (Finset.univ : Finset (Fin n)) x
      = if (∀ i : Fin n, x i = true) then (1 : F) else 0 := by
    show (∏ i, boolToField F (x i)) = _
    by_cases h : ∀ i : Fin n, x i = true
    · rw [if_pos h]
      rw [Finset.prod_congr rfl (fun i _ => by rw [h i] : ∀ i ∈ Finset.univ,
        boolToField F (x i) = boolToField F true)]
      simp [hbf]
    · rw [if_neg h]
      push_neg at h
      obtain ⟨i, hi⟩ := h
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      have hxf : x i = false := by
        cases hx : x i
        · rfl
        · exact absurd hx hi
      rw [hxf]
      rfl
  rw [hrhs, hbf]
  by_cases h : ∀ i : Fin n, x i = true
  · have hT : fullAndFn n x = true := (hfold (List.finRange n)).mpr (fun i _ => h i)
    rw [if_pos h, if_pos hT]
  · have hF' : ¬ fullAndFn n x = true := fun hc =>
      h (fun i => (hfold (List.finRange n)).mp hc i (List.mem_finRange i))
    rw [if_neg h, if_neg hF']

/-- **The degree pressure saturates linearly (proved)**: `boolPressure f ≤ n` for every `f`. -/
theorem boolPressure_le [Fintype F] [DecidableEq F] (f : (Fin n → Bool) → Bool) :
    boolPressure F f ≤ n :=
  nframeComplexity_le_of_mem_span (mem_sqfSpan_n _)

/-- **The easy full-AND attains the maximum pressure (proved)**: `boolPressure (fullAnd) = n`. -/
theorem boolPressure_fullAnd [Fintype F] [DecidableEq F] (hn : 0 < n) :
    boolPressure F (fullAndFn n) = n := by
  unfold boolPressure
  rw [show (fun x => boolToField F (fullAndFn n x))
      = sqfEval F (Finset.univ : Finset (Fin n)) from funext (boolToField_fullAnd F)]
  exact nframeComplexity_sqfEval_univ_eq hn

/-- The easy full-AND has linear circuit energy. -/
theorem cbudget_fullAnd_le : cbudget (fullAndFn n) ≤ 2 * n + 1 :=
  le_trans (cbudget_le_budget _) budget_fullAnd_le

/-- **The elimination (proved)**: every monotone transfer through the SPDP-degree pressure certifies at most `2n+1` —
*linear* — for **every** function: the pressure saturates at `n`, the easy full-AND attains that maximum, and its energy
is `≤ 2n+1`.  Pillar 3's degree pressure cannot be the GodMove. -/
theorem degree_pressure_capped [Fintype F] [DecidableEq F] (hn : 0 < n) (g : ℕ → ℕ)
    (hg : Monotone g)
    (transfer : ∀ f : (Fin n → Bool) → Bool, g (boolPressure F f) ≤ cbudget f)
    (f : (Fin n → Bool) → Bool) :
    g (boolPressure F f) ≤ 2 * n + 1 :=
  calc g (boolPressure F f) ≤ g n := hg (boolPressure_le F f)
    _ = g (boolPressure F (fullAndFn n)) := by rw [boolPressure_fullAnd F hn]
    _ ≤ cbudget (fullAndFn n) := transfer _
    _ ≤ 2 * n + 1 := cbudget_fullAnd_le

/-- **Not even quadratic (proved)**: for `n ≥ 2`, no monotone degree-pressure transfer certifies `n² + 2 < cbudget f` at
any `f` — the degree pressure falls short of the target at its second exponent, let alone super-polynomially. -/
theorem degree_pressure_not_godmove [Fintype F] [DecidableEq F] (hn : 2 ≤ n) (g : ℕ → ℕ)
    (hg : Monotone g)
    (transfer : ∀ f : (Fin n → Bool) → Bool, g (boolPressure F f) ≤ cbudget f)
    (f : (Fin n → Bool) → Bool) :
    ¬ (n ^ 2 + 2 < g (boolPressure F f)) := by
  have hcap := degree_pressure_capped F (by omega) g hg transfer f
  nlinarith

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.godmove_gives_target
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.pressure_dominated_by_easy
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.boolPressure_fullAnd
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.degree_pressure_capped
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.degree_pressure_not_godmove
