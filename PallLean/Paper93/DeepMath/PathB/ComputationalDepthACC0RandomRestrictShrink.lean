import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RestrictShrink
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SatFirstMoment

/-!
# Random-restriction collapse of the deduplicated boundary

`…ACC0RestrictShrink` proved the *single-variable* restriction `subst1` shrinks the deduplicated boundary `varSupp`.
This file iterates it to a **multi-variable restriction** `restrList` (a list of `(variable, value)` fixings) and
proves the **random-restriction collapse** at the deduplicated-boundary level: under the `p`-biased restriction
(each variable kept *live* with probability `p`), the surviving deduplicated boundary `varSupp C ∩ L` shrinks to
`p · |varSupp C|` in expectation, and a low-boundary restriction provably exists.

The multi-variable restriction is just iterated `subst1`, so `eval`/`varSupp`/`modOcc`/`ModsPos` all lift from the
single-variable lemmas for free (no re-proof of the `MOD` target-shift).  The probabilistic part reuses the existing
`p`-biased measure (`Exp`, `Pr`, `markov`, `exp_sum`, `exp_indicator_eq_survProb`).

## What is proved (clean axioms, no `sorry`)

* `restrList` / `applyRestr` — multi-variable restriction (iterated `subst1`) and its semantic assignment.
* `eval_restrList` — `eval (restrList C l) x = eval C (applyRestr l x)` (the restriction is genuine).
* `varSupp_restrList` / `modOcc_restrList_le` / `ModsPos_restrList` — boundary monotone under multi-restriction.
* `fixedListOf` / `varSupp_restr_compl_subset` — fixing the complement of a live set `L` leaves
  `varSupp (restrList …) ⊆ varSupp C ∩ L` (only live variables survive).
* `exp_liveBoundary_eq` — **`Exp p (|varSupp C ∩ L|) = p · |varSupp C|`** (proportional collapse in expectation).
* `exists_small_liveBoundary` — a live set `L` with `|varSupp C ∩ L| < a` exists once `p·|varSupp C| < a`.
* `dedup_restriction_collapses` — **headline**: there is a live set `L` such that, *for every* assignment of the
  fixed variables, the restricted circuit's deduplicated boundary is `< a` — the random-restriction collapse.

## Honest scope

This is the *proportional* collapse: `varSupp` shrinks to a `p`-fraction because fewer variables are free — a
first-moment fact, not a switching lemma.  The boundary collapse does **not** by itself give a SAT speedup: deciding
`SAT(C)` still branches over the `2^{#fixed}` assignments of the fixed variables, and `2^{#fixed} · 2^{p|vs|}` recovers
`2^{|vs|}` (no asymptotic gain alone).  The deep, still-open content is *super*-proportional collapse — that a random
restriction makes the *function* (not just the syntactic support) depend on far fewer variables, i.e. the high-moment
Håstad switching that kills an `AC⁰` subtree to a constant with high probability.  Still the cell/observer model;
nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictShrink

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ExtractObserver
open PallLean.Paper93.DeepMath.PathB.ACC0DedupShrink
open PallLean.Paper93.DeepMath.PathB.ACC0RestrictShrink
open PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingProb
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingChebyshev
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline
open PallLean.Paper93.DeepMath.PathB.ACC0SatFirstMoment

variable {n : ℕ}

/-! ## Multi-variable restriction (iterated `subst1`) -/

/-- Restrict a circuit by a list of `(variable, value)` fixings, applied left to right. -/
def restrList (C : ACC0Circuit n) : List (Fin n × Bool) → ACC0Circuit n
  | [] => C
  | p :: rest => restrList (subst1 C p.1 p.2) rest

/-- The semantic assignment the restriction list applies to an input. -/
def applyRestr : List (Fin n × Bool) → (Fin n → Bool) → (Fin n → Bool)
  | [], x => x
  | p :: rest, x => Function.update (applyRestr rest x) p.1 p.2

/-- **The multi-variable restriction is genuine (proved): `eval (restrList C l) x = eval C (applyRestr l x)`.** -/
theorem eval_restrList :
    ∀ (l : List (Fin n × Bool)) (C : ACC0Circuit n) (x : Fin n → Bool),
      eval (restrList C l) x = eval C (applyRestr l x) := by
  intro l
  induction l with
  | nil => intro C x; rfl
  | cons p rest ih =>
      intro C x
      show eval (restrList (subst1 C p.1 p.2) rest) x = eval C (applyRestr (p :: rest) x)
      rw [ih (subst1 C p.1 p.2) x, eval_subst1 p.1 p.2 C (applyRestr rest x)]
      rfl

/-- **The deduplicated boundary drops to `varSupp C \ (fixed variables)` (proved).** -/
theorem varSupp_restrList :
    ∀ (l : List (Fin n × Bool)) (C : ACC0Circuit n),
      varSupp (restrList C l) ⊆ varSupp C \ (l.map Prod.fst).toFinset := by
  intro l
  induction l with
  | nil => intro C; simp [restrList]
  | cons p rest ih =>
      intro C
      show varSupp (restrList (subst1 C p.1 p.2) rest) ⊆ varSupp C \ ((p :: rest).map Prod.fst).toFinset
      calc varSupp (restrList (subst1 C p.1 p.2) rest)
          ⊆ varSupp (subst1 C p.1 p.2) \ (rest.map Prod.fst).toFinset := ih (subst1 C p.1 p.2)
        _ ⊆ (varSupp C).erase p.1 \ (rest.map Prod.fst).toFinset :=
              Finset.sdiff_subset_sdiff (varSupp_subst1_subset p.1 p.2 C) (Finset.Subset.refl _)
        _ = varSupp C \ insert p.1 (rest.map Prod.fst).toFinset := by
              rw [Finset.erase_sdiff_comm, ← Finset.sdiff_insert]
        _ = varSupp C \ ((p :: rest).map Prod.fst).toFinset := by
              rw [List.map_cons, List.toFinset_cons]

/-- **The `MOD`-residue product does not grow under multi-restriction (proved).** -/
theorem modOcc_restrList_le :
    ∀ (l : List (Fin n × Bool)) (C : ACC0Circuit n), modOcc (restrList C l) ≤ modOcc C := by
  intro l
  induction l with
  | nil => intro C; exact le_refl _
  | cons p rest ih => intro C; exact le_trans (ih (subst1 C p.1 p.2)) (modOcc_subst1_le p.1 p.2 C)

/-- **Positive `MOD` moduli are preserved under multi-restriction (proved).** -/
theorem ModsPos_restrList :
    ∀ (l : List (Fin n × Bool)) (C : ACC0Circuit n), ModsPos C → ModsPos (restrList C l) := by
  intro l
  induction l with
  | nil => intro C h; exact h
  | cons p rest ih => intro C h; exact ih (subst1 C p.1 p.2) (ModsPos_subst1 p.1 p.2 C h)

/-! ## Fixing the complement of a live set -/

/-- The restriction list that fixes every variable in `K` to its value under `β`. -/
noncomputable def fixedListOf (K : Finset (Fin n)) (β : Fin n → Bool) : List (Fin n × Bool) :=
  K.toList.map (fun i => (i, β i))

/-- **The variables fixed by `fixedListOf K β` are exactly `K` (proved).** -/
theorem fixedListOf_fst (K : Finset (Fin n)) (β : Fin n → Bool) :
    ((fixedListOf K β).map Prod.fst).toFinset = K := by
  have h : (fixedListOf K β).map Prod.fst = K.toList := by
    unfold fixedListOf
    rw [List.map_map]
    exact List.map_id K.toList
  rw [h]
  exact K.toList_toFinset

/-- **Fixing the complement of a live set `L` leaves only live variables in the boundary (proved):
`varSupp (restrList C (fixedListOf Lᶜ β)) ⊆ varSupp C ∩ L`.** -/
theorem varSupp_restr_compl_subset (C : ACC0Circuit n) (L : Finset (Fin n)) (β : Fin n → Bool) :
    varSupp (restrList C (fixedListOf Lᶜ β)) ⊆ varSupp C ∩ L := by
  intro z hz
  have hmem := varSupp_restrList (fixedListOf Lᶜ β) C hz
  rw [fixedListOf_fst, Finset.mem_sdiff] at hmem
  rw [Finset.mem_inter]
  refine ⟨hmem.1, ?_⟩
  by_contra hzL
  exact hmem.2 (Finset.mem_compl.mpr hzL)

/-! ## The probabilistic collapse -/

/-- **A single live coordinate is kept with probability `p` (proved).** -/
theorem exp_coord_eq (p : ℝ) (i : Fin n) :
    Exp p (fun L => if i ∈ L then (1 : ℝ) else 0) = p := by
  have h := exp_indicator_eq_survProb p ({i} : Finset (Fin n))
  simp only [Finset.disjoint_singleton_left, not_not] at h
  rw [h]
  unfold survProb
  rw [Finset.card_singleton, pow_one]
  ring

/-- **The deduplicated boundary collapses to `p · |varSupp C|` in expectation (proved).**  Linearity of expectation
over the live-coordinate indicators of `varSupp C`. -/
theorem exp_liveBoundary_eq (p : ℝ) (C : ACC0Circuit n) :
    Exp p (fun L => ((varSupp C ∩ L).card : ℝ)) = p * (varSupp C).card := by
  have hcard : (fun L : Finset (Fin n) => ((varSupp C ∩ L).card : ℝ))
      = (fun L => ∑ i ∈ varSupp C, (if i ∈ L then (1 : ℝ) else 0)) := by
    funext L
    rw [← Finset.filter_mem_eq_inter, Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => by by_cases h : i ∈ L <;> simp [h])
  rw [hcard, exp_sum]
  simp_rw [exp_coord_eq]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-- **A low-boundary restriction exists (proved): if `p·|varSupp C| < a`, some live set leaves a deduplicated
boundary of size `< a`.**  Markov on the boundary size plus the probabilistic method. -/
theorem exists_small_liveBoundary (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (C : ACC0Circuit n)
    (a : ℝ) (ha : 0 < a) (hlt : p * (varSupp C).card < a) :
    ∃ L ∈ (Finset.univ : Finset (Fin n)).powerset, ((varSupp C ∩ L).card : ℝ) < a := by
  have hm := markov p hp0 hp1 (fun L => ((varSupp C ∩ L).card : ℝ)) (fun L => Nat.cast_nonneg _) a
  rw [exp_liveBoundary_eq] at hm
  have hpr : Pr p (fun L => a ≤ ((varSupp C ∩ L).card : ℝ)) < 1 := by
    by_contra hge
    push_neg at hge
    have hkey : a ≤ a * Pr p (fun L => a ≤ ((varSupp C ∩ L).card : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hge ha.le
      rwa [mul_one] at this
    linarith
  obtain ⟨L, hL, hLnot⟩ := exists_of_pr_lt_one p _ hpr
  push_neg at hLnot
  exact ⟨L, hL, hLnot⟩

/-- **Random-restriction collapse at the deduplicated-boundary level (proved).**  There is a live set `L` such that,
*for every* assignment `β` of the fixed (non-live) variables, the restricted circuit `restrList C (fixedListOf Lᶜ β)`
— a genuine restriction of `C` (`eval_restrList`), with `MOD` moduli preserved (`ModsPos_restrList`) and residue
product non-growing (`modOcc_restrList_le`) — has its deduplicated boundary collapsed below `a` (which is just above
the expectation `p·|varSupp C|`). -/
theorem dedup_restriction_collapses (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : ACC0Circuit n) (a : ℝ) (ha : 0 < a) (hlt : p * (varSupp C).card < a) :
    ∃ L ∈ (Finset.univ : Finset (Fin n)).powerset,
      ((varSupp C ∩ L).card : ℝ) < a ∧
      ∀ β : Fin n → Bool, varSupp (restrList C (fixedListOf Lᶜ β)) ⊆ varSupp C ∩ L := by
  obtain ⟨L, hL, hLa⟩ := exists_small_liveBoundary p hp0 hp1 C a ha hlt
  exact ⟨L, hL, hLa, fun β => varSupp_restr_compl_subset C L β⟩

end PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictShrink

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictShrink.eval_restrList
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictShrink.exp_liveBoundary_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictShrink.dedup_restriction_collapses
