import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameEpsBias

/-!
# N-Frame: the induced-matching route — explicit cut-rigidity via expanders

The ε-biased attempt failed on the union-bound-over-cuts barrier.  The induced-matching route
BYPASSES it: edge expansion is a DETERMINISTIC "for every cut" guarantee (proved for explicit
expanders via the spectral gap / Cheeger), so no union bound is needed.  The chain, worked on
paper, with the load-bearing linear-algebra core frozen in Lean:

    d-regular edge-expander M (explicit, e.g. Ramanujan), edge expansion h > 0
  ⟹ every balanced cut (S, Sᶜ) has ≥ h·N/2 crossing edges                          [expansion]
  ⟹ a matching of size ≥ h·N/(2(2d−1))                                             [greedy]
  ⟹ an INDUCED matching of size r ≥ h·N/(2(2d−1)(2d+1)) = Θ(N/d²)                  [greedy: each edge blocks ≤ 2d]
  ⟹ M_{S,Sᶜ} contains an r×r IDENTITY submatrix                                     [induced ⇒ identity]
  ⟹ rank_{F₂}(M_{S,Sᶜ}) ≥ r = Θ(N)   at EVERY balanced cut.                         [this file]

  `bilinSym_add_right` / `bilinSym_sum_right` / `bilinSym_zero_right` — bilinearity of the
        polarization in the direction slot.
  `induced_matching_distinct` — **PROVED, THE CORE**: given an induced matching (`s, t : Fin r
        → Fin N` with the detection matrix `bilinSym A (e_{t k})(e_{s l}) = [k=l]` — the
        identity submatrix of `M = A + Aᵀ`), the `2^r` tuple rows `∑_{k∈T} e_{s k}` are PAIRWISE
        DISTINGUISHED by `qform A` under completions.  So the induced matching gives cut-rank
        `≥ r`, hence `coneExcess ≥ r` via `cut_row_capacity`.

## Honest scope — this RESOLVES explicit cut-rigidity (correcting the earlier claim)

The induced-matching route gives an EXPLICIT cut-rigid `M`: a constant-degree edge-expander
(Ramanujan) has `rank_{F₂}(M_{S,Sᶜ}) = Θ(N)` at EVERY balanced cut, provably, no union bound.
This CORRECTS the earlier "spectral expanders do not suffice" — that was about the spectral-RANK
approach; the COMBINATORIAL edge-expansion → induced-matching → identity-submatrix route works.
Sub-target (a) — explicit every-cut `F₂`-rigid `M` — is thereby resolved, and with the drag it
gives `cbudget(qform) ≥ (2+c)N` for the flat quadratic form over an expander.

The remaining caveat is sub-target (b), UNCHANGED: `qform` is EASY (`O(dN)` gates), so this is a
`(2+c)N` lower bound for an easy function — the method now provably EXCEEDS the block-count cap
on an explicit family, but a hard-function separation still needs cut-rigidity AND hardness
together.  The expander chain's combinatorial steps (edge expansion → induced matching) are
standard graph theory, cited not re-formalized; the linear-algebra core (identity submatrix ⇒
`2^r` distinguished rows) is proved here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameInducedMatch

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameQuadForm
open PallLean.Paper93.DeepMath.PathB.NFrameEpsBias

variable {N : ℕ}

/-- The unit direction at coordinate `c`. -/
def unitDir (c : Fin N) : Fin N → ZMod 2 := fun i => if i = c then 1 else 0

/-- The tuple row for `T`: the sum of unit directions over the matched coordinates in `T`. -/
def rowSum {r : ℕ} (s : Fin r → Fin N) (T : Finset (Fin r)) : Fin N → ZMod 2 :=
  ∑ k ∈ T, unitDir (s k)

theorem bilinSym_zero_right (A : Fin N → Fin N → ZMod 2) (x : Fin N → ZMod 2) :
    bilinSym A x (0 : Fin N → ZMod 2) = 0 := by
  unfold bilinSym
  refine Finset.sum_eq_zero (fun i _ => ?_)
  refine Finset.sum_eq_zero (fun j _ => ?_)
  show A i j * (x i * (0 : Fin N → ZMod 2) j + (0 : Fin N → ZMod 2) i * x j) = 0
  simp

theorem bilinSym_zero_left (A : Fin N → Fin N → ZMod 2) (δ : Fin N → ZMod 2) :
    bilinSym A (0 : Fin N → ZMod 2) δ = 0 := by
  unfold bilinSym
  refine Finset.sum_eq_zero (fun i _ => ?_)
  refine Finset.sum_eq_zero (fun j _ => ?_)
  show A i j * ((0 : Fin N → ZMod 2) i * δ j + δ i * (0 : Fin N → ZMod 2) j) = 0
  simp

theorem bilinSym_add_right (A : Fin N → Fin N → ZMod 2) (x δ δ' : Fin N → ZMod 2) :
    bilinSym A x (δ + δ') = bilinSym A x δ + bilinSym A x δ' := by
  unfold bilinSym
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  show A i j * (x i * (δ + δ') j + (δ + δ') i * x j)
    = A i j * (x i * δ j + δ i * x j) + A i j * (x i * δ' j + δ' i * x j)
  simp only [Pi.add_apply]
  ring

theorem bilinSym_sum_right {ι : Type*} (A : Fin N → Fin N → ZMod 2) (x : Fin N → ZMod 2)
    (T : Finset ι) (f : ι → (Fin N → ZMod 2)) :
    bilinSym A x (∑ k ∈ T, f k) = ∑ k ∈ T, bilinSym A x (f k) := by
  classical
  induction T using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact bilinSym_zero_right A x
  | insert a s hk ih => rw [Finset.sum_insert hk, bilinSym_add_right, ih, Finset.sum_insert hk]

/-- `bilinSym A (e_{t k₀}) (rowSum s T) = if k₀ ∈ T then 1 else 0`, given the identity detection
matrix. -/
theorem bilinSym_rowSum {r : ℕ} (A : Fin N → Fin N → ZMod 2) (s t : Fin r → Fin N)
    (hid : ∀ k l, bilinSym A (unitDir (t k)) (unitDir (s l)) = if k = l then 1 else 0)
    (k₀ : Fin r) (T : Finset (Fin r)) :
    bilinSym A (unitDir (t k₀)) (rowSum s T) = if k₀ ∈ T then 1 else 0 := by
  unfold rowSum
  rw [bilinSym_sum_right]
  rw [Finset.sum_congr rfl (fun k _ => hid k₀ k)]
  exact Finset.sum_ite_eq T k₀ (fun _ => (1 : ZMod 2))

set_option maxHeartbeats 800000 in
/-- **THE CORE (proved)**: an induced matching (identity detection matrix) gives `2^r` pairwise
distinguished tuple rows — so cut-rank `≥ r`. -/
theorem induced_matching_distinct {r : ℕ} (A : Fin N → Fin N → ZMod 2) (s t : Fin r → Fin N)
    (hid : ∀ k l, bilinSym A (unitDir (t k)) (unitDir (s l)) = if k = l then 1 else 0)
    (T T' : Finset (Fin r)) (hne : T ≠ T') :
    ∃ x : Fin N → ZMod 2, qform A (x + rowSum s T) ≠ qform A (x + rowSum s T') := by
  classical
  -- a coordinate where T and T' differ
  obtain ⟨k₀, hk₀⟩ : ∃ k, ¬ (k ∈ T ↔ k ∈ T') := by
    by_contra hc
    push_neg at hc
    exact hne (Finset.ext hc)
  -- the difference direction is detected by e_{t k₀}
  have hbil : bilinSym A (unitDir (t k₀)) (rowSum s T + rowSum s T') = 1 := by
    rw [bilinSym_add_right, bilinSym_rowSum A s t hid k₀ T,
      bilinSym_rowSum A s t hid k₀ T']
    by_cases h1 : k₀ ∈ T <;> by_cases h2 : k₀ ∈ T'
    · exact absurd (iff_of_true h1 h2) hk₀
    · rw [if_pos h1, if_neg h2, add_zero]
    · rw [if_neg h1, if_pos h2, zero_add]
    · exact absurd (iff_of_false h1 h2) hk₀
  -- D(x) = qform A (x + rowSum T) + qform A (x + rowSum T') = bilinSym A x (u+u') + C
  set u := rowSum s T with hu
  set u' := rowSum s T' with hu'
  have hDx : ∀ x : Fin N → ZMod 2,
      qform A (x + u) + qform A (x + u')
        = bilinSym A x (u + u') + (qform A u + qform A u') := by
    intro x
    rw [qform_shift, qform_shift, bilinSym_add_right]
    generalize qform A x = p
    generalize bilinSym A x u = c1
    generalize qform A u = c2
    generalize bilinSym A x u' = c3
    generalize qform A u' = c4
    revert p c1 c2 c3 c4
    decide
  have hne_iff : ∀ a b : ZMod 2, a ≠ b ↔ a + b = 1 := by decide
  by_cases hC0 : qform A u + qform A u' = 0
  · -- D(e) = 1 + C = 1
    refine ⟨unitDir (t k₀), (hne_iff _ _).mpr ?_⟩
    rw [hDx, hbil, hC0, add_zero]
  · -- D(0) = C = 1
    refine ⟨0, (hne_iff _ _).mpr ?_⟩
    rw [hDx, bilinSym_add_right, bilinSym_zero_left, bilinSym_zero_left,
      add_zero, zero_add]
    rcases (by decide : ∀ z : ZMod 2, z ≠ 0 → z = 1) _ hC0 with h
    exact h

end PallLean.Paper93.DeepMath.PathB.NFrameInducedMatch

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInducedMatch.bilinSym_sum_right
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInducedMatch.induced_matching_distinct
