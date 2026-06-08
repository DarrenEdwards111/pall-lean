import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalSound

/-!
# Block-DT model, foundation 35: the exponential parity DNF lower bound (branch only)

The classic depth-2 circuit lower bound for parity, **unconditional** and **without the switching
lemma** — the direct minterm argument:

> A DNF that computes parity needs `≥ 2^(n-1)` terms.

A term satisfied by an odd-parity input must mention *every* variable (else flipping a missing one would
flip parity while still satisfying the term), so it has a unique satisfying input.  Hence distinct
odd-parity inputs force distinct terms, and there are `2^(n-1)` of them (`parity_true_card`).

* `term_covers_of_sat` — a term satisfied by an odd-parity input covers every variable.
* `sat_determines` — a fully-covering term has at most one satisfying input.
* `parity_dnf_size_ge` — **`2^(n-1) ≤ #terms`** for any DNF computing parity.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open DTree

variable {n : ℕ}

/-- A term satisfied by an odd-parity input covers every variable (else flipping a missing variable
flips parity while keeping the term satisfied). -/
theorem term_covers_of_sat {cs : List (Clause n)} (hpar : ∀ x, dnfValue cs x = parity x)
    {T : Clause n} (hT : T ∈ cs) {x : Fin n → Bool}
    (hsat : T.lits.all (fun ℓ => Rung4Literal.eval ℓ x) = true) (hpx : parity x = true) :
    ∀ j, (Rung4Literal.pos j) ∈ T.lits ∨ (Rung4Literal.neg j) ∈ T.lits := by
  intro j
  by_contra hcov
  rw [not_or] at hcov
  -- flipping j keeps T satisfied (j is not a variable of T)
  have hsat' : T.lits.all (fun ℓ => Rung4Literal.eval ℓ (Function.update x j (!x j))) = true := by
    rw [List.all_eq_true] at hsat ⊢
    intro ℓ hℓ
    have hℓj : litVarOf ℓ ≠ j := by
      rintro rfl
      cases ℓ with
      | pos i => exact hcov.1 (by simpa [litVarOf] using hℓ)
      | neg i => exact hcov.2 (by simpa [litVarOf] using hℓ)
    have : Function.update x j (!x j) (litVarOf ℓ) = x (litVarOf ℓ) :=
      Function.update_of_ne hℓj _ _
    rw [eval_eq_of_var _ _ ℓ this]
    exact hsat ℓ hℓ
  have hdnf : dnfValue cs (Function.update x j (!x j)) = true := by
    rw [dnfValue, List.any_eq_true]; exact ⟨T, hT, hsat'⟩
  rw [hpar, parity_flip, hpx] at hdnf
  simp at hdnf

/-- A fully-covering term has at most one satisfying input. -/
theorem sat_determines {T : Clause n}
    (hcov : ∀ j, (Rung4Literal.pos j) ∈ T.lits ∨ (Rung4Literal.neg j) ∈ T.lits)
    {x y : Fin n → Bool}
    (hx : T.lits.all (fun ℓ => Rung4Literal.eval ℓ x) = true)
    (hy : T.lits.all (fun ℓ => Rung4Literal.eval ℓ y) = true) : x = y := by
  rw [List.all_eq_true] at hx hy
  funext j
  rcases hcov j with hp | hp
  · have hxj := hx _ hp; have hyj := hy _ hp
    simp only [Rung4Literal.eval] at hxj hyj
    rw [hxj, hyj]
  · have hxj := hx _ hp; have hyj := hy _ hp
    simp only [Rung4Literal.eval, Bool.not_eq_true'] at hxj hyj
    rw [hxj, hyj]

/-- **The exponential parity DNF lower bound.**  Any DNF computing parity needs `≥ 2^(n-1)` terms. -/
theorem parity_dnf_size_ge (cs : List (Clause n)) (hn : 1 ≤ n)
    (hpar : ∀ x, dnfValue cs x = parity x) :
    2 ^ (n - 1) ≤ cs.length := by
  classical
  set f : (Fin n → Bool) → Clause n :=
    fun x => (cs.find? (fun T => T.lits.all (fun ℓ => Rung4Literal.eval ℓ x))).getD ⟨[]⟩ with hf
  -- f x is a term of cs satisfied by x, for odd-parity x
  have hfx : ∀ x, parity x = true →
      f x ∈ cs ∧ (f x).lits.all (fun ℓ => Rung4Literal.eval ℓ x) = true := by
    intro x hpx
    have hdnf : dnfValue cs x = true := by rw [hpar, hpx]
    rw [dnfValue, List.any_eq_true] at hdnf
    obtain ⟨T, hT, hTsat⟩ := hdnf
    cases hfind : cs.find? (fun T => T.lits.all (fun ℓ => Rung4Literal.eval ℓ x)) with
    | none =>
      rw [List.find?_eq_none] at hfind
      exact absurd hTsat (by simpa using hfind T hT)
    | some T' =>
      have hfeq : f x = T' := by rw [hf]; simp [hfind]
      rw [hfeq]
      refine ⟨List.mem_of_find?_eq_some hfind, ?_⟩
      have hp := List.find?_some hfind
      simpa using hp
  rw [← parity_true_card hn]
  refine le_trans (Finset.card_le_card_of_injOn f ?_ ?_) (List.toFinset_card_le cs)
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    rw [Finset.mem_coe, List.mem_toFinset]
    exact (hfx x hx.2).1
  · intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    have hsx := hfx x hx.2
    have hsy := hfx y hy.2
    have hcov := term_covers_of_sat hpar hsx.1 hsx.2 hx.2
    -- f x = f y, satisfied by both x and y
    refine sat_determines hcov hsx.2 ?_
    rw [hxy]; exact hsy.2

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_dnf_size_ge
