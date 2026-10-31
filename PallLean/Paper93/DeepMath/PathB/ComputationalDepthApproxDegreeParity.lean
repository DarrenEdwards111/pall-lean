import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# An approximate-degree lower bound, complete and axiom-clean: parity needs full degree `n`

The `KakeyaCEWWall` brick located the wall at *approximate* degree — a specific hard function that no
low-degree polynomial can approximate.  This file proves such a bound outright, with a Markov-free
elementary argument: the **real approximate degree of parity is the maximum `n`**.

Any real polynomial `q` that approximates the parity pattern `k ↦ k mod 2` to error `< 1/2` on the
weights `{0,…,n}` must have `q(k) - 1/2` change sign across every unit step (parity alternates), giving
`n` roots of `q - 1/2`, hence `deg q ≥ n`.

## What is proved

* **`parity_approx_degree`** — if `|q(k) - (k mod 2)| < 1/2` for all `k ≤ n`, then `n ≤ q.natDegree`.
  Proof: `g := q - 1/2` has strictly alternating sign on `0,1,…,n`, so by the intermediate value theorem
  it has a root in each open interval `(k, k+1)` (`n` distinct roots), and a polynomial with `n` distinct
  real roots has degree `≥ n`.

## Honest scope

This is a genuine, complete approximate-degree lower bound (the strongest possible, `= n`).  Its target,
**parity, is the canonical function *hard for* AC⁰** — it is *not itself in* AC⁰ (Håstad); its maximal
approximate degree is exactly the obstruction underlying Razborov–Smolensky AC⁰[p] separations.  An
in-AC⁰ function such as OR has the sharper-to-place `√n` (Nisan–Szegedy) bound, whose proof needs
Markov's inequality — a much heavier analytic formalization not attempted here.  Nothing here is
`P ≠ NP`; it is the approximate-degree obstruction, proved for the canonical witness.
-/

namespace PallLean.Paper93.DeepMath.PathB.ApproxDegreeParity

open Polynomial

/-- **Parity has real approximate degree `≥ n` (proved).**  Any polynomial approximating the parity
pattern to error `< 1/2` on `{0,…,n}` has degree at least `n`. -/
theorem parity_approx_degree (n : ℕ) (q : ℝ[X])
    (happrox : ∀ k : ℕ, k ≤ n → |q.eval (k : ℝ) - ((k % 2 : ℕ) : ℝ)| < 1 / 2) :
    n ≤ q.natDegree := by
  set g : ℝ[X] := q - C (1 / 2) with hgdef
  have geval : ∀ x : ℝ, g.eval x = q.eval x - 1 / 2 := by
    intro x; simp [hgdef]
  -- g is strictly negative at even weights, strictly positive at odd weights
  have gsign_even : ∀ k : ℕ, k ≤ n → k % 2 = 0 → g.eval (k : ℝ) < 0 := by
    intro k hk hpar
    have h := happrox k hk
    rw [hpar] at h
    simp only [Nat.cast_zero, sub_zero] at h
    rw [abs_lt] at h
    rw [geval]; linarith [h.2]
  have gsign_odd : ∀ k : ℕ, k ≤ n → k % 2 = 1 → 0 < g.eval (k : ℝ) := by
    intro k hk hpar
    have h := happrox k hk
    rw [hpar] at h
    simp only [Nat.cast_one] at h
    rw [abs_lt] at h
    rw [geval]; linarith [h.1]
  -- a root of g in each interval (k, k+1)
  have hcont : ContinuousOn (fun x => g.eval x) (Set.Icc (0 : ℝ) (n : ℝ)) :=
    (Polynomial.continuous g).continuousOn
  have hroot : ∀ k : ℕ, k < n → ∃ r : ℝ, (k : ℝ) < r ∧ g.eval r = 0 ∧ r < (k : ℝ) + 1 := by
    intro k hk
    have hcc : ContinuousOn (fun x => g.eval x) (Set.Icc (k : ℝ) ((k : ℝ) + 1)) :=
      (Polynomial.continuous g).continuousOn
    rcases Nat.even_or_odd k with he | ho
    · have hpar : k % 2 = 0 := Nat.even_iff.mp he
      have h1 : g.eval (k : ℝ) < 0 := gsign_even k (le_of_lt hk) hpar
      have h2 : 0 < g.eval ((k : ℝ) + 1) := by
        have := gsign_odd (k + 1) hk (by omega)
        push_cast at this; exact this
      obtain ⟨r, hrmem, hreq⟩ :=
        intermediate_value_Ioo (by linarith : (k : ℝ) ≤ (k : ℝ) + 1) hcc ⟨h1, h2⟩
      exact ⟨r, hrmem.1, hreq, hrmem.2⟩
    · have hpar : k % 2 = 1 := Nat.odd_iff.mp ho
      have h1 : 0 < g.eval (k : ℝ) := gsign_odd k (le_of_lt hk) hpar
      have h2 : g.eval ((k : ℝ) + 1) < 0 := by
        have := gsign_even (k + 1) hk (by omega)
        push_cast at this; exact this
      obtain ⟨r, hrmem, hreq⟩ :=
        intermediate_value_Ioo' (by linarith : (k : ℝ) ≤ (k : ℝ) + 1) hcc ⟨h2, h1⟩
      exact ⟨r, hrmem.1, hreq, hrmem.2⟩
  -- g ≠ 0
  have hg0 : g ≠ 0 := by
    intro h
    have hz := gsign_even 0 (Nat.zero_le n) rfl
    rw [h] at hz; simp at hz
  -- choose a root for each k < n
  classical
  let r : ℕ → ℝ := fun k => if hk : k < n then (hroot k hk).choose else 0
  have hr_root : ∀ k, k < n → g.IsRoot (r k) := by
    intro k hk; simp only [r, dif_pos hk]; exact (hroot k hk).choose_spec.2.1
  have hr_lb : ∀ k, k < n → (k : ℝ) < r k := by
    intro k hk; simp only [r, dif_pos hk]; exact (hroot k hk).choose_spec.1
  have hr_ub : ∀ k, k < n → r k < (k : ℝ) + 1 := by
    intro k hk; simp only [r, dif_pos hk]; exact (hroot k hk).choose_spec.2.2
  -- the roots are distinct
  have hinj : Set.InjOn r ↑(Finset.range n) := by
    intro a ha b hb hrab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rcases lt_trichotomy a b with h | h | h
    · exfalso
      have hab : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast h
      linarith [hr_ub a ha, hr_lb b hb, hrab]
    · exact h
    · exfalso
      have hba : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast h
      linarith [hr_ub b hb, hr_lb a ha, hrab]
  -- n distinct roots ⟹ natDegree ≥ n
  have hcard : (Finset.range n).card ≤ g.natDegree := by
    have hsub : (Finset.range n).image r ⊆ g.roots.toFinset := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      rw [Finset.mem_range] at hk
      rw [Multiset.mem_toFinset, Polynomial.mem_roots']
      exact ⟨hg0, hr_root k hk⟩
    calc (Finset.range n).card
        = ((Finset.range n).image r).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ g.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
      _ ≤ g.natDegree := Polynomial.card_roots' g
  rw [Finset.card_range] at hcard
  -- natDegree g ≤ natDegree q
  refine le_trans hcard ?_
  rw [hgdef]
  calc (q - C (1 / 2)).natDegree
      ≤ max q.natDegree (C (1 / 2 : ℝ)).natDegree := Polynomial.natDegree_sub_le _ _
    _ = q.natDegree := by rw [Polynomial.natDegree_C]; simp

end PallLean.Paper93.DeepMath.PathB.ApproxDegreeParity

#print axioms PallLean.Paper93.DeepMath.PathB.ApproxDegreeParity.parity_approx_degree
