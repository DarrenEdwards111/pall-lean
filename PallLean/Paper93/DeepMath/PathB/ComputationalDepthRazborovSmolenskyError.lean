import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskySubst
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBeigelTaruiPerGate

/-!
# Beigel–Tarui, rung 18: the whole-circuit RS error bound (correctness off a union of bad sets)

Rung 17 assembled the whole-circuit RS-substituted polynomial `arithApprox subsets f` and bounded its degree.  This file
proves its **correctness**: `arithApprox subsets f` computes `f.eval` on every input that avoids a per-gate **bad set**,
so the set of inputs where it errs is contained in the *union* of the per-gate bad sets — the error union bound for the
actual substituted polynomial.

This is the field-level analogue of rung 7's abstract `approx_correct`/`error_card_le`, and it must be done at the field
level: rung 7's Boolean abstraction is insufficient here because each `OR`/`AND` gate's approximator (rung 16's
`orApproxComp`) only computes correctly when its sub-inputs are **clean** `0/1` field values — merely "Boolean-correct"
sub-values (which could be any field element `≠ 1`) would break the subset-sum.  So the induction carries the *clean*
invariant `arithApproxVal subsets g (embed∘x) = embed (g.eval x)`, discharged gate-by-gate with rung 16's
`orApproxVal_fires`/`orApproxVal_allzero`.

  `badSet` — the per-gate bad set: for an `OR` (resp. `AND`) gate, the inputs on which the gate output is `true` (resp.
        `false`) yet **every** chosen subset has vanishing sub-sum (the RS "all-fail" event); `var`/`NOT` gates never err.
  `arithApprox_correct` — **PROVED, the correctness induction**: if `x` avoids every gate's bad set, then
        `arithApproxVal subsets f (embed∘x) = embed (f.eval x)` — the clean invariant, composed over the circuit.
  `arithApprox_error_subset` / `arithApprox_error_card_le` — **PROVED, the error union bound**: the error set is contained
        in `⋃_gates badSet g`, so `#errors ≤ ∑_gates #(badSet g)`.
  `arithApprox_poly_error_card_le` — **PROVED**: the same bound stated for the polynomial `eval` (via rung 17's
        `eval_arithApprox`), fusing with rung 17's degree bound — one polynomial, degree `((#subsets)(p-1))^depth`, erring
        on `≤ ∑_gates #(badSet g)` inputs.

## Honest scope

This completes the **structural** half of the whole-circuit RS approximation: correctness off a union of per-gate bad
sets, and the union bound on the error count — for the genuine substituted polynomial of rung 17, fused with its degree
bound.  What remains (rung 19): the **quantitative** per-gate bound `#(badSet g) ≤ 2^{n-t}`, which needs each gate's
subsets *chosen for that gate's own sub-function* via rung 8's averaging (`exists_low_error_orApprox`) — here `subsets` is
a single global list, so the bad sets are defined but not yet numerically bounded.  With that, `#errors ≤ #gates·2^{n-t} <
2^n` and the polynomial feeds rung 15's quasipolynomial AND count and the Toda `SYM` top to reach `SYM∘AND`.  The
composite-`MOD_m` case remains the proven two-fields barrier.  Nothing here is the Beigel–Tarui reduction in full,
`NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

open MvPolynomial
open scoped Classical
open PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase (BForm subforms embed embed_not)

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- **The per-gate bad set**: the inputs on which the gate's RS approximator can err even when its sub-inputs are the
clean embeds.  For an `OR` gate: the gate is `true` yet every chosen subset has vanishing sub-sum (the "all-fail" event).
For an `AND` gate (De Morgan): the gate is `false` yet the inner `OR` all-fails.  Variables and `NOT` never err. -/
noncomputable def badSet (subsets : List (Finset (Fin 2))) :
    BForm n → Finset (Fin n → Bool)
  | .var _ => ∅
  | .bnot _ => ∅
  | .bor a b => Finset.univ.filter (fun x => (a.eval x || b.eval x) = true ∧
      ∀ S ∈ subsets,
        (∑ i ∈ S, (![embed (a.eval x), embed (b.eval x)] : Fin 2 → ZMod p) i) = 0)
  | .band a b => Finset.univ.filter (fun x => (a.eval x && b.eval x) = false ∧
      ∀ S ∈ subsets,
        (∑ i ∈ S, (![1 - embed (a.eval x), 1 - embed (b.eval x)] : Fin 2 → ZMod p) i) = 0)

/-- **The correctness induction (proved)**: on every input avoiding all gates' bad sets, the assembled evaluator equals
the clean embed of the Boolean value — `arithApproxVal subsets f (embed∘x) = embed (f.eval x)`.  Each gate is discharged
with rung 16's `orApproxVal_fires` (gate fires on a nonzero sub-sum) / `orApproxVal_allzero` (gate vanishes when all
sub-sums vanish); the clean invariant is what lets the gates compose. -/
theorem arithApprox_correct (subsets : List (Finset (Fin 2))) (x : Fin n → Bool) :
    ∀ f : BForm n, (∀ g ∈ subforms f, x ∉ badSet (p := p) subsets g) →
      arithApproxVal (p := p) subsets f (fun i => embed (x i)) = embed (f.eval x) := by
  intro f
  induction f with
  | var i => intro _; simp [arithApproxVal, BForm.eval]
  | bnot a ih =>
      intro hok
      rw [arithApproxVal, ih (fun g hg => hok g (List.mem_cons_of_mem _ hg))]
      simp [BForm.eval, embed_not]
  | bor a b iha ihb =>
      intro hok
      have hxbad : x ∉ badSet (p := p) subsets (.bor a b) := hok _ (List.mem_cons_self ..)
      have iha' := iha (fun g hg => hok g (List.mem_cons_of_mem _ (List.mem_append_left _ hg)))
      have ihb' := ihb (fun g hg => hok g (List.mem_cons_of_mem _ (List.mem_append_right _ hg)))
      rw [arithApproxVal, iha', ihb', BForm.eval]
      by_cases hor : (a.eval x || b.eval x) = true
      · rw [badSet, Finset.mem_filter, not_and] at hxbad
        have h2 := hxbad (Finset.mem_univ x)
        rw [not_and] at h2
        have hnf := h2 hor
        push_neg at hnf
        obtain ⟨S, hS, hne⟩ := hnf
        rw [orApproxVal_fires _ subsets S hS hne, hor]; simp [embed]
      · rw [Bool.not_eq_true, Bool.or_eq_false_iff] at hor
        have hz : orApproxVal (![embed (a.eval x), embed (b.eval x)] : Fin 2 → ZMod p) subsets = 0 := by
          apply orApproxVal_allzero
          intro S _
          apply Finset.sum_eq_zero
          intro i _
          fin_cases i <;> simp [hor.1, hor.2, embed]
        rw [hz, hor.1, hor.2]; simp [embed]
  | band a b iha ihb =>
      intro hok
      have hxbad : x ∉ badSet (p := p) subsets (.band a b) := hok _ (List.mem_cons_self ..)
      have iha' := iha (fun g hg => hok g (List.mem_cons_of_mem _ (List.mem_append_left _ hg)))
      have ihb' := ihb (fun g hg => hok g (List.mem_cons_of_mem _ (List.mem_append_right _ hg)))
      rw [arithApproxVal, iha', ihb', BForm.eval]
      by_cases hand : (a.eval x && b.eval x) = true
      · have hz : orApproxVal
            (![1 - embed (a.eval x), 1 - embed (b.eval x)] : Fin 2 → ZMod p) subsets = 0 := by
          apply orApproxVal_allzero
          intro S _
          apply Finset.sum_eq_zero
          intro i _
          rw [Bool.and_eq_true] at hand
          fin_cases i <;> simp [hand.1, hand.2, embed]
        rw [hz, hand]; simp [embed]
      · rw [badSet, Finset.mem_filter, not_and] at hxbad
        have h2 := hxbad (Finset.mem_univ x)
        rw [not_and] at h2
        rw [Bool.not_eq_true] at hand
        have hnf := h2 hand
        push_neg at hnf
        obtain ⟨S, hS, hne⟩ := hnf
        rw [orApproxVal_fires _ subsets S hS hne, hand]; simp [embed]

/-- **The error set is contained in the union of bad sets (proved)**: every input on which the assembled evaluator
differs from the clean Boolean value lies in some gate's bad set. -/
theorem arithApprox_error_subset (subsets : List (Finset (Fin 2))) (f : BForm n) :
    Finset.univ.filter
        (fun x => arithApproxVal (p := p) subsets f (fun i => embed (x i)) ≠ embed (f.eval x))
      ⊆ (subforms f).toFinset.biUnion (badSet (p := p) subsets) := by
  intro x hx
  rw [Finset.mem_filter] at hx
  rw [Finset.mem_biUnion]
  by_contra hc
  push_neg at hc
  exact hx.2 (arithApprox_correct subsets x f (fun g hg => hc g (List.mem_toFinset.mpr hg)))

/-- **The error union bound (proved)**: the number of inputs where the assembled evaluator errs is at most the sum, over
gates, of the per-gate bad-set sizes. -/
theorem arithApprox_error_card_le (subsets : List (Finset (Fin 2))) (f : BForm n) :
    (Finset.univ.filter
        (fun x => arithApproxVal (p := p) subsets f (fun i => embed (x i)) ≠ embed (f.eval x))).card
      ≤ ∑ g ∈ (subforms f).toFinset, (badSet (p := p) subsets g).card :=
  le_trans (Finset.card_le_card (arithApprox_error_subset subsets f)) Finset.card_biUnion_le

/-- **The error union bound for the polynomial (proved)**: the substituted **polynomial** `arithApprox subsets f`
evaluated at `embed∘x` errs on at most `∑_gates #(badSet g)` inputs — the error half fused with rung 17's degree bound
(one polynomial, degree `((#subsets)(p-1))^depth`, this many errors). -/
theorem arithApprox_poly_error_card_le (subsets : List (Finset (Fin 2))) (f : BForm n) :
    (Finset.univ.filter (fun x =>
        (eval (fun i => embed (x i))) (arithApprox (p := p) subsets f) ≠ embed (f.eval x))).card
      ≤ ∑ g ∈ (subforms f).toFinset, (badSet (p := p) subsets g).card := by
  simpa only [eval_arithApprox] using arithApprox_error_card_le subsets f

end PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.arithApprox_correct
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.arithApprox_error_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.arithApprox_poly_error_card_le
