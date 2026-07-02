import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyUnboundedEval
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBeigelTaruiBase

/-!
# Beigel–Tarui, rung 22: the unbounded-circuit RS error bound (correctness off a union of bad sets)

Rung 20 gave the unbounded RS-substituted polynomial's polylog degree; rung 21 gave its substitution semantics.  This
file proves its **correctness**: `uArithApprox subsets f` computes `f.eval` on every input avoiding a per-gate **bad
set**, so its error set is contained in the union of the per-gate bad sets.  This is the unbounded fan-in analogue of
rung 18, carrying the same *clean* invariant `uArithApproxVal subsets g (embed∘x) = embed (g.eval x)`, but now over the
list-fold semantics of unbounded `OR`/`AND` and the nested recursion of `UForm`.

  `usubforms` — all gates of an unbounded formula (children flattened).
  `ubadSet` — the per-gate bad set: an unbounded `OR` gate that is `true` (resp. `AND` gate that is `false`) yet **every**
        chosen subset has vanishing sub-sum over the clean sub-values; `var`/`NOT` never err.
  `uArithApprox_correct` — **PROVED, the correctness induction**: `x` avoiding every gate's bad set ⇒ the clean invariant,
        discharged gate-by-gate with rung 21's `orApproxNVal_fires`/`orApproxNVal_allzero`, using the list-fold facts
        `foldr_or_false` / `foldr_and_true` to read off the Boolean value.
  `uArithApprox_error_subset` / `uArithApprox_error_card_le` — **PROVED, the error union bound**: `#errors ≤ ∑_gates
        #(ubadSet g)`.
  `uArithApprox_poly_error_card_le` — **PROVED**: the same for the polynomial `eval` (via rung 21's `eval_uArithApprox`),
        fusing with rung 20's degree bound — one polynomial, degree `((#subsets)(p-1))^depth`, this many errors.

## Honest scope

This completes the **structural** half of the unbounded RS approximation: correctness off a union of per-gate bad sets
and the union bound on the error count, fused with the (genuine, fan-in-independent) degree bound of rung 20.  What
remains — and it is the deep part — is the **quantitative** bound: for each unbounded gate, choosing its subsets by rung
8's averaging gives `#(ubadSet g) ≤ 2^{n-t}` *for that gate viewed as a function of the sub-inputs*, and combining these
across the circuit (the sub-inputs are correlated approximate values, not independent) to get whole-circuit error `< 2^n`.
Here `subsets` is a single global list, so the bad sets are defined but not numerically bounded.  With that bound, the
degree-`polylog`, error-`<2^n` polynomial feeds rung 15's quasipoly AND count and the Toda `SYM` top to reach `SYM∘AND`.
The composite-`MOD_m` case remains the proven two-fields barrier.  Nothing here is the Beigel–Tarui reduction in full,
`NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

open MvPolynomial
open scoped Classical
open PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase (embed embed_not)

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- All gates (subformulas) of an unbounded formula, children flattened. -/
def usubforms : UForm n → List (UForm n)
  | .var i => [.var i]
  | .unot a => (.unot a) :: usubforms a
  | .uor l => (.uor l) :: (l.map usubforms).flatten
  | .uand l => (.uand l) :: (l.map usubforms).flatten

/-- Every gate is a subformula of itself. -/
theorem mem_usubforms_self (f : UForm n) : f ∈ usubforms f := by
  cases f <;> (rw [usubforms]; exact List.mem_cons_self ..)

/-- Subformulas of a child are subformulas of a `NOT` gate. -/
theorem mem_usubforms_unot {a g : UForm n} (hg : g ∈ usubforms a) : g ∈ usubforms (.unot a) := by
  rw [usubforms]; exact List.mem_cons_of_mem _ hg

/-- Subformulas of a child are subformulas of an `OR` gate. -/
theorem mem_usubforms_uor {l : List (UForm n)} {a g : UForm n} (ha : a ∈ l) (hg : g ∈ usubforms a) :
    g ∈ usubforms (.uor l) := by
  rw [usubforms]
  exact List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨usubforms a, List.mem_map_of_mem ha, hg⟩)

/-- Subformulas of a child are subformulas of an `AND` gate. -/
theorem mem_usubforms_uand {l : List (UForm n)} {a g : UForm n} (ha : a ∈ l) (hg : g ∈ usubforms a) :
    g ∈ usubforms (.uand l) := by
  rw [usubforms]
  exact List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨usubforms a, List.mem_map_of_mem ha, hg⟩)

/-- **List `OR` reads off `false` (proved)**: if the `foldr`-`or` is `false`, every element is `false`. -/
theorem foldr_or_false {l : List Bool} (h : l.foldr (· || ·) false = false) : ∀ b ∈ l, b = false := by
  induction l with
  | nil => intro b hb; simp at hb
  | cons a t ih =>
    rw [List.foldr_cons, Bool.or_eq_false_iff] at h
    intro b hb
    rcases List.mem_cons.mp hb with rfl | ht
    · exact h.1
    · exact ih h.2 b ht

/-- **List `AND` reads off `true` (proved)**: if the `foldr`-`and` is `true`, every element is `true`. -/
theorem foldr_and_true {l : List Bool} (h : l.foldr (· && ·) true = true) : ∀ b ∈ l, b = true := by
  induction l with
  | nil => intro b hb; simp at hb
  | cons a t ih =>
    rw [List.foldr_cons, Bool.and_eq_true] at h
    intro b hb
    rcases List.mem_cons.mp hb with rfl | ht
    · exact h.1
    · exact ih h.2 b ht

omit [Fact p.Prime] in
/-- **All-zero list has zero indexed values (proved)**: if every element is `0`, then `getD j 0 = 0`. -/
theorem getD_eq_zero_of_forall {vals : List (ZMod p)} (h : ∀ v ∈ vals, v = 0) (j : ℕ) :
    vals.getD j 0 = 0 := by
  rcases lt_or_ge j vals.length with hj | hj
  · rw [List.getD_eq_getElem vals 0 hj]; exact h _ (List.getElem_mem hj)
  · rw [List.getD_eq_default vals 0 hj]

/-- **The per-gate bad set** for the unbounded substitution: an `OR` gate `true` (resp. `AND` gate `false`) yet every
chosen subset has vanishing sub-sum over the clean sub-values; `var`/`NOT` never err. -/
noncomputable def ubadSet (subsets : List (Finset ℕ)) : UForm n → Finset (Fin n → Bool)
  | .var _ => ∅
  | .unot _ => ∅
  | .uor l => Finset.univ.filter (fun x => (UForm.uor l).eval x = true ∧
      ∀ S ∈ subsets, linSumNVal (l.map (fun a => (embed (a.eval x) : ZMod p))) S = 0)
  | .uand l => Finset.univ.filter (fun x => (UForm.uand l).eval x = false ∧
      ∀ S ∈ subsets, linSumNVal (l.map (fun a => (1 - embed (a.eval x) : ZMod p))) S = 0)

/-- **The correctness induction (proved)**: on every input avoiding all gates' bad sets, the assembled unbounded
evaluator equals the clean embed of the Boolean value.  Each gate is discharged with rung 21's
`orApproxNVal_fires`/`orApproxNVal_allzero`, reading the Boolean value off the list fold via
`foldr_or_false`/`foldr_and_true`. -/
theorem uArithApprox_correct (subsets : List (Finset ℕ)) (x : Fin n → Bool) :
    ∀ f : UForm n, (∀ g ∈ usubforms f, x ∉ ubadSet (p := p) subsets g) →
      uArithApproxVal (p := p) subsets f (fun i => embed (x i)) = embed (f.eval x)
  | .var i => fun _ => by simp [uArithApproxVal, UForm.eval]
  | .unot a => fun hok => by
      rw [uArithApproxVal, uArithApprox_correct subsets x a
        (fun g hg => hok g (mem_usubforms_unot hg))]
      simp [UForm.eval, embed_not]
  | .uor l => fun hok => by
      have hvals : l.map (fun a => uArithApproxVal (p := p) subsets a (fun i => embed (x i)))
                 = l.map (fun a => (embed (a.eval x) : ZMod p)) := by
        apply List.map_congr_left
        intro a ha
        exact uArithApprox_correct subsets x a (fun g hg => hok g (mem_usubforms_uor ha hg))
      rw [uArithApproxVal, hvals]
      have hxbad : x ∉ ubadSet (p := p) subsets (.uor l) := hok _ (mem_usubforms_self _)
      by_cases hor : (UForm.uor l).eval x = true
      · rw [ubadSet, Finset.mem_filter, not_and] at hxbad
        have h2 := hxbad (Finset.mem_univ x)
        rw [not_and] at h2
        have hnf := h2 hor
        push_neg at hnf
        obtain ⟨S, hS, hne⟩ := hnf
        rw [orApproxNVal_fires _ subsets S hS hne, hor]; simp [embed]
      · rw [Bool.not_eq_true] at hor
        have hor' : (l.map (fun a => a.eval x)).foldr (· || ·) false = false := by
          simpa only [UForm.eval] using hor
        have hv : ∀ v ∈ l.map (fun a => (embed (a.eval x) : ZMod p)), v = 0 := by
          intro v hv; rw [List.mem_map] at hv; obtain ⟨a, ha, rfl⟩ := hv
          rw [foldr_or_false hor' _ (List.mem_map_of_mem ha)]; simp [embed]
        have hz : orApproxNVal (l.map (fun a => (embed (a.eval x) : ZMod p))) subsets = 0 :=
          orApproxNVal_allzero _ subsets (fun S _ => by
            rw [linSumNVal]; exact Finset.sum_eq_zero (fun j _ => getD_eq_zero_of_forall hv j))
        rw [hz, hor]; simp [embed]
  | .uand l => fun hok => by
      have hvals : l.map (fun a => (1 : ZMod p) - uArithApproxVal (p := p) subsets a (fun i => embed (x i)))
                 = l.map (fun a => (1 - embed (a.eval x) : ZMod p)) := by
        apply List.map_congr_left
        intro a ha
        rw [uArithApprox_correct subsets x a (fun g hg => hok g (mem_usubforms_uand ha hg))]
      rw [uArithApproxVal, hvals]
      have hxbad : x ∉ ubadSet (p := p) subsets (.uand l) := hok _ (mem_usubforms_self _)
      by_cases hand : (UForm.uand l).eval x = true
      · have hand' : (l.map (fun a => a.eval x)).foldr (· && ·) true = true := by
          simpa only [UForm.eval] using hand
        have hv : ∀ v ∈ l.map (fun a => (1 - embed (a.eval x) : ZMod p)), v = 0 := by
          intro v hv; rw [List.mem_map] at hv; obtain ⟨a, ha, rfl⟩ := hv
          rw [foldr_and_true hand' _ (List.mem_map_of_mem ha)]; simp [embed]
        have hz : orApproxNVal (l.map (fun a => (1 - embed (a.eval x) : ZMod p))) subsets = 0 :=
          orApproxNVal_allzero _ subsets (fun S _ => by
            rw [linSumNVal]; exact Finset.sum_eq_zero (fun j _ => getD_eq_zero_of_forall hv j))
        rw [hz, hand]; simp [embed]
      · rw [Bool.not_eq_true] at hand
        rw [ubadSet, Finset.mem_filter, not_and] at hxbad
        have h2 := hxbad (Finset.mem_univ x)
        rw [not_and] at h2
        have hnf := h2 hand
        push_neg at hnf
        obtain ⟨S, hS, hne⟩ := hnf
        rw [orApproxNVal_fires _ subsets S hS hne, hand]; simp [embed]

/-- **The error set is contained in the union of bad sets (proved)**. -/
theorem uArithApprox_error_subset (subsets : List (Finset ℕ)) (f : UForm n) :
    Finset.univ.filter
        (fun x => uArithApproxVal (p := p) subsets f (fun i => embed (x i)) ≠ embed (f.eval x))
      ⊆ (usubforms f).toFinset.biUnion (ubadSet (p := p) subsets) := by
  intro x hx
  rw [Finset.mem_filter] at hx
  rw [Finset.mem_biUnion]
  by_contra hc
  push_neg at hc
  exact hx.2 (uArithApprox_correct subsets x f (fun g hg => hc g (List.mem_toFinset.mpr hg)))

/-- **The error union bound (proved)**: `#errors ≤ ∑_gates #(ubadSet g)`. -/
theorem uArithApprox_error_card_le (subsets : List (Finset ℕ)) (f : UForm n) :
    (Finset.univ.filter
        (fun x => uArithApproxVal (p := p) subsets f (fun i => embed (x i)) ≠ embed (f.eval x))).card
      ≤ ∑ g ∈ (usubforms f).toFinset, (ubadSet (p := p) subsets g).card :=
  le_trans (Finset.card_le_card (uArithApprox_error_subset subsets f)) Finset.card_biUnion_le

/-- **The error union bound for the polynomial (proved)**: the unbounded substituted **polynomial** errs on
`≤ ∑_gates #(ubadSet g)` inputs — the error half fused with rung 20's genuine fan-in-independent degree bound. -/
theorem uArithApprox_poly_error_card_le (subsets : List (Finset ℕ)) (f : UForm n) :
    (Finset.univ.filter (fun x =>
        (eval (fun i => embed (x i))) (uArithApprox (p := p) subsets f) ≠ embed (f.eval x))).card
      ≤ ∑ g ∈ (usubforms f).toFinset, (ubadSet (p := p) subsets g).card := by
  simpa only [eval_uArithApprox] using uArithApprox_error_card_le subsets f

end PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.uArithApprox_correct
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.uArithApprox_error_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.uArithApprox_poly_error_card_le
