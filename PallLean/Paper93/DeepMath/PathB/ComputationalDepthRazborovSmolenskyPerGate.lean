import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyUnboundedError
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyInstantiate

/-!
# Beigel–Tarui, rung 23: the per-gate `2^{n-t}` error bound (base case, from rung 8's averaging)

Rung 22 bounded the unbounded-circuit error by `∑_gates #(ubadSet g)`.  This file supplies the **quantitative per-gate
bound** for the base case — an unbounded `OR` gate over the input variables themselves — by connecting `ubadSet` to rung
8's averaging existence (`exists_low_error_orApprox`).

  `varList` — the children `[var 0, …, var (n-1)]`, so `uor (varList n)` is the `OR` of all `n` input variables.
  `linSumNVal_varList` — **PROVED**: the value-level linear form over the variables' embeds, at a `ℕ`-subset obtained by
        `Finset.image Fin.val` from a `Fin n`-subset `S`, is exactly rung 3's subset-sum `ssum S x`.
  `varList_uor_eval` — **PROVED**: `(uor (varList n)).eval x = true ↔ ∃ i, x i = true` — the gate is `OR` of all bits.
  `exists_ubadSet_le` — **PROVED, the per-gate `2^{n-t}` bound**: there is a subset family (length `t`) making the gate's
        bad set satisfy `2^t · #(ubadSet …) ≤ 2^n`, i.e. `#(ubadSet …) ≤ 2^{n-t}`.  Proof: rung 8's averaging gives a
        `Fin n`-subset family whose RS approximator errs on `≤ 2^{n-t}` nonzero inputs; imaging it into `ℕ`-subsets, the
        gate's bad set is *exactly* that error set.

## Honest scope — the base case, not the whole circuit

This is the per-gate `2^{n-t}` bound for a gate **directly over the input variables**: there the truth-vector map
`x ↦ (a.eval x)_a` is the identity, so the gate's bad set coincides with rung 8's OR-of-variables error set, and the
`2^{n-t}` count transfers verbatim.  It is exactly the quantitative content of rung 8, re-expressed in the unbounded
`ubadSet` vocabulary and confirmed to slot into rung 22's union bound.  What it does **not** do — and this is the deep
remaining part — is bound `#(ubadSet g)` for a gate whose inputs are **sub-circuits**: there the truth-vector map is a
complicated, correlated function of `x`, its fibers are non-uniform, and the count no longer reduces to a single
application of rung 8; combining the per-gate bounds across a circuit of correlated approximate sub-values is the
natural-proofs-adjacent core of Smolensky's theorem.  The composite-`MOD_m` case remains the proven two-fields barrier.
Nothing here is the Beigel–Tarui reduction in full, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

open MvPolynomial
open scoped Classical
open PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase (embed)

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- The children `[var 0, …, var (n-1)]`: `uor (varList n)` is the `OR` of all `n` input variables. -/
def varList (n : ℕ) : List (UForm n) := (List.finRange n).map (fun i => UForm.var i)

/-- **`foldr`-`or` reads `true` (proved)**: the fold is `true` iff some element is `true`. -/
theorem foldr_or_true_iff {l : List Bool} : l.foldr (· || ·) false = true ↔ ∃ b ∈ l, b = true := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.foldr_cons, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨b, hb, hbt⟩)
      · exact ⟨a, List.mem_cons_self .., h⟩
      · exact ⟨b, List.mem_cons_of_mem _ hb, hbt⟩
    · rintro ⟨b, hb, hbt⟩
      rcases List.mem_cons.mp hb with rfl | ht
      · exact Or.inl hbt
      · exact Or.inr ⟨b, ht, hbt⟩

/-- **The variables' linear form is the subset-sum (proved)**: over the variables' embeds, the value-level linear form at
`S.image Fin.val` equals rung 3's `ssum S x`. -/
theorem linSumNVal_varList (x : Fin n → Bool) (S : Finset (Fin n)) :
    linSumNVal ((varList n).map (fun a => (embed (a.eval x) : ZMod p))) (S.image Fin.val)
      = ssum (p := p) S x := by
  have hmap : (varList n).map (fun a => (embed (a.eval x) : ZMod p))
            = (List.finRange n).map (fun i => (embed (x i) : ZMod p)) := by
    rw [varList, List.map_map]
    apply List.map_congr_left
    intro i _
    simp [UForm.eval]
  rw [linSumNVal, hmap, Finset.sum_image (fun a _ b _ h => Fin.val_injective h), ssum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [List.getD_eq_getElem _ 0 (by rw [List.length_map, List.length_finRange]; exact i.2),
    List.getElem_map]
  simp [xf, embed]

/-- **The gate is the `OR` of all bits (proved)**. -/
theorem varList_uor_eval (x : Fin n → Bool) :
    (UForm.uor (varList n)).eval x = true ↔ ∃ i, x i = true := by
  have h1 : (UForm.uor (varList n)).eval x
      = ((varList n).map (fun a => a.eval x)).foldr (· || ·) false := by simp only [UForm.eval]
  rw [h1, foldr_or_true_iff]
  constructor
  · rintro ⟨b, hb, hbt⟩
    rw [List.mem_map] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    rw [varList, List.mem_map] at ha
    obtain ⟨i, _, rfl⟩ := ha
    exact ⟨i, by simpa [UForm.eval] using hbt⟩
  · rintro ⟨i, hi⟩
    refine ⟨x i, ?_, hi⟩
    rw [List.mem_map]
    exact ⟨UForm.var i, by rw [varList, List.mem_map]; exact ⟨i, by simp, rfl⟩, by simp [UForm.eval]⟩

/-- **The per-gate `2^{n-t}` bound (proved)**: for the `OR`-of-all-variables gate there is a subset family of size `t`
whose bad set has `2^t · #(ubadSet …) ≤ 2^n` (i.e. `#(ubadSet …) ≤ 2^{n-t}`).  The gate's bad set is *exactly* rung 8's
OR-of-variables error set (imaged into `ℕ`-subsets), so rung 8's averaging count transfers. -/
theorem exists_ubadSet_le (t : ℕ) :
    ∃ subsets : List (Finset ℕ), subsets.length = t ∧
      2 ^ t * (ubadSet (p := p) subsets (UForm.uor (varList n))).card ≤ 2 ^ n := by
  obtain ⟨f, hf⟩ := exists_low_error_orApprox (p := p) (n := n) t
  refine ⟨(List.ofFn f).map (fun S => S.image Fin.val), by simp, ?_⟩
  have hset : ubadSet (p := p) ((List.ofFn f).map (fun S => S.image Fin.val)) (UForm.uor (varList n))
            = (NZ n).filter (fun x => orApprox (p := p) (List.ofFn f) x ≠ 1) := by
    rw [ubadSet]
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, NZ, Finset.mem_filter]
    constructor
    · rintro ⟨_, hgate, hall⟩
      refine ⟨⟨Finset.mem_univ x, (varList_uor_eval x).mp hgate⟩, ?_⟩
      rw [orApprox_ne_one_iff, mem_allFail]
      intro j
      have hj := hall ((f j).image Fin.val)
        (by rw [List.mem_map]; exact ⟨f j, List.mem_ofFn.mpr ⟨j, rfl⟩, rfl⟩)
      rwa [linSumNVal_varList] at hj
    · rintro ⟨⟨_, hnz⟩, hne⟩
      rw [orApprox_ne_one_iff, mem_allFail] at hne
      refine ⟨Finset.mem_univ x, (varList_uor_eval x).mpr hnz, ?_⟩
      intro S hS
      rw [List.mem_map] at hS
      obtain ⟨S', hS', rfl⟩ := hS
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hS'
      rw [linSumNVal_varList]; exact hne j
  rw [hset]; exact hf

end PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.linSumNVal_varList
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.exists_ubadSet_le
