import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyPerGateGen

/-!
# Beigel–Tarui, rung 26: the per-gate `2^{n-t}` bound for `AND` gates and all gate types

Rung 25 gave the per-gate `2^{n-t}` bound for an arbitrary `OR` gate.  This file completes the per-gate side by adding
the `AND` gate (the exact De Morgan dual) and the trivial `var`/`NOT` gates (empty bad sets), packaging all four `UForm`
constructors.

  `redAnd` — the negated reduced input `redAnd l x j = ¬(l.get j).eval x` (the inner `OR`'s input under De Morgan).
  `linSumNVal_gen_neg` — **PROVED**: over the negated children's embeds (`1 - embed(child) = embed(¬child)`), the linear
        form at `S.image Fin.val` equals `ssum S (redAnd l x)`.
  `uand_eval_iff` / `uand_redNZ_iff` — **PROVED**: `(uand l).eval x = false ↔ ∃ j, redAnd l x j = true` — the `AND` gate
        is `false` iff some child is `false`, i.e. the inner `OR` (De Morgan) has a nonzero reduced input.
  `exists_ubadSet_uand_le` — **PROVED, the per-gate bound for an arbitrary `AND` gate**: some length-`t` subset family
        makes `2^t · #(ubadSet subsets (uand l)) ≤ 2^n`; its bad set is rung 24's `red`-bad set for `redAnd`.
  `exists_ubadSet_le_of_gate` — **PROVED, all gate types**: for *every* `UForm` gate there is a length-`t` subset family
        with `2^t · #(ubadSet subsets g) ≤ 2^n`.

## Honest scope

This discharges the per-gate `2^{n-t}` bound for *every* gate type of the unbounded circuit.  Combined with rung 24's
`whole_circuit_error_lt`, a whole-circuit error `< 2^n` follows **once all gates share a single subset family** — the last
remaining bookkeeping (a union-over-gates averaging with the same pointwise `2^{-t}` bound).  This introduces no new
mathematics beyond rungs 23–25.  The composite-`MOD_m` case remains the proven two-fields barrier.  Nothing here is the
Beigel–Tarui reduction in full, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

open MvPolynomial
open scoped Classical
open PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase (embed embed_not)

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- The negated reduced input of an `AND` gate: `¬(l.get j).eval x` (the inner `OR`'s input under De Morgan). -/
def redAnd (l : List (UForm n)) (x : Fin n → Bool) : Fin l.length → Bool :=
  fun j => !(l.get j).eval x

/-- **The negated children's linear form is `ssum` of `redAnd` (proved)**: `1 - embed(child) = embed(¬child)`. -/
theorem linSumNVal_gen_neg (l : List (UForm n)) (x : Fin n → Bool) (S : Finset (Fin l.length)) :
    linSumNVal (l.map (fun a => (1 - embed (a.eval x) : ZMod p))) (S.image Fin.val)
      = ssum (p := p) S (redAnd l x) := by
  have hmap : l.map (fun a => (1 - embed (a.eval x) : ZMod p))
            = l.map (fun a => (embed (!(a.eval x)) : ZMod p)) := by
    apply List.map_congr_left; intro a _; rw [embed_not]
  rw [hmap, linSumNVal, Finset.sum_image (fun a _ b _ h => Fin.val_injective h), ssum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [List.getD_eq_getElem _ 0 (by rw [List.length_map]; exact j.2), List.getElem_map]
  simp [xf, embed, redAnd]

/-- **`foldr`-`and` reads `false` (proved)**: the fold is `false` iff some element is `false`. -/
theorem foldr_and_false_iff {l : List Bool} : l.foldr (· && ·) true = false ↔ ∃ b ∈ l, b = false := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.foldr_cons, Bool.and_eq_false_iff, ih]
    constructor
    · rintro (h | ⟨b, hb, hbf⟩)
      · exact ⟨a, List.mem_cons_self .., h⟩
      · exact ⟨b, List.mem_cons_of_mem _ hb, hbf⟩
    · rintro ⟨b, hb, hbf⟩
      rcases List.mem_cons.mp hb with rfl | ht
      · exact Or.inl hbf
      · exact Or.inr ⟨b, ht, hbf⟩

/-- **The `AND` gate is `false` iff a child is `false` (proved)**. -/
theorem uand_eval_iff (l : List (UForm n)) (x : Fin n → Bool) :
    (UForm.uand l).eval x = false ↔ ∃ j : Fin l.length, (l.get j).eval x = false := by
  have h1 : (UForm.uand l).eval x = ((l.map (fun a => a.eval x)).foldr (· && ·) true) := by
    simp only [UForm.eval]
  rw [h1, foldr_and_false_iff]
  constructor
  · rintro ⟨b, hb, hbf⟩
    rw [List.mem_map] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp ha
    exact ⟨j, hbf⟩
  · rintro ⟨j, hj⟩
    exact ⟨(l.get j).eval x, List.mem_map.mpr ⟨l.get j, List.get_mem .., rfl⟩, hj⟩

/-- **The `AND`-gate reduced input is nonzero iff the gate is `false` (proved)**. -/
theorem uand_redNZ_iff (l : List (UForm n)) (x : Fin n → Bool) :
    (UForm.uand l).eval x = false ↔ ∃ j : Fin l.length, redAnd l x j = true := by
  rw [uand_eval_iff]
  refine exists_congr (fun j => ?_)
  simp only [redAnd]
  cases (l.get j).eval x <;> simp

/-- **The per-gate `2^{n-t}` bound for an arbitrary `AND` gate (proved)**. -/
theorem exists_ubadSet_uand_le (l : List (UForm n)) (t : ℕ) :
    ∃ subsets : List (Finset ℕ), subsets.length = t ∧
      2 ^ t * (ubadSet (p := p) subsets (UForm.uand l)).card ≤ 2 ^ n := by
  obtain ⟨F, hF⟩ := exists_low_error_red (p := p) (redAnd l) t
  refine ⟨(List.ofFn F).map (fun S => S.image Fin.val), by simp, ?_⟩
  have hset : ubadSet (p := p) ((List.ofFn F).map (fun S => S.image Fin.val)) (UForm.uand l)
            = (redNZ (redAnd l)).filter (fun x => F ∈ allFail (p := p) (redAnd l x) t) := by
    rw [ubadSet]
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, redNZ, Finset.mem_filter]
    constructor
    · rintro ⟨_, hgate, hall⟩
      refine ⟨⟨Finset.mem_univ x, (uand_redNZ_iff l x).mp hgate⟩, ?_⟩
      rw [mem_allFail]
      intro i
      have hi := hall ((F i).image Fin.val)
        (by rw [List.mem_map]; exact ⟨F i, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩)
      rw [linSumNVal_gen_neg] at hi
      exact hi
    · rintro ⟨⟨_, hnz⟩, hne⟩
      rw [mem_allFail] at hne
      refine ⟨Finset.mem_univ x, (uand_redNZ_iff l x).mpr hnz, ?_⟩
      intro S hS
      rw [List.mem_map] at hS
      obtain ⟨S', hS', rfl⟩ := hS
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hS'
      rw [linSumNVal_gen_neg]
      exact hne i
  rw [hset]
  simpa only [redNumErr] using hF

/-- **The per-gate `2^{n-t}` bound for every gate type (proved)**: variables and `NOT` have empty bad sets; `OR`/`AND`
use rungs 25/26. -/
theorem exists_ubadSet_le_of_gate (g : UForm n) (t : ℕ) :
    ∃ subsets : List (Finset ℕ), subsets.length = t ∧
      2 ^ t * (ubadSet (p := p) subsets g).card ≤ 2 ^ n := by
  cases g with
  | var i => exact ⟨List.replicate t ∅, by simp, by rw [ubadSet]; simp⟩
  | unot a => exact ⟨List.replicate t ∅, by simp, by rw [ubadSet]; simp⟩
  | uor l => exact exists_ubadSet_uor_le l t
  | uand l => exact exists_ubadSet_uand_le l t

end PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.exists_ubadSet_uand_le
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.exists_ubadSet_le_of_gate
