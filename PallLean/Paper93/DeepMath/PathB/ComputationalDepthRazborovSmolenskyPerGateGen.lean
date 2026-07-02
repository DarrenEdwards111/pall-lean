import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyPerGate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyLift

/-!
# Beigel–Tarui, rung 25: the per-gate `2^{n-t}` bound for an arbitrary `OR` gate

Rung 23 proved the per-gate `2^{n-t}` bound only for the `OR`-of-all-variables gate; rung 24 proved the
correlation-insensitive averaging `exists_low_error_red` for an arbitrary reduced-input map.  This file closes the loop:
it instantiates `exists_low_error_red` on a *general* `OR` gate `uor l` (whose children `l` may be arbitrary
sub-circuits) via the reduced input `red x = (child truth values)`, and translates the `Fin (l.length)`-subset family
into the `ℕ`-subset list of `ubadSet`.

  `linSumNVal_gen` — **PROVED**: the value-level linear form over the children's embeds, at `S.image Fin.val`, equals the
        subset-sum `ssum S (fun j ↦ (l.get j).eval x)` of the reduced input — the general form of rung 23's
        `linSumNVal_varList`.
  `uor_eval_iff` — **PROVED**: `(uor l).eval x = true ↔ ∃ j, (l.get j).eval x = true` — the gate is the `OR` of its
        children.
  `exists_ubadSet_uor_le` — **PROVED, the per-gate bound for an arbitrary `OR` gate**: for any children `l`, there is a
        subset family (length `t`) with `2^t · #(ubadSet subsets (uor l)) ≤ 2^n`.  The gate's bad set is *exactly* rung
        24's `red`-bad set (imaged into `ℕ`-subsets), with `red x = (child truth values)`, so the
        correlation-insensitive count of `exists_low_error_red` transfers.

## Honest scope

This discharges the per-gate `2^{n-t}` bound for **every** `OR` gate — over arbitrary sub-circuits, not just variables —
by feeding rung 24's `exists_low_error_red` through the same `Fin → ℕ` subset translation rung 23 used for the base case.
The `AND` gate is the exact De Morgan dual (its bad set uses `1 - embed(child)`, the negated children), and `var`/`NOT`
gates have empty bad sets; assembling all gate types with a *single* subset family and plugging into rung 24's
`whole_circuit_error_lt` is the remaining bookkeeping.  This is the last mechanical piece of the unbounded RS
approximation's error side; it introduces no new mathematics beyond rungs 23–24.  The composite-`MOD_m` case remains the
proven two-fields barrier.  Nothing here is the Beigel–Tarui reduction in full, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

open MvPolynomial
open scoped Classical
open PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase (embed)

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- **The children's linear form is the reduced subset-sum (proved)**: general form of `linSumNVal_varList`. -/
theorem linSumNVal_gen (l : List (UForm n)) (x : Fin n → Bool) (S : Finset (Fin l.length)) :
    linSumNVal (l.map (fun a => (embed (a.eval x) : ZMod p))) (S.image Fin.val)
      = ssum (p := p) S (fun j => (l.get j).eval x) := by
  rw [linSumNVal, Finset.sum_image (fun a _ b _ h => Fin.val_injective h), ssum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [List.getD_eq_getElem _ 0 (by rw [List.length_map]; exact j.2), List.getElem_map]
  simp [xf, embed]

/-- **The gate is the `OR` of its children (proved)**. -/
theorem uor_eval_iff (l : List (UForm n)) (x : Fin n → Bool) :
    (UForm.uor l).eval x = true ↔ ∃ j : Fin l.length, (l.get j).eval x = true := by
  have h1 : (UForm.uor l).eval x = ((l.map (fun a => a.eval x)).foldr (· || ·) false) := by
    simp only [UForm.eval]
  rw [h1, foldr_or_true_iff]
  constructor
  · rintro ⟨b, hb, hbt⟩
    rw [List.mem_map] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp ha
    exact ⟨j, hbt⟩
  · rintro ⟨j, hj⟩
    exact ⟨(l.get j).eval x, List.mem_map.mpr ⟨l.get j, List.get_mem .., rfl⟩, hj⟩

/-- **The per-gate `2^{n-t}` bound for an arbitrary `OR` gate (proved)**: for any children `l`, there is a subset family
of size `t` whose bad set satisfies `2^t · #(ubadSet …) ≤ 2^n`.  The gate's bad set is exactly rung 24's `red`-bad set
for `red x = (child truth values)`, so `exists_low_error_red`'s correlation-insensitive count transfers verbatim. -/
theorem exists_ubadSet_uor_le (l : List (UForm n)) (t : ℕ) :
    ∃ subsets : List (Finset ℕ), subsets.length = t ∧
      2 ^ t * (ubadSet (p := p) subsets (UForm.uor l)).card ≤ 2 ^ n := by
  obtain ⟨F, hF⟩ := exists_low_error_red (p := p) (fun x => fun j => (l.get j).eval x) t
  refine ⟨(List.ofFn F).map (fun S => S.image Fin.val), by simp, ?_⟩
  have hset : ubadSet (p := p) ((List.ofFn F).map (fun S => S.image Fin.val)) (UForm.uor l)
            = (redNZ (fun x => fun j => (l.get j).eval x)).filter
                (fun x => F ∈ allFail (p := p) (fun j => (l.get j).eval x) t) := by
    rw [ubadSet]
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, redNZ, Finset.mem_filter]
    constructor
    · rintro ⟨_, hgate, hall⟩
      refine ⟨⟨Finset.mem_univ x, (uor_eval_iff l x).mp hgate⟩, ?_⟩
      rw [mem_allFail]
      intro i
      have hi := hall ((F i).image Fin.val)
        (by rw [List.mem_map]; exact ⟨F i, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩)
      rw [linSumNVal_gen] at hi
      exact hi
    · rintro ⟨⟨_, hnz⟩, hne⟩
      rw [mem_allFail] at hne
      refine ⟨Finset.mem_univ x, (uor_eval_iff l x).mpr hnz, ?_⟩
      intro S hS
      rw [List.mem_map] at hS
      obtain ⟨S', hS', rfl⟩ := hS
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hS'
      rw [linSumNVal_gen]
      exact hne i
  rw [hset]
  simpa only [redNumErr] using hF

end PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.linSumNVal_gen
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.exists_ubadSet_uor_le
