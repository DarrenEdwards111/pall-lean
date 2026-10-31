import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FullTowerValue

/-!
# The full-tower value is Boolean: `vval t ∈ {0,1}` (PROVED)

The cash-out's second piece.  `ACC0FullTowerExtract` showed the rep equals `vval` over `ZMod (p^{2^k})`;
this shows `vval` is genuinely a `{0,1}` value, so the extraction is an **exact Boolean** value:

  `vval_mem_bool` — for every `FMTower t`: `vval p t = 0 ∨ vval p t = 1`.

By induction: a leaf `[p ∣ y]` and a `MOD` if-value are `{0,1}`; an `AND` (product) of `{0,1}` values is
`{0,1}`; an `OR` (De Morgan `1 − ∏(1 − ·)`) of `{0,1}` values is `{0,1}`.  Combined with
`full_tower_extract`, over the common modulus the full `MOD`/`AND`/`OR` tower's polylog-degree
representation equals the circuit's exact Boolean output.

## What is proved (clean axioms, no `sorry`)

* `prod_bool` — a list product of `{0,1}` integers is `{0,1}`.
* `vval_mem_bool` / `_list` — the full-tower value is `{0,1}` (mutual recursion).

## Honest scope

The full-tower value is Boolean.  With `full_tower_extract` the extraction is exact Boolean over
`ZMod (p^{2^k})`.  The remaining cash-out: choosing `2^k` against the global count (so the *integer* value,
not just mod `p^{2^k}`, is `{0,1}` and the support is quasipoly), the `SYM∘AND` form, and the
`NEXP ⊄ ACC⁰` contradiction.  Williams-strength, **not** built.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0FullTowerBool

open PallLean.Paper93.DeepMath.PathB.ACC0FullTowerValue (FMTower vval)

/-- **A list product of `{0,1}` integers is `{0,1}` (proved).** -/
theorem prod_bool (L : List ℤ) (h : ∀ x ∈ L, x = 0 ∨ x = 1) : L.prod = 0 ∨ L.prod = 1 := by
  induction L with
  | nil => right; simp
  | cons a t ih =>
    rw [List.prod_cons]
    rcases h a (by simp) with ha | ha <;> rcases ih (fun x hx => h x (by simp [hx])) with hp | hp <;>
      simp [ha, hp]

mutual

/-- **The full-tower value is Boolean (proved): `vval p t = 0 ∨ vval p t = 1`.** -/
theorem vval_mem_bool (p : ℕ) : (t : FMTower) → vval p t = 0 ∨ vval p t = 1
  | .leaf y => by rw [vval]; split <;> simp
  | .modN ts => by rw [vval]; split <;> simp
  | .andN ts => by
      rw [vval]
      exact prod_bool _ (fun x hx => by
        simp only [List.mem_map] at hx; obtain ⟨t, ht, rfl⟩ := hx
        exact vval_mem_bool_list p ts t ht)
  | .orN ts => by
      rw [vval]
      have hp : (ts.map (fun t => 1 - vval p t)).prod = 0 ∨ (ts.map (fun t => 1 - vval p t)).prod = 1 :=
        prod_bool _ (fun x hx => by
          simp only [List.mem_map] at hx; obtain ⟨t, ht, rfl⟩ := hx
          rcases vval_mem_bool_list p ts t ht with h | h <;> simp [h])
      rcases hp with h | h <;> simp [h]

/-- List companion. -/
theorem vval_mem_bool_list (p : ℕ) :
    (ts : List FMTower) → ∀ t ∈ ts, vval p t = 0 ∨ vval p t = 1
  | [] => fun t ht => absurd ht (by simp)
  | a :: ts => fun t ht => by
      rcases List.mem_cons.mp ht with rfl | hmem
      · exact vval_mem_bool p t
      · exact vval_mem_bool_list p ts t hmem

end

/-!
**Full-tower value is Boolean.**  `vval p t ∈ {0,1}` for every `MOD`/`AND`/`OR` tower; with
`full_tower_extract` the extraction over `ZMod (p^{2^k})` is the exact Boolean output.  Choosing `2^k`
against the global count, the `SYM∘AND` form, and the `NEXP ⊄ ACC⁰` contradiction remain.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0FullTowerBool

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FullTowerBool.vval_mem_bool
