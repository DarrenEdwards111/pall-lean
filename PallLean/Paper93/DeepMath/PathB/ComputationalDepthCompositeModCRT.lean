import Mathlib

/-!
# Composite `MOD_m`: the CRT decomposition into prime-power `MOD` gates

The Razborov–Smolensky polynomial method (formalised end-to-end for the *prime-power* case, `MOD_p` over `F_p`) hits a
genuine wall for **composite** moduli `m` with two or more distinct prime factors — the *two-fields barrier*: no single
field `F` makes every `MOD` gate of a multi-prime circuit low-degree.  This file supplies the structural half of the
composite story: the **Chinese Remainder decomposition** of a `MOD_m` gate into a conjunction of prime-power `MOD` gates.

  `modZero m k` — the "count `≡ 0 (mod m)`" indicator (the zero-residue `MOD_m` gate value on a subset-count `k`).
  `modZero_mul` — **PROVED (CRT, binary)**: for coprime `a, b`, `modZero (a*b) k = modZero a k ∧ modZero b k`.
  `modZero_prod` — **PROVED (CRT, general)**: for a list of pairwise-coprime factors, `modZero (∏ factors) k` is the `AND`
        over the factors of their `modZero` — so `MOD_m` for `m = ∏ pᵢ^{eᵢ}` is exactly `⋀ᵢ MOD_{pᵢ^{eᵢ}}`.
  `modAccept` / `modAccept_mul` — the accept (nonzero-residue) form: `MOD_{a·b}` accepts iff `MOD_a` **or** `MOD_b` does.
  `mod6_eq` / `mod6_accept_eq` — the canonical `MOD_6 = MOD_2 ∧ MOD_3` (the smallest two-prime instance).

## Honest scope — the structural reduction, not the barrier's resolution

This decomposition is exact and elementary: `MOD_m` reduces to a conjunction of prime-power `MOD` gates, `MOD_{pᵢ^{eᵢ}}`.
Each *individual* `MOD_{pᵢ^{eᵢ}}` is low-degree over a field of characteristic `pᵢ` (the repo's `modGateP`, via Fermat) —
but the conjunction runs over gates of **different** characteristics, and there is no single field making them all
low-degree simultaneously.  That is the *two-fields barrier*, exactly what the earlier `MOD_6`/`ACC⁰[6]` arc proved is a
genuine wall.  Crossing it is Toda's theorem / the symmetric representation over `ℤ` (the `SYM⁺` construction) — the
`NEXP`-strength frontier of Williams' method — which is **not** established here.  This file supplies only the CRT
reduction (the structural ingredient), and states the barrier explicitly.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CompositeMod

/-- The zero-residue `MOD_m` gate value on a subset-count `k`: `true` iff `m ∣ k` (count `≡ 0 mod m`). -/
def modZero (m k : ℕ) : Bool := decide (m ∣ k)

/-- The accept (nonzero-residue) `MOD_m` gate value: `true` iff `m ∤ k`. -/
def modAccept (m k : ℕ) : Bool := decide (¬ m ∣ k)

/-- **CRT, binary (proved)**: for coprime `a, b`, the `MOD_{a·b}` zero-gate is the conjunction of the `MOD_a` and `MOD_b`
zero-gates. -/
theorem modZero_mul {a b : ℕ} (h : Nat.Coprime a b) (k : ℕ) :
    modZero (a * b) k = (modZero a k && modZero b k) := by
  have hiff : (a * b ∣ k) ↔ (a ∣ k ∧ b ∣ k) :=
    ⟨fun hd => ⟨dvd_trans (dvd_mul_right a b) hd, dvd_trans (dvd_mul_left b a) hd⟩,
     fun ⟨ha, hb⟩ => Nat.Coprime.mul_dvd_of_dvd_of_dvd h ha hb⟩
  show decide (a * b ∣ k) = (decide (a ∣ k) && decide (b ∣ k))
  rw [decide_eq_decide.mpr hiff, Bool.decide_and]

/-- **Coprimality with a list product (proved)**: coprime to each factor ⇒ coprime to the product. -/
theorem coprime_prod_right {a : ℕ} {t : List ℕ} (h : ∀ b ∈ t, Nat.Coprime a b) :
    Nat.Coprime a t.prod := by
  induction t with
  | nil => simp
  | cons b s ih =>
    rw [List.prod_cons]
    exact Nat.Coprime.mul_right (h b (List.mem_cons_self ..))
      (ih (fun c hc => h c (List.mem_cons_of_mem _ hc)))

/-- **CRT, general (proved)**: for pairwise-coprime factors, the `MOD_{∏ factors}` zero-gate is the `AND` over the factors
of their `MOD` zero-gates — i.e. `MOD_m` for `m = ∏ pᵢ^{eᵢ}` is `⋀ᵢ MOD_{pᵢ^{eᵢ}}`. -/
theorem modZero_prod (l : List ℕ) (k : ℕ) (h : l.Pairwise Nat.Coprime) :
    modZero l.prod k = l.all (fun d => modZero d k) := by
  induction l with
  | nil => simp [modZero]
  | cons a t ih =>
    rw [List.pairwise_cons] at h
    rw [List.prod_cons, modZero_mul (coprime_prod_right h.1) k, ih h.2, List.all_cons]

/-- **CRT, accept form (proved)**: `MOD_{a·b}` accepts iff `MOD_a` or `MOD_b` accepts (De Morgan of the zero-gate). -/
theorem modAccept_mul {a b : ℕ} (h : Nat.Coprime a b) (k : ℕ) :
    modAccept (a * b) k = (modAccept a k || modAccept b k) := by
  have hiff : (¬ a * b ∣ k) ↔ (¬ a ∣ k ∨ ¬ b ∣ k) := by
    rw [← not_and_or]
    exact not_congr ⟨fun hd => ⟨dvd_trans (dvd_mul_right a b) hd, dvd_trans (dvd_mul_left b a) hd⟩,
      fun ⟨ha, hb⟩ => Nat.Coprime.mul_dvd_of_dvd_of_dvd h ha hb⟩
  show decide (¬ a * b ∣ k) = (decide (¬ a ∣ k) || decide (¬ b ∣ k))
  rw [decide_eq_decide.mpr hiff, Bool.decide_or]

/-- **`MOD_6 = MOD_2 ∧ MOD_3` (proved)**: the smallest two-distinct-prime instance — the canonical `ACC⁰[6]` witness of
the two-fields barrier. -/
theorem mod6_eq (k : ℕ) : modZero 6 k = (modZero 2 k && modZero 3 k) := by
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h6, modZero_mul (by decide) k]

/-- **`MOD_6` accepts iff `MOD_2` or `MOD_3` accepts (proved)**. -/
theorem mod6_accept_eq (k : ℕ) : modAccept 6 k = (modAccept 2 k || modAccept 3 k) := by
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h6, modAccept_mul (by decide) k]

/-- **`MOD_6` via the general list decomposition (proved)**: `modZero 6 = ⋀ over [2,3]`, an instance of `modZero_prod`. -/
theorem mod6_prod (k : ℕ) : modZero 6 k = [2, 3].all (fun d => modZero d k) := by
  have h6 : (6 : ℕ) = ([2, 3] : List ℕ).prod := by norm_num
  rw [h6, modZero_prod [2, 3] k (by decide)]

end PallLean.Paper93.DeepMath.PathB.CompositeMod

#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.modZero_prod
#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.mod6_eq
#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.modAccept_mul
