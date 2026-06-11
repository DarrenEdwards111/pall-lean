import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer9KarpLipton
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer8ShannonExplicit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer7ParityFamily

/-!
# Layer 9 — some language is outside `P/poly` (the family-level Shannon consequence)

A genuine, sorry-free theorem: **`∃ L, L ∉ P/poly`** — there is a boolean language not computed by any
poly-size general-circuit family.  This is the circuit-*family* form of the Shannon counting bound
(`exists_function_needing_exp_size`): at each length the diagonal language uses a function requiring size
`≈ 2ⁿ/n`, which eventually beats every polynomial size bound.

* `SIZE_mono` — `SIZE n` is monotone in the size budget.
* `exists_lang_not_in_Ppoly` — `∃ L : BoolLang, ¬ Ppoly L`.  Proof: take `L n` to be a Shannon-hard
  function at length `n` (`∉ SIZE n (2ⁿ/(n+6)−1)`); if `L ∈ P/poly` with poly bound `p`, then
  `exists_poly_lt_pow` gives an `n` with `(p n + 1)(n+6) ≤ 2ⁿ`, i.e. `p n ≤ 2ⁿ/(n+6) − 1`, so
  `L n ∈ SIZE n (p n) ⊆ SIZE n (2ⁿ/(n+6)−1)` — contradicting hardness.

**Honest status.**  This is real and nontrivial, but **nonconstructive** (the language is chosen
per-length from Shannon's existence; it names no explicit language) and it is a statement about a
*hard-to-compute* language, **not** about `NP`.  It is **not** `NP ⊄ P/poly` and **not** `P ≠ NP`: the open
frontier asks for an **explicit / `NP`** language outside `P/poly`, which is exactly the barrier-blocked
step fenced in `SCOPE_LAYER8_EXPLICIT_LOWER_BOUND_FRONTIER.md`.  This theorem is the easy "some language is
hard" floor, lifted to the `P/poly`/family level.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer9

open PallLean.Paper93.DeepMath.PathB

/-- `SIZE n` is monotone in the size budget. -/
theorem SIZE_mono {n s s' : ℕ} (h : s ≤ s') : Layer8.SIZE n s ⊆ Layer8.SIZE n s' :=
  fun _ ⟨c, hcs, hcf⟩ => ⟨c, le_trans hcs h, hcf⟩

/-- **Some boolean language is outside `P/poly`.**  (Nonconstructive; not about `NP`; not `P ≠ NP`.) -/
theorem exists_lang_not_in_Ppoly : ∃ L : Layer7.BoolLang, ¬ Ppoly L := by
  classical
  refine ⟨fun n => Classical.choose (Layer8.exists_function_needing_exp_size n), ?_⟩
  rintro ⟨p, ⟨a, c, b, hp⟩, hcomp⟩
  obtain ⟨n, hn1, hlt⟩ := Layer7.exists_poly_lt_pow 2 (by decide) (7 * (a + b + 1)) (c + 1) 0
  have hnc : (1 : ℕ) ≤ n ^ c := Nat.one_le_pow _ _ (by omega)
  have hb1 : a * n ^ c + b + 1 ≤ (a + b + 1) * n ^ c := by
    have hb : b ≤ b * n ^ c := Nat.le_mul_of_pos_right b (by omega)
    rw [show (a + b + 1) * n ^ c = a * n ^ c + b * n ^ c + n ^ c from by ring]
    omega
  have hbprod : (a * n ^ c + b + 1) * (n + 6) ≤ 7 * (a + b + 1) * n ^ (c + 1) := by
    calc (a * n ^ c + b + 1) * (n + 6) ≤ ((a + b + 1) * n ^ c) * (7 * n) :=
          Nat.mul_le_mul hb1 (by omega)
      _ = 7 * (a + b + 1) * n ^ (c + 1) := by rw [pow_succ]; ring
  have hpn1 : (p n + 1) * (n + 6) ≤ 2 ^ n := by
    calc (p n + 1) * (n + 6) ≤ (a * n ^ c + b + 1) * (n + 6) :=
          Nat.mul_le_mul_right _ (by have := hp n; omega)
      _ ≤ 7 * (a + b + 1) * n ^ (c + 1) := hbprod
      _ ≤ 2 ^ n := by simpa using hlt.le
  have hpdiv : p n ≤ 2 ^ n / (n + 6) - 1 := by
    have h2 : p n + 1 ≤ 2 ^ n / (n + 6) := (Nat.le_div_iff_mul_le (by omega)).mpr hpn1
    omega
  have hLn := Classical.choose_spec (Layer8.exists_function_needing_exp_size n)
  obtain ⟨cir, hcs, hcf⟩ := SIZE_mono hpdiv (hcomp n)
  exact absurd hcs (Nat.not_le.mpr (hLn cir hcf))

end PallLean.Paper93.DeepMath.PathB.Layer9

#print axioms PallLean.Paper93.DeepMath.PathB.Layer9.exists_lang_not_in_Ppoly
