import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer7ParityFamily
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4PadSubcircuits

/-!
# Layer 7 (open frontier) — `MOD_q` is not in nonuniform `AC⁰[p]` (`p ≠ q`, circuit-family level)

The general-`q` analogue of `ComputationalDepthLayer7ParityFamily`: lifting the per-length
`mod_q_family_false` (Layer 4) to a **circuit-family language** statement.

* `modqLang q` — the `MOD_q` language (`true` iff `#ones ≡ 0 (mod q)`).
* `modq_not_in_nonuniform_AC0p` — for distinct primes `p ≠ q`: **no constant-depth, polynomially-size-
  bounded `AC⁰[p]` circuit family computes the `MOD_q` language.**  Proof: at length `2m+1` with
  `m = 8·((p-1)t)^{2d}` and the residue-shifted lengths `(2m+1)+(q-j)`, feed the family into
  `mod_q_family_false`; its size hypothesis `4q·(#subcircuits + (2m+1+q)) ≤ p^t` holds because the left
  side is polynomial in `t` (`#subcircuits ≤ sizeBound`, `IsPolyBounded`) while `p^t` is exponential, via
  `exists_poly_lt_pow`; the band-margin window holds by `m`'s choice.

## Honest framing (must travel with this theorem)

As with PARITY: this is a **nonuniform circuit-family** lower bound for an **explicit, easy (P-computable)**
language (`MOD_q ∈ P ⊆ NP`).  It is **NOT** `P ≠ NP`, **NOT** `NP ⊄ AC⁰[p]` in any deep sense, and **NOT**
a statement about hard `NP` functions.  The new content vs Layer 4 is only the family/asymptotic packaging.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer7

open PallLean.Paper93.DeepMath.PathB Finset

/-- The **`MOD_q` language**: at each length, `true` iff the input has `≡ 0 (mod q)` many `true`s. -/
def modqLang (q : ℕ) : BoolLang :=
  fun _ x => decide ((Finset.univ.filter (fun i => x i = true)).card % q = 0)

open Classical in
/-- **`MOD_q` is not in nonuniform `AC⁰[p]`** (distinct primes `p ≠ q`).  No constant-depth,
polynomially-size-bounded `AC⁰[p]` circuit family computes the `MOD_q` language.  (Honest level-2
corollary — *not* `P ≠ NP`, *not* a hard-`NP`-function separation; see the module docstring.) -/
theorem modq_not_in_nonuniform_AC0p (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p)
    (F : AC0pFamily p) (hpoly : IsPolyBounded F.sizeBound) :
    ¬ F.Computes (modqLang q) := by
  intro hComp
  obtain ⟨a, c, b, hsz⟩ := hpoly
  set d := F.depthBound with hd_def
  set K := 16 * (p - 1) ^ (d * 2) + 1 + q with hK_def
  obtain ⟨t, ht1, htlt⟩ := exists_poly_lt_pow p (Fact.out (p := p.Prime)).two_le
      (4 * q * (a + b + 1) * K ^ (c + 1)) (d * 2 * (c + 1)) 0
  set m := 8 * (((p - 1) * t) ^ d) ^ 2 with hm_def
  have hpt1 : 1 ≤ (p - 1) * t :=
    Nat.mul_pos (by have := (Fact.out (p := p.Prime)).two_le; omega) (by omega)
  have htpow : 1 ≤ t ^ (d * 2) := Nat.one_le_pow _ _ (by omega)
  have hMpos : 1 ≤ 2 * m + 1 + q := by omega
  have hMle : 2 * m + 1 + q ≤ K * t ^ (d * 2) := by
    have e : (((p - 1) * t) ^ d) ^ 2 = (p - 1) ^ (d * 2) * t ^ (d * 2) := by rw [← pow_mul, mul_pow]
    rw [hm_def, hK_def, show 2 * (8 * (((p - 1) * t) ^ d) ^ 2) + 1 + q
        = 16 * (((p - 1) * t) ^ d) ^ 2 + 1 + q from by ring, e]
    nlinarith [htpow, Nat.zero_le ((p - 1) ^ (d * 2))]
  have hwin : 16 * (((p - 1) * t) ^ d) ^ 2 < 2 * m + 3 := by
    have h2m : 2 * m = 16 * (((p - 1) * t) ^ d) ^ 2 := by rw [hm_def]; ring
    omega
  apply Layer4.mod_q_family_false p q hpq ht1 hpt1 (fun j => F.circ ((2 * m + 1) + (q - j)))
    (fun j _ x => by rw [hComp ((2 * m + 1) + (q - j)) x]; rfl)
    (fun j _ => F.isAC0p _)
    ?_
    (fun j _ => F.hdepth _)
    hwin
  -- Size hypothesis: `4q·(#subcircuits + (2m+1+q)) ≤ p^t` for each residue `j`.
  intro j _
  set L := (2 * m + 1) + (q - j) with hL_def
  have hLM : L ≤ 2 * m + 1 + q := by rw [hL_def]; omega
  have hsub : (Layer3.subcircuits (F.circ L)).toFinset.card ≤ a * (2 * m + 1 + q) ^ c + b := by
    refine le_trans (le_trans (F.hsize L) (hsz L)) ?_
    have hLc : L ^ c ≤ (2 * m + 1 + q) ^ c := Nat.pow_le_pow_left hLM c
    nlinarith [hLc, Nat.zero_le a]
  have hcollapse : a * (2 * m + 1 + q) ^ c + b + (2 * m + 1 + q)
      ≤ (a + b + 1) * (2 * m + 1 + q) ^ (c + 1) := by
    have h1 : (2 * m + 1 + q) ^ c ≤ (2 * m + 1 + q) ^ (c + 1) := Nat.pow_le_pow_right hMpos (by omega)
    have h2 : (2 * m + 1 + q) ≤ (2 * m + 1 + q) ^ (c + 1) := by
      calc (2 * m + 1 + q) = (2 * m + 1 + q) ^ 1 := (pow_one _).symm
        _ ≤ (2 * m + 1 + q) ^ (c + 1) := Nat.pow_le_pow_right hMpos (by omega)
    have h3 : 1 ≤ (2 * m + 1 + q) ^ (c + 1) := Nat.one_le_pow _ _ (by omega)
    nlinarith [h1, h2, h3, Nat.zero_le a, Nat.zero_le b]
  have hMpow : (2 * m + 1 + q) ^ (c + 1) ≤ K ^ (c + 1) * t ^ (d * 2 * (c + 1)) := by
    calc (2 * m + 1 + q) ^ (c + 1) ≤ (K * t ^ (d * 2)) ^ (c + 1) := Nat.pow_le_pow_left hMle (c + 1)
      _ = K ^ (c + 1) * (t ^ (d * 2)) ^ (c + 1) := mul_pow _ _ _
      _ = K ^ (c + 1) * t ^ (d * 2 * (c + 1)) := by rw [← pow_mul]
  have hfin : 4 * q * ((Layer3.subcircuits (F.circ L)).toFinset.card + (2 * m + 1 + q))
      ≤ (4 * q * (a + b + 1) * K ^ (c + 1)) * t ^ (d * 2 * (c + 1)) := by
    have hstep : (Layer3.subcircuits (F.circ L)).toFinset.card + (2 * m + 1 + q)
        ≤ (a + b + 1) * K ^ (c + 1) * t ^ (d * 2 * (c + 1)) := by
      calc (Layer3.subcircuits (F.circ L)).toFinset.card + (2 * m + 1 + q)
          ≤ (a * (2 * m + 1 + q) ^ c + b) + (2 * m + 1 + q) := by omega
        _ ≤ (a + b + 1) * (2 * m + 1 + q) ^ (c + 1) := hcollapse
        _ ≤ (a + b + 1) * (K ^ (c + 1) * t ^ (d * 2 * (c + 1))) := Nat.mul_le_mul_left _ hMpow
        _ = (a + b + 1) * K ^ (c + 1) * t ^ (d * 2 * (c + 1)) := by ring
    calc 4 * q * ((Layer3.subcircuits (F.circ L)).toFinset.card + (2 * m + 1 + q))
        ≤ 4 * q * ((a + b + 1) * K ^ (c + 1) * t ^ (d * 2 * (c + 1))) := Nat.mul_le_mul_left _ hstep
      _ = (4 * q * (a + b + 1) * K ^ (c + 1)) * t ^ (d * 2 * (c + 1)) := by ring
  exact le_of_lt (lt_of_le_of_lt hfin (by simpa using htlt))

end PallLean.Paper93.DeepMath.PathB.Layer7

#print axioms PallLean.Paper93.DeepMath.PathB.Layer7.modq_not_in_nonuniform_AC0p
