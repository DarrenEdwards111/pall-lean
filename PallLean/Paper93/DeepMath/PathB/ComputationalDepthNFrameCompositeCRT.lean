import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameModpAndFlatten

/-!
# Decomposing the composite barrier: `MOD_m = ∧_i MOD_{pᵢ^{eᵢ}}` (CRT)

The composite middle-modulus flattening was proved impossible (`…CompositeFlatten`).  This file decomposes the barrier
into its constituents: by CRT, a composite `MOD_m∘AND` gate is the **conjunction of prime-power `MOD∘AND` gates**, each of
which *does* flatten — over its own matching field.

  `modMFn m S` — `MOD_m∘AND` (residue 0) as a Boolean function `[#(accepting AND gates) ≡ 0 mod m]`.
  `modMFn_mul_coprime` — **CRT (proved)**: for coprime `a, b`, `MOD_{ab}∘AND = MOD_a∘AND ∧ MOD_b∘AND`.
  `modMFn_prod_coprime` — the full factorisation: for pairwise-coprime moduli, `MOD_{∏mᵢ}∘AND = ⋀ᵢ MOD_{mᵢ}∘AND`.
  `mod6_eq_mod2_and_mod3` — the concrete case: `MOD_6∘AND = MOD_2∘AND ∧ MOD_3∘AND`.

## What this pins down — the barrier is *purely* the field incompatibility

Each prime-power factor `MOD_{pᵢ^{eᵢ}}∘AND` flattens to a low-degree monomial-`AND` polynomial **over `F_{pᵢ}`**
(the `char`-matching case, `…ModpAndFlatten`: `nframeComplexity_charModAndFn_le`).  So a composite `MOD_m` gate is a
conjunction of pieces that are *each individually flattenable* — just over **different, incompatible characteristics**.
The obstruction is therefore *entirely* the multi-field problem: no single field flattens all the factors
(`nframeComplexity_charModFn_le` two-fields blind spot, C15), and the CRT product ring `∏ F_{pᵢ}` where they would
combine is not a field (`zmod6_not_isField`, C16).

So the composite barrier is now decomposed to a single sharp statement: **`MOD_6 = MOD_2 ∧ MOD_3`, each half flattens over
its own field, and the halves live over `F_2` and `F_3` which cannot be merged into one field for the dimension
argument.** Crossing it means flattening a conjunction across two incompatible characteristics at once — the genuinely
open step.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACC0

open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)

variable {n mm : ℕ}

/-- `MOD_m∘AND` (residue 0) as a Boolean function: `[#(accepting AND gates) ≡ 0 mod m]`. -/
def modMFn (m : ℕ) (S : Fin mm → Finset (Fin n)) : (Fin n → Bool) → Bool :=
  fun x => decide ((∑ j, if monoAND (S j) x then 1 else 0) % m = 0)

/-- **CRT decomposition (proved)**: for coprime `a, b`, `MOD_{ab}∘AND = MOD_a∘AND ∧ MOD_b∘AND`. -/
theorem modMFn_mul_coprime {a b : ℕ} (hab : Nat.Coprime a b) (S : Fin mm → Finset (Fin n)) :
    modMFn (a * b) S = fun x => modMFn a S x && modMFn b S x := by
  funext x
  simp only [modMFn]
  rw [← Bool.decide_and, decide_eq_decide, Nat.dvd_iff_mod_eq_zero.symm,
      Nat.dvd_iff_mod_eq_zero.symm, Nat.dvd_iff_mod_eq_zero.symm]
  constructor
  · intro h; exact ⟨(dvd_mul_right a b).trans h, (dvd_mul_left b a).trans h⟩
  · rintro ⟨ha, hb⟩; exact hab.mul_dvd_of_dvd_of_dvd ha hb

/-- **The full factorisation (proved)**: for pairwise-coprime moduli, `MOD_{∏ mᵢ}∘AND = ⋀ᵢ MOD_{mᵢ}∘AND`. -/
theorem modMFn_prod_coprime {ι : Type*} (s : Finset ι) (mo : ι → ℕ)
    (hco : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (mo i) (mo j)) (S : Fin mm → Finset (Fin n)) :
    modMFn (∏ i ∈ s, mo i) S = fun x => ∏ i ∈ s, modMFn (mo i) S x := by
  classical
  induction s using Finset.induction with
  | empty => funext x; simp only [modMFn, Nat.mod_one, Finset.prod_empty]; rfl
  | insert a s ha ih =>
    have hcoS : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (mo i) (mo j) :=
      fun i hi j hj hij => hco i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hcopr : Nat.Coprime (mo a) (∏ i ∈ s, mo i) :=
      Nat.Coprime.prod_right (fun i hi =>
        hco a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (fun h => ha (h ▸ hi)))
    rw [Finset.prod_insert ha, modMFn_mul_coprime hcopr, ih hcoS]
    funext x
    rw [Finset.prod_insert ha]
    rfl

/-- **The concrete case (proved)**: `MOD_6∘AND = MOD_2∘AND ∧ MOD_3∘AND` — the `MOD_6` barrier's two flattenable halves,
living over `F_2` and `F_3`. -/
theorem mod6_eq_mod2_and_mod3 (S : Fin mm → Finset (Fin n)) :
    modMFn 6 S = fun x => modMFn 2 S x && modMFn 3 S x :=
  modMFn_mul_coprime (a := 2) (b := 3) (by decide) S

end PallLean.Paper93.DeepMath.PathB.NFrameACC0

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.modMFn_mul_coprime
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.modMFn_prod_coprime
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.mod6_eq_mod2_and_mod3
