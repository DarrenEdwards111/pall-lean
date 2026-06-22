import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Mod6SymAndDepth2
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0AlgorithmicEscape

/-!
# Exact MOD-layer SYM∘AND for arbitrary modulus (PROVED)

A genuine run at the **exact MOD-layer SYM∘AND** (the symmetric-counting exact form), generalising the
`MOD₆∘AND` base case (`ACC0Mod6SymAndDepth2`) to arbitrary modulus/residue, and proving the *MOD-layer*
essence: an entire layer of `MOD` gates over a shared bottom `AND`-base is determined by the **single**
satisfied-`AND` count.

The bottom layer is the `satCount` — the number of satisfied degree-`≤ D` `AND` gates.  This is the
exact symmetric-counting form: every `MOD_m` gate at residue `r` over that base is *exactly*
`countMod`-style `(satCount % m = r)`, a symmetric function of the bottom `AND`s; and a whole MOD-layer
reads one and the same integer count.

## What is proved (clean axioms, no `sorry`)

* `modm_depth2_symAnd_repr` — `MOD_m∘AND` at residue `r` *is* `modmSym m r ∘ satCount` (exact SYM∘AND).
* `modm_depth2_countMod` — the residue-`0` gate is exactly the `countMod (satCount) m` observable.
* `modm_depth2_symmetric` — the gate depends only on `satCount` (the SYM content).
* `modLayer_reads_single_count` — **the MOD-layer essence**: every gate in a layer of MOD gates over a
  shared `AND`-base is invariant under equal `satCount`, i.e. the whole layer is a function of one count.
* `modm_bottom_count_le_quasipoly` — the bottom `AND`-base has `≤ (n+1)^D` distinct gates (quasipoly).

## Honest scope

This is the **exact** depth-2 MOD-layer SYM∘AND base case for *all* moduli, plus the single-count
essence of a MOD-layer — the genuine symmetric-counting form Williams' route needs at the bottom.  The
deep open content is unchanged: the **composition / mini-Beigel–Tarui blow-up lemma** (composing
`MOD/AND/OR/NOT` of SYM∘AND-represented subcircuits with quasipoly blow-up) is the remaining gap to a
full exact ACC⁰ SYM∘AND.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModmSymAndDepth2

open PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2 (satCount mod6_bottom_count_le_quasipoly)
open PallLean.Paper93.DeepMath.PathB.ACC0AlgorithmicEscape (countMod count_computes_all_moduli)

variable {n t D : ℕ}

/-- **The top symmetric function**: `MOD_m` at residue `r` of a count. -/
def modmSym (m r s : ℕ) : Prop := s % m = r

/-- **The depth-2 `MOD_m∘AND` circuit at residue `r`**: the count of satisfied bottom `AND`s is `≡ r (mod m)`. -/
def modmAndCircuit (m r : ℕ) (supports : Fin t → Finset (Fin n)) (x : Fin n → Bool) : Prop :=
  satCount supports x % m = r

/-- **Exact `SYM∘AND` representation for arbitrary `(m, r)` (proved).**  The depth-2 circuit *is* the
symmetric function `modmSym m r` applied to the satisfied-`AND` count — the defining `SYM∘AND` form. -/
theorem modm_depth2_symAnd_repr (m r : ℕ) (supports : Fin t → Finset (Fin n)) (x : Fin n → Bool) :
    modmAndCircuit m r supports x ↔ modmSym m r (satCount supports x) := Iff.rfl

/-- **The residue-`0` gate is exactly the `countMod` observable (proved).**  A single integer count feeds
`countMod (·) m` for *every* modulus `m` — the symmetric-counting observable. -/
theorem modm_depth2_countMod (m : ℕ) (supports : Fin t → Finset (Fin n)) (x : Fin n → Bool) :
    modmAndCircuit m 0 supports x ↔ countMod (satCount supports x) m = true := by
  unfold modmAndCircuit
  rw [count_computes_all_moduli]
  simp [Nat.mod_zero]

/-- **The depth-2 circuit is symmetric in the `AND` layer (proved).**  It depends only on `satCount`. -/
theorem modm_depth2_symmetric (m r : ℕ) (supports supports' : Fin t → Finset (Fin n))
    (x y : Fin n → Bool) (h : satCount supports x = satCount supports' y) :
    modmAndCircuit m r supports x ↔ modmAndCircuit m r supports' y := by
  unfold modmAndCircuit; rw [h]

/-- **The MOD-layer essence (proved): a whole layer of MOD gates over a shared `AND`-base is determined
by the single satisfied-`AND` count.**  For any family of `(modulus, residue)` pairs sharing the bottom
`AND`-base `supports`, every gate is invariant under equal `satCount` — the entire MOD-layer is a
function of one integer count.  This is the exact symmetric-counting form. -/
theorem modLayer_reads_single_count {k : ℕ} (L : Fin k → ℕ × ℕ)
    (supports : Fin t → Finset (Fin n)) (x y : Fin n → Bool)
    (h : satCount supports x = satCount supports y) (i : Fin k) :
    modmAndCircuit (L i).1 (L i).2 supports x ↔ modmAndCircuit (L i).1 (L i).2 supports y := by
  unfold modmAndCircuit; rw [h]

/-- **Quasipolynomial bottom-`AND` count (proved), modulus-independent.**  The bottom layer of distinct
degree-`≤ D` `AND` gates has `≤ (n+1)^D` gates — the same Beigel–Tarui bound, now for the general
MOD-layer base. -/
theorem modm_bottom_count_le_quasipoly (supports : Fin t → Finset (Fin n))
    (hD : ∀ j, (supports j).card ≤ D) (hinj : Function.Injective supports) :
    t ≤ (n + 1) ^ D :=
  mod6_bottom_count_le_quasipoly supports hD hinj

/-!
**Exact MOD-layer SYM∘AND proved for all moduli.**  `MOD_m∘AND` at any residue is exactly
`modmSym m r ∘ satCount`; the residue-`0` gate is the `countMod` observable; a whole MOD-layer over a
shared `AND`-base reads one integer count; the bottom layer is quasipoly.  This is the genuine
symmetric-counting base.  The composition / mini-Beigel–Tarui blow-up lemma remains the open gap to a
full exact ACC⁰ SYM∘AND.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModmSymAndDepth2

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModmSymAndDepth2.modm_depth2_symAnd_repr
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModmSymAndDepth2.modLayer_reads_single_count
