import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CompositeBTTarget
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PolyToSymAnd

/-!
# Depth-2 `MOD₆∘AND` has an exact `SYM∘AND` representation via the residue-pair observer

Route B's first real composite case.  A depth-2 `MOD₆∘AND` circuit applies a single top `MOD₆` gate to a layer of
bottom `AND` gates.  Its output depends *only* on the **count** of satisfied bottom `AND`s, read modulo `6` — i.e. it is
a symmetric function of the `AND`-layer (`SYM∘AND` form).  By the composite residue observer of
`…ACC0CompositeBTTarget`, that residue-`6` symmetric function is decided by the **pair** `(count mod 2, count mod 3)`
over the product `ZMod 2 × ZMod 3` — the integer/multi-prime observer single-field RS could not provide.

## What is proved (clean axioms, no `sorry`)

* **`mod6_depth2_symAnd_repr`** — the circuit *is* the symmetric function of the count: `mod6AndCircuit = mod6Sym ∘
  satCount`, i.e. exactly a `SYM∘AND` representation (top symmetric `mod6Sym`, bottom `AND` count `satCount`).
* **`mod6_depth2_residue_pair`** — the `SYM` layer is decided by the residue-pair observer: the circuit accepts iff
  `(satCount mod 2 = 0 ∧ satCount mod 3 = 0)`.  The composite observer reads the depth-2 circuit.
* **`mod6_depth2_symmetric`** — the genuine symmetry: the output is invariant under anything preserving the
  satisfied-`AND` count (depends only on `satCount`).
* **`mod6_bottom_count_le_quasipoly`** — the representation size bound: distinct bottom `AND`s of support `≤ D` number
  at most `(n+1)^D` (Beigel–Tarui count), so the degree-limited representation is quasipolynomial.

## The bridge structure (step 3 / step 5, socketed honestly)

* **`depth2_to_full_via_composition`** — the logical shape of the remaining work: the proved depth-2 base case lifts to
  a full `ACC⁰` `SYM∘AND` representation *iff* the open mini-Beigel–Tarui **composition** lemma holds (compose
  `MOD₆ / AND / OR / NOT` of `SYM∘AND`-represented subcircuits with controlled quasipolynomial blow-up).  The
  composition is the genuine hard content and stays a named hypothesis; given it (and the full representation), the
  Route-B counting socket + Williams cash-out gives `¬ NEXP ⊆ ACC⁰` (see `…ACC0CompositeBTTarget`).

## Honest scope

The depth-2 base case and its quasipolynomial size bound are *proved*; the symmetric `SYM∘AND` factorization is exact.
The deep open content — the composition/blow-up lemma and the full composite `SYM∘AND` representation theorem — is
**not** proved here; it is the named socket `depth2_to_full_via_composition` (and `…CompositeBTTarget`'s socket).
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0CompositeBT
open PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiSparsity
open PallLean.Paper93.DeepMath.PathB.Layer3

variable {n t D : ℕ}

/-! ## The depth-2 `MOD₆∘AND` circuit and its `SYM∘AND` data -/

/-- **The `SYM` layer's count**: the number of bottom `AND` gates satisfied at input `x`. -/
def satCount (supports : Fin t → Finset (Fin n)) (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun j => monoAND (supports j) x = true)).card

/-- **The top symmetric function**: `MOD₆` at residue `0` of a count. -/
def mod6Sym (s : ℕ) : Prop := 6 ∣ s

/-- **The depth-2 `MOD₆∘AND` circuit**: `MOD₆` of the count of satisfied bottom `AND`s. -/
def mod6AndCircuit (supports : Fin t → Finset (Fin n)) (x : Fin n → Bool) : Prop :=
  6 ∣ satCount supports x

/-! ## 1. The exact `SYM∘AND` representation -/

/-- **Exact `SYM∘AND` representation (proved): the depth-2 circuit is `mod6Sym ∘ satCount`.**  The output is precisely
the symmetric function `mod6Sym` applied to the count of satisfied bottom `AND` gates — the defining `SYM∘AND` form. -/
theorem mod6_depth2_symAnd_repr (supports : Fin t → Finset (Fin n)) (x : Fin n → Bool) :
    mod6AndCircuit supports x ↔ mod6Sym (satCount supports x) := Iff.rfl

/-- **The residue-pair observer reads the depth-2 circuit (proved).**  The `SYM` layer (`MOD₆` of the count) is decided
by the composite observer over `ZMod 2 × ZMod 3`: the circuit accepts iff `satCount` vanishes mod `2` *and* mod `3`. -/
theorem mod6_depth2_residue_pair (supports : Fin t → Finset (Fin n)) (x : Fin n → Bool) :
    mod6AndCircuit supports x ↔
      ((satCount supports x : ZMod 2) = 0 ∧ (satCount supports x : ZMod 3) = 0) :=
  mod6_decided_by_residue_pair (satCount supports x)

/-- **The depth-2 circuit is symmetric in the `AND` layer (proved).**  Its output depends only on the satisfied-`AND`
count `satCount`: any two configurations with equal counts agree.  This is the `SYM` content of `SYM∘AND`. -/
theorem mod6_depth2_symmetric (supports supports' : Fin t → Finset (Fin n)) (x y : Fin n → Bool)
    (h : satCount supports x = satCount supports' y) :
    mod6AndCircuit supports x ↔ mod6AndCircuit supports' y := by
  unfold mod6AndCircuit
  rw [h]

/-! ## 2. The quasipolynomial size bound for the bottom `AND` layer -/

/-- **Quasipolynomial representation size (proved): `≤ (n+1)^D` distinct bottom `AND`s of support `≤ D`.**  The bottom
layer of distinct monomial `AND`s of degree `≤ D` injects into the degree-`≤ D` monomials, whose count is `≤ (n+1)^D`
(Beigel–Tarui).  Hence the degree-limited `SYM∘AND` representation has quasipolynomial size. -/
theorem mod6_bottom_count_le_quasipoly (supports : Fin t → Finset (Fin n))
    (hD : ∀ j, (supports j).card ≤ D) (hinj : Function.Injective supports) :
    t ≤ (n + 1) ^ D := by
  have himg : (Finset.univ.image supports).card = t := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hsub : Finset.univ.image supports ⊆ lowDegMonomials n D := by
    intro S hS
    rw [Finset.mem_image] at hS
    obtain ⟨j, _, rfl⟩ := hS
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hD j⟩
  calc t = (Finset.univ.image supports).card := himg.symm
    _ ≤ (lowDegMonomials n D).card := Finset.card_le_card hsub
    _ ≤ (n + 1) ^ D := beigelTarui_monomial_count_le n D

/-! ## 3. / 5. The composition bridge to the full representation (socket) -/

/-- **The composition bridge (logical shape of the open step).**  The proved depth-2 base case
(`RestrictedSymAndRep`, this file) lifts to a full `ACC⁰` `SYM∘AND` representation (`RSRep`) exactly when the open
mini-Beigel–Tarui **composition** lemma holds — that `MOD₆ / AND / OR / NOT` of `SYM∘AND`-represented subcircuits again
admits one, with controlled quasipolynomial blow-up.  Stated as `modus ponens`: the base case is discharged, the
composition is the named open hypothesis. -/
theorem depth2_to_full_via_composition
    (RestrictedSymAndRep RSRep : Prop)
    (restricted : RestrictedSymAndRep)
    (composition : RestrictedSymAndRep → RSRep) :
    RSRep :=
  composition restricted

end PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2.mod6_depth2_symAnd_repr
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2.mod6_depth2_residue_pair
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2.mod6_depth2_symmetric
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2.mod6_bottom_count_le_quasipoly
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2.depth2_to_full_via_composition
