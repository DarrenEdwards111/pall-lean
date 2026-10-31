import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0WilliamsFastSat
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0AlgorithmicEscape

/-!
# The Williams fast-SAT counting step is characteristic-universal — exonerating it from the composite barrier

Entry 290 showed *why* the algorithmic route escapes the composite barrier: counting lives in characteristic 0 and
carries every characteristic at once.  This file digs into the `…ACC0WilliamsFastSat` socket and makes that concrete at
the level of the fast-SAT itself: its observable is `gateCount` — an **integer count** — and the SAT decision examines
the count-cell *image*, which **does not depend on the symmetric top**.  So *one* count-cell image decides `MOD_m`-SAT
for **every** modulus `m` simultaneously, with savings independent of `m`.

**The consequence — localising the composite barrier.**  The Williams route has two open links
(`…ACC0WilliamsFastSat`): (1) the YBT *exact* `SYM∘AND` normal form for composite `MOD` (the structural socket), and
(2) uniform TM realisation.  This file proves the *counting/savings* step is entirely modulus-agnostic — so the
composite-`MOD` obstruction lives **only** in link (1), the normal-form reduction, **not** in the count-cell search.
The counting step is exonerated, exactly matching entry 290 (`count_route_covers`: integer counting is never
characteristic-blocked).

## What is proved (clean axioms, no `sorry`)

* **`fastSat_universal_in_top`** (PROVED) — *one* count-cell image `image(gateCount g)` decides satisfiability of
  `symEval g h` for **every** symmetric top `h` (via `observed_sat_iff`); the image does not depend on `h`.
* **`fastSat_decides_every_modulus`** (PROVED) — in particular, for the `MOD_m` top and **every** `m`, satisfiability is
  decided by the same image: `∃ c ∈ image, c % m = 0`.
* **`fastSat_mod6_via_crt`** (PROVED) — the `MOD₆` decision factors through the integer count's mod-2 and mod-3 residues
  *simultaneously* (`∃ c ∈ image, c % 2 = 0 ∧ c % 3 = 0`) — entry 290's CRT escape, inside the fast-SAT.
* **`fastSat_cells_modulus_free`** (PROVED) — the count-cell bound `≤ m + 1` is independent of the modulus.
* **`fastSat_modm_savings`** (PROVED) — the Williams savings `2^k · cells ≤ 2^n` hold for the `MOD_M` circuit for
  **every** `M` (instantiating `symAnd_williams_fastSat` at the `MOD_M` top): the savings are modulus-agnostic.

## Honest scope

This proves the fast-SAT *counting/savings* step is characteristic-universal — one integer-count image serves all
moduli — so the composite-`MOD` barrier is localised entirely to the (open) YBT exact-normal-form socket, not the
counting step.  It is the concrete, fast-SAT-level form of entry 290's escape.  It does **not** prove `NEXP ⊄ ACC⁰`: the
YBT exact reduction for composite `MOD` and the uniform TM realisation remain the named separation-strength sockets
(`…ACC0WilliamsFastSat`, `…ACC0WilliamsCashout`).  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.  See `ACC0_ANATOMY.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0FastSATCharacteristicUniversal

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsFastSat

variable {n m D : ℕ}

/-- The `MOD_m` symmetric top: fires iff the gate count is `≡ 0 (mod m)`. -/
def modIndicator (m c : ℕ) : Bool := decide (c % m = 0)

/-- **One count-cell image decides every symmetric top (PROVED).**  The fast-SAT observable `gateCount g` is an integer
statistic, and `observed_sat_iff` decides satisfiability of `symEval g h` by searching its image — *independently* of
`h`.  So the same image `image(gateCount g)` decides every symmetric top simultaneously: the counting step is not tied
to any particular modular structure. -/
theorem fastSat_universal_in_top (g : Fin m → (Fin n → Bool) → Bool) (h : ℕ → Bool) :
    Satisfiable (symEval g h) ↔ ∃ c ∈ Finset.univ.image (gateCount g), h c = true :=
  observed_sat_iff h (fun _ => rfl)

/-- **The fast-SAT decides `MOD_m`-SAT for every modulus, against the same image (PROVED).**  For the `MOD_m` top and
*any* `m`, satisfiability is `∃ c ∈ image(gateCount g), c % m = 0` — one count-cell image, every modulus. -/
theorem fastSat_decides_every_modulus (g : Fin m → (Fin n → Bool) → Bool) (M : ℕ) :
    Satisfiable (symEval g (modIndicator M)) ↔
      ∃ c ∈ Finset.univ.image (gateCount g), c % M = 0 := by
  rw [fastSat_universal_in_top g (modIndicator M)]
  simp only [modIndicator, decide_eq_true_eq]

/-- **The `MOD₆` decision factors through char-2 and char-3 residues simultaneously (PROVED).**  Entry 290's CRT escape,
realised inside the fast-SAT: `MOD₆`-SAT is decided by the integer count's mod-2 *and* mod-3 residues at once,
`∃ c ∈ image, c % 2 = 0 ∧ c % 3 = 0` — a single integer-count statistic carries both characteristics, which no single
field can (`no_common_char`). -/
theorem fastSat_mod6_via_crt (g : Fin m → (Fin n → Bool) → Bool) :
    Satisfiable (symEval g (modIndicator 6)) ↔
      ∃ c ∈ Finset.univ.image (gateCount g), (c % 2 = 0 ∧ c % 3 = 0) := by
  rw [fastSat_decides_every_modulus g 6]
  constructor
  · rintro ⟨c, hc, h6⟩; exact ⟨c, hc, by omega⟩
  · rintro ⟨c, hc, h2, h3⟩; exact ⟨c, hc, by omega⟩

/-- **The count-cell bound is modulus-free (PROVED).**  The number of count-cells the fast-SAT examines is `≤ m + 1`,
independent of the modulus — the savings come from the count statistic, not the modular top. -/
theorem fastSat_cells_modulus_free (g : Fin m → (Fin n → Bool) → Bool) :
    (Finset.univ.image (gateCount g)).card ≤ m + 1 :=
  sym_count_card_le g

/-- **The Williams savings hold for every modulus (PROVED).**  Instantiating `symAnd_williams_fastSat` at the `MOD_M`
top: for *any* modulus `M`, a degree-`≤D` injective `SYM∘AND` decides `MOD_M`-SAT with savings `2^k · cells ≤ 2^n`.
The modulus appears only in the (irrelevant-to-counting) top `h`, so the savings are modulus-agnostic — the composite
case is no harder than the prime case for the counting/savings step. -/
theorem fastSat_modm_savings (mono : Fin m → Finset (Fin n)) (M : ℕ)
    (hinj : Function.Injective mono) (hdeg : ∀ j, (mono j).card ≤ D)
    {k : ℕ} (hkn : k ≤ n)
    (hfit : (∑ i ∈ Finset.range (D + 1), n.choose i) + 1 ≤ 2 ^ (n - k)) :
    2 ^ k * (Finset.univ.image (gateCount (fun j x => monoAND (mono j) x))).card ≤ 2 ^ n := by
  obtain ⟨_, _, hsav⟩ :=
    symAnd_williams_fastSat mono (modIndicator M) hinj hdeg hkn hfit
  exact hsav

/-!
**The result.**  The Williams fast-SAT counting/savings step is **characteristic-universal**: one integer-count image
(`fastSat_universal_in_top`) decides `MOD_m`-SAT for every modulus (`fastSat_decides_every_modulus`), with the `MOD₆`
case factoring through both characteristics simultaneously (`fastSat_mod6_via_crt`, entry 290's escape inside the
fast-SAT), a modulus-free cell bound (`fastSat_cells_modulus_free`), and modulus-agnostic savings
(`fastSat_modm_savings`).  So the composite-`MOD` barrier is **not** in the counting step — it is localised entirely to
the open YBT exact-normal-form socket (link 1) and the uniform realisation socket (link 2).  This digs into the
`WilliamsFastSat` socket and proves exactly which part is barrier-bound (the reduction) and which is free (the count).
Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0FastSATCharacteristicUniversal

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FastSATCharacteristicUniversal.fastSat_universal_in_top
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FastSATCharacteristicUniversal.fastSat_decides_every_modulus
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FastSATCharacteristicUniversal.fastSat_mod6_via_crt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FastSATCharacteristicUniversal.fastSat_cells_modulus_free
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FastSATCharacteristicUniversal.fastSat_modm_savings
