import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSeparatingMeasure

/-!
# A non-algebraic wiring measure — genuinely small on the P side

The P-side upper bound (A) demands a measure that is **small for small circuits**.  SPDP rank was meant
to be that ("P-time ⇒ low rank") but is **not**: it is `> n²⁰⁰` for *every* machine
(`cookLevinExactWithinProfile_false_at_2pow804`), so it is large in the bulk as well as the boundary —
no gap.  The failure is that arithmetization can't see the circuit's wiring.

Here is a measure that *does* read the wiring — **circuit depth**, defined by structural recursion on the
Boolean gates (`input/const/not/and/or`), not by any ring evaluation.  Its induced function-measure
`minDepth` is the minimum depth over circuits computing `f`.  It is **provably small on the P side**:

* **`minDepth_le_of_mem`** — condition (A): `f ∈ SIZE n s → minDepth n f ≤ s`.  (Via `depth ≤ size`.)

So `minDepth` is a genuine non-algebraic wiring measure that satisfies the P-side bound SPDP failed.  It
plugs straight into the target:

* **`depthMeasure`** — `¬(minDepth poly-bounded on L) → SeparatingMeasure L`, and
* **`depthMeasure_gives_separation`** — the hardness of `minDepth` on `L` would prove `L ∉ P/poly`.

What remains open is exactly (B): whether `minDepth` (or any wiring measure) is superpolynomial on the
target.  Being non-algebraic, it *dodges* the algebrization barrier that killed SPDP — it is on the right
side of the barriers, with (A) discharged.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.WiringMeasure

open PallLean.Paper93.DeepMath.PathB
open Layer8

variable {n : ℕ}

/-- **Circuit depth** — a wiring quantity read by structural recursion on the Boolean gates. -/
def depth : Circuit n → ℕ
  | .input _ => 0
  | .const _ => 0
  | .not c => depth c + 1
  | .and a b => max (depth a) (depth b) + 1
  | .or a b => max (depth a) (depth b) + 1

/-- **Depth is bounded by size (proved).**  So any measure induced by depth inherits the P-side bound. -/
theorem depth_le_size (c : Circuit n) : depth c ≤ c.size := by
  induction c with
  | input i => simp [depth, Circuit.size]
  | const b => simp [depth, Circuit.size]
  | not c ih => simp only [depth, Circuit.size]; omega
  | and a b iha ihb => simp only [depth, Circuit.size]; omega
  | or a b iha ihb => simp only [depth, Circuit.size]; omega

/-- **Minimum circuit depth** — the wiring function-measure. -/
noncomputable def minDepth (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf { d | ∃ c : Circuit n, Computes c f ∧ depth c = d }

/-- **(A): the wiring measure is small on the P side (proved).**  A size-`s` circuit for `f` bounds
`minDepth n f` by `s` — small circuits keep the measure small, exactly the P-side upper bound. -/
theorem minDepth_le_of_mem {n s : ℕ} {f : (Fin n → Bool) → Bool}
    (hmem : f ∈ Layer8.SIZE n s) : minDepth n f ≤ s := by
  obtain ⟨c, hcs, hcf⟩ := hmem
  have h1 : minDepth n f ≤ depth c := Nat.sInf_le ⟨c, hcf, rfl⟩
  have h2 : depth c ≤ c.size := depth_le_size c
  omega

/-- **The wiring separating measure (proved).**  If `minDepth` is not polynomially bounded on `L`, it is
a `SeparatingMeasure` for `L` — a non-algebraic, circuit-structural witness with (A) already discharged. -/
noncomputable def depthMeasure (L : Layer7.BoolLang)
    (hB : ¬ ∃ p : ℕ → ℕ, Layer7.IsPolyBounded p ∧ ∀ n, minDepth n (L n) ≤ p n) :
    SeparatingMeasure.SeparatingMeasure L where
  I := minDepth
  h := fun m => m
  hpoly := ⟨2, 1, 2, fun m => by show m ≤ 2 * m ^ 1 + 2; rw [pow_one]; omega⟩
  circuitBounded := fun _ _ _ hmem => minDepth_le_of_mem hmem
  hardOnTarget := hB

/-- **The wiring route to the separation (proved).**  Superpolynomial `minDepth` on `L` proves
`L ∉ P/poly`.  This is exactly the open content — (B) for a non-algebraic wiring measure. -/
theorem depthMeasure_gives_separation (L : Layer7.BoolLang)
    (hB : ¬ ∃ p : ℕ → ℕ, Layer7.IsPolyBounded p ∧ ∀ n, minDepth n (L n) ≤ p n) :
    ¬ Layer9.Ppoly L :=
  SeparatingMeasure.separatingMeasure_not_ppoly (depthMeasure L hB)

end PallLean.Paper93.DeepMath.PathB.WiringMeasure

#print axioms PallLean.Paper93.DeepMath.PathB.WiringMeasure.minDepth_le_of_mem
#print axioms PallLean.Paper93.DeepMath.PathB.WiringMeasure.depthMeasure_gives_separation
