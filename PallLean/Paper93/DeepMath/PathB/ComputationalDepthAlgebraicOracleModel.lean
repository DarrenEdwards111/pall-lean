import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRelativizationBarrier
import Mathlib.Data.ZMod.Basic

/-!
# A concrete algebraic-oracle model instantiating the algebrization barrier

`OracleCircuitModel` grounded the **relativization** (Baker–Gill–Solovay) barrier in a real Boolean
oracle-circuit model.  This file does the same for the **algebrization** (Aaronson–Wigderson) barrier,
whose extra content is that the oracle is queried **over a ring** (its low-degree extension), not only at
Boolean points — yet on the Boolean points it still equals the target, so the same collapse defeats
*algebrizing* separating measures too.

* **`ACirc n R`** — arithmetic circuits over a commutative ring `R` on `n` Boolean inputs (embedded by
  `ι : Bool → R`), with `add/mul/const` gates **plus algebraic oracle gates** querying `A : (Fin k → R) → R`.
* **`evalA ι A c` / `sizeA c`** — ring-valued evaluation and gate size; the circuit computes a Boolean
  function via a decoder `decode : R → Bool`.
* **`SIZErelA ι decode A n s`** — a genuine `SIZErel` for the abstract framework (over algebraic oracles).
* **`concrete_algebraic_collapse`** — the AW mechanism concretely: relative to the algebraic oracle that
  **extends** `L` (agrees with `L` after decoding on embedded Boolean queries), one algebraic gate on the
  inputs computes `L n` in size `n + 1`.  So `L` is easy relative to its extension — `OracleCollapseBarrier`
  holds.
* **`no_relativizing_separatingMeasure_algebraic`** — plugging this into the abstract obstruction: **no
  measure separates `L` relative to every algebraic oracle.**  Non-vacuous: instantiated over `ZMod 2`.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.AlgebraicOracleModel

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.RelativizationBarrier

/-- An **algebraic oracle** over `R`: answers a query `(Fin k → R) → R` at ring points. -/
abbrev AOracle (R : Type*) := (k : ℕ) → (Fin k → R) → R

/-- **Arithmetic oracle circuits** on `n` Boolean inputs, valued in `R`. -/
inductive ACirc (n : ℕ) (R : Type*) : Type _
  | inp : Fin n → ACirc n R
  | const : R → ACirc n R
  | add : ACirc n R → ACirc n R → ACirc n R
  | mul : ACirc n R → ACirc n R → ACirc n R
  | aoracle : (k : ℕ) → (Fin k → ACirc n R) → ACirc n R

variable {n : ℕ} {R : Type*} [CommRing R]

/-- Ring-valued evaluation relative to an algebraic oracle `A`, embedding Boolean inputs by `ι`. -/
def evalA (ι : Bool → R) (A : AOracle R) : ACirc n R → (Fin n → Bool) → R
  | .inp i, x => ι (x i)
  | .const r, _ => r
  | .add a b, x => evalA ι A a x + evalA ι A b x
  | .mul a b, x => evalA ι A a x * evalA ι A b x
  | .aoracle k ch, x => A k (fun i => evalA ι A (ch i) x)

/-- Gate size of an arithmetic oracle circuit. -/
def sizeA : ACirc n R → ℕ
  | .inp _ => 1
  | .const _ => 1
  | .add a b => sizeA a + sizeA b + 1
  | .mul a b => sizeA a + sizeA b + 1
  | .aoracle _ ch => (∑ i, sizeA (ch i)) + 1

/-- **The algebraic-oracle-relativized size class**: Boolean functions computed (after decoding) by a
size-`≤ s` arithmetic oracle circuit with algebraic oracle `A`.  A genuine `SIZErel`. -/
def SIZErelA (ι : Bool → R) (decode : R → Bool) (A : AOracle R) (n s : ℕ) :
    Set ((Fin n → Bool) → Bool) :=
  { f | ∃ c : ACirc n R, sizeA c ≤ s ∧ ∀ x, decode (evalA ι A c x) = f x }

/-- The single-oracle-gate arithmetic circuit querying the embedded inputs directly. -/
def directQueryA (n : ℕ) (R : Type*) : ACirc n R := .aoracle n (fun i => .inp i)

theorem evalA_directQueryA (ι : Bool → R) (A : AOracle R) (x : Fin n → Bool) :
    evalA ι A (directQueryA n R) x = A n (fun i => ι (x i)) := rfl

theorem sizeA_directQueryA (n : ℕ) : sizeA (directQueryA n R) = n + 1 := by
  simp only [directQueryA, sizeA]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/-- **The concrete algebraic collapse (proved).**  Given a Boolean embedding `ι` with a left-inverse
`decode` (`decode ∘ ι = id`), the algebraic oracle `A_L` that extends `L`
(`A_L k q = ι (L k (decode ∘ q))`) makes the target easy: one algebraic gate computes `L n` in size
`n + 1`.  Hence `OracleCollapseBarrier L (SIZErelA ι decode)`. -/
theorem concrete_algebraic_collapse (L : Layer7.BoolLang)
    (ι : Bool → R) (decode : R → Bool) (hrt : ∀ b, decode (ι b) = b) :
    OracleCollapseBarrier L (SIZErelA ι decode) := by
  refine ⟨(fun k q => ι (L k (fun i => decode (q i)))), (fun n => n + 1),
    ⟨2, 1, 2, fun n => by show n + 1 ≤ 2 * n ^ 1 + 2; rw [pow_one]; omega⟩, ?_⟩
  intro n
  refine ⟨directQueryA n R, le_of_eq (sizeA_directQueryA n), fun x => ?_⟩
  rw [evalA_directQueryA]
  show decode (ι (L n (fun i => decode (ι (x i))))) = L n x
  simp only [hrt]

/-- **THE CONCRETE ALGEBRIZATION OBSTRUCTION (proved).**  In this arithmetic oracle-circuit model no
measure separates `L` relative to every algebraic oracle: the algebraic extension of `L` collapses it,
contradicting condition (B). -/
theorem no_relativizing_separatingMeasure_algebraic (L : Layer7.BoolLang)
    (ι : Bool → R) (decode : R → Bool) (hrt : ∀ b, decode (ι b) = b)
    (rm : RelativizingSeparatingMeasure L (SIZErelA ι decode)) : False :=
  no_relativizing_separatingMeasure (SIZErelA ι decode) rm
    (concrete_algebraic_collapse L ι decode hrt)

/-! ### Non-vacuity: a concrete field instance over `ZMod 2` -/

/-- Boolean embedding into `ZMod 2`. -/
def ι₂ : Bool → ZMod 2 := fun b => if b then 1 else 0

/-- Decoder `ZMod 2 → Bool`. -/
def decode₂ : ZMod 2 → Bool := fun r => decide (r = 1)

theorem decode₂_ι₂ : ∀ b, decode₂ (ι₂ b) = b := by decide

/-- **The algebrization barrier is inhabited over `ZMod 2` (proved).**  A real field, a real embedding,
a real collapse. -/
theorem zmod2_algebraic_collapse (L : Layer7.BoolLang) :
    OracleCollapseBarrier L (SIZErelA ι₂ decode₂) :=
  concrete_algebraic_collapse L ι₂ decode₂ decode₂_ι₂

theorem no_relativizing_separatingMeasure_zmod2 (L : Layer7.BoolLang)
    (rm : RelativizingSeparatingMeasure L (SIZErelA ι₂ decode₂)) : False :=
  no_relativizing_separatingMeasure (SIZErelA ι₂ decode₂) rm (zmod2_algebraic_collapse L)

end PallLean.Paper93.DeepMath.PathB.AlgebraicOracleModel

#print axioms PallLean.Paper93.DeepMath.PathB.AlgebraicOracleModel.concrete_algebraic_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.AlgebraicOracleModel.no_relativizing_separatingMeasure_zmod2
