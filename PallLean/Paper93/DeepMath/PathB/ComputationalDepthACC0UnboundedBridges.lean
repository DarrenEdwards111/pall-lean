import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UnboundedFanin

/-!
# Entry 325 — the NW bridges ported onto the unbounded-fan-in model `UCirc` (proved)

Entry 324 built the faithful unbounded-fan-in `ACC⁰[m]` model `UCirc` (semantics, depth, size, modulus accounting, the
substitution `usubst`, and the defining unbounded-fan-in/constant-depth property).  This file **ports the two NW
bridges** — the Yao predictor (entry 321) and the reconstruction (entry 322) — onto `UCirc`, so the bridges are now
faithful to *unbounded fan-in* as well as depth and gate type.

**The Yao predictor as a `MOD₂` gadget.**  In `UCirc`, `XOR(a,b) = ¬MOD₂([a,b])` (since `MOD₂` fires on an *even* count,
so its negation fires on an *odd* count `= a ⊕ b`).  The guess-and-correct predictor `(x gidx) ⊕ ¬D` is therefore
`upredictor D gidx := ¬MOD₂([var gidx, ¬D])` — a genuine `ACC⁰[2]` circuit of depth `D.depth + 3`.

**The reconstruction via substitution.**  The reconstructed circuit is `usubst tables P` (the predictor `P` with the
hardwired block tables substituted into its inputs), reusing entry 324's `usubst`/`usubst_eval`/`usubst_depth_le` — so
its semantics and *depth* (additive) are already proved in the unbounded model.

## What is proved (clean axioms, no `sorry`)

* **`upredictor`, `upredictor_eval`** — the Yao predictor in `UCirc` computes the guess-and-correct rule
  `if D then g else ¬g`.
* **`upredictor_depth`** (PROVED) — `depth (upredictor D gidx) = D.depth + 3`: constant depth overhead.
* **`upredictor_isACC0`** (PROVED) — the predictor is `ACC⁰[2]` (its only `MOD` gate is `MOD₂`) when `D` is.
* **`UComputes`, `HasUCircuitOfDepth`, `HasUCircuitOfSize`** — a circuit computes `f`; `f` has a `UCirc` of bounded
  depth / size.
* **`usubst_size_le`** (PROVED) — substitution size bound `≤ size P · M`.
* **`ureconstructed_computes`** — the reconstructed circuit `usubst tables P` computes `f` from the composition
  correctness (via `usubst_eval`).
* **`ureconstructed_hasDepth`** / **`ureconstructed_hasSize`** (PROVED) — the reconstructed circuit is bounded-depth
  (`≤ P.depth + dt`) and bounded-size (`≤ size P · M`) — the unbounded-fan-in analogue of entry 322's
  `reconstructed_hasCircuit`, now `ACC⁰`-faithful in fan-in.

## Honest scope

This ports the Yao and reconstruction bridges onto the genuine unbounded-fan-in `ACC⁰[2]` model: the predictor is an
explicit `MOD₂` gadget of constant depth, and the reconstruction is `usubst` with proved semantics, depth, and size.
The bridges are now faithful in depth, gate type, **and** fan-in.  This still rests, as always, on the irreducible
hardness of the witness function and the design (the genuine inputs of the NW argument), and on the composition
correctness of the predictor and tables.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UnboundedBridges

open PallLean.Paper93.DeepMath.PathB.ACC0UnboundedFanin
open PallLean.Paper93.DeepMath.PathB.ACC0UnboundedFanin.UCirc

/-- **The Yao predictor in `UCirc`.**  `(x gidx) ⊕ ¬D`, realised as `¬MOD₂([var gidx, ¬D])` — a parity (`MOD₂`) over the
guessed input bit and the negated distinguisher, negated.  Outputs the guess when `D` accepts, the flipped guess
otherwise. -/
def upredictor {n : ℕ} (D : UCirc n) (gidx : Fin n) : UCirc n :=
  UCirc.unot (UCirc.umod 2 [UCirc.var gidx, UCirc.unot D])

/-- **The Yao predictor computes the guess-and-correct rule (PROVED).** -/
theorem upredictor_eval {n : ℕ} (D : UCirc n) (gidx : Fin n) (x : Fin n → Bool) :
    UCirc.eval x (upredictor D gidx) = (if UCirc.eval x D then x gidx else !(x gidx)) := by
  simp only [upredictor, UCirc.eval, List.map_cons, List.map_nil]
  cases hD : UCirc.eval x D <;> cases hg : x gidx <;> rfl

/-- **The Yao predictor adds constant depth (PROVED).**  `depth (upredictor D gidx) = D.depth + 3` (a `MOD₂` over a
`NOT`, all negated). -/
theorem upredictor_depth {n : ℕ} (D : UCirc n) (gidx : Fin n) :
    (upredictor D gidx).depth = D.depth + 3 := by
  simp only [upredictor, UCirc.depth, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
  omega

/-- **The Yao predictor is `ACC⁰[2]` (PROVED).**  If `D` uses only `MOD₂` gates, so does the predictor — its only
modular gate is the `MOD₂` it introduces. -/
theorem upredictor_isACC0 {n : ℕ} (D : UCirc n) (gidx : Fin n) (hD : IsACC0m 2 D) :
    IsACC0m 2 (upredictor D gidx) := by
  intro q hq
  have hmod : (upredictor D gidx).moduli = 2 :: D.moduli := by
    simp [upredictor, UCirc.moduli]
  rw [hmod, List.mem_cons] at hq
  rcases hq with h | h
  · exact h
  · exact hD q h

/-- **A `UCirc` computes a Boolean function.** -/
def UComputes {n : ℕ} (C : UCirc n) (f : (Fin n → Bool) → Bool) : Prop := ∀ x, UCirc.eval x C = f x

/-- **`f` has an unbounded-fan-in circuit of depth `≤ d`.** -/
def HasUCircuitOfDepth {n : ℕ} (f : (Fin n → Bool) → Bool) (d : ℕ) : Prop :=
  ∃ C : UCirc n, C.depth ≤ d ∧ UComputes C f

/-- **`f` has an unbounded-fan-in circuit of size `≤ s`.** -/
def HasUCircuitOfSize {n : ℕ} (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : UCirc n, C.size ≤ s ∧ UComputes C f

/-- **Substitution size bound (PROVED).**  `size (usubst g P) ≤ size P · M` when every sub-circuit has size `≤ M`
(`M ≥ 1`). -/
theorem usubst_size_le {n n' : ℕ} (g : Fin n → UCirc n') (M : ℕ)
    (hM : ∀ i, (g i).size ≤ M) (hM1 : 1 ≤ M) :
    ∀ C : UCirc n, (usubst g C).size ≤ C.size * M := by
  intro C
  induction C using UCirc.induction with
  | var i => simpa only [usubst, UCirc.size, one_mul] using hM i
  | const b => simp only [usubst, UCirc.size, one_mul]; exact hM1
  | unot c ih => simp only [usubst, UCirc.size]; nlinarith [ih, hM1]
  | uand cs ih =>
      have hsum : ((cs.map (usubst g)).map UCirc.size).sum ≤ (cs.map UCirc.size).sum * M := by
        rw [List.map_map, ← List.sum_map_mul_right]
        exact List.sum_le_sum (fun c hc => ih c hc)
      simp only [usubst, UCirc.size]; nlinarith [hsum, hM1]
  | uor cs ih =>
      have hsum : ((cs.map (usubst g)).map UCirc.size).sum ≤ (cs.map UCirc.size).sum * M := by
        rw [List.map_map, ← List.sum_map_mul_right]
        exact List.sum_le_sum (fun c hc => ih c hc)
      simp only [usubst, UCirc.size]; nlinarith [hsum, hM1]
  | umod m cs ih =>
      have hsum : ((cs.map (usubst g)).map UCirc.size).sum ≤ (cs.map UCirc.size).sum * M := by
        rw [List.map_map, ← List.sum_map_mul_right]
        exact List.sum_le_sum (fun c hc => ih c hc)
      simp only [usubst, UCirc.size]; nlinarith [hsum, hM1]

/-- **The reconstructed circuit computes `f` (PROVED).**  If the predictor `P` composed with the table sub-circuits
computes `fbool`, then `usubst tables P` computes `fbool` (via `usubst_eval`). -/
theorem ureconstructed_computes {n Nc : ℕ} (P : UCirc Nc) (tables : Fin Nc → UCirc n)
    (fbool : (Fin n → Bool) → Bool)
    (hcomp : ∀ x, UCirc.eval (fun j => UCirc.eval x (tables j)) P = fbool x) :
    UComputes (usubst tables P) fbool :=
  fun x => (usubst_eval tables x P).trans (hcomp x)

/-- **The reconstructed circuit is bounded-depth (PROVED) — the unbounded-fan-in, depth-faithful reconstruction.**  A
depth-`≤ dt` table family wired into the predictor `P` gives a reconstruction of depth `≤ P.depth + dt` computing
`fbool`. -/
theorem ureconstructed_hasDepth {n Nc : ℕ} (P : UCirc Nc) (tables : Fin Nc → UCirc n)
    (fbool : (Fin n → Bool) → Bool) (dt : ℕ) (hg : ∀ j, (tables j).depth ≤ dt)
    (hcomp : ∀ x, UCirc.eval (fun j => UCirc.eval x (tables j)) P = fbool x) :
    HasUCircuitOfDepth fbool (P.depth + dt) :=
  ⟨usubst tables P, usubst_depth_le tables dt hg P, ureconstructed_computes P tables fbool hcomp⟩

/-- **The reconstructed circuit is bounded-size (PROVED).**  Size `≤ size P · M` when every table has size `≤ M`. -/
theorem ureconstructed_hasSize {n Nc : ℕ} (P : UCirc Nc) (tables : Fin Nc → UCirc n)
    (fbool : (Fin n → Bool) → Bool) (M : ℕ) (hM : ∀ j, (tables j).size ≤ M) (hM1 : 1 ≤ M)
    (hcomp : ∀ x, UCirc.eval (fun j => UCirc.eval x (tables j)) P = fbool x) :
    HasUCircuitOfSize fbool (P.size * M) :=
  ⟨usubst tables P, usubst_size_le tables M hM hM1 P, ureconstructed_computes P tables fbool hcomp⟩

/-!
**The NW bridges, on `UCirc`.**  The Yao predictor is the explicit `MOD₂` gadget `upredictor` (computes the
guess-and-correct rule, depth `D.depth + 3`, `ACC⁰[2]`), and the reconstruction is `usubst tables P` (computes `f`,
bounded depth `≤ P.depth + dt`, bounded size `≤ size P · M`).  Both bridges are now faithful in **depth, gate type, and
unbounded fan-in** — the full `ACC⁰` model.  As always, the construction rests on the irreducible hardness of the
witness and the design.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UnboundedBridges

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UnboundedBridges.upredictor_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UnboundedBridges.upredictor_depth
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UnboundedBridges.upredictor_isACC0
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UnboundedBridges.usubst_size_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UnboundedBridges.ureconstructed_hasDepth
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UnboundedBridges.ureconstructed_hasSize
