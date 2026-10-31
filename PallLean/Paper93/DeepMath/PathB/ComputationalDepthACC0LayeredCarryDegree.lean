import Mathlib

/-!
# Layered-carry degree analysis — per-prime layers are low-degree; the composite combination is the wall

Entry 241 proved the *single-field full-count* indicator costs degree `Θ(N)` (too expensive).  The open question
(roadmap): can **p-adic carry / per-prime layers** realise the exact composite count at *low* degree while keeping
quasipoly size?  This file does the honest analysis.  The finding is the honest middle, not a crossing and not a full
no-go:

* **Per-prime layers are low-degree (PROVED).**  The residue of the count mod `p` is *linear* (degree 1), and the
  `MOD_p`-is-zero indicator `1 - (∑ X_i)^(p-1)` has total degree `≤ p-1` — **independent of `n` and of the count range
  `N`**.  So a single prime layer does *not* blow up degree (contrast entry-241's `Θ(N)` single-field full count).
* **The composite combination is the open wall (socket).**  For composite `m = ∏ pᵢ`, `MOD_m = ⋀ᵢ MOD_{pᵢ}` lives over
  *different* fields `F_{pᵢ}`; combining the per-prime low-degree indicators into *one* low-degree polynomial (or the
  higher p-adic carry digits for prime powers) is exactly the open `ACC⁰[m]` barrier (Smolensky-strength).

⚠️ **No crossing, no faked no-go.**  The proved part is the *good news* (per-prime layers are cheap).  The composite
combination — whether it can be low-degree — is **not** settled here; that is the separation-strength wall.

## What is proved (clean axioms, no `sorry`)

* **`linearCountPoly := ∑ X_i`**; **`linearCount_totalDegree_le_one`** (PROVED) — the count residue mod `p` is realised
  by a *linear* polynomial.  **`linearCount_eval`** (PROVED) — it evaluates to `countSum` (the count mod `p`).
* **`modpIndicatorPoly := 1 - (∑ X_i)^(p-1)`**; **`modpIndicator_totalDegree_le`** (PROVED) — total degree `≤ p-1`,
  *independent of `n`/`N`*.  **`modpIndicator_eval`** (PROVED) — it computes `[count ≡ 0 mod p]` (Fermat:
  `s^(p-1) = [s ≠ 0]`).

## The open question (named, not settled)

For composite `m`, is `MOD_m` (`= ⋀ MOD_{pᵢ}`, over different `F_{pᵢ}`) realisable by a single *low-degree* polynomial
over a common field?  Equivalently, do the carry/digit layers combine at low degree?  **If yes → an `ACC⁰[m]`
crossing; if no → the formal Smolensky obstruction.**  Not settled here (it is the entry-238 `CarryRefinementCrossing` /
entry-241 open layered question).

## Honest scope

The proved content settles the *per-prime* layer: it is low total degree (`≤ p-1`, independent of `n`), so layering
does **not** reintroduce the entry-241 `Θ(N)` cost *within a single prime*.  This is genuine good news for the layered
route.  What remains open is the **cross-prime / carry combination** for composite `m` — combining low-degree per-prime
indicators into one low-degree composite indicator — which is the open, separation-strength `ACC⁰[m]` wall.  This file
does not resolve it (neither crossing nor no-go).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

open MvPolynomial Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0LayeredCarryDegree

variable (n p : ℕ) [Fact p.Prime]

/-- A boolean as a field element. -/
def boolToZMod (b : Bool) : ZMod p := if b then 1 else 0

/-- The count of true bits, read mod `p`. -/
def countSum (x : Fin n → Bool) : ZMod p := ∑ i, boolToZMod p (x i)

/-- The linear polynomial `∑ X_i` realising the count residue mod `p` (digit-0 layer). -/
noncomputable def linearCountPoly : MvPolynomial (Fin n) (ZMod p) := ∑ i, X i

/-- The `MOD_p`-is-zero indicator polynomial `1 - (∑ X_i)^(p-1)`. -/
noncomputable def modpIndicatorPoly : MvPolynomial (Fin n) (ZMod p) := 1 - (∑ i, X i) ^ (p - 1)

/-- **The count residue mod `p` is linear (PROVED).**  `(∑ X_i).totalDegree ≤ 1` — the digit-0 layer costs degree 1,
independent of `n`. -/
theorem linearCount_totalDegree_le_one : (linearCountPoly n p).totalDegree ≤ 1 := by
  unfold linearCountPoly
  calc (∑ i, X i : MvPolynomial (Fin n) (ZMod p)).totalDegree
      ≤ Finset.univ.sup (fun i => (X i : MvPolynomial (Fin n) (ZMod p)).totalDegree) :=
        totalDegree_finset_sum _ _
    _ ≤ 1 := by apply Finset.sup_le; intro i _; rw [totalDegree_X]

/-- **The linear count polynomial evaluates to the count mod `p` (PROVED).** -/
theorem linearCount_eval (x : Fin n → Bool) :
    eval (fun i => boolToZMod p (x i)) (linearCountPoly n p) = countSum n p x := by
  unfold linearCountPoly countSum
  rw [map_sum]
  simp only [eval_X]

/-- **The `MOD_p` indicator has total degree `≤ p-1`, independent of `n` (PROVED).**  This is the key layered fact: a
single prime layer is low-degree regardless of the count range `N` — contrast entry-241's `Θ(N)` single-field full
count. -/
theorem modpIndicator_totalDegree_le : (modpIndicatorPoly n p).totalDegree ≤ p - 1 := by
  unfold modpIndicatorPoly
  calc (1 - (∑ i, X i) ^ (p - 1) : MvPolynomial (Fin n) (ZMod p)).totalDegree
      ≤ max (1 : MvPolynomial (Fin n) (ZMod p)).totalDegree (((∑ i, X i) ^ (p - 1)).totalDegree) :=
        totalDegree_sub _ _
    _ ≤ p - 1 := by
        rw [totalDegree_one]
        refine max_le (Nat.zero_le _) ?_
        calc ((∑ i, X i : MvPolynomial (Fin n) (ZMod p)) ^ (p - 1)).totalDegree
            ≤ (p - 1) * (∑ i, X i : MvPolynomial (Fin n) (ZMod p)).totalDegree := totalDegree_pow _ _
          _ ≤ (p - 1) * 1 := by
              refine Nat.mul_le_mul_left _ ?_
              calc (∑ i, X i : MvPolynomial (Fin n) (ZMod p)).totalDegree
                  ≤ Finset.univ.sup (fun i => (X i : MvPolynomial (Fin n) (ZMod p)).totalDegree) :=
                    totalDegree_finset_sum _ _
                _ ≤ 1 := by apply Finset.sup_le; intro i _; rw [totalDegree_X]
          _ = p - 1 := mul_one _

/-- **The `MOD_p` indicator computes `[count ≡ 0 mod p]` (PROVED).**  `eval (boolToZMod ∘ x) modpIndicatorPoly =
if countSum = 0 then 1 else 0` — Fermat: `s^(p-1) = [s ≠ 0]`, so `1 - s^(p-1) = [s = 0]`. -/
theorem modpIndicator_eval (x : Fin n → Bool) :
    eval (fun i => boolToZMod p (x i)) (modpIndicatorPoly n p)
      = if countSum n p x = 0 then 1 else 0 := by
  unfold modpIndicatorPoly countSum
  rw [map_sub, map_one, map_pow, map_sum]
  simp only [eval_X]
  by_cases h : (∑ i, boolToZMod p (x i)) = 0
  · rw [h]
    simp [zero_pow (by have := (Fact.out : p.Prime).two_le; omega : p - 1 ≠ 0)]
  · rw [if_neg h, ZMod.pow_card_sub_one_eq_one h]; ring

end PallLean.Paper93.DeepMath.PathB.ACC0LayeredCarryDegree

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LayeredCarryDegree.linearCount_totalDegree_le_one
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LayeredCarryDegree.modpIndicator_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LayeredCarryDegree.modpIndicator_eval
