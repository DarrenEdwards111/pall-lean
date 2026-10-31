import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMajorityAlgebraicImmunity

/-!
# Attacking the construction: the balancedness seed of the RS/BT probabilistic `OR`

The socket `ApproxToExactSymmetricDecode` (`…ACC0ApproxToExactDecode`) left one open clause = Wall 1: produce
quasipolynomially many *low-degree* approximants that are *majority-correct at every point*.  The classical route is
the Razborov–Smolensky / Beigel–Tarui **probabilistic polynomial**, whose atom is the random `F₂` linear form.  This
file proves that atom's analytic seed.

For an unbounded-fan-in `OR` on input `v : Fin m → Bool`, a single random linear form `L_S(v) = ⊕_{i∈S} v_i` (over a
uniformly random subset `S`) is a one-sided predictor of `OR`:

* on `v = 0` (`OR = 0`): `L_S(v) = 0` for **every** `S` — never a false positive (`pv_false`);
* on `v ≠ 0` (`OR = 1`): `L_S(v) = 1` for **exactly half** the subsets `S` — `pv_balanced`.

The balancedness on nonzero inputs is the crux: it is *why* a random parity is an unbiased predictor, and it is what
the degree-`t` boosting (`OR` of `t` independent forms ⇒ correct with probability `1 - 2^{-t}`) and the final
probabilistic-method sampling (Chernoff + union bound ⇒ a *quasipoly* majority-correct family) are built on.  Proved
here by the toggle involution `S ↦ S △ {j}` (for a coordinate `j` with `v_j = 1`), which flips the form's parity and
so pairs the parity-`0` subsets with the parity-`1` subsets bijectively.

## What is proved (clean axioms, no `sorry`)

* `pv` — the `F₂` linear form `L_S(v) = ⊕_{i∈S} v_i`; `tog` — the toggle involution; `pv_tog` / `tog_tog`.
* `pv_false` — on the all-`0` input the form is `0` for every `S` (one-sided: `OR = 0` ⇒ no false positive).
* `pv_balanced` — **the seed**: for `v` with some bit set, exactly `2^{m-1}` of the `2^m` subsets give form value `1`
  (a random linear form predicts `OR = 1` correctly with probability exactly `1/2`).

## Honest scope — what this is and is not

This is the genuine analytic atom of the BT probabilistic polynomial — the balancedness that makes a random parity an
unbiased predictor.  It is **not** the full construction.  Two steps remain, untouched and not faked:

1. **Degree-`t` boosting** — `OR` of `t` independent forms is correct with probability `1 - 2^{-t}` (`> 1/2` for
   `t ≥ 2`); a product/independence count over `pv_balanced`.
2. **Quasipoly sampling** — Chernoff concentration + a union bound over the `2^n` inputs to extract `r = O(n)`
   boosted forms that are majority-correct *everywhere*, giving the quasipoly low-degree family the socket needs.

Also note a basis caveat: these `F₂`-linear (parity) forms are low *polynomial* degree but high *monomial-`AND`*
degree, whereas `IsLowDegreeGate` (`…ACC0ApproxToExactDecode`) is monomial-`AND`-based; bridging the two bases is the
standard `AND`/`XOR` translation in the RS argument.  Steps 1–2 plus that bridge are the remaining Beigel–Tarui
analytic work — **Wall 1**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md` and
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticForm

open Finset

variable {m : ℕ}

/-- The `F₂` **linear form** `L_S(v) = ⊕_{i ∈ S} v_i`. -/
def pv (v : Fin m → Bool) (S : Finset (Fin m)) : ZMod 2 :=
  ∑ i ∈ S, (if v i then 1 else 0)

/-- The **toggle** of coordinate `j`: `S ↦ S △ {j}` (remove `j` if present, else insert it). -/
def tog (j : Fin m) (S : Finset (Fin m)) : Finset (Fin m) :=
  if j ∈ S then S.erase j else insert j S

/-- **Toggling is an involution (proved).** -/
theorem tog_tog (j : Fin m) (S : Finset (Fin m)) : tog j (tog j S) = S := by
  unfold tog
  by_cases h : j ∈ S
  · rw [if_pos h, if_neg (Finset.notMem_erase j S), Finset.insert_erase h]
  · rw [if_neg h, if_pos (Finset.mem_insert_self j S), Finset.erase_insert h]

/-- **Toggling a coordinate with `v_j = 1` flips the form's parity (proved): `pv v (tog j S) = pv v S + 1`.** -/
theorem pv_tog (v : Fin m → Bool) (j : Fin m) (hj : v j = true) (S : Finset (Fin m)) :
    pv v (tog j S) = pv v S + 1 := by
  unfold tog pv
  by_cases h : j ∈ S
  · rw [if_pos h]
    have hsum : (if v j then (1 : ZMod 2) else 0)
          + ∑ i ∈ S.erase j, (if v i then (1 : ZMod 2) else 0)
        = ∑ i ∈ S, (if v i then (1 : ZMod 2) else 0) :=
      Finset.add_sum_erase S (fun i => if v i then (1 : ZMod 2) else 0) h
    simp only [hj, if_true] at hsum
    rw [← hsum]
    exact (by decide : ∀ p : ZMod 2, p = 1 + p + 1) _
  · rw [if_neg h, Finset.sum_insert h]
    simp only [hj, if_true]
    exact add_comm 1 _

/-- **One-sidedness (proved): on the all-`0` input the form is `0` for every `S`.**  So a random linear form never
gives a false positive for `OR` (when `OR = 0`). -/
theorem pv_false (S : Finset (Fin m)) : pv (fun _ => false) S = 0 := by
  simp [pv]

/-- **The balancedness seed (proved): for `v` with some bit set, exactly `2^{m-1}` of the `2^m` subsets give form
value `1`.**  Equivalently, a uniformly random linear form predicts `OR = 1` correctly with probability exactly
`1/2` — the analytic atom of the RS/BT probabilistic `OR`.  Proved by the parity-flipping toggle involution. -/
theorem pv_balanced (v : Fin m → Bool) (j : Fin m) (hj : v j = true) :
    ((Finset.univ : Finset (Finset (Fin m))).filter (fun S => pv v S = 1)).card = 2 ^ (m - 1) := by
  classical
  -- the parity-`0` and parity-`1` subsets are equinumerous, via the toggle involution
  have hEO : ((Finset.univ : Finset (Finset (Fin m))).filter (fun S => pv v S = 0)).card
      = ((Finset.univ : Finset (Finset (Fin m))).filter (fun S => pv v S = 1)).card := by
    apply Finset.card_bij' (fun S _ => tog j S) (fun S _ => tog j S)
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      rw [pv_tog v j hj, hS]; decide
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      rw [pv_tog v j hj, hS]; decide
    · intro S _; exact tog_tog j S
    · intro S _; exact tog_tog j S
  -- the two classes partition the `2^m` subsets
  have hpart : ((Finset.univ : Finset (Finset (Fin m))).filter (fun S => pv v S = 0)).card
      + ((Finset.univ : Finset (Finset (Fin m))).filter (fun S => pv v S = 1)).card = 2 ^ m := by
    have hcompl := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Finset (Fin m)))) (fun S => pv v S = 0)
    have hne : ((Finset.univ : Finset (Finset (Fin m))).filter (fun S => ¬ pv v S = 0))
        = ((Finset.univ : Finset (Finset (Fin m))).filter (fun S => pv v S = 1)) :=
      Finset.filter_congr (fun S _ =>
        (by decide : ∀ a : ZMod 2, (¬ a = 0) ↔ a = 1) (pv v S))
    rw [hne] at hcompl
    rw [hcompl, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  -- `m ≥ 1` since `j : Fin m`, so `2^m = 2 · 2^{m-1}`; combine
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le j.val) j.is_lt
  have hsucc : 2 ^ m = 2 * 2 ^ (m - 1) := by
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos hm]
    rw [pow_succ, Nat.pred_eq_sub_one]; ring
  omega

end PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticForm

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticForm.tog_tog
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticForm.pv_tog
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticForm.pv_false
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticForm.pv_balanced
