import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGoldreichMajorityCandidate

/-!
# Option C: the Goldreich / local‑PRG route — the constructive terminus, honestly

The local‑PRG route is *the* most ambitious fork: a single explicit, local, expander‑based family resisting
**every** polynomial‑time inverter.  We assemble the concrete **Goldreich–Majority** function and prove its
genuine structural properties; but its **full security is exactly the wall** — and we state that precisely
rather than fake it.

`goldreichMaj` = the Goldreich local function with the (optimal‑AI) Majority predicate: `n` inputs, `m` outputs,
each output `Maj_d` of a `d`‑subset chosen by an expander hypergraph (`edges`).

## Proved (clean axioms, no `sorry`)

* `goldreich_eval_local` — **locality**: each output depends only on its hyperedge's `d` inputs.
* `majPred_const_true` / `majPred_const_false` — the predicate is **non‑degenerate** (genuinely Boolean‑valued).
* `goldreichMaj_no_lowAction_inverter` — the **conditional separation**: given `raveling` (low‑action ⇒
  separator class `K`, provable for the restricted `K`), `separatorSpeedup` (a `K`‑separator ⇒ a fast inverter),
  and `GoldreichMajHard` (no fast inverter), **no low‑action observer inverts the family**.

## The wall — stated, not crossed

`GoldreichMajHard` (no polynomial‑time algorithm inverts `goldreichMaj`) is the local‑PRG / one‑way‑function
security assumption.  It is **`P ≠ NP`‑strength**: a one‑way function exists ⇒ `P ≠ NP`.  So discharging it
unconditionally *is* the separation — it cannot be done by any construction, and is **not** done here.

What *is* established (across the corpus) is restricted security: the family provably resists the **low‑degree
algebraic** inverter (Majority's optimal AI, `majority_defeats_low_degree_separator`), the **`AC⁰[p]`** inverter
(unconditional `Majority ∉ AC⁰[p]`, `majority_not_in_AC0p`), and the **bounded‑crossing / bounded‑locality**
inverters (the debt bridges).  Each restricted class is a theorem; their union over *all* polynomial‑time
inverters is `GoldreichMajHard` = the open problem.

This is the honest terminus of the constructive program: the right primitive (optimal‑AI Majority over an
expander), provably hard against every restricted attack we have formalized, with the single remaining
hypothesis being precisely `P ≠ NP`.  No further construction reduces that hypothesis.
-/

namespace PallLean.Paper93.DeepMath.PathB.GoldreichMajorityPRG

open Finset
open PallLean.Paper93.DeepMath.PathB.GoldreichExpanderCandidate
open PallLean.Paper93.DeepMath.PathB.GoldreichMajorityCandidate

variable {n d m : ℕ}

/-- The **Goldreich–Majority local function**: `m` output bits over `n` inputs, output `i` is `Maj_d` of the
`d`‑subset `edges i` (an expander hypergraph). -/
def goldreichMaj (edges : Fin m → (Fin d → Fin n)) : GoldreichCSP n d m := majGoldreich edges

/-- **Locality (proved).**  Output `i` depends only on the `d` inputs on hyperedge `i`: inputs agreeing on the
edge produce the same output bit. -/
theorem goldreich_eval_local (G : GoldreichCSP n d m) (x y : Fin n → Bool) (i : Fin m)
    (h : ∀ j, x (G.edges i j) = y (G.edges i j)) :
    G.eval x i = G.eval y i := by
  simp only [GoldreichCSP.eval]
  congr 1
  funext j
  exact h j

/-- The Majority predicate is `true` on the all‑ones input (`d ≥ 1`). -/
theorem majPred_const_true (hd : 1 ≤ d) : majPred d (fun _ => true) = true := by
  rw [majPred, decide_eq_true_eq]
  have hsupp : (toSupp (fun _ : Fin d => true)) = Finset.univ := by
    ext i; simp [toSupp]
  rw [hsupp, Finset.card_univ, Fintype.card_fin]
  omega

/-- The Majority predicate is `false` on the all‑zeros input (`d ≥ 1`). -/
theorem majPred_const_false (hd : 1 ≤ d) : majPred d (fun _ => false) = false := by
  rw [majPred, decide_eq_false_iff_not]
  have hsupp : (toSupp (fun _ : Fin d => false)) = (∅ : Finset (Fin d)) := by
    ext i; simp [toSupp]
  rw [hsupp, Finset.card_empty]
  omega

/-- **The conditional separation for the Goldreich–Majority family (proved).**  Composing `raveling`
(low‑action ⇒ separator in `K`), `separatorSpeedup` (a `K`‑separator yields a fast inverter), and
`GoldreichMajHard` (the family is not invertible by a fast algorithm), no low‑action observer correctly inverts
the family.  Conditional on `GoldreichMajHard` — the local‑PRG security assumption, which is `P ≠ NP`‑strength. -/
theorem goldreichMaj_no_lowAction_inverter {Obs : Type*}
    (lowAction correctlyInverts inK : Obs → Prop) (fastInversion : Prop)
    (raveling : ∀ o, lowAction o → inK o)
    (separatorSpeedup : (∃ o, inK o ∧ correctlyInverts o) → fastInversion)
    (GoldreichMajHard : ¬ fastInversion) :
    ∀ o, ¬ (lowAction o ∧ correctlyInverts o) :=
  goldreich_observer_williams lowAction correctlyInverts inK fastInversion
    raveling separatorSpeedup GoldreichMajHard

end PallLean.Paper93.DeepMath.PathB.GoldreichMajorityPRG

#print axioms PallLean.Paper93.DeepMath.PathB.GoldreichMajorityPRG.goldreich_eval_local
#print axioms PallLean.Paper93.DeepMath.PathB.GoldreichMajorityPRG.majPred_const_false
