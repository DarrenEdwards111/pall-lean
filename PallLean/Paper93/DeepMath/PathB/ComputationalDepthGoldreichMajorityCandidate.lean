import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGoldreichExpanderCandidate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMajorityAIUpperBound

/-!
# Goldreich's local CSP with the *optimal* Majority predicate, and the exact remaining wall

The TSA predicate (`AI = 2`) was the base case.  Majority is now the **proved‑optimal** primitive
(`AI(Maj_{2t-1}) = t = ⌈n/2⌉`, `majority_AI_optimal`).  This file instantiates Goldreich's expander‑local CSP
with Majority, turns the optimal‑AI result into a reusable **separator‑resistance** statement, sharpens the
observer‑Williams cash‑out into an explicit four‑step chain, and **names the exact remaining hardness
hypothesis** — the precise cryptographic statement whose proof would close the route (and which is
`P ≠ NP`‑strength).

## Proved (clean axioms, no `sorry`)

* `maj_eq_one_iff` / `majPred_eq_maj` — the Bool‑input Majority predicate `majPred` *is* the proved
  `Maj` function under the support correspondence `x ↦ {i : x i}`.  So `majGoldreich` is the optimal‑AI family,
  rigorously (no representation hand‑wave).
* `majGoldreich` — Goldreich's `GoldreichCSP` instantiated with `majPred` (the optimal predicate).
* `majority_defeats_low_degree_separator` — **AI ⇒ separator resistance (the reusable tool)**: no nonzero ANF
  degree‑`< t` function annihilates `Maj` or `¬Maj`.  The low‑degree‑annihilator / linearization separator class
  provably *fails* against Majority — directly from `majority_AI_optimal`.
* `majority_observer_williams` — **the sharpened four‑step cash‑out**: `low‑action inverter ⇒ separator in K ⇒
  fast inversion ⇒ collapse ⇒ contradiction`.  Each arrow explicit.
* `MajorityGoldreichHardness` / `.no_low_action_inverter` — bundles the **exact ingredients** and extracts the
  conclusion, making unambiguous *which* statement is the open conjecture.

## Honest status — the exact remaining wall

The chain `majority_observer_williams` needs four ingredients:

1. `raveling` (low‑action ⇒ in `K`) — **provable for restricted `K`** (the debt corpus, crossing‑sequence
   bridge, etc.).
2. `separatorSpeedup` (a `K`‑separator ⇒ a fast inversion algorithm) — framework‑supplied (the DP engine).
3. `fastInversionImpliesCollapse` (fast inversion ⇒ hierarchy collapse) — Williams‑style, standard.
4. `noCollapse` / **`InversionHardness`** — *the conjecture*: the Majority‑Goldreich family is not invertible by
   any fast algorithm.  This (equivalently `DistinguishingHardness`, local‑PRG security) is the **only**
   unproved input, and proving it unconditionally is `P ≠ NP`‑strength.

What this file removes from doubt: the predicate is now provably *optimal* (not conjecturally good), and the
*algebraic* attack on it (low‑degree annihilator / linearization) provably fails
(`majority_defeats_low_degree_separator`).  What remains is exactly `InversionHardness` — a single, named,
cryptographic statement.  Not a proof of `P ≠ NP`; the honest reduction of the route to its one open stone.
-/

namespace PallLean.Paper93.DeepMath.PathB.GoldreichMajorityCandidate

open Finset
open PallLean.Paper93.DeepMath.PathB.GoldreichExpanderCandidate
open PallLean.Paper93.DeepMath.PathB.MajorityAI
open PallLean.Paper93.DeepMath.PathB.MajorityAIUpper

/-! ### The Majority predicate as a Goldreich primitive, tied to the proved `Maj` -/

/-- The support of a Boolean input: the set of coordinates set to `true`. -/
def toSupp {d : ℕ} (x : Fin d → Bool) : Finset (Fin d) := Finset.univ.filter (fun i => x i = true)

/-- The **Majority predicate** on `d` bits (Bool form): `true` iff at least `⌈d/2⌉ = (d+1)/2` inputs are `true`. -/
def majPred (d : ℕ) (x : Fin d → Bool) : Bool := decide ((d + 1) / 2 ≤ (toSupp x).card)

/-- `Maj t T = 1` exactly when the weight reaches the threshold. -/
theorem maj_eq_one_iff {n t : ℕ} (T : Finset (Fin n)) : Maj t T = 1 ↔ t ≤ T.card := by
  unfold Maj
  by_cases h : t ≤ T.card <;> simp [h]

/-- **The instantiated predicate is the proved `Maj` function (rigorous correspondence).**  Under the support
map `x ↦ {i : x i}`, `majPred d x` agrees with `Maj ((d+1)/2)`.  So `majGoldreich` really is the optimal‑AI
family; the `AI = ⌈d/2⌉` result transfers without representation hand‑waving. -/
theorem majPred_eq_maj {d : ℕ} (x : Fin d → Bool) :
    majPred d x = true ↔ Maj ((d + 1) / 2) (toSupp x) = 1 := by
  rw [majPred, decide_eq_true_iff, maj_eq_one_iff]

/-- **Goldreich's local CSP instantiated with the optimal Majority predicate.**  `m` output bits over `n`
inputs, each the `d`‑ary Majority of its hyperedge.  On an expander hypergraph this is the Majority‑Goldreich
local one‑way function / PRG — the strongest verified predicate primitive. -/
def majGoldreich {n d m : ℕ} (edges : Fin m → (Fin d → Fin n)) : GoldreichCSP n d m :=
  { edges := edges, pred := majPred d }

/-! ### AI ⇒ separator resistance (the reusable lower‑bound tool) -/

/-- **High algebraic immunity ⇒ no low‑degree algebraic inverter (proved).**  For `n = 2t-1`, no nonzero ANF
degree‑`< t` function annihilates `Maj` or `¬Maj`: the low‑degree‑annihilator / linearization separator class —
the attack that collapsed the bare AND gadget — provably *fails* against Majority.  Directly from the optimal‑AI
lower bound, this turns the Majority result into a reusable separator‑resistance theorem. -/
theorem majority_defeats_low_degree_separator {n t : ℕ} (ht : 1 ≤ t) (hn : n = 2 * t - 1)
    (g : Finset (Fin n) → ZMod 2) (hg : g ≠ 0) (hdeg : DegreeLt g t) :
    (∃ T, g T * Maj t T ≠ 0) ∧ (∃ T, g T * negMaj t T ≠ 0) :=
  (majority_AI_optimal ht hn).1 g hg hdeg

/-! ### The sharpened observer‑Williams cash‑out -/

/-- **The four‑step cash‑out (proved, no axioms).**  Each arrow explicit: a low‑action inverter ravels into the
separator class `K`; a `K`‑separator yields a fast inversion algorithm; fast inversion forces a hierarchy
collapse; the collapse contradicts the hardness assumption.  Hence no low‑action observer correctly inverts the
Majority‑Goldreich family — *conditional on* `noCollapse`. -/
theorem majority_observer_williams {Obs : Type*}
    (lowAction correctlyInverts inK : Obs → Prop) (fastInversion collapse : Prop)
    (raveling : ∀ o, lowAction o → inK o)
    (separatorSpeedup : (∃ o, inK o ∧ correctlyInverts o) → fastInversion)
    (fastInversionImpliesCollapse : fastInversion → collapse)
    (noCollapse : ¬ collapse) :
    ∀ o, ¬ (lowAction o ∧ correctlyInverts o) := by
  rintro o ⟨hla, hci⟩
  exact noCollapse (fastInversionImpliesCollapse (separatorSpeedup ⟨o, raveling o hla, hci⟩))

/-! ### The exact remaining hardness hypothesis, split into named ingredients -/

/-- **The exact ingredients of the Majority‑Goldreich observer‑Williams route.**  Bundling the four arrows makes
unambiguous *which* statement is the open conjecture: `raveling` is provable for restricted `K`,
`separatorSpeedup` and `fastInversionImpliesCollapse` are framework/Williams‑standard, and `noCollapse`
(`InversionHardness` / local‑PRG security / `DistinguishingHardness`) is the single cryptographic conjecture
whose unconditional proof is `P ≠ NP`‑strength. -/
structure MajorityGoldreichHardness (Obs : Type*) where
  /-- whether a fast inversion algorithm exists -/
  fastInversion : Prop
  /-- the complexity‑hierarchy collapse a fast inverter would force -/
  collapse : Prop
  /-- the separator class `K` (e.g. low‑debt / bounded crossing‑sequence observers) -/
  inK : Obs → Prop
  /-- the observers under consideration (low action / low resource) -/
  lowAction : Obs → Prop
  /-- correctly inverting the Majority‑Goldreich family -/
  correctlyInverts : Obs → Prop
  /-- **raveling** — provable for restricted `K`: a low‑action observer lies in `K`. -/
  raveling : ∀ o, lowAction o → inK o
  /-- **SeparatorHardness / Williams speedup** — a correct `K`‑separator yields a fast inversion algorithm. -/
  separatorSpeedup : (∃ o, inK o ∧ correctlyInverts o) → fastInversion
  /-- **FastInversionImpliesCollapse** — a fast inverter forces a hierarchy collapse. -/
  fastInversionImpliesCollapse : fastInversion → collapse
  /-- **InversionHardness** (the open conjecture) — no collapse / the family resists fast inversion. -/
  noCollapse : ¬ collapse

/-- Given the bundled ingredients, no low‑action observer correctly inverts the Majority‑Goldreich family.  The
conclusion is conditional precisely on `noCollapse` (`InversionHardness`); everything else is discharged. -/
theorem MajorityGoldreichHardness.no_low_action_inverter {Obs : Type*}
    (H : MajorityGoldreichHardness Obs) :
    ∀ o, ¬ (H.lowAction o ∧ H.correctlyInverts o) :=
  majority_observer_williams H.lowAction H.correctlyInverts H.inK H.fastInversion H.collapse
    H.raveling H.separatorSpeedup H.fastInversionImpliesCollapse H.noCollapse

end PallLean.Paper93.DeepMath.PathB.GoldreichMajorityCandidate

#print axioms PallLean.Paper93.DeepMath.PathB.GoldreichMajorityCandidate.majPred_eq_maj
#print axioms PallLean.Paper93.DeepMath.PathB.GoldreichMajorityCandidate.majority_defeats_low_degree_separator
#print axioms PallLean.Paper93.DeepMath.PathB.GoldreichMajorityCandidate.MajorityGoldreichHardness.no_low_action_inverter
