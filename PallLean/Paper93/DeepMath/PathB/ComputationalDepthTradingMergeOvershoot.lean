import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTradingOptimality

/-!
# Why you can't get `2cos(π/7)` from this system: adding a sound merge rule OVERSHOOTS the known optimum

The instruction was "build the space-parameter system if you want `2cos(π/7)`."  Working the mathematics first
overturned my own earlier framing and produced a sharper, machine-checked finding:

* **The `2cos(π/7)` improvements are NOT a space-parameter matter.**  Lipton–Viglas (`√2`), Fortnow–van Melkebeek
  (`φ`), and Williams (`2cos(π/7)`) are all lower bounds in the *same* subpolynomial-space regime
  (`DTISP(·, n^{o(1)})`, which is what the `AlternationTrading` system already models); the gains come from better
  *proofs*, not a space exponent.  My earlier "needs a space parameter" claim was wrong.

* **A natural, sound merge rule makes the simplified system OVERSHOOT `2cos(π/7)`.**  Adding
  `(∃ n^a)(∃ n^b) → (∃ n^{max(a,b)})` (sound: guess both blocks together, size `max` up to `n^{o(1)}`), a
  `speedup;slowdown;speedup;slowdown;merge;slowdown` derivation reaches base `c³/(1+c+c²)`, giving a contradiction
  whenever `c³ < 1 + c + c²` — threshold the **tribonacci constant `≈ 1.8393`**, which is **greater** than
  `2cos(π/7) ≈ 1.8019`.

`merge_overshoots_2cos` machine-checks this: there is a `c` (namely `91/50 = 1.82`) that is **above** the
Buss–Williams optimum `2cos(π/7)` (root of `bwPoly` in `(1.8,1.81)`) yet at which this system derives a
contradiction.  Since Buss–Williams optimality is a correct theorem for the *real* trading system, the simplified
rules here must be strictly more generous than the faithful ones — they are **not a sound model** of alternation
trading, and cannot be used to certify the real `2cos(π/7)`.

**Conclusion.**  The real `2cos(π/7)` requires the *faithful* FvM/Williams rules — with the precise
configuration-size, space-exponent, and alternation-count corrections that the `max`/`n^0` idealizations here drop
— a substantial separate formalization, and even then achievability is a proof *sequence* (sup, not one proof) and
optimality is the Buss–Williams LP/computer-search result.  This file is the honest boundary: it proves the
shortcut overshoots, rather than manufacturing the constant.  The `bwPoly` root (`= 2cos(π/7)`) remains pinned.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TradingMergeOvershoot

open PallLean.Paper93.DeepMath.PathB.AlternationTrading
open PallLean.Paper93.DeepMath.PathB.TradingOptimality

variable {c : ℚ}

/-- The trading moves extended with a sound merge of two adjacent same-type quantifiers. -/
inductive StepM (c : ℚ) : Line → Line → Prop
  | ofStep {L L' : Line} : Step c L L' → StepM c L L'
  /-- Merge adjacent same-type quantifiers: `(Q n^{a₁})(Q n^{a₂}) → (Q n^{max a₁ a₂})`. -/
  | merge (qs : List (Bool × ℚ)) (b : Bool) (a1 a2 r : ℚ) :
      StepM c ⟨qs ++ [(b, a1), (b, a2)], r⟩ ⟨qs ++ [(b, max a1 a2)], r⟩

/-- Reflexive-transitive closure of the merge-extended system. -/
inductive StepsM (c : ℚ) : Line → Line → Prop
  | refl (L : Line) : StepsM c L L
  | tail {L L' L'' : Line} : StepsM c L L' → StepM c L' L'' → StepsM c L L''

/-- **The merged derivation.**  For `c ≥ 1` with `c³ < 1 + c + c²`, a
`speedup;slowdown;speedup;slowdown;merge;slowdown` derivation drives the base of `DTISP(n^1)` below `1` — a
contradiction — reaching final base `c³/(1+c+c²)`. -/
theorem merged_contradiction (hc : 1 ≤ c) (hcube : c ^ 3 < 1 + c + c ^ 2) :
    ∃ L_f : Line, StepsM c ⟨[], 1⟩ L_f ∧ L_f.quants = [] ∧ L_f.base < 1 := by
  have hd : (0 : ℚ) < 1 + c + c ^ 2 := by nlinarith [hc]
  set d : ℚ := 1 + c + c ^ 2 with hddef
  set x : ℚ := c ^ 2 / d with hxdef
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hx1 : x ≤ 1 := by rw [hxdef, div_le_one hd]; nlinarith [hc]
  have h1x : (0 : ℚ) ≤ 1 - x := by linarith [hx1]
  have hcx : c * (1 - x) - x = c / d := by
    rw [hxdef]; field_simp; ring
  have h4pos : (0 : ℚ) ≤ c * (1 - x) - x := by rw [hcx]; positivity
  have hkey : c * (c * (1 - x) - x) = x := by rw [hcx, hxdef]; ring
  have hy : x ≤ c * (1 - x) := by nlinarith [hcx, h4pos]
  -- the six steps
  have s1 : StepM c ⟨[], 1⟩ ⟨[(true, x), (false, 0)], 1 - x⟩ :=
    StepM.ofStep (Step.speedup [] 1 x hx0 hx1)
  have s2 : StepM c ⟨[(true, x), (false, 0)], 1 - x⟩ ⟨[(true, x)], c * (1 - x)⟩ := by
    have h := Step.slowdown (c := c) [(true, x)] false 0 (1 - x) le_rfl
    rw [max_eq_right h1x] at h
    exact StepM.ofStep h
  have s3 : StepM c ⟨[(true, x)], c * (1 - x)⟩ ⟨[(true, x), (true, x), (false, 0)], c * (1 - x) - x⟩ :=
    StepM.ofStep (Step.speedup [(true, x)] (c * (1 - x)) x hx0 hy)
  have s4 : StepM c ⟨[(true, x), (true, x), (false, 0)], c * (1 - x) - x⟩
      ⟨[(true, x), (true, x)], c * (c * (1 - x) - x)⟩ := by
    have h := Step.slowdown (c := c) [(true, x), (true, x)] false 0 (c * (1 - x) - x) le_rfl
    rw [max_eq_right h4pos] at h
    exact StepM.ofStep h
  have s5 : StepM c ⟨[(true, x), (true, x)], c * (c * (1 - x) - x)⟩
      ⟨[(true, x)], c * (c * (1 - x) - x)⟩ := by
    have h := StepM.merge (c := c) [] true x x (c * (c * (1 - x) - x))
    rw [max_self] at h
    exact h
  have s6 : StepM c ⟨[(true, x)], c * (c * (1 - x) - x)⟩ ⟨[], c * x⟩ := by
    have h := Step.slowdown (c := c) [] true x (c * (c * (1 - x) - x)) hx0
    rw [max_eq_left (le_of_eq hkey)] at h
    exact StepM.ofStep h
  refine ⟨⟨[], c * x⟩, ((((((StepsM.refl _).tail s1).tail s2).tail s3).tail s4).tail s5).tail s6,
    rfl, ?_⟩
  -- c * x < 1  ⟺  c³/(1+c+c²) < 1  ⟺  c³ < 1+c+c²
  rw [hxdef, show c * (c ^ 2 / d) = c ^ 3 / d from by ring, div_lt_one hd]
  exact hcube

/-- **The overshoot, machine-checked.**  There is a `c` (`= 1.82`) strictly above the Buss–Williams optimum
`2cos(π/7)` (the root of `bwPoly` in `(1.8, 1.81)`) at which this merge-extended system STILL derives a
contradiction.  Hence the simplified rules overshoot the known optimum and are not a faithful model — the real
`2cos(π/7)` cannot be obtained from them. -/
theorem merge_overshoots_2cos :
    ∃ c : ℚ,
      (∀ root : ℝ, root ∈ Set.Ioo (1.8 : ℝ) 1.81 → bwPoly root = 0 → root < (c : ℝ))
      ∧ (∃ L_f : Line, StepsM c ⟨[], 1⟩ L_f ∧ L_f.quants = [] ∧ L_f.base < 1) := by
  refine ⟨91 / 50, ?_, ?_⟩
  · intro root hroot _
    have : root < 1.81 := hroot.2
    have h : (1.81 : ℝ) < (91 / 50 : ℚ) := by norm_num
    linarith
  · exact merged_contradiction (by norm_num) (by norm_num)

end PallLean.Paper93.DeepMath.PathB.TradingMergeOvershoot

#print axioms PallLean.Paper93.DeepMath.PathB.TradingMergeOvershoot.merged_contradiction
#print axioms PallLean.Paper93.DeepMath.PathB.TradingMergeOvershoot.merge_overshoots_2cos
