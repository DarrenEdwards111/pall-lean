import Mathlib

/-!
# The alternation-trading proof system, formalized — with the first rung of the cap ladder

Round-3 residue, built: the proof system Buss–Williams analyze, as a formal syntactic object over `ℚ` exponents,
together with (i) a machine-checked **nonvacuity** witness — a concrete one-speedup derivation strictly decreases
the deterministic base whenever `c² < 1 + c` (the golden-ratio rung `c < φ ≈ 1.618`) — and (ii) the **first cap
rung**: derivations that use NO speedup step cannot decrease the base at all, hence derive no contradiction.

## The system

A **line** `⟨quants, base⟩` denotes the class `(Q₁ n^{q₁}) … (Q_k n^{q_k}) DTISP(n^{base}, n^{o(1)})` — a list of
quantifier blocks (`Bool` = ∃/∀, `ℚ` = exponent; head = outermost, last = innermost) then a deterministic
time-and-space-bounded base with exponent `base`.  Under the hypothesis-for-contradiction
`NTIME(n) ⊆ DTISP(n^c, n^{o(1)})` (with `c ≥ 1`), the sound moves are:

* **speedup** — split the base at guessed block-boundary configurations, introducing two innermost quantifiers:
  `DTISP(n^r) ⊆ (∃ n^x)(∀ n^{o(1)}) DTISP(n^{r−x})` for `0 ≤ x ≤ r`.  **The only rule that decreases the base.**
* **slowdown** — collapse the innermost quantifier into the base at cost `c`:
  `(Q n^x) DTISP(n^r) ⊆ DTISP(n^{c·max(x,r)})`.
* **weakening** — increase any exponent (monotone).
* **complementation** — flip all quantifier types (a `co-` closure; exponents unchanged).

## What is proved (honest scope)

* `stepNS_base_mono`, `base_mono_of_noSpeedup` — the speedup-free fragment is base-non-decreasing;
* `noSpeedup_no_contradiction` — **cap rung 0**: no speedup-free derivation takes `DTISP(n^r)` to `DTISP(n^{r'})`
  with `r' < r` (the impossible-by-hierarchy inclusion), i.e. speedup is *necessary* for any contradiction;
* `speedup_enables_contradiction` — **nonvacuity**: a concrete `speedup;slowdown;slowdown` derivation reaches
  base `c²r/(1+c) < r` when `c² < 1 + c`, so the system proves `SAT ∉ TISP(n^c)` for `c < φ`.

The full **Buss–Williams optimality** — that the best exponent achievable over *all* derivations is exactly
`2cos(π/7) ≈ 1.8019`, and the intermediate rungs `√2` (Lipton–Viglas) and `φ` (Fortnow–van Melkebeek) — is a
delicate analysis of the exponent recurrence over every derivation shape; it is the remaining meta-theorem and is
NOT proved here.  This file pins the system and its two endpoints (necessity of speedup; a working speedup
derivation), leaving the optimal cap as the stated open target.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.AlternationTrading

/-- A line of an alternation-trading proof: quantifier blocks (outermost first) over a `DTISP` base exponent. -/
structure Line where
  /-- Quantifier blocks: `(existential?, exponent)`, head outermost, last innermost. -/
  quants : List (Bool × ℚ)
  /-- The deterministic `DTISP` time exponent. -/
  base : ℚ

variable {c : ℚ}

/-- The full set of sound moves (including speedup). -/
inductive Step (c : ℚ) : Line → Line → Prop
  /-- Split the base, adding an `∃ n^x` and a negligible `∀` innermost; base drops by `x`. -/
  | speedup (qs : List (Bool × ℚ)) (r x : ℚ) (hx : 0 ≤ x) (hxr : x ≤ r) :
      Step c ⟨qs, r⟩ ⟨qs ++ [(true, x), (false, 0)], r - x⟩
  /-- Collapse the innermost quantifier into the base at cost `c`. -/
  | slowdown (qs : List (Bool × ℚ)) (Q : Bool) (x r : ℚ) (hx : 0 ≤ x) :
      Step c ⟨qs ++ [(Q, x)], r⟩ ⟨qs, c * max x r⟩
  /-- Increase the base exponent. -/
  | weaken (qs : List (Bool × ℚ)) (r r' : ℚ) (h : r ≤ r') :
      Step c ⟨qs, r⟩ ⟨qs, r'⟩
  /-- Flip all quantifier types. -/
  | complement (qs : List (Bool × ℚ)) (r : ℚ) :
      Step c ⟨qs, r⟩ ⟨qs.map (fun p => (!p.1, p.2)), r⟩

/-- Reflexive-transitive closure: a full derivation. -/
inductive Steps (c : ℚ) : Line → Line → Prop
  | refl (L : Line) : Steps c L L
  | tail {L L' L'' : Line} : Steps c L L' → Step c L' L'' → Steps c L L''

/-- The **speedup-free** fragment (the three base-non-decreasing moves). -/
inductive StepNS (c : ℚ) : Line → Line → Prop
  | slowdown (qs : List (Bool × ℚ)) (Q : Bool) (x r : ℚ) (hx : 0 ≤ x) :
      StepNS c ⟨qs ++ [(Q, x)], r⟩ ⟨qs, c * max x r⟩
  | weaken (qs : List (Bool × ℚ)) (r r' : ℚ) (h : r ≤ r') :
      StepNS c ⟨qs, r⟩ ⟨qs, r'⟩
  | complement (qs : List (Bool × ℚ)) (r : ℚ) :
      StepNS c ⟨qs, r⟩ ⟨qs.map (fun p => (!p.1, p.2)), r⟩

/-- Reflexive-transitive closure of the speedup-free fragment. -/
inductive StepsNS (c : ℚ) : Line → Line → Prop
  | refl (L : Line) : StepsNS c L L
  | tail {L L' L'' : Line} : StepsNS c L L' → StepNS c L' L'' → StepsNS c L L''

/-- Each speedup-free move does not decrease the base exponent. -/
theorem stepNS_base_mono (hc : 1 ≤ c) {L L' : Line} (h : StepNS c L L') : L.base ≤ L'.base := by
  cases h with
  | slowdown qs Q x r hx =>
    show r ≤ c * max x r
    have h1 : r ≤ max x r := le_max_right x r
    have h2 : (0 : ℚ) ≤ max x r := le_trans hx (le_max_left x r)
    nlinarith [h1, h2, hc, mul_nonneg (by linarith : (0:ℚ) ≤ c - 1) h2]
  | weaken qs r r' hle => exact hle
  | complement qs r => exact le_refl _

/-- **The speedup-free fragment is base-non-decreasing.** -/
theorem base_mono_of_noSpeedup (hc : 1 ≤ c) {L L' : Line} (h : StepsNS c L L') :
    L.base ≤ L'.base := by
  induction h with
  | refl => exact le_refl _
  | tail _ step ih => exact le_trans ih (stepNS_base_mono hc step)

/-- **Cap rung 0.**  No speedup-free derivation takes `DTISP(n^r)` to `DTISP(n^{r'})` with `r' < r` — the
inclusion a contradiction would need.  Speedup is *necessary* to derive any contradiction. -/
theorem noSpeedup_no_contradiction (hc : 1 ≤ c) {r r' : ℚ}
    (h : StepsNS c ⟨[], r⟩ ⟨[], r'⟩) : r ≤ r' :=
  base_mono_of_noSpeedup hc h

/-- **Nonvacuity.**  A concrete `speedup; slowdown; slowdown` derivation strictly decreases the base — from `r`
to `c²r/(1+c)` — whenever `c² < 1 + c`.  So the system proves `SAT ∉ TISP(n^c)` for `c < φ`; the full system
(more speedups) reaches `2cos(π/7)`, the stated open cap. -/
theorem speedup_enables_contradiction (hc : 1 ≤ c) (hphi : c ^ 2 < 1 + c) {r : ℚ} (hr : 0 < r) :
    ∃ L_f : Line, Steps c ⟨[], r⟩ L_f ∧ L_f.quants = [] ∧ L_f.base < r := by
  have hc0' : (0 : ℚ) < c := by linarith
  have hc0 : (0 : ℚ) < 1 + c := by linarith
  set x : ℚ := c * r / (1 + c) with hxdef
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hxr : x ≤ r := by
    rw [hxdef, div_le_iff₀ hc0]; nlinarith [hr]
  have hrx : r - x = r / (1 + c) := by rw [hxdef]; field_simp; ring
  have hrx0 : 0 ≤ r - x := by rw [hrx]; positivity
  have hcrx : c * (r - x) = x := by rw [hrx, hxdef]; ring
  -- the three steps
  have s1 : Step c ⟨[], r⟩ ⟨[(true, x), (false, 0)], r - x⟩ := Step.speedup [] r x hx0 hxr
  have hmax1 : max (0 : ℚ) (r - x) = r - x := max_eq_right hrx0
  have s2 : Step c ⟨[(true, x), (false, 0)], r - x⟩ ⟨[(true, x)], c * (r - x)⟩ := by
    have h := Step.slowdown (c := c) [(true, x)] false 0 (r - x) (le_refl 0)
    rwa [hmax1] at h
  have hm : max x (c * (r - x)) = x := max_eq_left (le_of_eq hcrx)
  have s3 : Step c ⟨[(true, x)], c * (r - x)⟩ ⟨[], c * x⟩ := by
    have h := Step.slowdown (c := c) [] true x (c * (r - x)) hx0
    rwa [hm] at h
  refine ⟨⟨[], c * x⟩, ((Steps.refl _).tail s1).tail s2 |>.tail s3, rfl, ?_⟩
  -- c * x < r  ⟺  c²r/(1+c) < r  ⟺  c² < 1 + c
  rw [hxdef, show c * (c * r / (1 + c)) = c ^ 2 * r / (1 + c) from by ring, div_lt_iff₀ hc0]
  nlinarith [hphi, hr]

end PallLean.Paper93.DeepMath.PathB.AlternationTrading

#print axioms PallLean.Paper93.DeepMath.PathB.AlternationTrading.noSpeedup_no_contradiction
#print axioms PallLean.Paper93.DeepMath.PathB.AlternationTrading.speedup_enables_contradiction
