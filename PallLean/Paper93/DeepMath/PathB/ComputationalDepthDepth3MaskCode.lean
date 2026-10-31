import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DescentCount

/-!
# Block-DT model, foundation 52: branching holography, step 4j — term-relative mask code (branch only)

The bridge to the `(3^w)^s` label bound: a block mask is encoded by its values on the *positions* of its
(peel-recovered) term — a term-independent list of `≤ w` ternary slots — and recovered from that code
together with the term.  This is what lets the global label live in a `(3^w)^s` space rather than carrying
the freed-variable set (which would be `n`-dependent / vacuous, cf. brick 47).

* `maskOnTerm T m` — the per-literal code `T.lits.map (m ∘ litVarOf)` (length `|T.lits| ≤ w`).
* `maskFromTerm T vals` — recover a mask from a code and the term (look the variable up in the term).
* `maskFromTerm_maskOnTerm` — recovery is exact for masks supported on the term's variables (which the
  descent masks are, by `freeVarsOf_subset_litVars`).

So `(term, code)` determines the mask, and the code is one of `≤ 3^|T.lits| ≤ 3^w`.  Assembling the global
`|Labels| ≤ (3^w)^s` (pad codes to `Fin w`, list to `Fin F`) + the p-biased measure remain.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The per-literal code of a mask relative to a term: the mask's value at each literal's variable. -/
def maskOnTerm (T : Clause n) (m : Fin n → Option Bool) : List (Option Bool) :=
  T.lits.map (fun ℓ => m (litVarOf ℓ))

/-- Recover a mask from a term-relative code: look the variable up among the term's literal-variables. -/
def maskFromTerm (T : Clause n) (vals : List (Option Bool)) : Fin n → Option Bool :=
  fun v => (((T.lits.map litVarOf).zip vals).lookup v).join

/-- Looking up `v` in the zipped (variable, mask-value) list returns `some (m v)` exactly when `v` is one
of the term's literal-variables. -/
theorem lookup_zip_maps (l : List (Rung4Literal n)) (m : Fin n → Option Bool) (v : Fin n) :
    ((l.map litVarOf).zip (l.map (fun ℓ => m (litVarOf ℓ)))).lookup v
      = if v ∈ l.map litVarOf then some (m v) else none := by
  induction l with
  | nil => simp
  | cons ℓ l ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons, List.mem_cons]
    by_cases hℓ : v = litVarOf ℓ
    · subst hℓ; simp
    · have hbeq : (v == litVarOf ℓ) = false := by simpa using hℓ
      rw [hbeq]
      simp only [ih]
      by_cases hmem : v ∈ l.map litVarOf
      · simp [hmem]
      · simp [hmem, hℓ]

/-- **Exact recovery.**  For a mask supported on the term's literal-variables, the term-relative code
recovers it. -/
theorem maskFromTerm_maskOnTerm (T : Clause n) (m : Fin n → Option Bool)
    (hsupp : ∀ v, v ∉ T.lits.map litVarOf → m v = none) :
    maskFromTerm T (maskOnTerm T m) = m := by
  funext v
  rw [maskFromTerm, maskOnTerm, lookup_zip_maps]
  by_cases hv : v ∈ T.lits.map litVarOf
  · rw [if_pos hv]; rfl
  · rw [if_neg hv]; exact (hsupp v hv).symm

/-- **The descent masks are term-relative-codable.**  Each `descentSatMasks` block mask is supported on
its term's variables (`freeVarsOf ⊆ litVars`), so its term-relative code recovers it. -/
theorem descentMask_recover (σ : Fin n → Option Bool) (T : Clause n) (x : Fin n → Bool) :
    maskFromTerm T (maskOnTerm T (fun v => if v ∈ freeVarsOf σ T then some (x v) else none))
      = (fun v => if v ∈ freeVarsOf σ T then some (x v) else none) := by
  apply maskFromTerm_maskOnTerm
  intro v hv
  rw [if_neg (fun hf => hv (freeVarsOf_subset_litVars σ T v hf))]

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.maskFromTerm_maskOnTerm
