import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinCNFEncode

/-!
# Cook–Levin M2 — the tableau variable-indexing scheme

The tableau has three families of Boolean variables — cell bits `c[t][p]`, head one-hot `h[t][p]`, and state one-hot
`s[t][q]`.  To emit them as a single CNF over `ℕ`-indexed SAT variables (the `Lit = ℕ × Bool` of the semantics),
each `(family, t, x)` must get a **distinct** index, so the clauses never accidentally alias two logical variables.

This file gives such a scheme and proves it injective.  A bijective pairing `Nat.pair` folds `(t, x)` into one
index; multiplying by `3` and adding the family tag `0/1/2` keeps the three families disjoint (distinct residues mod
`3`).  Hence the whole map `(family, t, x) ↦ index` is injective — the exact well-formedness the tableau clauses
(`fixBits`, `oneHot`, transition) need.  Per `SCOPE_COOKLEVIN.md` the full assembly + poly emitter is deferred; this
is one more genuine, non-circular brick.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex

open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode

/-- The SAT variable for cell bit `c[t][p]`. -/
def cellVar (t p : ℕ) : ℕ := 3 * Nat.pair t p

/-- The SAT variable for head bit `h[t][p]`. -/
def headVar (t p : ℕ) : ℕ := 3 * Nat.pair t p + 1

/-- The SAT variable for state bit `s[t][q]`. -/
def stateVar (t q : ℕ) : ℕ := 3 * Nat.pair t q + 2

/-! ## Injectivity within each family -/

theorem cellVar_inj {t p t' p' : ℕ} (h : cellVar t p = cellVar t' p') : t = t' ∧ p = p' := by
  have hp : Nat.pair t p = Nat.pair t' p' := by unfold cellVar at h; omega
  have h2 := congrArg Nat.unpair hp
  rw [Nat.unpair_pair, Nat.unpair_pair] at h2
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

theorem headVar_inj {t p t' p' : ℕ} (h : headVar t p = headVar t' p') : t = t' ∧ p = p' := by
  have hp : Nat.pair t p = Nat.pair t' p' := by unfold headVar at h; omega
  have h2 := congrArg Nat.unpair hp
  rw [Nat.unpair_pair, Nat.unpair_pair] at h2
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

theorem stateVar_inj {t q t' q' : ℕ} (h : stateVar t q = stateVar t' q') : t = t' ∧ q = q' := by
  have hp : Nat.pair t q = Nat.pair t' q' := by unfold stateVar at h; omega
  have h2 := congrArg Nat.unpair hp
  rw [Nat.unpair_pair, Nat.unpair_pair] at h2
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

/-! ## Disjointness across families (distinct residues mod 3) -/

theorem cell_ne_head (t p t' p' : ℕ) : cellVar t p ≠ headVar t' p' := by
  unfold cellVar headVar; omega

theorem cell_ne_state (t p t' q' : ℕ) : cellVar t p ≠ stateVar t' q' := by
  unfold cellVar stateVar; omega

theorem head_ne_state (t p t' q' : ℕ) : headVar t p ≠ stateVar t' q' := by
  unfold headVar stateVar; omega

/-! ## Consequences for the encoding: the head / state variable lists are duplicate-free -/

theorem headVar_injective (t : ℕ) : Function.Injective (headVar t) := fun _ _ h => (headVar_inj h).2

theorem stateVar_injective (t : ℕ) : Function.Injective (stateVar t) := fun _ _ h => (stateVar_inj h).2

/-- The head-position variable list at time `t` (over `[0, n)`) has no duplicates — so its `oneHot` `atMostOne`
clauses genuinely constrain distinct positions. -/
theorem headVars_nodup (t n : ℕ) : ((List.range n).map (headVar t)).Nodup :=
  (List.nodup_range).map (headVar_injective t)

/-- Likewise for the state-variable list. -/
theorem stateVars_nodup (t n : ℕ) : ((List.range n).map (stateVar t)).Nodup :=
  (List.nodup_range).map (stateVar_injective t)

end PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
