import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameKWHardDirection

/-!
# N-Frame: Spira rebalancing — the converter from depth to volume

The missing middle of the KW route, proved: **every transducer rebalances to depth `O(log volume)`**.  With the
two-sided KW characterization this closes the converter: a superlogarithmic game lower bound for any target now
*implies* a superpolynomial volume lower bound — the open frontier is reduced to the game bound alone.

**The construction.**  Walk from the root into the larger child until the subtree volume first drops to
`W := V/2`; the crossing guarantees `W ≤ 2·vol s ≤ 2W` (`spira_separator`, which also returns the surgery context
`g` with its semantic and volume invariants).  Replace `s` by each constant, rebalance the three pieces recursively,
and reassemble with a mux `(s' ∧ a') ∨ (¬s' ∧ b')` — three extra depth per round.  Each round shrinks the potential
`volume + 8` by a factor `7/8` (for `volume ≥ 25`), giving the rounds bound and, at `k = 6(log₂(V+8)+1)` rounds
(`(8/7)^6 > 2`), the logarithmic headline.

  `spira_separator` — **PROVED**: the balanced-split subtree and its context, with all invariants.
  `spira_rounds` — **PROVED**: `7^k·(volume+8) ≤ 32·8^k` ⇒ an equivalent transducer of depth `≤ 3k + 24`.
  `spira_depth_le` — **PROVED, the theorem**: depth `≤ 18·(log₂(volume+8)+1) + 24`.
  `depthBudget_le_log_budget` — **PROVED**: `depthBudget f ≤ 18·(log₂(budget f + 8)+1) + 24`.
  `kwCost_le_log_budget` — **PROVED, the converter closed**: `kwCost f ≤ 36·(log₂(budget f + 8)+1) + 48` — a
        superlogarithmic game bound forces a superpolynomial budget.

## Honest scope

Of the frontier trio, two are now theorems (hard direction, Spira); what remains is exactly one open question: a
**superlogarithmic lower bound for the SAT boundary game** — "maintaining one globally coherent witness across many
clauses costs communication".  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The separator -/

/-- **The separator (proved)**: any transducer of volume `> W ≥ 1` contains a subtree `s` with
`W ≤ 2·volume s` and `volume s ≤ W`, together with the surgery context `g`: replacing `s` by anything that agrees
with it pointwise preserves the evaluation, and the volume of the replacement is exact. -/
theorem spira_separator {n : ℕ} (W : ℕ) (hW : 1 ≤ W) :
    ∀ c : Trans n, W < volume c →
    ∃ (s : Trans n) (g : Trans n → Trans n),
      (∀ r x, eval r x = eval s x → eval (g r) x = eval c x) ∧
      (∀ r, volume (g r) = volume c - volume s + volume r) ∧
      W ≤ 2 * volume s ∧ volume s ≤ W := by
  intro c
  induction c with
  | var i =>
    intro h
    have h' : W < 1 := h
    omega
  | cst b =>
    intro h
    have h' : W < 1 := h
    omega
  | un op s₀ ih =>
    intro h
    have h' : W < volume s₀ + 1 := h
    by_cases hc : volume s₀ ≤ W
    · refine ⟨s₀, fun r => Trans.un op r, ?_, ?_, ?_, hc⟩
      · intro r x hrx
        show op (eval r x) = op (eval s₀ x)
        rw [hrx]
      · intro r
        show volume r + 1 = volume s₀ + 1 - volume s₀ + volume r
        omega
      · omega
    · push_neg at hc
      obtain ⟨s, g', hsem, hvol, hlo, hhi⟩ := ih hc
      refine ⟨s, fun r => Trans.un op (g' r), ?_, ?_, hlo, hhi⟩
      · intro r x hrx
        show op (eval (g' r) x) = op (eval s₀ x)
        rw [hsem r x hrx]
      · intro r
        have hv := hvol r
        have hs_le : volume s ≤ volume s₀ := by omega
        show volume (g' r) + 1 = volume s₀ + 1 - volume s + volume r
        omega
  | bin op t₁ t₂ ih₁ ih₂ =>
    intro h
    have h' : W < volume t₁ + volume t₂ + 1 := h
    by_cases hord : volume t₂ ≤ volume t₁
    · by_cases hc : volume t₁ ≤ W
      · refine ⟨t₁, fun r => Trans.bin op r t₂, ?_, ?_, ?_, hc⟩
        · intro r x hrx
          show op (eval r x) (eval t₂ x) = op (eval t₁ x) (eval t₂ x)
          rw [hrx]
        · intro r
          show volume r + volume t₂ + 1 = volume t₁ + volume t₂ + 1 - volume t₁ + volume r
          omega
        · omega
      · push_neg at hc
        obtain ⟨s, g', hsem, hvol, hlo, hhi⟩ := ih₁ hc
        refine ⟨s, fun r => Trans.bin op (g' r) t₂, ?_, ?_, hlo, hhi⟩
        · intro r x hrx
          show op (eval (g' r) x) (eval t₂ x) = op (eval t₁ x) (eval t₂ x)
          rw [hsem r x hrx]
        · intro r
          have hv := hvol r
          have hs_le : volume s ≤ volume t₁ := by omega
          show volume (g' r) + volume t₂ + 1
              = volume t₁ + volume t₂ + 1 - volume s + volume r
          omega
    · push_neg at hord
      by_cases hc : volume t₂ ≤ W
      · refine ⟨t₂, fun r => Trans.bin op t₁ r, ?_, ?_, ?_, hc⟩
        · intro r x hrx
          show op (eval t₁ x) (eval r x) = op (eval t₁ x) (eval t₂ x)
          rw [hrx]
        · intro r
          show volume t₁ + volume r + 1 = volume t₁ + volume t₂ + 1 - volume t₂ + volume r
          omega
        · omega
      · push_neg at hc
        obtain ⟨s, g', hsem, hvol, hlo, hhi⟩ := ih₂ hc
        refine ⟨s, fun r => Trans.bin op t₁ (g' r), ?_, ?_, hlo, hhi⟩
        · intro r x hrx
          show op (eval t₁ x) (eval (g' r) x) = op (eval t₁ x) (eval t₂ x)
          rw [hsem r x hrx]
        · intro r
          have hv := hvol r
          have hs_le : volume s ≤ volume t₂ := by omega
          show volume t₁ + volume (g' r) + 1
              = volume t₁ + volume t₂ + 1 - volume s + volume r
          omega

/-! ### The mux -/

theorem eval_mux_true {n : ℕ} (s' a' b' : Trans n) (x : Fin n → Bool)
    (hs : eval s' x = true) :
    eval (Trans.bin or (Trans.bin and s' a') (Trans.bin and (Trans.un not s') b')) x
      = eval a' x := by
  show ((eval s' x && eval a' x) || (!(eval s' x) && eval b' x)) = eval a' x
  rw [hs]
  cases eval a' x <;> rfl

theorem eval_mux_false {n : ℕ} (s' a' b' : Trans n) (x : Fin n → Bool)
    (hs : eval s' x = false) :
    eval (Trans.bin or (Trans.bin and s' a') (Trans.bin and (Trans.un not s') b')) x
      = eval b' x := by
  show ((eval s' x && eval a' x) || (!(eval s' x) && eval b' x)) = eval b' x
  rw [hs]
  cases eval b' x <;> rfl

theorem depth_mux_le {n : ℕ} (s' a' b' : Trans n) (D : ℕ)
    (h1 : depth s' ≤ D) (h2 : depth a' ≤ D) (h3 : depth b' ≤ D) :
    depth (Trans.bin or (Trans.bin and s' a') (Trans.bin and (Trans.un not s') b'))
      ≤ D + 3 := by
  show max (max (depth s') (depth a') + 1) (max (depth s' + 1) (depth b') + 1) + 1 ≤ D + 3
  have m1 : max (depth s') (depth a') ≤ D := max_le h1 h2
  have m2 : max (depth s' + 1) (depth b') ≤ D + 1 := max_le (by omega) (by omega)
  have m3 : max (max (depth s') (depth a') + 1) (max (depth s' + 1) (depth b') + 1)
      ≤ D + 2 := max_le (by omega) (by omega)
  omega

/-! ### The rounds induction -/

/-- **The rounds bound (proved)**: `7^k·(volume+8) ≤ 32·8^k` yields an equivalent transducer of depth `≤ 3k+24`. -/
theorem spira_rounds {n : ℕ} :
    ∀ (k : ℕ) (t : Trans n), 7 ^ k * (volume t + 8) ≤ 32 * 8 ^ k →
    ∃ t' : Trans n, eval t' = eval t ∧ depth t' ≤ 3 * k + 24 := by
  intro k
  induction k with
  | zero =>
    intro t ht
    rw [pow_zero, pow_zero, one_mul, Nat.mul_one] at ht
    refine ⟨t, rfl, ?_⟩
    have h := depth_lt_volume t
    omega
  | succ k ih =>
    intro t ht
    by_cases hsmall : volume t ≤ 24
    · refine ⟨t, rfl, ?_⟩
      have := depth_lt_volume t
      omega
    · push_neg at hsmall
      obtain ⟨s, g, hsem, hvol, hlo, hhi⟩ :=
        spira_separator (volume t / 2) (by omega) t (by omega)
      have hvol_g : ∀ b : Bool, volume (g (Trans.cst b)) = volume t - volume s + 1 :=
        fun b => hvol (Trans.cst b)
      have hs_le_t : volume s ≤ volume t := by omega
      -- each piece shrinks the potential by 7/8
      have hpiece_s : 8 * (volume s + 8) ≤ 7 * (volume t + 8) := by omega
      have hpiece_g : ∀ b : Bool,
          8 * (volume (g (Trans.cst b)) + 8) ≤ 7 * (volume t + 8) := by
        intro b
        rw [hvol_g b]
        omega
      -- lift through the schedule
      have hlift : ∀ p : Trans n, 8 * (volume p + 8) ≤ 7 * (volume t + 8) →
          7 ^ k * (volume p + 8) ≤ 32 * 8 ^ k := by
        intro p hp
        have h1 : 7 ^ k * (8 * (volume p + 8)) ≤ 7 ^ k * (7 * (volume t + 8)) :=
          Nat.mul_le_mul_left _ hp
        have h2 : 7 ^ k * (7 * (volume t + 8)) = 7 ^ (k + 1) * (volume t + 8) := by
          rw [pow_succ]
          ring
        have h4 : (32 : ℕ) * 8 ^ (k + 1) = 8 * (32 * 8 ^ k) := by
          rw [pow_succ]
          ring
        have h5 : 7 ^ k * (8 * (volume p + 8)) = 8 * (7 ^ k * (volume p + 8)) := by
          ring
        omega
      obtain ⟨s', hs'e, hs'd⟩ := ih s (hlift s hpiece_s)
      obtain ⟨a', ha'e, ha'd⟩ := ih (g (Trans.cst true)) (hlift _ (hpiece_g true))
      obtain ⟨b', hb'e, hb'd⟩ := ih (g (Trans.cst false)) (hlift _ (hpiece_g false))
      refine ⟨Trans.bin or (Trans.bin and s' a') (Trans.bin and (Trans.un not s') b'),
        ?_, ?_⟩
      · funext x
        by_cases hsx : eval s x = true
        · have hs'x : eval s' x = true := by
            rw [hs'e]
            exact hsx
          rw [eval_mux_true s' a' b' x hs'x]
          have := congrFun ha'e x
          rw [this]
          exact hsem (Trans.cst true) x hsx.symm
        · have hsxf : eval s x = false := by
            cases hcc : eval s x
            · rfl
            · exact absurd hcc hsx
          have hs'x : eval s' x = false := by
            rw [hs'e]
            exact hsxf
          rw [eval_mux_false s' a' b' x hs'x]
          have := congrFun hb'e x
          rw [this]
          exact hsem (Trans.cst false) x hsxf.symm
      · have := depth_mux_le s' a' b' (3 * k + 24) hs'd ha'd hb'd
        omega

/-! ### The theorem and the converter -/

/-- **Spira's theorem for the boundary model (proved)**: every transducer rebalances to depth
`≤ 18·(log₂(volume+8)+1) + 24`. -/
theorem spira_depth_le {n : ℕ} (t : Trans n) :
    ∃ t' : Trans n, eval t' = eval t ∧
      depth t' ≤ 18 * (Nat.log 2 (volume t + 8) + 1) + 24 := by
  set L := Nat.log 2 (volume t + 8) with hL
  have hsched : 7 ^ (6 * (L + 1)) * (volume t + 8) ≤ 32 * 8 ^ (6 * (L + 1)) := by
    have h1 : volume t + 8 < 2 ^ (L + 1) :=
      Nat.lt_pow_succ_log_self (by omega) _
    have h5 : (7 : ℕ) ^ (6 * (L + 1)) * (volume t + 8)
        ≤ 7 ^ (6 * (L + 1)) * 2 ^ (L + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : (7 : ℕ) ^ (6 * (L + 1)) * 2 ^ (L + 1) = (7 ^ 6 * 2) ^ (L + 1) := by
      rw [mul_pow, ← pow_mul]
    have h3 : ((7 : ℕ) ^ 6 * 2) ^ (L + 1) ≤ ((8 : ℕ) ^ 6) ^ (L + 1) :=
      Nat.pow_le_pow_left (by norm_num) _
    have h4 : ((8 : ℕ) ^ 6) ^ (L + 1) = 8 ^ (6 * (L + 1)) := by
      rw [← pow_mul]
    have h6 : (8 : ℕ) ^ (6 * (L + 1)) ≤ 32 * 8 ^ (6 * (L + 1)) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  obtain ⟨t', he, hd⟩ := spira_rounds (6 * (L + 1)) t hsched
  exact ⟨t', he, by omega⟩

/-- **The depth budget is logarithmic in the volume budget (proved)**. -/
theorem depthBudget_le_log_budget {n : ℕ} (f : (Fin n → Bool) → Bool) :
    depthBudget f ≤ 18 * (Nat.log 2 (budget f + 8) + 1) + 24 := by
  have hne : {v | ∃ t : Trans n, eval t = f ∧ volume t = v}.Nonempty :=
    ⟨volume (dnfFor f), dnfFor f, eval_dnfFor f, rfl⟩
  obtain ⟨t, ht, hvol⟩ := Nat.sInf_mem hne
  obtain ⟨t', he, hd⟩ := spira_depth_le t
  have hft : eval t' = f := by
    rw [he, ht]
  have h1 : depthBudget f ≤ depth t' := Nat.sInf_le ⟨t', hft, rfl⟩
  have h2 : volume t = budget f := hvol
  rw [← h2]
  omega

/-- **THE CONVERTER, CLOSED (proved)**: `kwCost f ≤ 36·(log₂(budget f + 8)+1) + 48`.  Contrapositive: a
superlogarithmic lower bound for the boundary game forces a superpolynomial volume budget.  The frontier is now
exactly one open question — the game bound for `sat3Family`. -/
theorem kwCost_le_log_budget {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    kwCost f ≤ 36 * (Nat.log 2 (budget f + 8) + 1) + 48 := by
  have h1 := kwCost_le_two_depthBudget hn f
  have h2 := depthBudget_le_log_budget f
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.spira_separator
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.spira_rounds
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.spira_depth_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.depthBudget_le_log_budget
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.kwCost_le_log_budget
