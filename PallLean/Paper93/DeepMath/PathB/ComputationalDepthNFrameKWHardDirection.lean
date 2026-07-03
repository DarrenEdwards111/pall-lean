import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSATKWGame

/-!
# N-Frame: the KW hard direction — protocols compile back to shallow transducers

The converse of the game compiler: **a protocol solving the boundary game for `f` yields a transducer computing `f`
of depth ≤ cost + 1**.  With the easy direction this closes the two-sided Karchmer–Wigderson characterization for
the boundary model: game communication *is* transducer depth, up to a factor of two.

**The construction (classical, made Trans-native).**  Induction on the protocol over rectangles `X × Y`
(`X` on Alice's 1-side, `Y` on Bob's 0-side): an Alice node splits `X` and becomes an **OR**; a Bob node splits `Y`
and becomes an **AND**; a leaf announcing `i` forces `x i` constant on `X` and opposite on `Y` (any two `X`-values
differing at `i` could not both differ from a `Y`-value), so the leaf is the literal `xᵢ` or `¬xᵢ`.

  `kwProt_to_trans` — **PROVED, the hard direction**: separation over any rectangle with `depth ≤ cost + 1`.
  `depthBudget_le_kwCost_succ` / `kwCost_le_two_depthBudget` — **PROVED, the characterization**:
        `depthBudget f ≤ kwCost f + 1` and `kwCost f ≤ 2·depthBudget f`.
  `sat3_depthBudget_lb` — **PROVED**: `sat3M N ≤ 4^(depthBudget (sat3Family N))` — an unconditional depth lower
        bound for the definite SAT target (`≥ log₄ m` — the log scale, from the protocol lower bound).

## Honest scope

The characterization makes the frontier exact: superlogarithmic `kwCost (sat3Family N)` **is** superlogarithmic
`depthBudget (sat3Family N)` — one open question, two equivalent faces.  Still open and named: **Spira rebalancing**
(`depthBudget ≲ log budget`), which would convert a superlog game bound into a superpoly volume bound, and the
superlog game bound itself (the research wall).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **The KW hard direction (proved)**: a protocol correct on the rectangle `X × Y` compiles to a transducer of
depth `≤ cost + 1` that is `true` on `X` and `false` on `Y`. -/
theorem kwProt_to_trans {n : ℕ} (p : KWProt n) :
    ∀ X Y : (Fin n → Bool) → Prop,
      (∀ x y, X x → Y y → x (p.run x y) ≠ y (p.run x y)) →
      ∃ t : Trans n, depth t ≤ p.cost + 1 ∧
        (∀ x, X x → eval t x = true) ∧ (∀ y, Y y → eval t y = false) := by
  induction p with
  | out i =>
    intro X Y hsolve
    by_cases hX : ∃ x, X x
    · by_cases hY : ∃ y, Y y
      · obtain ⟨x₀, hx₀⟩ := hX
        obtain ⟨y₀, hy₀⟩ := hY
        -- the leaf forces x i constant on X and opposite on Y
        have hXval : ∀ x, X x → x i = x₀ i := by
          intro x hx
          have h1 : x i ≠ y₀ i := hsolve x y₀ hx hy₀
          have h2 : x₀ i ≠ y₀ i := hsolve x₀ y₀ hx₀ hy₀
          cases hxi : x i <;> cases hx₀i : x₀ i <;> cases hy₀i : y₀ i <;>
            first
              | rfl
              | (exfalso; rw [hxi, hy₀i] at h1; exact h1 rfl)
              | (exfalso; rw [hx₀i, hy₀i] at h2; exact h2 rfl)
        have hYval : ∀ y, Y y → y i = !(x₀ i) := by
          intro y hy
          have h2 : x₀ i ≠ y i := hsolve x₀ y hx₀ hy
          cases hyi : y i <;> cases hx₀i : x₀ i <;>
            first
              | rfl
              | (exfalso; rw [hx₀i, hyi] at h2; exact h2 rfl)
        cases hv : x₀ i
        · -- the negative literal ¬xᵢ
          refine ⟨Trans.un not (Trans.var i), ?_, ?_, ?_⟩
          · show (0 : ℕ) + 1 ≤ 0 + 1
            omega
          · intro x hx
            show not (x i) = true
            rw [hXval x hx, hv]
            rfl
          · intro y hy
            show not (y i) = false
            rw [hYval y hy, hv]
            rfl
        · -- the positive literal xᵢ
          refine ⟨Trans.var i, ?_, ?_, ?_⟩
          · exact Nat.zero_le _
          · intro x hx
            show x i = true
            rw [hXval x hx]
            exact hv
          · intro y hy
            show y i = false
            rw [hYval y hy, hv]
            rfl
      · push_neg at hY
        exact ⟨Trans.cst true, Nat.zero_le _, fun x _ => rfl,
          fun y hy => absurd hy (hY y)⟩
    · push_neg at hX
      exact ⟨Trans.cst false, Nat.zero_le _, fun x hx => absurd hx (hX x),
        fun y _ => rfl⟩
  | askA q l r ihl ihr =>
    intro X Y hsolve
    obtain ⟨t₁, hd₁, hX₁, hY₁⟩ := ihl (fun x => X x ∧ q x = true) Y (by
      intro x y hx hy
      have h := hsolve x y hx.1 hy
      rw [KWProt.run_askA, if_pos hx.2] at h
      exact h)
    obtain ⟨t₂, hd₂, hX₂, hY₂⟩ := ihr (fun x => X x ∧ ¬(q x = true)) Y (by
      intro x y hx hy
      have h := hsolve x y hx.1 hy
      rw [KWProt.run_askA, if_neg hx.2] at h
      exact h)
    refine ⟨Trans.bin or t₁ t₂, ?_, ?_, ?_⟩
    · show max (depth t₁) (depth t₂) + 1 ≤ max l.cost r.cost + 1 + 1
      have hm : max (depth t₁) (depth t₂) ≤ max l.cost r.cost + 1 :=
        max_le (le_trans hd₁ (by have := Nat.le_max_left l.cost r.cost; omega))
          (le_trans hd₂ (by have := Nat.le_max_right l.cost r.cost; omega))
      omega
    · intro x hx
      show (eval t₁ x || eval t₂ x) = true
      by_cases hq : q x = true
      · rw [hX₁ x ⟨hx, hq⟩]
        exact Bool.true_or _
      · rw [hX₂ x ⟨hx, hq⟩]
        exact Bool.or_true _
    · intro y hy
      show (eval t₁ y || eval t₂ y) = false
      rw [hY₁ y hy, hY₂ y hy]
      rfl
  | askB q l r ihl ihr =>
    intro X Y hsolve
    obtain ⟨t₁, hd₁, hX₁, hY₁⟩ := ihl X (fun y => Y y ∧ q y = true) (by
      intro x y hx hy
      have h := hsolve x y hx hy.1
      rw [KWProt.run_askB, if_pos hy.2] at h
      exact h)
    obtain ⟨t₂, hd₂, hX₂, hY₂⟩ := ihr X (fun y => Y y ∧ ¬(q y = true)) (by
      intro x y hx hy
      have h := hsolve x y hx hy.1
      rw [KWProt.run_askB, if_neg hy.2] at h
      exact h)
    refine ⟨Trans.bin and t₁ t₂, ?_, ?_, ?_⟩
    · show max (depth t₁) (depth t₂) + 1 ≤ max l.cost r.cost + 1 + 1
      have hm : max (depth t₁) (depth t₂) ≤ max l.cost r.cost + 1 :=
        max_le (le_trans hd₁ (by have := Nat.le_max_left l.cost r.cost; omega))
          (le_trans hd₂ (by have := Nat.le_max_right l.cost r.cost; omega))
      omega
    · intro x hx
      show (eval t₁ x && eval t₂ x) = true
      rw [hX₁ x hx, hX₂ x hx]
      rfl
    · intro y hy
      show (eval t₁ y && eval t₂ y) = false
      by_cases hq : q y = true
      · rw [hY₁ y ⟨hy, hq⟩]
        exact Bool.false_and _
      · rw [hY₂ y ⟨hy, hq⟩]
        exact Bool.and_false _

/-! ### The two-sided characterization -/

/-- **Characterization, hard side (proved)**: `depthBudget f ≤ kwCost f + 1`. -/
theorem depthBudget_le_kwCost_succ {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    depthBudget f ≤ kwCost f + 1 := by
  have hne : {c | ∃ p : KWProt n, Solves p f ∧ p.cost = c}.Nonempty := by
    refine ⟨(kwProtOf hn (dnfFor f)).cost, kwProtOf hn (dnfFor f), ?_, rfl⟩
    have := kwProtOf_solves hn (dnfFor f)
    rw [eval_dnfFor] at this
    exact this
  obtain ⟨p, hp, hcost⟩ := Nat.sInf_mem hne
  obtain ⟨t, hd, hX, hY⟩ := kwProt_to_trans p (fun x => f x = true) (fun y => f y = false)
    (fun x y hx hy => hp x y hx hy)
  have hft : eval t = f := by
    funext x
    cases hfx : f x
    · exact hY x hfx
    · exact hX x hfx
  have h1 : depthBudget f ≤ depth t := Nat.sInf_le ⟨t, hft, rfl⟩
  have h2 : p.cost = kwCost f := hcost
  omega

/-- **Characterization, easy side (proved)**: `kwCost f ≤ 2·depthBudget f`. -/
theorem kwCost_le_two_depthBudget {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    kwCost f ≤ 2 * depthBudget f := by
  have hne : {d | ∃ t : Trans n, eval t = f ∧ depth t = d}.Nonempty :=
    ⟨depth (dnfFor f), dnfFor f, eval_dnfFor f, rfl⟩
  obtain ⟨t, ht, hdep⟩ := Nat.sInf_mem hne
  have hs : Solves (kwProtOf hn t) f := by
    rw [← ht]
    exact kwProtOf_solves hn t
  have h1 : kwCost f ≤ (kwProtOf hn t).cost := Nat.sInf_le ⟨kwProtOf hn t, hs, rfl⟩
  have h2 := kwProtOf_cost hn t
  have h3 : depth t = depthBudget f := hdep
  omega

/-- **The two-sided KW theorem for the boundary model (proved)**: game communication is transducer depth up to a
factor of two — the frontier question has exactly one face. -/
theorem kw_characterization {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    depthBudget f ≤ kwCost f + 1 ∧ kwCost f ≤ 2 * depthBudget f :=
  ⟨depthBudget_le_kwCost_succ hn f, kwCost_le_two_depthBudget hn f⟩

/-! ### The unconditional SAT depth lower bound -/

/-- **SAT depth lower bound (proved)**: `sat3M N ≤ 4^(depthBudget (sat3Family N))` — every transducer computing the
definite SAT target has depth `≥ log₄ m`.  The log scale; the superlog version is the frontier. -/
theorem sat3_depthBudget_lb (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N) :
    sat3M N ≤ 4 ^ depthBudget (sat3Family N) := by
  have hN : 0 < N := by
    by_contra h
    push_neg at h
    interval_cases N
    revert hm3
    decide
  have h1 := sat3_kwCost_lb N hv hm3
  have h2 := kwCost_le_two_depthBudget hN (sat3Family N)
  have h3 : (2 : ℕ) ^ kwCost (sat3Family N)
      ≤ 2 ^ (2 * depthBudget (sat3Family N)) :=
    Nat.pow_le_pow_right (by omega) h2
  have h4 : (2 : ℕ) ^ (2 * depthBudget (sat3Family N))
      = 4 ^ depthBudget (sat3Family N) := by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul]
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.kwProt_to_trans
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.kw_characterization
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_depthBudget_lb
