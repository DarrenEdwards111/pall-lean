import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameFoolingCap

/-!
# N-Frame: the tree→DAG wall, quantified — what the game route can and cannot certify

The final wall between the boundary program and `sat3Target`, surveyed with theorems.

  `budget_le_two_pow_cbudget` — **PROVED, the unfolding**: every circuit unfolds into a tree at exponential cost —
        `budget f ≤ 2^(cbudget f + 1)` (each gate at most doubles the unfolded volume; with `cbudget ≤ budget`
        already proved, the tree/DAG gap is bracketed exactly: linear one way, exponential the other).
  `kwCost_le_linear_cbudget` — **PROVED, the transfer**: `kwCost f ≤ 36·cbudget f + 228` — through unfolding and
        Spira, boundary-game bounds convert to **circuit-size** bounds at linear rate.
  `kwCost_ceiling` — **PROVED, the ceiling**: `kwCost f ≤ 72n + 300` for *every* function — game cost is
        universally linear (it measures depth, and depth caps linearly).
  `kw_route_cbudget_ceiling` — **PROVED, the wall itself**: the circuit-size bound derivable through the game,
        `(kwCost f − 228)/36`, never exceeds `2n + 2`.

## Honest scope — the program's exact reach

The chain is now fully quantified: a superlogarithmic game bound for sat3 (the surviving open question) would give
superpolynomial **formula** size — historic, far beyond current knowledge — and, through the linear transfer, a
circuit-size bound of at most `~2n`.  `sat3Target` (superpolynomial `cbudget`) is **provably outside the reach of
the entire KW/depth route**: it requires size-specific, sharing-aware methods — consistent with the classical
situation, where general circuit lower bounds stall at small-constant·n.  Both remaining walls — superpoly
`χ(sat3)` by non-elementary methods, and size-specific circuit techniques — are research-open, named, and not
claimed.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The unfolding: circuits to trees at exponential cost -/

/-- Unfold one gate into a tree, given trees for the earlier wires. -/
def treeOf {n : ℕ} (acc : List (Trans n)) : CGate n → Trans n
  | .var i => Trans.var i
  | .cst b => Trans.cst b
  | .un op j => Trans.un op (acc.getD j (Trans.cst false))
  | .bin op i j => Trans.bin op (acc.getD i (Trans.cst false)) (acc.getD j (Trans.cst false))

/-- Unfold a circuit into the list of its wire trees. -/
def unfoldAll {n : ℕ} (acc : List (Trans n)) : List (CGate n) → List (Trans n)
  | [] => acc
  | g :: gs => unfoldAll (acc ++ [treeOf acc g]) gs

theorem map_getD_eval {n : ℕ} (x : Fin n → Bool) (l : List (Trans n)) (j : ℕ) :
    (l.map (fun t => eval t x)).getD j false = eval (l.getD j (Trans.cst false)) x := by
  induction l generalizing j with
  | nil => cases j <;> rfl
  | cons t ts ih =>
    cases j with
    | zero => rfl
    | succ jj => exact ih jj

/-- The unfolded trees evaluate to the circuit's wire values. -/
theorem unfoldAll_evals {n : ℕ} (x : Fin n → Bool) :
    ∀ (gs : List (CGate n)) (acc : List (Trans n)),
      (unfoldAll acc gs).map (fun t => eval t x) = runFrom x (acc.map (fun t => eval t x)) gs := by
  intro gs
  induction gs with
  | nil => intro acc; rfl
  | cons g rest ih =>
    intro acc
    show (unfoldAll (acc ++ [treeOf acc g]) rest).map _
        = runFrom x ((acc.map (fun t => eval t x)) ++ [evalGate x (acc.map (fun t => eval t x)) g]) rest
    rw [ih (acc ++ [treeOf acc g]), List.map_append]
    congr 2
    show [eval (treeOf acc g) x] = [evalGate x (acc.map (fun t => eval t x)) g]
    congr 1
    cases g with
    | var i => rfl
    | cst b => rfl
    | un op j =>
      show op (eval (acc.getD j (Trans.cst false)) x) = op ((acc.map _).getD j false)
      rw [map_getD_eval]
    | bin op i j =>
      show op (eval (acc.getD i (Trans.cst false)) x) (eval (acc.getD j (Trans.cst false)) x)
          = op ((acc.map _).getD i false) ((acc.map _).getD j false)
      rw [map_getD_eval, map_getD_eval]

theorem getD_volume_le {n : ℕ} (acc : List (Trans n)) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ t ∈ acc, volume t ≤ B) (j : ℕ) :
    volume (acc.getD j (Trans.cst false)) ≤ B := by
  induction acc generalizing j with
  | nil =>
    cases j <;> exact hB1
  | cons t ts ih =>
    cases j with
    | zero => exact hB t List.mem_cons_self
    | succ jj =>
      exact ih (fun t' ht' => hB t' (List.mem_cons_of_mem t ht')) jj

/-- Each unfolded tree is bounded: the accumulator bound at most doubles per gate. -/
theorem unfoldAll_volume {n : ℕ} :
    ∀ (gs : List (CGate n)) (acc : List (Trans n)) (B : ℕ), 1 ≤ B →
      (∀ t ∈ acc, volume t ≤ B) →
      ∀ t ∈ unfoldAll acc gs, volume t ≤ (B + 1) * 2 ^ gs.length := by
  intro gs
  induction gs with
  | nil =>
    intro acc B hB1 hB t ht
    have h1 := hB t ht
    have h2 : (B + 1) * 2 ^ (List.length ([] : List (CGate n))) = B + 1 := by
      rw [List.length_nil, pow_zero, Nat.mul_one]
    omega
  | cons g rest ih =>
    intro acc B hB1 hB t ht
    have hnew : volume (treeOf acc g) ≤ 2 * B + 1 := by
      cases g with
      | var i =>
        show (1 : ℕ) ≤ 2 * B + 1
        omega
      | cst b =>
        show (1 : ℕ) ≤ 2 * B + 1
        omega
      | un op j =>
        show volume (acc.getD j (Trans.cst false)) + 1 ≤ 2 * B + 1
        have := getD_volume_le acc B hB1 hB j
        omega
      | bin op i j =>
        show volume (acc.getD i (Trans.cst false))
            + volume (acc.getD j (Trans.cst false)) + 1 ≤ 2 * B + 1
        have h1 := getD_volume_le acc B hB1 hB i
        have h2 := getD_volume_le acc B hB1 hB j
        omega
    have hacc' : ∀ t' ∈ acc ++ [treeOf acc g], volume t' ≤ 2 * B + 1 := by
      intro t' ht'
      rcases List.mem_append.mp ht' with h | h
      · have := hB t' h
        omega
      · rw [List.mem_singleton] at h
        subst h
        exact hnew
    have hres := ih (acc ++ [treeOf acc g]) (2 * B + 1) (by omega) hacc' t ht
    have harith : (2 * B + 1 + 1) * 2 ^ rest.length = (B + 1) * 2 ^ (g :: rest).length := by
      show _ = (B + 1) * 2 ^ (rest.length + 1)
      rw [pow_succ]
      ring
    omega

theorem getD_mem_or {α : Type} (l : List α) (k : ℕ) (d : α) :
    l.getD k d ∈ l ∨ l.getD k d = d := by
  induction l generalizing k with
  | nil => right; cases k <;> rfl
  | cons a l ih =>
    cases k with
    | zero => left; exact List.mem_cons_self
    | succ kk =>
      rcases ih kk with h | h
      · left
        exact List.mem_cons_of_mem a h
      · right
        exact h

/-- **The unfolding theorem (proved)**: every circuit unfolds into an equivalent tree at exponential cost.  With
`cbudget ≤ budget`, the tree/DAG gap is bracketed exactly. -/
theorem budget_le_two_pow_cbudget {n : ℕ} (f : (Fin n → Bool) → Bool) :
    budget f ≤ 2 ^ (cbudget f + 1) := by
  have hne : {s | ∃ c : List (CGate n), computes c f ∧ c.length = s}.Nonempty := by
    refine ⟨(compile 0 (dnfFor f)).length, compile 0 (dnfFor f), ?_, rfl⟩
    have := compile_computes (dnfFor f)
    rwa [show (fun x => eval (dnfFor f) x) = f from funext (fun x => by
      rw [eval_dnfFor])] at this
  obtain ⟨c, hcomp, hlen⟩ := Nat.sInf_mem hne
  set tree : Trans n := (unfoldAll [] c).getD (c.length - 1) (Trans.cst false) with htree
  have heval : eval tree = f := by
    funext x
    have h1 : eval tree x = ((unfoldAll [] c).map (fun t => eval t x)).getD
        (c.length - 1) false := by
      rw [map_getD_eval]
    rw [h1, unfoldAll_evals x c []]
    exact hcomp x
  have hvol : volume tree ≤ 2 ^ (c.length + 1) := by
    rcases getD_mem_or (unfoldAll [] c) (c.length - 1) (Trans.cst false) with h | h
    · have := unfoldAll_volume c [] 1 (le_refl 1) (fun t ht => absurd ht List.not_mem_nil)
        tree (htree ▸ h)
      have harith : (1 + 1) * 2 ^ c.length = 2 ^ (c.length + 1) := by
        rw [pow_succ]
        ring
      omega
    · rw [htree, h]
      show (1 : ℕ) ≤ 2 ^ (c.length + 1)
      exact Nat.one_le_two_pow
  have hbud : budget f ≤ volume tree := Nat.sInf_le ⟨tree, heval, rfl⟩
  have hcb : c.length = cbudget f := hlen
  rw [← hcb]
  omega

/-! ### The transfer and the ceiling -/

/-- **The transfer (proved)**: game communication is linear in circuit size — boundary-game lower bounds convert
to circuit-size lower bounds at rate `1/36`. -/
theorem kwCost_le_linear_cbudget {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    kwCost f ≤ 36 * cbudget f + 228 := by
  have h1 := kwCost_le_log_budget hn f
  have h2 := budget_le_two_pow_cbudget f
  have hpow : budget f + 8 ≤ 2 ^ (cbudget f + 4) := by
    have hA : (2 : ℕ) ^ (cbudget f + 4) = 8 * 2 ^ (cbudget f + 1) := by
      rw [show cbudget f + 4 = (cbudget f + 1) + 3 from by omega, pow_add]
      ring
    have hge : (2 : ℕ) ≤ 2 ^ (cbudget f + 1) :=
      le_trans (by omega) (Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ cbudget f + 1))
    omega
  have hlog : Nat.log 2 (budget f + 8) ≤ cbudget f + 4 := by
    have := Nat.log_mono_right (b := 2) hpow
    rwa [Nat.log_pow (by omega)] at this
  omega

theorem three_n_le_pow (n : ℕ) : 3 * n + 2 ≤ 2 ^ (n + 2) := by
  induction n with
  | zero =>
    show (2 : ℕ) ≤ 2 ^ 2
    omega
  | succ k ihk =>
    have h4 : (4 : ℕ) ≤ 2 ^ (k + 2) :=
      le_trans (by omega) (Nat.pow_le_pow_right (by omega) (by omega : 2 ≤ k + 2))
    have hstep : (2 : ℕ) ^ (k + 1 + 2) = 2 * 2 ^ (k + 2) := by
      rw [pow_succ]
      ring
    omega

/-- **The ceiling (proved)**: game communication is universally linear — the game measures depth, and depth caps
linearly for every function. -/
theorem kwCost_ceiling {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    kwCost f ≤ 72 * n + 300 := by
  have h1 := kwCost_le_log_budget hn f
  have hbud : budget f ≤ (3 * n + 2) * 2 ^ n + 1 :=
    le_trans (budget_le_budgetAt 3 (exists_width_le_three f)) (budgetAt_three_le_exp f)
  have hpow : budget f + 8 ≤ 2 ^ (2 * n + 6) := by
    have h32 := three_n_le_pow n
    have hprod : (3 * n + 2) * 2 ^ n ≤ 2 ^ (2 * n + 2) := by
      have := Nat.mul_le_mul_right (2 ^ n) h32
      have hpp : (2 : ℕ) ^ (n + 2) * 2 ^ n = 2 ^ (2 * n + 2) := by
        rw [← pow_add]
        congr 1
        omega
      omega
    have hA : (2 : ℕ) ^ (2 * n + 2) ≤ 2 ^ (2 * n + 5) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hB : (32 : ℕ) ≤ 2 ^ (2 * n + 5) :=
      le_trans (by omega) (Nat.pow_le_pow_right (by omega) (by omega : 5 ≤ 2 * n + 5))
    have hC : (2 : ℕ) ^ (2 * n + 6) = 2 ^ (2 * n + 5) + 2 ^ (2 * n + 5) := by
      rw [pow_succ]
      ring
    omega
  have hlog : Nat.log 2 (budget f + 8) ≤ 2 * n + 6 := by
    have := Nat.log_mono_right (b := 2) hpow
    rwa [Nat.log_pow (by omega)] at this
  omega

/-- **THE WALL, QUANTIFIED (proved)**: the circuit-size bound derivable through the boundary game never exceeds
`2n + 2` — superpolynomial `cbudget` (`sat3Target`) is provably outside the reach of the entire KW/depth route. -/
theorem kw_route_cbudget_ceiling {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    (kwCost f - 228) / 36 ≤ 2 * n + 2 := by
  have h := kwCost_ceiling hn f
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.budget_le_two_pow_cbudget
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.kwCost_le_linear_cbudget
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.kwCost_ceiling
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.kw_route_cbudget_ceiling
