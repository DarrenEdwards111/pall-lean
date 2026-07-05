import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCurvatureAccumulation

/-!
# N-Frame: cut factorization — the frontier determination and the excess charge

The structural rung of curvature accumulation.  Two honest theorems:

  `frontier_val_agree` — **PROVED, the cut factorization**: a *relative* `cone_val_agree`.  Fix a frontier
        set `F` of wires.  If two inputs agree on every frontier wire's value, and every non-frontier
        variable gate of the cone reads a coordinate on which they agree, then they agree on the entire
        cone — in particular the output.  The output factors through the frontier: `F`-values plus the
        own-side variables determine `f`.  (Generalizes `cone_val_agree`, which is the `F = ∅` case.)
  `coneExcess_ge_multiReader` — **PROVED, the excess charge**: `coneExcess` bounds the number of cone
        wires with two or more readers.  Every multi-reader wire contributes at least one to the excess
        sum.

Together: the output factors through any frontier, and a frontier made of genuinely-shared (multi-reader)
wires is charged one unit of curvature per wire.

## Honest scope

These are the structural halves.  The remaining semantic content — that a *minimal separating* frontier
for a high-row-count partition must contain `Ω(m)` multi-reader wires (so that few-reader wires cannot
route `2^Ω(m)` distinct rows, via `shared_split_row_capacity`) — is the accumulation mountain, unclaimed.
The chain would read: many rows ⇒ any separating frontier is large ⇒ `Ω(m)` multi-reader wires ⇒
`coneExcess ≥ Ω(m)` ⇒ `cbudget ≥ 2N + Ω(m)`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE CUT FACTORIZATION (proved)**: a frontier's wire values plus the own-side variables determine
the whole cone. -/
theorem frontier_val_agree {n : ℕ} (c : List (CGate n)) (root : ℕ) (F : Finset ℕ)
    (x x' : Fin n → Bool)
    (hFval : ∀ p ∈ F, (runFrom x [] c).getD p false = (runFrom x' [] c).getD p false)
    (hfront : ∀ q ∈ coneOf c root, q ∉ F →
      ∀ i, c.getD q (CGate.cst false) = CGate.var i → x i = x' i) :
    ∀ q, q ∈ coneOf c root →
      (runFrom x [] c).getD q false = (runFrom x' [] c).getD q false := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq
    by_cases hqF : q ∈ F
    · exact hFval q hqF
    · by_cases hlen : q < c.length
      · rw [output_getD_at x c q hlen, output_getD_at x' c q hlen]
        cases hg : c.getD q (CGate.cst false) with
        | var i =>
          show x i = x' i
          exact hfront q hq hqF i hg
        | cst b => rfl
        | un op j =>
          show op ((runFrom x [] (c.take q)).getD j false)
              = op ((runFrom x' [] (c.take q)).getD j false)
          by_cases hj : j < q
          · rw [takeRun_getD x c q j hj (le_of_lt hlen),
              takeRun_getD x' c q j hj (le_of_lt hlen)]
            rw [ih j hj (cone_child c root q hq j (by
              rw [childrenOf_eq_un c q op j hg, if_pos hj]
              exact Finset.mem_singleton_self j))]
          · have hxlen : (runFrom x [] (c.take q)).length ≤ j := by
              rw [runFrom_length x (c.take q) [], List.length_take]
              show ([] : List Bool).length + min q c.length ≤ j
              simp only [List.length_nil]
              omega
            have hxlen' : (runFrom x' [] (c.take q)).length ≤ j := by
              rw [runFrom_length x' (c.take q) [], List.length_take]
              show ([] : List Bool).length + min q c.length ≤ j
              simp only [List.length_nil]
              omega
            rw [List.getD_eq_default _ false hxlen, List.getD_eq_default _ false hxlen']
        | bin op j k =>
          show op ((runFrom x [] (c.take q)).getD j false)
                ((runFrom x [] (c.take q)).getD k false)
              = op ((runFrom x' [] (c.take q)).getD j false)
                ((runFrom x' [] (c.take q)).getD k false)
          have hjv : (runFrom x [] (c.take q)).getD j false
              = (runFrom x' [] (c.take q)).getD j false := by
            by_cases hj : j < q
            · rw [takeRun_getD x c q j hj (le_of_lt hlen),
                takeRun_getD x' c q j hj (le_of_lt hlen)]
              exact ih j hj (cone_child c root q hq j (by
                rw [childrenOf_eq_bin c q op j k hg]
                apply Finset.mem_union_left
                rw [if_pos hj]
                exact Finset.mem_singleton_self j))
            · have hxlen : (runFrom x [] (c.take q)).length ≤ j := by
                rw [runFrom_length x (c.take q) [], List.length_take]
                show ([] : List Bool).length + min q c.length ≤ j
                simp only [List.length_nil]
                omega
              have hxlen' : (runFrom x' [] (c.take q)).length ≤ j := by
                rw [runFrom_length x' (c.take q) [], List.length_take]
                show ([] : List Bool).length + min q c.length ≤ j
                simp only [List.length_nil]
                omega
              rw [List.getD_eq_default _ false hxlen, List.getD_eq_default _ false hxlen']
          have hkv : (runFrom x [] (c.take q)).getD k false
              = (runFrom x' [] (c.take q)).getD k false := by
            by_cases hk : k < q
            · rw [takeRun_getD x c q k hk (le_of_lt hlen),
                takeRun_getD x' c q k hk (le_of_lt hlen)]
              exact ih k hk (cone_child c root q hq k (by
                rw [childrenOf_eq_bin c q op j k hg]
                apply Finset.mem_union_right
                rw [if_pos hk]
                exact Finset.mem_singleton_self k))
            · have hxlen : (runFrom x [] (c.take q)).length ≤ k := by
                rw [runFrom_length x (c.take q) [], List.length_take]
                show ([] : List Bool).length + min q c.length ≤ k
                simp only [List.length_nil]
                omega
              have hxlen' : (runFrom x' [] (c.take q)).length ≤ k := by
                rw [runFrom_length x' (c.take q) [], List.length_take]
                show ([] : List Bool).length + min q c.length ≤ k
                simp only [List.length_nil]
                omega
              rw [List.getD_eq_default _ false hxlen, List.getD_eq_default _ false hxlen']
          rw [hjv, hkv]
      · have hL : (runFrom x [] c).length ≤ q := by
          rw [runFrom_length x c []]
          show ([] : List Bool).length + c.length ≤ q
          simp only [List.length_nil]
          omega
        have hL' : (runFrom x' [] c).length ≤ q := by
          rw [runFrom_length x' c []]
          show ([] : List Bool).length + c.length ≤ q
          simp only [List.length_nil]
          omega
        rw [List.getD_eq_default _ false hL, List.getD_eq_default _ false hL']

/-- **THE EXCESS CHARGE (proved)**: `coneExcess` bounds the number of multi-reader cone wires. -/
theorem coneExcess_ge_multiReader {n : ℕ} (c : List (CGate n)) (root : ℕ) :
    ((coneOf c root).erase root |>.filter
      (fun w => 2 ≤ ((coneOf c root).filter (fun q => w ∈ childrenOf c q)).card)).card
    ≤ coneExcess c root := by
  classical
  set R : Finset ℕ := coneOf c root with hR
  set rd : ℕ → ℕ := fun w => (R.filter (fun q => w ∈ childrenOf c q)).card with hrd
  set M : Finset ℕ := (R.erase root).filter (fun w => 2 ≤ rd w) with hM
  have hstep : M.card ≤ ∑ w ∈ M, (rd w - 1) := by
    have hone : ∑ w ∈ M, (1 : ℕ) = M.card := by
      rw [Finset.sum_const, smul_eq_mul, mul_one]
    rw [← hone]
    apply Finset.sum_le_sum
    intro w hw
    have h2 := (Finset.mem_filter.mp hw).2
    omega
  have hsub : ∑ w ∈ M, (rd w - 1) ≤ ∑ w ∈ R.erase root, (rd w - 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => Nat.zero_le _)
  calc M.card ≤ ∑ w ∈ M, (rd w - 1) := hstep
    _ ≤ ∑ w ∈ R.erase root, (rd w - 1) := hsub
    _ = coneExcess c root := rfl

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.frontier_val_agree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.coneExcess_ge_multiReader
