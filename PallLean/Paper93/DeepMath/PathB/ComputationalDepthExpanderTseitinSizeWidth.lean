import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinRestrictDerivation
import Mathlib.Data.Nat.Log

/-!
# Tree-like BSW size–width recursion (size–width brick 3)

The logarithmic recursion that turns the engines of brick 3a into the tree-like
Ben-Sasson–Wigderson bound

  `proofWidth ≤ w₀ + ⌈log₂ size⌉`  (`tree_width_le`)

for a refutation of any axiom set (`w₀` = max initial clause width).  At the root
resolution on pivot `p` (edge `e = p.1`), the two children restrict to refutations
of the two single-edge restrictions of the formula (`restrict_W`), each of strictly
smaller size; the recursion narrows them and recombines via the **asymmetric**
per-variable bound (`asymmetric`), placing the `+1` on the *smaller* subtree.  The
key arithmetic is `clog_two_succ`: `2·L ≤ n ⇒ ⌈log₂ L⌉ + 1 ≤ ⌈log₂ n⌉`, so the
`+1` on the smaller half is absorbed.

Termination is by strong induction on the size *fuel* `n` (the restricted children
have strictly smaller size), with weakening handled by the structural induction on
the derivation (a weakening leaves `size` unchanged but is structurally smaller).
-/

namespace PallLean.Paper93.DeepMath.PathB.TseitinRestriction

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TseitinResolution

variable {Edge : Type*} [DecidableEq Edge]

/-- `2·L ≤ m` and `L ≥ 1` give `⌈log₂ L⌉ + 1 ≤ ⌈log₂ m⌉` — the arithmetic that lets
the `+1` on the smaller subtree be absorbed into the logarithm. -/
theorem clog_two_succ {L m : ℕ} (hL : 1 ≤ L) (hLm : 2 * L ≤ m) :
    Nat.clog 2 L + 1 ≤ Nat.clog 2 m := by
  have hb : (1 : ℕ) < 2 := one_lt_two
  have hm : m ≤ 2 ^ Nat.clog 2 m := Nat.le_pow_clog hb m
  have hk1 : 1 ≤ Nat.clog 2 m := by
    rcases Nat.eq_zero_or_pos (Nat.clog 2 m) with h0 | h
    · rw [h0] at hm; simp at hm; omega
    · exact h
  have hpow : (2 : ℕ) ^ Nat.clog 2 m = 2 * 2 ^ (Nat.clog 2 m - 1) := by
    conv_lhs => rw [show Nat.clog 2 m = (Nat.clog 2 m - 1) + 1 from by omega]
    rw [pow_succ]; ring
  have hLpow : L ≤ 2 ^ (Nat.clog 2 m - 1) := by
    have : 2 * L ≤ 2 * 2 ^ (Nat.clog 2 m - 1) := by rw [← hpow]; exact le_trans hLm hm
    omega
  have := (Nat.le_pow_iff_clog_le hb).mp hLpow
  omega

/-- **Tree-like BSW size–width (brick 3).**  Stated with a size *fuel* `n` for the
strong induction.  Any refutation of `C = ∅` of size `≤ n` over an axiom set of
width `≤ w₀` has a refutation of width `≤ w₀ + ⌈log₂ n⌉`. -/
theorem treeC (w₀ : ℕ) : ∀ (n : ℕ) {Axiom : ResolutionClause (TLit Edge) → Prop}
    (_ : ∀ C, Axiom C → C.width ≤ w₀) {C : ResolutionClause (TLit Edge)}
    (W : WDerivation tcompl Axiom C), W.size ≤ n → C = ∅ →
    ∃ W' : WDerivation tcompl Axiom ∅, W'.proofWidth ≤ w₀ + Nat.clog 2 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro Axiom hw₀ C W
    induction W with
    | @ax C₀ h =>
        intro _ hC0
        subst hC0
        exact ⟨WDerivation.ax h, by simp [WDerivation.proofWidth_ax, ResolutionClause.width]⟩
    | @resolve CL CR L R p ihL ihR =>
        intro hWn hres
        clear ihL ihR
        simp only [WDerivation.size_resolve] at hWn
        rw [ResolutionClause.resolvent] at hres
        obtain ⟨hCLe, hCRe⟩ := Finset.union_eq_empty.mp hres
        have hCLsub : CL ⊆ {p} := by
          intro l hl
          by_cases hlp : l = p
          · simp [hlp]
          · exact absurd (Finset.mem_erase.mpr ⟨hlp, hl⟩) (by rw [hCLe]; exact Finset.notMem_empty l)
        have hCRsub : CR ⊆ {tcompl p} := by
          intro l hl
          by_cases hlp : l = tcompl p
          · simp [hlp]
          · exact absurd (Finset.mem_erase.mpr ⟨hlp, hl⟩) (by rw [hCRe]; exact Finset.notMem_empty l)
        have hLpos : 1 ≤ L.size := WDerivation.size_pos L
        have hRpos : 1 ≤ R.size := WDerivation.size_pos R
        have hLsize : L.size < n := by omega
        have hRsize : R.size < n := by omega
        have hw₀R : ∀ (v : ZMod 2) C, RestrictAxiom (singleEdge p.1 v) Axiom C → C.width ≤ w₀ := by
          rintro v C ⟨C₀, hax, _, rfl⟩
          exact le_trans (liveClause_width_le _ _) (hw₀ C₀ hax)
        have hLLempty : ∀ v, liveClause (singleEdge p.1 v) CL = ∅ := by
          intro v
          apply Finset.subset_empty.mp
          intro l hl
          obtain ⟨hlCL, hlive⟩ := Finset.mem_filter.mp hl
          have hl1 : l.1 ≠ p.1 := singleEdge_eq_none.mp hlive
          rw [show l = p from Finset.mem_singleton.mp (hCLsub hlCL)] at hl1
          exact (hl1 rfl).elim
        have hRRempty : ∀ v, liveClause (singleEdge p.1 v) CR = ∅ := by
          intro v
          apply Finset.subset_empty.mp
          intro l hl
          obtain ⟨hlCR, hlive⟩ := Finset.mem_filter.mp hl
          have hl1 : l.1 ≠ p.1 := singleEdge_eq_none.mp hlive
          rw [show l = tcompl p from Finset.mem_singleton.mp (hCRsub hlCR)] at hl1
          exact (hl1 rfl).elim
        have hnsL : ∀ v, v ≠ p.2 → ¬ clauseSatisfied (singleEdge p.1 v) CL := by
          rintro v hv ⟨l, hlCL, hl⟩
          rw [show l = p from Finset.mem_singleton.mp (hCLsub hlCL)] at hl
          simp [singleEdge] at hl
          exact hv hl
        have hnsR : ∀ v, v ≠ p.2 + 1 → ¬ clauseSatisfied (singleEdge p.1 v) CR := by
          rintro v hv ⟨l, hlCR, hl⟩
          rw [show l = tcompl p from Finset.mem_singleton.mp (hCRsub hlCR)] at hl
          simp [singleEdge, tcompl] at hl
          exact hv hl
        have hne : p.2 + 1 ≠ p.2 := by
          have := (by decide : ∀ x : ZMod 2, x ≠ x + 1) p.2; intro h; exact this h.symm
        by_cases hLR : L.size ≤ R.size
        · -- L smaller: `+1` on L.  L restricted by `p.2+1`, R by `(p.2+1)+1`.
          obtain ⟨WL0, hWL0s, _⟩ := restrict_W (singleEdge p.1 (p.2 + 1)) L (hnsL _ hne)
          obtain ⟨WL', hWL'w⟩ := IH L.size hLsize (hw₀R _) WL0 hWL0s (hLLempty _)
          obtain ⟨WR0, hWR0s, _⟩ :=
            restrict_W (singleEdge p.1 (p.2 + 1 + 1)) R
              (hnsR _ ((by decide : ∀ x : ZMod 2, x + 1 + 1 ≠ x + 1) p.2))
          obtain ⟨WR', hWR'w⟩ := IH R.size hRsize (hw₀R _) WR0 hWR0s (hRRempty _)
          obtain ⟨W, hWw⟩ := asymmetric p.1 (p.2 + 1) hw₀ WL' WR'
          refine ⟨W, le_trans hWw ?_⟩
          have h1 : WR'.proofWidth ≤ w₀ + Nat.clog 2 n :=
            le_trans hWR'w (Nat.add_le_add_left (Nat.clog_mono_right 2 (le_of_lt hRsize)) w₀)
          have hclog : Nat.clog 2 L.size + 1 ≤ Nat.clog 2 n := clog_two_succ hLpos (by omega)
          have h2 : WL'.proofWidth + 1 ≤ w₀ + Nat.clog 2 n := by omega
          exact max_le (max_le h1 h2) (Nat.le_add_right _ _)
        · -- R smaller: `+1` on R.  R restricted by `p.2`, L by `p.2+1`.
          push_neg at hLR
          obtain ⟨WR0, hWR0s, _⟩ := restrict_W (singleEdge p.1 p.2) R (hnsR _ hne.symm)
          obtain ⟨WR', hWR'w⟩ := IH R.size hRsize (hw₀R _) WR0 hWR0s (hRRempty _)
          obtain ⟨WL0, hWL0s, _⟩ := restrict_W (singleEdge p.1 (p.2 + 1)) L (hnsL _ hne)
          obtain ⟨WL', hWL'w⟩ := IH L.size hLsize (hw₀R _) WL0 hWL0s (hLLempty _)
          obtain ⟨W, hWw⟩ := asymmetric p.1 p.2 hw₀ WR' WL'
          refine ⟨W, le_trans hWw ?_⟩
          have h1 : WL'.proofWidth ≤ w₀ + Nat.clog 2 n :=
            le_trans hWL'w (Nat.add_le_add_left (Nat.clog_mono_right 2 (le_of_lt hLsize)) w₀)
          have hclog : Nat.clog 2 R.size + 1 ≤ Nat.clog 2 n := clog_two_succ hRpos (by omega)
          have h2 : WR'.proofWidth + 1 ≤ w₀ + Nat.clog 2 n := by omega
          exact max_le (max_le h1 h2) (Nat.le_add_right _ _)
    | @weaken CC C' D hsub ihD =>
        intro hWn hC'
        exact ihD hWn (Finset.subset_empty.mp (hC' ▸ hsub))

/-- **Tree-like BSW size–width, headline form.**  Every weakening-resolution
refutation has a refutation of width `≤ w₀ + ⌈log₂ size⌉`. -/
theorem tree_width_le {Axiom : ResolutionClause (TLit Edge) → Prop} {w₀ : ℕ}
    (hw₀ : ∀ C, Axiom C → C.width ≤ w₀) (W : WDerivation tcompl Axiom ∅) :
    ∃ W' : WDerivation tcompl Axiom ∅, W'.proofWidth ≤ w₀ + Nat.clog 2 W.size :=
  treeC w₀ W.size hw₀ W le_rfl rfl

end PallLean.Paper93.DeepMath.PathB.TseitinRestriction

#print axioms PallLean.Paper93.DeepMath.PathB.TseitinRestriction.tree_width_le
