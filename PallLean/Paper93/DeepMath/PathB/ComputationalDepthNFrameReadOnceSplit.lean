import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSlotConnectivity

/-!
# N-Frame: the read-once split — excess zero forces a bipartite top decomposition

The structural half of the read-once impossibility, complete.  A circuit with `coneExcess = 0` is
read-once-shaped: no wire has two readers, so the root's two sub-cones cannot share a single gate — and the
function computed splits at the top over two *disjoint* wire cones.

  `cone_trans` — cones are transitive: a cone member's cone is contained in the ambient cone.
  `excess_zero_cones_disjoint` — **PROVED, the engine**: at excess zero, distinct children of the root have
        disjoint cones.  (Maximal shared gate: its two upward parents are distinct cone readers — either
        two parents on the two sides, or one side degenerates to the child itself and the root joins as
        second reader — and a wire with two cone readers contributes `1` to `coneExcess`.)
  `excess_zero_top_split` — **PROVED, the split**: excess zero + binary root ⇒
        `f x = op (wireL x) (wireR x)` with `coneOf L` and `coneOf R` disjoint.  By `cone_val_agree` and
        read-uniqueness each side sees a *disjoint* set of variables: `f` is a two-decomposable function
        of a bipartition of its inputs.

## Honest scope — the remaining halves of the read-once kill

To conclude `coneExcess ≥ 1` for minimal SAT circuits (hence `cbudget ≥ 2mD` via `sat3_excess_priced`),
two named rungs remain.  (1) *Root-shape reduction* (mechanical): var/cst roots die by the dictator and
constancy flips; `un` roots and degenerate `bin op L L` roots force `L = length − 2` by Normal Form IV and
die by prefix-truncation or last-gate-negation surgery — each a shorter circuit, contradicting minimality.
(2) *No bipartite split* (the semantic wall): SAT must refute `f = op (g|_S, h|_T)` for **every** nontrivial
bipartition.  The certificate shape is a clash pair — one pair of coordinates showing an XOR-type 2×2
pattern in one context and an AND-type pattern in another, which no fixed `op` can serve across a cut.  The
pair (designated sign bit, pin-block sign bit) already gives the XOR side from `sat3Context_probe_eval`
(updating the pin sign *is* updating `bvec`); the AND side needs a two-literal workhorse eval; and covering
every cut needs a spanning connected clash graph — that is the honest wall.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Cone transitivity -/

theorem cone_trans {n : ℕ} (c : List (CGate n)) (root s : ℕ) (hs : s ∈ coneOf c root)
    (q : ℕ) (hq : q ∈ coneOf c s) : q ∈ coneOf c root := by
  have main : ∀ d q, q ∈ coneOf c s → s - q = d → q ∈ coneOf c root := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro q hq hd
      rcases cone_parent c s q hq with heq | ⟨r, hr, hchild⟩
      · rw [heq]
        exact hs
      · have hrs : r ≤ s := cone_le c s r hr
        have hqr : q < r := children_lt c r q hchild
        have hrcone : r ∈ coneOf c root := ih (s - r) (by omega) r hr rfl
        exact cone_child c root r hrcone q hchild
  exact main (s - q) q hq rfl

/-! ### The disjointness engine -/

/-- **THE ENGINE (proved)**: at excess zero, distinct children of the root have disjoint cones — a shared
gate would hand some wire two distinct cone readers, and every extra reader is priced by `coneExcess`. -/
theorem excess_zero_cones_disjoint {n : ℕ} (c : List (CGate n)) (root L R : ℕ)
    (hex : coneExcess c root = 0)
    (hL : L ∈ childrenOf c root) (hR : R ∈ childrenOf c root) (hLR : L ≠ R) :
    Disjoint (coneOf c L) (coneOf c R) := by
  classical
  rw [Finset.disjoint_left]
  intro w₀ hwL₀ hwR₀
  exfalso
  set I : Finset ℕ := coneOf c L ∩ coneOf c R with hI
  have hIne : I.Nonempty := ⟨w₀, Finset.mem_inter.mpr ⟨hwL₀, hwR₀⟩⟩
  have hwmem := I.max'_mem hIne
  have hwL : I.max' hIne ∈ coneOf c L := (Finset.mem_inter.mp hwmem).1
  have hwR : I.max' hIne ∈ coneOf c R := (Finset.mem_inter.mp hwmem).2
  have hLroot : L ∈ coneOf c root := cone_child c root root (cone_self c root) L hL
  have hRroot : R ∈ coneOf c root := cone_child c root root (cone_self c root) R hR
  have hLlt : L < root := children_lt c root L hL
  have hRlt : R < root := children_lt c root R hR
  -- a wire with two distinct cone readers contradicts excess zero
  have hkill : ∀ u r₁ r₂, u ∈ coneOf c root → u ≠ root →
      r₁ ∈ coneOf c root → r₂ ∈ coneOf c root → r₁ ≠ r₂ →
      u ∈ childrenOf c r₁ → u ∈ childrenOf c r₂ → False := by
    intro u r₁ r₂ huc hune hr₁ hr₂ hne h₁ h₂
    have hsub : ({r₁, r₂} : Finset ℕ)
        ⊆ (coneOf c root).filter (fun q => u ∈ childrenOf c q) := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · exact Finset.mem_filter.mpr ⟨hr₁, h₁⟩
      · rw [Finset.mem_singleton] at hz'
        subst hz'
        exact Finset.mem_filter.mpr ⟨hr₂, h₂⟩
    have hc2 : ({r₁, r₂} : Finset ℕ).card = 2 := Finset.card_pair hne
    have h2le := Finset.card_le_card hsub
    have hle : ((coneOf c root).filter (fun q => u ∈ childrenOf c q)).card - 1
        ≤ coneExcess c root := by
      unfold coneExcess
      exact Finset.single_le_sum
        (f := fun w' => ((coneOf c root).filter (fun q => w' ∈ childrenOf c q)).card - 1)
        (fun w' _ => Nat.zero_le _)
        (Finset.mem_erase.mpr ⟨hune, huc⟩)
    omega
  rcases cone_parent c L (I.max' hIne) hwL with heqL | ⟨r₁, hr₁, hch₁⟩
  · rcases cone_parent c R (I.max' hIne) hwR with heqR | ⟨r₂, hr₂, hch₂⟩
    · exact hLR (heqL.symm.trans heqR)
    · -- the shared gate IS L: readers are the root and a gate inside cone R
      have hr₂le : r₂ ≤ R := cone_le c R r₂ hr₂
      exact hkill (I.max' hIne) root r₂
        (cone_trans c root L hLroot _ hwL)
        (by rw [heqL]; omega)
        (cone_self c root)
        (cone_trans c root R hRroot r₂ hr₂)
        (by omega)
        (by rw [heqL]; exact hL)
        hch₂
  · rcases cone_parent c R (I.max' hIne) hwR with heqR | ⟨r₂, hr₂, hch₂⟩
    · -- the shared gate IS R: symmetric
      have hr₁le : r₁ ≤ L := cone_le c L r₁ hr₁
      exact hkill (I.max' hIne) root r₁
        (cone_trans c root R hRroot _ hwR)
        (by rw [heqR]; omega)
        (cone_self c root)
        (cone_trans c root L hLroot r₁ hr₁)
        (by omega)
        (by rw [heqR]; exact hR)
        hch₁
    · -- interior shared gate: parents on both sides; equal parents contradict maximality
      by_cases hpar : r₁ = r₂
      · subst hpar
        have hr₁I : r₁ ∈ I := Finset.mem_inter.mpr ⟨hr₁, hr₂⟩
        have hlt : I.max' hIne < r₁ := children_lt c r₁ _ hch₁
        have hle := Finset.le_max' I r₁ hr₁I
        omega
      · exact hkill (I.max' hIne) r₁ r₂
          (cone_trans c root L hLroot _ hwL)
          (by
            have := cone_le c L (I.max' hIne) hwL
            omega)
          (cone_trans c root L hLroot r₁ hr₁)
          (cone_trans c root R hRroot r₂ hr₂)
          hpar hch₁ hch₂

/-! ### The top split -/

/-- **THE SPLIT (proved)**: excess zero + binary root ⇒ `f = op (wireL) (wireR)` over disjoint cones — the
computed function is two-decomposable over a bipartition of its wire supports. -/
theorem excess_zero_top_split {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hex : coneExcess c (c.length - 1) = 0)
    (op : Bool → Bool → Bool) (L R : ℕ)
    (hroot : c.getD (c.length - 1) (CGate.cst false) = CGate.bin op L R)
    (hLlt : L < c.length - 1) (hRlt : R < c.length - 1) (hLR : L ≠ R) :
    Disjoint (coneOf c L) (coneOf c R) ∧
    ∀ x : Fin n → Bool,
      f x = op ((runFrom x [] c).getD L false) ((runFrom x [] c).getD R false) := by
  have hLch : L ∈ childrenOf c (c.length - 1) := by
    rw [childrenOf_eq_bin c (c.length - 1) op L R hroot]
    exact Finset.mem_union_left _
      (by rw [if_pos hLlt]; exact Finset.mem_singleton_self L)
  have hRch : R ∈ childrenOf c (c.length - 1) := by
    rw [childrenOf_eq_bin c (c.length - 1) op L R hroot]
    exact Finset.mem_union_right _
      (by rw [if_pos hRlt]; exact Finset.mem_singleton_self R)
  refine ⟨excess_zero_cones_disjoint c (c.length - 1) L R hex hLch hRch hLR, ?_⟩
  intro x
  have h : (runFrom x [] c).getD (c.length - 1) false = f x := hcomp x
  rw [← h, output_getD_at x c (c.length - 1) (by omega), hroot]
  show op ((runFrom x [] (c.take (c.length - 1))).getD L false)
      ((runFrom x [] (c.take (c.length - 1))).getD R false)
    = op ((runFrom x [] c).getD L false) ((runFrom x [] c).getD R false)
  have hpre : ∀ q, q < c.length - 1 →
      (runFrom x [] (c.take (c.length - 1))).getD q false
        = (runFrom x [] c).getD q false := by
    intro q hq
    have hVlen : (runFrom x [] (c.take (c.length - 1))).length = c.length - 1 := by
      rw [runFrom_length]
      simp only [List.length_nil, List.length_take]
      omega
    have hfull : runFrom x [] c
        = runFrom x (runFrom x [] (c.take (c.length - 1))) (c.drop (c.length - 1)) := by
      conv_lhs => rw [← List.take_append_drop (c.length - 1) c]
      rw [runFrom_append]
    rw [hfull, runFrom_getD_stable x (c.drop (c.length - 1))
      (runFrom x [] (c.take (c.length - 1))) q (by rw [hVlen]; omega)]
  rw [hpre L hLlt, hpre R hRlt]

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cone_trans
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.excess_zero_cones_disjoint
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.excess_zero_top_split
