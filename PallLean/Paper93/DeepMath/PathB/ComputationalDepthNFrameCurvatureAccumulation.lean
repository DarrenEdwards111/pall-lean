import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDynamicSPDPBridge

/-!
# N-Frame: curvature accumulation I — the row-capacity engine for shared interfaces

The first rung of Track C.  The `+1` came from refuting **zero**-interface splits
(`f = op (g|_S, h|_T)`, nothing shared).  Accumulation must refute splits whose two sides share a
`k`-coordinate interface, and charge `k` against the curvature.  This file proves the capacity core:

  `shared_split_row_capacity` — **PROVED, the engine**: if `f = op (g, h)` with `g` reading only `A`
        and `h` only `B`, then any family of contexts with **pairwise-distinct rows** (restrictions to
        `A \ B`) has size at most `2^(|A ∩ B| + 1)`.  Rows are determined by the interface trace
        `(y|_{A∩B}, h y)` — a pigeonhole over `2^k · 2` values.  Contrapositive: **many distinct rows
        force a large shared interface.**

SAT has `2^(m−2)` distinct block-restrictions (`sat3_block_subfunction_count`), so a top split whose
`A \ B`-side captures a designated block forces an interface of size `≥ m − 3` — exponentially many
rows cannot flow through a small interface.

## Honest scope — the accumulation plan, named

Turning this into `coneExcess ≥ Ω(m)` needs two further rungs, neither claimed here:
(1) **cut factorization** — a wire's value is determined by its own-side variables plus the values on
the exit wires of the shared cone region (a relative `cone_val_agree`), and every exit wire has two
distinct cone readers, so `coneExcess ≥ #exit wires`; (2) **per-partition row counts** — for the
*circuit's own* top cut, one side must carry `2^Ω(m)` distinct restrictions (the pin-toggle family
generalized to adversarial partitions).  With both, the chain reads: many rows ⇒ large interface ⇒
many exit wires ⇒ `coneExcess ≥ Ω(m)` ⇒ `cbudget ≥ 2N + Ω(m)`.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE ROW-CAPACITY ENGINE (proved)**: pairwise-distinct rows are bounded by `2^(interface + 1)` —
every row is determined by its interface trace. -/
theorem shared_split_row_capacity {n : ℕ} (f : (Fin n → Bool) → Bool)
    (A B : Finset (Fin n)) (op : Bool → Bool → Bool) (g h : (Fin n → Bool) → Bool)
    (hg : ∀ x y : Fin n → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin n → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, f x = op (g x) (h x))
    (Y : Finset (Fin n → Bool))
    (hdist : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' →
      ∃ x, f (mixOn (A \ B) x y) ≠ f (mixOn (A \ B) x y')) :
    Y.card ≤ 2 ^ ((A ∩ B).card + 1) := by
  classical
  by_contra hbig
  push_neg at hbig
  -- the interface trace
  set φ : (Fin n → Bool) → ((↥(A ∩ B) → Bool) × Bool) :=
    fun y => (fun w => y w.val, h y) with hφ
  have hcard : (Finset.univ : Finset ((↥(A ∩ B) → Bool) × Bool)).card
      < Y.card := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_coe,
      Fintype.card_bool]
    have h2 : (2 : ℕ) ^ (A ∩ B).card * 2 = 2 ^ ((A ∩ B).card + 1) := by
      rw [pow_succ]
    omega
  obtain ⟨y, hy, y', hy', hne, hcol⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (fun y _ => Finset.mem_univ (φ y))
  -- equal traces force equal rows
  have hWeq : ∀ i, i ∈ A ∩ B → y i = y' i := by
    intro i hi
    have := congrFun (congrArg Prod.fst hcol) ⟨i, hi⟩
    exact this
  have hHeq : h y = h y' := congrArg Prod.snd hcol
  have hrows : ∀ x, f (mixOn (A \ B) x y) = f (mixOn (A \ B) x y') := by
    intro x
    rw [hf, hf]
    congr 1
    · -- the g-side: agree on all of A
      apply hg
      intro i hi
      show (if i ∈ A \ B then x i else y i) = (if i ∈ A \ B then x i else y' i)
      by_cases hiS : i ∈ A \ B
      · rw [if_pos hiS, if_pos hiS]
      · rw [if_neg hiS, if_neg hiS]
        have hiW : i ∈ A ∩ B := by
          rw [Finset.mem_inter]
          rw [Finset.mem_sdiff] at hiS
          refine ⟨hi, ?_⟩
          by_contra hiB
          exact hiS ⟨hi, hiB⟩
        exact hWeq i hiW
    · -- the h-side: both mixes agree with the underlying context on B
      have h1 : h (mixOn (A \ B) x y) = h y := by
        apply hh
        intro i hi
        show (if i ∈ A \ B then x i else y i) = y i
        rw [if_neg (fun hiS => (Finset.mem_sdiff.mp hiS).2 hi)]
      have h2 : h (mixOn (A \ B) x y') = h y' := by
        apply hh
        intro i hi
        show (if i ∈ A \ B then x i else y' i) = y' i
        rw [if_neg (fun hiS => (Finset.mem_sdiff.mp hiS).2 hi)]
      rw [h1, h2, hHeq]
  obtain ⟨x, hx⟩ := hdist y hy y' hy' hne
  exact hx (hrows x)

/-- **THE CONTRAPOSITIVE, dictionary form (proved)**: a context family with pairwise-distinct rows
forces the shared interface to be at least logarithmically large. -/
theorem rows_force_interface {n : ℕ} (f : (Fin n → Bool) → Bool)
    (A B : Finset (Fin n)) (op : Bool → Bool → Bool) (g h : (Fin n → Bool) → Bool)
    (hg : ∀ x y : Fin n → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin n → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, f x = op (g x) (h x))
    (Y : Finset (Fin n → Bool))
    (hdist : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' →
      ∃ x, f (mixOn (A \ B) x y) ≠ f (mixOn (A \ B) x y'))
    (k : ℕ) (hY : 2 ^ (k + 1) < Y.card) :
    k < (A ∩ B).card := by
  by_contra hcon
  push_neg at hcon
  have h1 := shared_split_row_capacity f A B op g h hg hh hf Y hdist
  have h2 : (2 : ℕ) ^ ((A ∩ B).card + 1) ≤ 2 ^ (k + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.shared_split_row_capacity
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.rows_force_interface
