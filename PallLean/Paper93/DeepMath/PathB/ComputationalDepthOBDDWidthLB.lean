import PallLean.Paper93.DeepMath.PathB.ComputationalDepthOneWayCommLB
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDIndexMachine

/-!
# Branching-program (OBDD) width lower bound for doubled INDEX

A second concrete model where the doubled-INDEX language is hard while lying in `P`: an ordered
binary decision diagram (oblivious, layered read-once branching program reading its input
left-to-right) computing `dIndexLang` needs **width `≥ 2^m`**.

The state reached after reading a prefix determines the rest of the computation — hence the
subfunction at that cut — so the number of states is at least the subfunction count
(`obdd_subfun_le`).  With `dIndexLang`'s `≥ 2^m` subfunctions at the middle cut
(`LangRankKill`), any OBDD for it has `≥ 2^m` states.  Combined with `dIndexInP`, this is a
second unconditional `P`-vs-restricted separation: polynomial time does not imply
sub-exponential OBDD width (i.e. sublinear branching-program space).

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.OBDDWidthLB

open PallLean.Paper93.DeepMath.PathB.ComposableMachine (InP)
open PallLean.Paper93.DeepMath.PathB.LangRankKill (dIndexLang)
open PallLean.Paper93.DeepMath.PathB.OneWayCommLB (subfuns subfuns_dIndexComm dIndexComm)
open PallLean.Paper93.DeepMath.PathB.DIndexMachine (dIndexInP)

/-- An ordered binary decision diagram over state type `Q`: a start state, a per-position
transition (read the bit at position `i`), and an output map.  Reads the input left-to-right. -/
structure OBDD (Q : Type) where
  /-- The start state. -/
  start : Q
  /-- Transition at position `i`: current state and read bit ↦ next state. -/
  step : ℕ → Q → Bool → Q
  /-- The output at the final state. -/
  out : Q → Bool

/-- The state reached from `q` at position `i` after reading the list. -/
def OBDD.trajFrom {Q : Type} (bp : OBDD Q) : ℕ → Q → List Bool → Q
  | _, q, [] => q
  | i, q, b :: bs => bp.trajFrom (i + 1) (bp.step i q b) bs

/-- The output of the OBDD on an input. -/
def OBDD.run {Q : Type} (bp : OBDD Q) (w : List Bool) : Bool :=
  bp.out (bp.trajFrom 0 bp.start w)

/-- The OBDD computes `f` if its output matches on every input. -/
def OBDD.Computes {Q : Type} (bp : OBDD Q) (f : List Bool → Bool) : Prop :=
  ∀ w, bp.run w = f w

/-- Reading a concatenation continues from the prefix's state (with the position advanced). -/
theorem OBDD.trajFrom_append {Q : Type} (bp : OBDD Q) (p : List Bool) :
    ∀ (i : ℕ) (q : Q) (s : List Bool),
      bp.trajFrom i q (p ++ s) = bp.trajFrom (i + p.length) (bp.trajFrom i q p) s := by
  induction p with
  | nil => intro i q s; simp [OBDD.trajFrom]
  | cons b p ih =>
    intro i q s
    show bp.trajFrom (i + 1) (bp.step i q b) (p ++ s)
      = bp.trajFrom (i + (p.length + 1)) (bp.trajFrom (i + 1) (bp.step i q b) p) s
    rw [ih (i + 1), show i + 1 + p.length = i + (p.length + 1) from by omega]

/-- **The width lower bound.**  An OBDD computing `f` has at least as many states as `f` has
distinct subfunctions at any cut `c`: each subfunction is determined by the state reached after
the prefix, so the states surject onto the subfunctions. -/
theorem obdd_subfun_le {Q : Type} [Fintype Q] (bp : OBDD Q) (f : List Bool → Bool)
    (hf : bp.Computes f) (c e : ℕ) :
    (subfuns fun u : Fin c → Bool => fun v : Fin e → Bool =>
        f (List.ofFn u ++ List.ofFn v)).card ≤ Fintype.card Q := by
  have hsub : (subfuns fun u : Fin c → Bool => fun v : Fin e → Bool =>
      f (List.ofFn u ++ List.ofFn v))
      ⊆ Finset.univ.image fun q : Q => fun v : Fin e → Bool =>
          bp.out (bp.trajFrom c q (List.ofFn v)) := by
    intro g hg
    simp only [subfuns, Finset.mem_image, Finset.mem_univ, true_and] at hg ⊢
    obtain ⟨u, rfl⟩ := hg
    refine ⟨bp.trajFrom 0 bp.start (List.ofFn u), ?_⟩
    funext v
    have hrun : f (List.ofFn u ++ List.ofFn v)
        = bp.out (bp.trajFrom 0 bp.start (List.ofFn u ++ List.ofFn v)) :=
      (hf (List.ofFn u ++ List.ofFn v)).symm
    rw [hrun, bp.trajFrom_append (List.ofFn u) 0 bp.start (List.ofFn v)]
    simp only [Nat.zero_add, List.length_ofFn]
  calc (subfuns fun u : Fin c → Bool => fun v : Fin e → Bool =>
          f (List.ofFn u ++ List.ofFn v)).card
      ≤ (Finset.univ.image fun q : Q => fun v : Fin e → Bool =>
          bp.out (bp.trajFrom c q (List.ofFn v))).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset Q).card := Finset.card_image_le
    _ = Fintype.card Q := by rw [Finset.card_univ]

/-- **Doubled INDEX needs OBDD width `≥ 2^m`.**  Any OBDD computing `dIndexLang` has at least
`2^m` states, from its `≥ 2^m` subfunctions at the middle cut. -/
theorem dIndex_obdd_width_ge {Q : Type} [Fintype Q] (bp : OBDD Q)
    (hf : bp.Computes dIndexLang) (m : ℕ) : 2 ^ m ≤ Fintype.card Q := by
  have hle := obdd_subfun_le bp dIndexLang hf (3 * m + 3) (3 * m + 3)
  have hcard : (subfuns (dIndexComm m)).card ≤ Fintype.card Q := hle
  rw [subfuns_dIndexComm] at hcard
  exact le_trans (LangRankKill.two_pow_le_subfunCountAt_dIndex m) hcard

/-- **P ⊄ sub-exponential OBDD width (unconditional).**  `dIndexLang` is decided in polynomial
time, yet any OBDD (ordered branching program) computing it has width `≥ 2^m` on length-`(6m+6)`
inputs — exponential in the block size, i.e. linear branching-program space.  Polynomial time
does not imply sublinear branching-program width. -/
theorem dIndex_P_but_exp_obdd :
    InP dIndexLang
      ∧ ∀ (Q : Type) [Fintype Q] (bp : OBDD Q), bp.Computes dIndexLang → ∀ m, 2 ^ m ≤ Fintype.card Q :=
  ⟨dIndexInP, fun Q _ bp hf m => @dIndex_obdd_width_ge Q _ bp hf m⟩

end PallLean.Paper93.DeepMath.PathB.OBDDWidthLB
