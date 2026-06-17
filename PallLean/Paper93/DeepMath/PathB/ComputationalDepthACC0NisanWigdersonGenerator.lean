import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0IKWNisanWigderson

/-!
# The Nisan–Wigderson generator — combinatorial design (proved) + the hybrid argument (socketed)

Entry 189 exposed the NW derandomisation as the socket `NWDerandomization : HardFunction → Derandomization`.  The NW
generator has two classical components: a **combinatorial design** (a family of sets with bounded pairwise
intersections) and the **hybrid argument** (the design + a hard function give a generator that fools `ACC⁰`).  This file
decomposes the NW socket into those two, proves the decomposition glue, and *actually proves* a genuine combinatorial
design — the disjoint (zero-intersection) base case.

## What is proved (clean axioms, no `sorry`)

* **`disjoint_design`** — a genuine NW design (the disjoint base case): for any `m, k`, there are `m` sets each of size
  `k` that are pairwise disjoint (the blocks `[i·k, i·k+k)`).  A real combinatorial design (intersection `0`); the
  efficient low-intersection NW designs are the quantitative refinement.
* **`NWGeneratorFromDesign`** — the hybrid-argument socket: a design + a hard function yield the derandomisation.
* **`nwDerandomization_from_design`** — the decomposition glue: a design + the hybrid argument ⇒ `NWDerandomization`.

## Honest scope

This decomposes the NW socket of entry 189 into a **combinatorial design** (proved here for the disjoint base case) and
the **hybrid argument** (the generator-fools-`ACC⁰` analysis, a named socket), with the glue proved.  The disjoint design
is a real construction but the *inefficient* one (seed length `m·k`); the genuine NW generator needs the *low-intersection*
designs (seed length `O(k²/log m)`) and the hybrid argument that a circuit distinguishing the generator yields a small
circuit for the hard function — both classical results (Nisan–Wigderson 1994) requiring circuit-complexity infrastructure
absent here, left as the named socket.  This does **not** prove the NW generator; it builds the combinatorial base case
and the decomposition.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonGenerator

open PallLean.Paper93.DeepMath.PathB.ACC0IKWNisanWigderson (NWDerandomization)

/-- **A genuine combinatorial NW design (proved): the disjoint base case.**  For any `m, k`, the `m` blocks
`S i = [i·k, i·k+k)` each have size `k` and are pairwise disjoint — a Nisan–Wigderson design with pairwise intersection
`0`.  (The efficient NW designs trade disjointness for a shorter seed via bounded — not zero — intersections; this is
the base case.) -/
theorem disjoint_design (m k : ℕ) :
    ∃ S : Fin m → Finset ℕ, (∀ i, (S i).card = k) ∧ (∀ i j, i ≠ j → Disjoint (S i) (S j)) := by
  refine ⟨fun i => Finset.Ico (i.val * k) (i.val * k + k), fun i => ?_, fun i j hij => ?_⟩
  · rw [Nat.card_Ico]; omega
  · rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Ico] at hx hx'
    have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases Nat.lt_or_ge i.val j.val with h | h
    · have hb : i.val * k + k ≤ j.val * k := by
        calc i.val * k + k = (i.val + 1) * k := by ring
          _ ≤ j.val * k := Nat.mul_le_mul_right k (by omega)
      omega
    · have hb : j.val * k + k ≤ i.val * k := by
        calc j.val * k + k = (j.val + 1) * k := by ring
          _ ≤ i.val * k := Nat.mul_le_mul_right k (by omega)
      omega

/-- **The NW hybrid-argument socket.**  A combinatorial design together with a hard function yields the derandomisation
— the generator `G(y) = (f(y|_{S₁}), …, f(y|_{Sₘ}))` fools `ACC⁰`, since a distinguishing circuit would give a small
circuit for `f` (the NW hybrid argument).  Stated, not proved. -/
def NWGeneratorFromDesign (Design HardFunction Derandomization : Prop) : Prop :=
  Design → HardFunction → Derandomization

/-- **The NW decomposition glue (proved): design + hybrid ⇒ `NWDerandomization`.**  Given a combinatorial design and the
hybrid argument, a hard function yields the derandomisation — composing the entry-189 NW socket out of the design and the
hybrid analysis. -/
theorem nwDerandomization_from_design (Design HardFunction Derandomization : Prop)
    (hd : Design) (hyb : NWGeneratorFromDesign Design HardFunction Derandomization) :
    NWDerandomization HardFunction Derandomization :=
  fun hf => hyb hd hf

end PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonGenerator

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonGenerator.disjoint_design
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonGenerator.nwDerandomization_from_design
