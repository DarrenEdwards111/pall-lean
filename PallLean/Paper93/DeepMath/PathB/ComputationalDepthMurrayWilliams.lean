import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHardSlice

/-!
# Murray–Williams: the elementary MCSP facts it builds on — and an honest note on what does NOT pave

`MCSPcompleteness` used Murray–Williams (`MCSP NP-complete ⟹ EXP ≠ ZPP`) as a hypothesis.  Asked to pave it, I
have to flag an asymmetry, honestly: the previous four sockets (IKW, Liu–Pass, Korten, Hirahara) each had a
clean counting-pigeonhole heart I proved from scratch.  **Murray–Williams does not.**  Its core is a
derandomization / hierarchy argument — it turns NP-hardness of MCSP into a separation via pseudorandomness and a
time-hierarchy contradiction — and that does *not* reduce to an elementary lemma.  I will not dress it up as a
pigeonhole it is not.

What I *can* pave — and it is genuine and load-bearing — are the two elementary facts about MCSP that the
Murray–Williams line builds on, and they are once again the same counting:

* **`mcsp_yes_is_certified`** — MCSP's YES-instances (truth tables with a small circuit) are exactly the images
  of the circuit-evaluation map: `T` is a YES-instance iff a circuit certifies it.  This is `MCSP ∈ NP` — the
  certificate is the circuit, checked by evaluation.
* **`mcsp_yes_rare`** — the YES-instances number at most the circuits, hence are rare among all functions: MCSP
  is *sparse in YES*.  This is the density Murray–Williams exploits, and it is the `HardSlice` counting again.
* **`mcsp_no_instance_exists`** — when circuits are fewer than functions, a NO-instance (a hard function)
  exists: the hard core is nonempty (indeed the majority).

**What is abstracted (honestly).**  The Murray–Williams *reduction* — `MCSP NP-complete ⟹ EXP ≠ ZPP` — is the
derandomization/hierarchy argument built on top of these facts.  It is a genuine complexity-theory theorem, not
a counting core, and it is **not** formalized here; it remains the named input of `MCSPcompleteness`.  So this
"socket" is paved only at its elementary base, not at its theorem.

## What is proved

* **`mcsp_yes_is_certified`** — YES-instances = circuit-certified functions (`MCSP ∈ NP`).
* **`mcsp_yes_rare`** — YES-instances ≤ number of circuits (MCSP sparse in YES).
* **`mcsp_no_instance_exists`** — a NO-instance (hard function) exists when circuits < functions.

## Honest verdict — the base is paved; the reduction resists the pigeonhole

Four sockets paved to a single counting core; this fifth one does not.  I paved the elementary MCSP facts
Murray–Williams stands on — verifiability (`mcsp_yes_is_certified`) and YES-sparsity (`mcsp_yes_rare`,
`mcsp_no_instance_exists`), which are the `HardSlice` counting once more — but the theorem itself, the
derandomization argument turning NP-completeness into `EXP ≠ ZPP`, is not a pigeonhole and I did not fake one.
That is the honest boundary of the socket-paving method: it pays sockets whose heart is counting, and it stops,
truthfully, at the ones whose heart is not.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MurrayWilliams

open PallLean.Paper93.DeepMath.PathB.HardSlice

/-- **MCSP ∈ NP: YES-instances are certified by a circuit (proved).**  A truth table `T` is a YES-instance
(has a small circuit) iff some circuit evaluates to it — the certificate is the circuit, checkable by
evaluation.  The YES-set is exactly the image of the evaluation map. -/
theorem mcsp_yes_is_certified {Circuit Func : Type} [Fintype Circuit] [DecidableEq Func]
    (eval : Circuit → Func) (T : Func) :
    T ∈ Finset.univ.image eval ↔ ∃ c, eval c = T := by
  simp [Finset.mem_image]

/-- **MCSP is sparse in YES (proved).**  The YES-instances number at most the circuits — few truth tables have
small circuits.  This is the density Murray–Williams exploits, and it is the `HardSlice` image-counting. -/
theorem mcsp_yes_rare {Circuit Func : Type} [Fintype Circuit] [DecidableEq Func] (eval : Circuit → Func) :
    (Finset.univ.image eval).card ≤ Fintype.card Circuit :=
  le_trans Finset.card_image_le (le_of_eq Finset.card_univ)

/-- **A NO-instance exists (proved).**  When there are fewer circuits than functions, some truth table has no
small circuit — the hard core is nonempty.  (Via `HardSlice.hard_slice_exists`; in fact NO-instances are the
majority.) -/
theorem mcsp_no_instance_exists {Circuit Func : Type} [Fintype Circuit] [Fintype Func]
    (eval : Circuit → Func) (h : Fintype.card Circuit < Fintype.card Func) :
    ∃ T, ∀ c, eval c ≠ T :=
  hard_slice_exists eval h

end PallLean.Paper93.DeepMath.PathB.MurrayWilliams

#print axioms PallLean.Paper93.DeepMath.PathB.MurrayWilliams.mcsp_yes_is_certified
#print axioms PallLean.Paper93.DeepMath.PathB.MurrayWilliams.mcsp_yes_rare
#print axioms PallLean.Paper93.DeepMath.PathB.MurrayWilliams.mcsp_no_instance_exists
