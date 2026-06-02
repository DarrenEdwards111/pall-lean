import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingEncPath

/-!
# The encoder label and direct injectivity

**STATUS: REAL.  THE ENCODER LABEL CLOSES INJECTIVITY (ρ = σ) DIRECTLY.**

The encoder canonical path `encLits ρ cs` (decode side fully discharged by `encLits_decode`)
is labelled by the *flat per-term index sequence*: for each `σ*`-confirmed term, the positions
of its path literals (`blockOf`), flattened with `ungroupBlocks`.  Combining

* `encLits_decode` — the completion decodes back to `ρ`;
* `termWalkLab_blockOf_eq` — the index-block walk equals the proved `termBlock` walk;
* `termWalkLab_flat_det` — equal completions + equal flat labels ⇒ same recovered set,

gives **injectivity directly**: equal completions and equal flat labels force `ρ = σ`.  This
is stronger than the abstract `hlabdet` (it is the `hrec` field of the count scaffold), so it
plugs straight into `card_bad_le_finset_label`.

The one explicit hypothesis is that the confirmed terms have **nonempty** index-blocks
(`hblk`) — needed because `ungroupBlocks` is injective only on nonempty blocks (an empty block
leaves no boundary marker).  An empty block arises only from a term that is `σ*`-satisfied yet
contributes no path variable; we surface this as a hypothesis rather than hide it.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The encoder's per-term index-blocks: positions of each `σ*`-confirmed term's path
literals. -/
def encBlocks (ρ : Restriction n) (cs : List (Clause n)) : List (List ℕ) :=
  (cs.filter (termSat (complete ρ (encLits ρ cs)))).map (blockOf (encLits ρ cs))

/-- The encoder's flat label: the index-blocks flattened to a single `(index, isLast)`
sequence. -/
def encFlatLabel (ρ : Restriction n) (cs : List (Clause n)) : List (ℕ × Bool) :=
  ungroupBlocks (encBlocks ρ cs)

/-- The full-fuel `termBlock` walk equals the index-block label walk. -/
theorem encWalk_eq_lab (τ : Restriction n) (lit : List (Rung4Literal n)) (cs : List (Clause n)) :
    termWalkVars τ (termBlock lit) cs cs.length
      = termWalkLab τ cs ((cs.filter (termSat τ)).map (blockOf lit)) := by
  have e1 := termWalk_eq_filter_full τ (termBlock lit) cs cs.length (List.length_filter_le _ _)
  have e2 := termWalk_eq_filter_full τ (termBlock lit) cs ((cs.filter (termSat τ)).length)
    (le_refl _)
  rw [termWalkLab_blockOf_eq, e1, e2]

/-- **Encoder injectivity (the `hrec` field).**  Two restrictions with equal encoder
completions and equal encoder flat labels are equal.  No assumption beyond per-term
distinct-variable literals and nonempty confirmed index-blocks. -/
theorem encLits_label_inj (ρ σ : Restriction n) (cs : List (Clause n))
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hblkρ : ∀ b ∈ encBlocks ρ cs, b ≠ [])
    (hblkσ : ∀ b ∈ encBlocks σ cs, b ≠ [])
    (hcomplete : complete ρ (encLits ρ cs) = complete σ (encLits σ cs))
    (hlabel : encFlatLabel ρ cs = encFlatLabel σ cs) :
    ρ = σ := by
  have hRρ := encLits_decode ρ cs hcs
  have hRσ := encLits_decode σ cs hcs
  rw [encWalk_eq_lab] at hRρ hRσ
  have hdet : termWalkLab (complete ρ (encLits ρ cs)) cs (encBlocks ρ cs)
      = termWalkLab (complete σ (encLits σ cs)) cs (encBlocks σ cs) :=
    termWalkLab_flat_det hblkρ hblkσ hcomplete hlabel
  -- `hRρ`/`hRσ` are over `encBlocks _ _` definitionally; rewrite via the chain
  rw [show ((cs.filter (termSat (complete ρ (encLits ρ cs)))).map (blockOf (encLits ρ cs)))
        = encBlocks ρ cs from rfl] at hRρ
  rw [show ((cs.filter (termSat (complete σ (encLits σ cs)))).map (blockOf (encLits σ cs)))
        = encBlocks σ cs from rfl] at hRσ
  rw [hdet, hcomplete] at hRρ
  exact hRρ.symm.trans hRσ

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.encLits_label_inj
