import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingEncPath
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingFlatLabel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingDnfCount

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

/-! ## Packing the flat label into `PathLabel w s` and the `(2w)^s` count -/

variable {w s : ℕ}

/-- Embed a `ℕ` index into `Fin w` (junk `default` if out of range). -/
def natToFin (w : ℕ) [NeZero w] (i : ℕ) : Fin w := if h : i < w then ⟨i, h⟩ else default

theorem natToFin_val [NeZero w] {i : ℕ} (h : i < w) : (natToFin w i).val = i := by
  simp [natToFin, h]

/-- Coerce a flat `(ℕ, Bool)` label into a flat `(Fin w, Bool)` label. -/
def toFinW (w : ℕ) [NeZero w] (l : List (ℕ × Bool)) : List (Fin w × Bool) :=
  l.map (fun p => (natToFin w p.1, p.2))

/-- The left inverse on in-range indices. -/
def finToNat : Fin w × Bool → ℕ × Bool := fun p => (p.1.val, p.2)

theorem finToNat_toFinW [NeZero w] : ∀ {l : List (ℕ × Bool)}, (∀ p ∈ l, p.1 < w) →
    (toFinW w l).map finToNat = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro hl
    have ha : a.1 < w := hl a (List.mem_cons.mpr (Or.inl rfl))
    have htl := ih (fun p hp => hl p (List.mem_cons.mpr (Or.inr hp)))
    simp only [toFinW, List.map_cons] at htl ⊢
    rw [htl]
    congr 1
    simp [finToNat, natToFin_val ha]

theorem toFinW_inj (w : ℕ) [NeZero w] {l l' : List (ℕ × Bool)}
    (hl : ∀ p ∈ l, p.1 < w) (hl' : ∀ p ∈ l', p.1 < w)
    (h : toFinW w l = toFinW w l') : l = l' := by
  have := congrArg (List.map (finToNat (w := w))) h
  rwa [finToNat_toFinW hl, finToNat_toFinW hl'] at this

/-- The packed encoder label: the flat `(ℕ, Bool)` sequence coerced to `Fin w` and folded
into `PathLabel w s`. -/
def packLabel (w s : ℕ) [NeZero w] (ρ : Restriction n) (cs : List (Clause n)) : PathLabel w s :=
  flatToLabel (toFinW w (encFlatLabel ρ cs))

/-- A `blockOf` index is a literal position, hence below the term's width. -/
theorem blockOf_lt {litList : List (Rung4Literal n)} {T : Clause n} {i : ℕ}
    (hi : i ∈ blockOf litList T) : i < T.lits.length := by
  rw [blockOf, List.mem_filter, List.mem_range] at hi
  exact hi.1

/-- **`hidx` is a clause-width consequence.**  If every clause has width `≤ w`, then every
index of the encoder flat label is `< w`.  So the `indices < w` side condition of the count is
not an assumption but a proved consequence of the standard width bound. -/
theorem encFlatLabel_idx_lt (ρ : Restriction n) {cs : List (Clause n)}
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w) :
    ∀ p ∈ encFlatLabel ρ cs, p.1 < w := by
  intro p hp
  rw [encFlatLabel] at hp
  obtain ⟨b, hb, hpb⟩ := ungroupBlocks_fst_mem hp
  rw [encBlocks, List.mem_map] at hb
  obtain ⟨T, hT, hbT⟩ := hb
  subst hbT
  exact lt_of_lt_of_le (blockOf_lt hpb) (hwidth T (List.mem_of_mem_filter hT))

/-- **The `(2w)^s` switching count for the concrete encoder.**  For a bad set whose encoder
flat labels have length exactly `s` and indices `< w` (clause width), with nonempty confirmed
blocks, and whose completions land in `Short`:

  `|Bad| ≤ |Short| · (2w)^s`.

Everything is discharged by proved components — `hdecode` by `encLits_decode`, `hrec` by
`encLits_label_inj` through the packed label — leaving only the structural side conditions on
the bad set (length `s`, width `w`, nonempty blocks, `Short` membership). -/
theorem encLits_switching_count [NeZero w] {cs : List (Clause n)}
    {Bad Short : Finset (Restriction n)}
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hblk : ∀ ρ ∈ Bad, ∀ b ∈ encBlocks ρ cs, b ≠ [])
    (hlen : ∀ ρ ∈ Bad, (encFlatLabel ρ cs).length = s)
    (hidx : ∀ ρ ∈ Bad, ∀ p ∈ encFlatLabel ρ cs, p.1 < w)
    (hmem : ∀ ρ ∈ Bad, complete ρ (encLits ρ cs) ∈ Short) :
    Bad.card ≤ Short.card * (2 * w) ^ s := by
  refine card_bad_le_encoding (fun ρ => complete ρ (encLits ρ cs))
    (fun ρ => packLabel w s ρ cs) hmem ?_
  intro ρ hρ σ hσ hE hlab
  have hlenρ : (toFinW w (encFlatLabel ρ cs)).length = s := by
    simp only [toFinW, List.length_map]; exact hlen ρ hρ
  have hlenσ : (toFinW w (encFlatLabel σ cs)).length = s := by
    simp only [toFinW, List.length_map]; exact hlen σ hσ
  have h1 : toFinW w (encFlatLabel ρ cs) = toFinW w (encFlatLabel σ cs) :=
    flatToLabel_inj hlenρ hlenσ hlab
  have h2 : encFlatLabel ρ cs = encFlatLabel σ cs :=
    toFinW_inj w (hidx ρ hρ) (hidx σ hσ) h1
  exact encLits_label_inj ρ σ cs hcs (hblk ρ hρ) (hblk σ hσ) hE h2

/-- **The `(2w)^s` count from clause width.**  Same as `encLits_switching_count`, with the
`indices < w` side condition discharged from a clause-width bound `T.lits.length ≤ w` — the
form matching the standard switching-lemma setup (width-`w` clauses). -/
theorem encLits_switching_count_width [NeZero w] {cs : List (Clause n)}
    {Bad Short : Finset (Restriction n)}
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hblk : ∀ ρ ∈ Bad, ∀ b ∈ encBlocks ρ cs, b ≠ [])
    (hlen : ∀ ρ ∈ Bad, (encFlatLabel ρ cs).length = s)
    (hmem : ∀ ρ ∈ Bad, complete ρ (encLits ρ cs) ∈ Short) :
    Bad.card ≤ Short.card * (2 * w) ^ s :=
  encLits_switching_count hcs hblk hlen (fun ρ _ => encFlatLabel_idx_lt ρ hwidth) hmem

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.encLits_label_inj
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.encLits_switching_count
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.encLits_switching_count_width
