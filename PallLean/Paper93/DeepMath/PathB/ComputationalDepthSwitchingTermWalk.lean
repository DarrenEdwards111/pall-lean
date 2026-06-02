import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingHastad
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingWalk
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCompletionVars

/-!
# The DNF decoder walk on the sound `termSat` selector

**STATUS: REAL.  THE WALK FOLD OVER THE SOUND SELECTOR.**

The decoder walks `cs`, at each step finding the first term satisfied under `σ*` (the sound
selector — `dropWhile_eq_of_prefix` lands on it since the prefix is non-`termSat`), collects
that term's block variables, and recurses on the terms after it.  Unlike the CNF walk this
needs no `hpre`: the selector is `termSat`, which is sound by `find_termSat_first_processed`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The decoder's collected variable set: walk `cs`, collect the block of each
`termSat`-confirmed term, advance past it. -/
def termWalkVars (σstar : Restriction n) (sel : Clause n → Finset (Fin n)) :
    List (Clause n) → ℕ → Finset (Fin n)
  | _, 0 => ∅
  | cs, k + 1 =>
    match cs.dropWhile (fun T => !termSat σstar T) with
    | [] => ∅
    | T :: rest => sel T ∪ termWalkVars σstar sel rest k

theorem termWalkVars_zero (σstar : Restriction n) (sel : Clause n → Finset (Fin n))
    (cs : List (Clause n)) : termWalkVars σstar sel cs 0 = ∅ := rfl

/-- **One-step walk correctness.**  When the first `termSat` term in `cs` is `T` (with the
prefix non-`termSat`), the walk collects `sel T` and recurses on the terms after `T`. -/
theorem termWalk_step (σstar : Restriction n) (sel : Clause n → Finset (Fin n))
    {cs : List (Clause n)} {pre : List (Clause n)} {T : Clause n} {rest : List (Clause n)}
    (k : ℕ) (hcs : cs = pre ++ T :: rest)
    (hpre : ∀ T' ∈ pre, termSat σstar T' = false) (hT : termSat σstar T = true) :
    termWalkVars σstar sel cs (k + 1) = sel T ∪ termWalkVars σstar sel rest k := by
  have hdw : cs.dropWhile (fun T => !termSat σstar T) = T :: rest := by
    rw [hcs]
    exact dropWhile_eq_of_prefix (fun T' hT' => by simp [hpre T' hT']) (by simp [hT])
  show (match cs.dropWhile (fun T => !termSat σstar T) with
    | [] => ∅ | T :: rest => sel T ∪ termWalkVars σstar sel rest k) = _
  rw [hdw]

/-- Dropping a `¬p` prefix does not change the `p`-filter. -/
theorem filter_dropWhile_not {α : Type*} (p : α → Bool) (l : List α) :
    (l.dropWhile (fun x => !p x)).filter p = l.filter p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hunfold : (a :: l).dropWhile (fun x => !p x)
        = match !p a with | true => l.dropWhile (fun x => !p x) | false => a :: l := rfl
    cases hpa : p a with
    | true => rw [hunfold, hpa]; simp [List.filter_cons, hpa]
    | false => rw [hunfold, hpa]; simp only [Bool.not_false]; rw [List.filter_cons, hpa]; simp; exact ih

/-- **Walk = first-`k` confirmed blocks.**  The walk collects the block of each of the
first `k` `termSat`-confirmed terms (the ones the sound selector lands on, in order). -/
theorem termWalkVars_eq_filter (σstar : Restriction n) (sel : Clause n → Finset (Fin n)) :
    ∀ (k : ℕ) (cs : List (Clause n)),
      termWalkVars σstar sel cs k
        = ((cs.filter (termSat σstar)).take k).foldr (fun T acc => sel T ∪ acc) ∅ := by
  intro k
  induction k with
  | zero => intro cs; simp [termWalkVars]
  | succ k ih =>
    intro cs
    show (match cs.dropWhile (fun T => !termSat σstar T) with
      | [] => ∅ | T :: rest => sel T ∪ termWalkVars σstar sel rest k) = _
    have hfd : (cs.dropWhile (fun T => !termSat σstar T)).filter (termSat σstar)
        = cs.filter (termSat σstar) := filter_dropWhile_not (termSat σstar) cs
    cases hdw : cs.dropWhile (fun T => !termSat σstar T) with
    | nil =>
      rw [hdw] at hfd
      simp only [List.filter_nil] at hfd
      rw [← hfd]; simp
    | cons T rest =>
      rw [hdw] at hfd
      have hT : termSat σstar T = true := by
        have := dropWhile_head_not hdw; simpa using this
      rw [List.filter_cons, hT] at hfd
      show sel T ∪ termWalkVars σstar sel rest k
        = ((cs.filter (termSat σstar)).take (k + 1)).foldr (fun T acc => sel T ∪ acc) ∅
      rw [ih rest, ← hfd]
      simp

/-- **Recovery wrapper.**  If the walk collects exactly the path variables, then freeing
them from `σ*` returns `ρ` — `decode_encode_id` for the DNF walk, modulo the encoder bridge
`heq` (that the walk's output equals the path-variable set). -/
theorem termWalk_recovers_of_eq {ρ : Restriction n} {litList : List (Rung4Literal n)}
    {sel : Clause n → Finset (Fin n)} {cs : List (Clause n)} {k : ℕ}
    (hfree : ∀ v ∈ litList.map litVar, ρ v = none)
    (heq : termWalkVars (complete ρ litList) sel cs k = ((litList.map litVar).toFinset)) :
    freeOn (complete ρ litList) (termWalkVars (complete ρ litList) sel cs k) = ρ := by
  rw [heq]
  exact freeOn_complete_recover hfree (fun _ => List.mem_toFinset)

/-- With enough fuel, the walk collects the block of *every* `termSat`-confirmed term. -/
theorem termWalk_eq_filter_full (σstar : Restriction n) (sel : Clause n → Finset (Fin n))
    (cs : List (Clause n)) (k : ℕ) (h : (cs.filter (termSat σstar)).length ≤ k) :
    termWalkVars σstar sel cs k
      = (cs.filter (termSat σstar)).foldr (fun T acc => sel T ∪ acc) ∅ := by
  rw [termWalkVars_eq_filter, List.take_of_length_le h]

/-- **DNF decoder `decode_encode_id` (sound selector).**  The decoder recovers `ρ` from
`σ*` and the per-term blocks, with the single encoder bridge `hcollect`: the blocks of the
`σ*`-satisfied terms collect to the path-variable set.  Everything else (the sound selector,
the walk, the recovery) is discharged. -/
theorem termWalk_decode_encode {ρ : Restriction n} {litList : List (Rung4Literal n)}
    {sel : Clause n → Finset (Fin n)} {cs : List (Clause n)} {k : ℕ}
    (hfree : ∀ v ∈ litList.map litVar, ρ v = none)
    (hfuel : (cs.filter (termSat (complete ρ litList))).length ≤ k)
    (hcollect : (cs.filter (termSat (complete ρ litList))).foldr (fun T acc => sel T ∪ acc) ∅
        = (litList.map litVar).toFinset) :
    freeOn (complete ρ litList) (termWalkVars (complete ρ litList) sel cs k) = ρ := by
  apply termWalk_recovers_of_eq hfree
  rw [termWalk_eq_filter_full _ _ _ _ hfuel, hcollect]

/-- Membership in the walk's output: a variable is collected iff it is in the block of one
of the first `k` `termSat`-confirmed terms. -/
theorem mem_termWalkVars {σstar : Restriction n} {sel : Clause n → Finset (Fin n)}
    {cs : List (Clause n)} {k : ℕ} {v : Fin n} :
    v ∈ termWalkVars σstar sel cs k
      ↔ ∃ T ∈ ((cs.filter (termSat σstar)).take k), v ∈ sel T := by
  rw [termWalkVars_eq_filter, mem_foldr_union]

/-- **Encoder bridge reduction.**  `hcollect` (the walk collects exactly the path-variable
set) reduces to two clean encoder inclusions: every confirmed term's block is path
variables, and every path variable lies in some confirmed term's block. -/
theorem hcollect_of {σstar : Restriction n} {sel : Clause n → Finset (Fin n)}
    {cs : List (Clause n)} {k : ℕ} {P : Finset (Fin n)}
    (hfuel : (cs.filter (termSat σstar)).length ≤ k)
    (hsub : ∀ T ∈ cs.filter (termSat σstar), sel T ⊆ P)
    (hcover : ∀ v ∈ P, ∃ T ∈ cs.filter (termSat σstar), v ∈ sel T) :
    termWalkVars σstar sel cs k = P := by
  apply Finset.Subset.antisymm
  · intro v hv
    rw [mem_termWalkVars] at hv
    obtain ⟨T, hT, hvT⟩ := hv
    exact hsub T (List.mem_of_mem_take hT) hvT
  · intro v hv
    rw [mem_termWalkVars]
    obtain ⟨T, hT, hvT⟩ := hcover v hv
    rw [List.take_of_length_le hfuel]
    exact ⟨T, hT, hvT⟩

/-- **DNF decoder recovery from the two encoder inclusions.**  `freeOn σ* (walk) = ρ`,
needing only: enough fuel, each confirmed term's block ⊆ path variables, and every path
variable lies in some confirmed term's block.  This is the minimal encoder interface —
both inclusions hold for the block-path encoder (where `σ*` satisfies each processed term
and its block is its free literals). -/
theorem termWalk_decode_encode' {ρ : Restriction n} {litList : List (Rung4Literal n)}
    {sel : Clause n → Finset (Fin n)} {cs : List (Clause n)} {k : ℕ}
    (hfree : ∀ v ∈ litList.map litVar, ρ v = none)
    (hfuel : (cs.filter (termSat (complete ρ litList))).length ≤ k)
    (hsub : ∀ T ∈ cs.filter (termSat (complete ρ litList)),
        sel T ⊆ (litList.map litVar).toFinset)
    (hcover : ∀ v ∈ (litList.map litVar).toFinset,
        ∃ T ∈ cs.filter (termSat (complete ρ litList)), v ∈ sel T) :
    freeOn (complete ρ litList) (termWalkVars (complete ρ litList) sel cs k) = ρ := by
  exact termWalk_recovers_of_eq hfree (hcollect_of hfuel hsub hcover)

/-- The per-term block selector: the variables of `T` that are path variables. -/
def termBlock (litList : List (Rung4Literal n)) (T : Clause n) : Finset (Fin n) :=
  (T.lits.map litVar).toFinset ∩ (litList.map litVar).toFinset

/-- **DNF decoder recovery from the single encoder property `hterm`.**  Choosing the block
selector `termBlock` (a term's path-variables), the decoder recovers `ρ` needing only that
*every path literal lies in a `termSat`-confirmed term* — `hsub` is automatic (`∩ ⊆`) and
`hcover` follows.  `hterm` is the lone remaining encoder obligation. -/
theorem termWalk_decode_of_hterm {ρ : Restriction n} {litList : List (Rung4Literal n)}
    {cs : List (Clause n)} {k : ℕ}
    (hfree : ∀ v ∈ litList.map litVar, ρ v = none)
    (hfuel : (cs.filter (termSat (complete ρ litList))).length ≤ k)
    (hterm : ∀ ℓ ∈ litList,
        ∃ T ∈ cs, ℓ ∈ T.lits ∧ termSat (complete ρ litList) T = true) :
    freeOn (complete ρ litList) (termWalkVars (complete ρ litList) (termBlock litList) cs k) = ρ := by
  refine termWalk_decode_encode' hfree hfuel ?_ ?_
  · intro T _ v hv; exact (Finset.mem_inter.mp hv).2
  · intro v hv
    rw [List.mem_toFinset, List.mem_map] at hv
    obtain ⟨ℓ, hℓlit, hℓv⟩ := hv
    obtain ⟨T, hTcs, hℓT, hTsat⟩ := hterm ℓ hℓlit
    refine ⟨T, List.mem_filter.mpr ⟨hTcs, hTsat⟩, ?_⟩
    rw [termBlock, Finset.mem_inter, List.mem_toFinset, List.mem_toFinset]
    exact ⟨List.mem_map.mpr ⟨ℓ, hℓT, hℓv⟩, List.mem_map.mpr ⟨ℓ, hℓlit, hℓv⟩⟩

/-- **End-to-end decode for the single-term DNF (base case).**  For one *live* term `T`
with distinct variables, taking the path literals to be `T`'s free literals, the decoder
recovers `ρ` with no further hypothesis: the whole machine (sound selector, walk, recovery)
closes.  `litList = freeLits ρ T`, `σ* = complete ρ (freeLits ρ T)`. -/
theorem termWalk_decode_single {ρ : Restriction n} {T : Clause n} {k : ℕ}
    (hlive : ∀ ℓ ∈ T.lits, litFalse ρ ℓ = false)
    (hnd : (T.lits.map litVar).Nodup) (hk : 1 ≤ k) :
    freeOn (complete ρ (freeLits ρ T))
      (termWalkVars (complete ρ (freeLits ρ T)) (termBlock (freeLits ρ T)) [T] k) = ρ := by
  have hfree : ∀ v ∈ (freeLits ρ T).map litVar, ρ v = none := by
    intro v hv; rw [List.mem_map] at hv; obtain ⟨ℓ, hℓ, hv⟩ := hv
    rw [← hv]
    have := (List.mem_filter.mp hℓ).2
    rw [litFree_var] at this; exact Option.isNone_iff_eq_none.mp this
  have hsub : List.Sublist (freeLits ρ T) T.lits := List.filter_sublist
  have hnd' : ((freeLits ρ T).map litVar).Nodup :=
    List.Nodup.sublist (List.Sublist.map litVar hsub) hnd
  have hsatT : termSat (complete ρ (freeLits ρ T)) T = true := by
    refine term_processed_termSat (fun ℓ hℓ hf => ?_) hlive hnd' hfree
    exact List.mem_filter.mpr ⟨hℓ, hf⟩
  have hfuel : ([T].filter (termSat (complete ρ (freeLits ρ T)))).length ≤ k := by
    rw [List.filter_cons, hsatT]; simpa using hk
  refine termWalk_decode_of_hterm hfree hfuel (fun ℓ hℓ => ⟨T, by simp, ?_, hsatT⟩)
  exact (List.mem_filter.mp hℓ).1

/-- **Multi-term `hterm`.**  Taking the path literals to be the free literals of a list
`ps` of *live* terms (with distinct variables across the blocks), every path literal lies
in its term, which is `termSat` under `σ*` (`term_processed_termSat`).  No dynamic path
needed — just the block structure. -/
theorem hterm_of_blocks {ρ : Restriction n} {cs ps : List (Clause n)}
    (hps : ∀ T ∈ ps, T ∈ cs)
    (hlive : ∀ T ∈ ps, ∀ ℓ ∈ T.lits, litFalse ρ ℓ = false)
    (hnd : ((ps.flatMap (freeLits ρ)).map litVar).Nodup)
    (hfree : ∀ v ∈ (ps.flatMap (freeLits ρ)).map litVar, ρ v = none) :
    ∀ ℓ ∈ ps.flatMap (freeLits ρ),
      ∃ T ∈ cs, ℓ ∈ T.lits ∧ termSat (complete ρ (ps.flatMap (freeLits ρ))) T = true := by
  intro ℓ hℓ
  rw [List.mem_flatMap] at hℓ
  obtain ⟨T, hTps, hℓT⟩ := hℓ
  refine ⟨T, hps T hTps, (List.mem_filter.mp hℓT).1, ?_⟩
  refine term_processed_termSat (fun ℓ' hℓ' hf => ?_) (hlive T hTps) hnd hfree
  rw [List.mem_flatMap]
  exact ⟨T, hTps, List.mem_filter.mpr ⟨hℓ', hf⟩⟩

/-- **Multi-term DNF decoder closes.**  For any list `ps` of live terms with distinct
variables across their free-literal blocks, the decoder recovers `ρ` from `σ*` and the
per-term blocks — `decode_encode_id` for the multi-term DNF. -/
theorem termWalk_decode_blocks {ρ : Restriction n} {cs ps : List (Clause n)} {k : ℕ}
    (hps : ∀ T ∈ ps, T ∈ cs)
    (hlive : ∀ T ∈ ps, ∀ ℓ ∈ T.lits, litFalse ρ ℓ = false)
    (hnd : ((ps.flatMap (freeLits ρ)).map litVar).Nodup)
    (hfuel : (cs.filter (termSat (complete ρ (ps.flatMap (freeLits ρ))))).length ≤ k) :
    freeOn (complete ρ (ps.flatMap (freeLits ρ)))
        (termWalkVars (complete ρ (ps.flatMap (freeLits ρ)))
          (termBlock (ps.flatMap (freeLits ρ))) cs k) = ρ := by
  have hfree : ∀ v ∈ (ps.flatMap (freeLits ρ)).map litVar, ρ v = none := by
    intro v hv; rw [List.mem_map] at hv; obtain ⟨ℓ, hℓ, hv⟩ := hv
    rw [← hv]
    rw [List.mem_flatMap] at hℓ; obtain ⟨T, _, hℓT⟩ := hℓ
    have := (List.mem_filter.mp hℓT).2; rw [litFree_var] at this
    exact Option.isNone_iff_eq_none.mp this
  exact termWalk_decode_of_hterm hfree hfuel (hterm_of_blocks hps hlive hnd hfree)

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.termWalk_step
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.termWalk_decode_encode
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.termWalk_decode_single
