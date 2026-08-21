import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultiSwitchingCommonTree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingDnfCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3WitnessReconstruct
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3WitnessSeqProps

/-!
# Finite labels for common multi-switching witnesses

A common bad path pays once for its shared branch transcript.  The remaining bookkeeping records,
for each gate, its number of contiguous active runs and, for each of its terms, its multiplicity on
the common path.  All counts lie between zero and the shared depth.  This file gives the exact finite
label space and connects it to the generic injective counting theorem; constructing the canonical
bad-path packing is the next combinatorial obligation.
-/

namespace PallLean.Paper93.DeepMath.PathB.MultiSwitching

open PallLean.Paper93.DeepMath.PathB.SwitchingCounting
open PallLean.Paper93.DeepMath.PathB.Depth3

/-- Assignment-followed canonical witness: literal position and active-term index at every query.
Unlike `deepestWitSeq`, this follows the exact branch selected by `x`. -/
def runWitSeq {n : ℕ} (cs : List (Clause n)) :
    ℕ → Restriction n → (Fin n → Bool) → List (ℕ × ℕ)
  | 0, _, _ => []
  | fuel + 1, σ, x =>
      if anyTermSat cs σ then []
      else match activeTerm cs σ with
        | none => []
        | some T => match (freeLits σ T).head? with
          | none => []
          | some ℓ => (freeLitPos σ T, activeTermIdx cs σ) ::
              if x (litVar ℓ)
              then runWitSeq cs fuel (fixVar σ (litVar ℓ) true) x
              else runWitSeq cs fuel (fixVar σ (litVar ℓ) false) x

/-- A raw witness entry tagged by its gate of origin. -/
abbrev TaggedWitEntry (G : ℕ) := Fin G × (ℕ × ℕ)

/-- The compact reconstruction key: gate first, then active-term index. -/
def taggedWitKey {G : ℕ} (e : TaggedWitEntry G) : Fin G × ℕ := (e.1, e.2.2)

/-- Concatenate the assignment-followed witnesses in canonical gate order. -/
def taggedRawWitSeq {n G : ℕ} (gates : Fin G → List (Clause n))
    (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool) : List (TaggedWitEntry G) :=
  (List.ofFn fun g => (runWitSeq (gates g) fuel σ x).map fun pc => (g, pc)).flatten

/-- Decode the variable named by a tagged `(gate, literal-position, term-index)` entry. -/
def taggedWitVar? {n G : ℕ} (gates : Fin G → List (Clause n))
    (e : TaggedWitEntry G) : Option (Fin n) :=
  ((gates e.1)[e.2.2]?).bind fun T => T.lits[e.2.1]?.map litVar

/-- Stable first-occurrence filter.  Entries with no decoded variable are discarded; repeated
variables are discarded after their first occurrence. -/
def freshTaggedAux {n G : ℕ} (gates : Fin G → List (Clause n)) :
    Finset (Fin n) → List (TaggedWitEntry G) → List (TaggedWitEntry G)
  | _, [] => []
  | seen, e :: es =>
      match taggedWitVar? gates e with
      | none => freshTaggedAux gates seen es
      | some v => if v ∈ seen then freshTaggedAux gates seen es
        else e :: freshTaggedAux gates (insert v seen) es

/-- The canonical globally fresh tagged witness stream.  This is the semantic source of the
corrected position and multiplicity components. -/
def freshTaggedWitSeq {n G : ℕ} (gates : Fin G → List (Clause n))
    (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool) : List (TaggedWitEntry G) :=
  freshTaggedAux gates ∅ (taggedRawWitSeq gates fuel σ x)

/-- Fresh filtering only removes raw entries and never reorders them. -/
theorem freshTaggedAux_sublist {n G : ℕ} (gates : Fin G → List (Clause n)) :
    ∀ (seen : Finset (Fin n)) (es : List (TaggedWitEntry G)),
      List.Sublist (freshTaggedAux gates seen es) es := by
  intro seen es
  induction es generalizing seen with
  | nil => simp [freshTaggedAux]
  | cons e es ih =>
      rw [freshTaggedAux]
      cases hvar : taggedWitVar? gates e with
      | none => exact (ih seen).cons _
      | some v =>
          by_cases hv : v ∈ seen
          · simp only [hvar, hv, if_true]
            exact (ih seen).cons _
          · simp only [hvar, hv, if_false]
            exact (ih (insert v seen)).cons_cons e

theorem freshTaggedWitSeq_sublist {n G : ℕ} (gates : Fin G → List (Clause n))
    (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool) :
    List.Sublist (freshTaggedWitSeq gates fuel σ x) (taggedRawWitSeq gates fuel σ x) :=
  freshTaggedAux_sublist gates ∅ _

/-- Stable first-occurrence filtering preserves exactly the decoded-variable set outside the
already-seen set. -/
theorem freshTaggedAux_vars_toFinset {n G : ℕ} (gates : Fin G → List (Clause n)) :
    ∀ (seen : Finset (Fin n)) (es : List (TaggedWitEntry G)),
      ((freshTaggedAux gates seen es).filterMap (taggedWitVar? gates)).toFinset =
        ((es.filterMap (taggedWitVar? gates)).toFinset \ seen) := by
  intro seen es
  induction es generalizing seen with
  | nil => simp [freshTaggedAux]
  | cons e es ih =>
      rw [freshTaggedAux]
      cases hvar : taggedWitVar? gates e with
      | none => simpa [hvar] using ih seen
      | some v =>
          by_cases hv : v ∈ seen
          · simp only [hvar, hv, if_true]
            rw [ih seen]
            simp only [List.filterMap_cons, hvar, Option.toList_some,
              List.singleton_append, List.toFinset_cons]
            ext q
            simp only [Finset.mem_sdiff, Finset.mem_insert]
            by_cases hq : q = v <;> simp [hq, hv]
          · simp only [hvar, hv, if_false]
            simp only [List.filterMap_cons, hvar, List.toFinset_cons]
            rw [ih (insert v seen)]
            ext q
            simp only [Finset.mem_insert, Finset.mem_sdiff]
            by_cases hq : q = v <;> simp [hq, hv]

theorem freshTaggedWitSeq_vars_toFinset {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ)
    (σ : Restriction n) (x : Fin n → Bool) :
    ((freshTaggedWitSeq gates fuel σ x).filterMap (taggedWitVar? gates)).toFinset =
      ((taggedRawWitSeq gates fuel σ x).filterMap (taggedWitVar? gates)).toFinset := by
  simpa [freshTaggedWitSeq] using
    freshTaggedAux_vars_toFinset gates (∅ : Finset (Fin n))
      (taggedRawWitSeq gates fuel σ x)

/-- Every retained entry has a decoded variable.  This is the first invariant needed to show that
the fresh tagged stream and the normalized query stream have the same length. -/
theorem freshTaggedAux_var_isSome {n G : ℕ} (gates : Fin G → List (Clause n)) :
    ∀ (seen : Finset (Fin n)) (es : List (TaggedWitEntry G)) (e : TaggedWitEntry G),
      e ∈ freshTaggedAux gates seen es → (taggedWitVar? gates e).isSome = true := by
  intro seen es
  induction es generalizing seen with
  | nil => simp [freshTaggedAux]
  | cons a es ih =>
      intro e he
      rw [freshTaggedAux] at he
      cases hvar : taggedWitVar? gates a with
      | none => exact ih seen e (by simpa [hvar] using he)
      | some v =>
          by_cases hv : v ∈ seen
          · simp only [hvar, hv, if_true] at he
            exact ih seen e he
          · simp only [hvar, hv, if_false, List.mem_cons] at he
            rcases he with rfl | he
            · simp [hvar]
            · exact ih (insert v seen) e he

/-- Decoding does not shorten a fresh stream, because entries without a variable were removed by
`freshTaggedAux`. -/
theorem freshTaggedAux_filterMap_length {n G : ℕ} (gates : Fin G → List (Clause n)) :
    ∀ (seen : Finset (Fin n)) (es : List (TaggedWitEntry G)),
      ((freshTaggedAux gates seen es).filterMap (taggedWitVar? gates)).length =
        (freshTaggedAux gates seen es).length := by
  intro seen es
  induction es generalizing seen with
  | nil => simp [freshTaggedAux]
  | cons e es ih =>
      rw [freshTaggedAux]
      cases hvar : taggedWitVar? gates e with
      | none => simpa using ih seen
      | some v =>
          by_cases hv : v ∈ seen
          · simpa [hvar, hv] using ih seen
          · simp [hvar, hv, ih (insert v seen)]

/-- The stable freshness filter emits no decoded variable twice. -/
theorem freshTaggedAux_vars_nodup {n G : ℕ} (gates : Fin G → List (Clause n)) :
    ∀ (seen : Finset (Fin n)) (es : List (TaggedWitEntry G)),
      ((freshTaggedAux gates seen es).filterMap (taggedWitVar? gates)).Nodup := by
  intro seen es
  induction es generalizing seen with
  | nil => simp [freshTaggedAux]
  | cons e es ih =>
      rw [freshTaggedAux]
      cases hvar : taggedWitVar? gates e with
      | none => simpa using ih seen
      | some v =>
          by_cases hv : v ∈ seen
          · simpa [hvar, hv] using ih seen
          · simp only [hvar, hv, if_false, List.filterMap_cons,
              List.nodup_cons]
            refine ⟨?_, ih (insert v seen)⟩
            intro hmem
            have hset := congrArg (fun s : Finset (Fin n) => v ∈ s)
              (freshTaggedAux_vars_toFinset gates (insert v seen) es)
            have : False := by
              simpa [List.mem_toFinset, hmem] using hset
            exact this.elim

theorem freshTaggedWitSeq_vars_nodup {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ)
    (σ : Restriction n) (x : Fin n → Bool) :
    ((freshTaggedWitSeq gates fuel σ x).filterMap
      (taggedWitVar? gates)).Nodup := by
  exact freshTaggedAux_vars_nodup gates ∅ _

/-- `witDecode` is the finite-set form of pointwise optional decoding. -/
theorem witDecode_eq_filterMap_toFinset {n : ℕ} (cs : List (Clause n)) :
    ∀ ws : List (ℕ × ℕ),
      witDecode cs ws =
        (ws.filterMap fun pc =>
          ((cs[pc.2]?).bind fun T => T.lits[pc.1]?).map litVar).toFinset := by
  intro ws
  induction ws with
  | nil => simp [witDecode]
  | cons pc ws ih =>
      simp only [witDecode, List.filterMap_cons]
      cases hdec : (cs[pc.2]?).bind (fun T => T.lits[pc.1]?) with
      | none => simp [hdec, ih]
      | some ell => simp [hdec, ih]

/-- The assignment-followed witness has exactly one entry per raw canonical query. -/
theorem runWitSeq_length_eq_queryVars {n : ℕ} (cs : List (Clause n)) :
    ∀ (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool),
    (runWitSeq cs fuel σ x).length =
      (CommonTree.queryVars (CommonTree.ofBool (canonicalDT cs fuel σ)) x).length := by
  intro fuel
  induction fuel with
  | zero =>
      intro σ x
      by_cases hsat : anyTermSat cs σ = true <;>
        simp [runWitSeq, canonicalDT, hsat, CommonTree.ofBool, CommonTree.queryVars]
  | succ fuel ih =>
      intro σ x
      by_cases hsat : anyTermSat cs σ = true
      · simp [runWitSeq, canonicalDT, hsat, CommonTree.ofBool, CommonTree.queryVars]
      · cases hT : activeTerm cs σ with
        | none => simp [runWitSeq, canonicalDT, hsat, hT, CommonTree.ofBool,
            CommonTree.queryVars]
        | some T =>
          cases hh : (freeLits σ T).head? with
          | none => simp [runWitSeq, canonicalDT, hsat, hT, hh, CommonTree.ofBool,
              CommonTree.queryVars]
          | some ℓ =>
            by_cases hx : x (litVar ℓ)
            · simp [runWitSeq, canonicalDT, hsat, hT, hh, hx, CommonTree.ofBool,
                CommonTree.queryVars, ih]
            · simp [runWitSeq, canonicalDT, hsat, hT, hh, hx, CommonTree.ofBool,
                CommonTree.queryVars, ih]

/-- Decoding the assignment-followed term/position annotations recovers the exact queried-variable
set of the corresponding canonical gate path. -/
theorem witDecode_runWitSeq {n : ℕ} (cs : List (Clause n)) :
    ∀ (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool),
    witDecode cs (runWitSeq cs fuel σ x) =
      (CommonTree.queryVars (CommonTree.ofBool (canonicalDT cs fuel σ)) x).toFinset := by
  intro fuel
  induction fuel with
  | zero =>
      intro σ x
      by_cases hsat : anyTermSat cs σ = true <;>
        simp [runWitSeq, canonicalDT, hsat, witDecode, CommonTree.ofBool,
          CommonTree.queryVars]
  | succ fuel ih =>
      intro σ x
      by_cases hsat : anyTermSat cs σ = true
      · simp [runWitSeq, canonicalDT, hsat, witDecode, CommonTree.ofBool,
          CommonTree.queryVars]
      · cases hT : activeTerm cs σ with
        | none => simp [runWitSeq, canonicalDT, hsat, hT, witDecode, CommonTree.ofBool,
            CommonTree.queryVars]
        | some T =>
          cases hh : (freeLits σ T).head? with
          | none => simp [runWitSeq, canonicalDT, hsat, hT, hh, witDecode,
              CommonTree.ofBool, CommonTree.queryVars]
          | some ℓ =>
            have hc : cs[activeTermIdx cs σ]? = some T := by
              rw [List.getElem?_eq_getElem (activeTermIdx_lt hT), getElem_activeTermIdx hT]
            have hp : T.lits[freeLitPos σ T]? = some ℓ := by
              rw [List.getElem?_eq_getElem (freeLitPos_lt hh), getElem_freeLitPos hh]
            by_cases hx : x (litVar ℓ)
            · simp [runWitSeq, canonicalDT, hsat, hT, hh, hx, witDecode, hc, hp,
                CommonTree.ofBool, CommonTree.queryVars, ih]
            · simp [runWitSeq, canonicalDT, hsat, hT, hh, hx, witDecode, hc, hp,
                CommonTree.ofBool, CommonTree.queryVars, ih]

/-- The globally fresh tagged stream decodes to exactly the normalized canonical-family path set. -/
theorem freshTaggedWitSeq_vars_eq_pathVars {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    (x : Fin n → Bool) (hext : Rung4Restriction.Extends σ x) :
    ((freshTaggedWitSeq gates fuel σ x).filterMap
      (taggedWitVar? gates)).toFinset =
        CommonTree.pathVars σ (canonicalFamilyTree gates fuel σ) x := by
  rw [freshTaggedWitSeq_vars_toFinset,
    pathVars_canonicalFamily_eq_raw gates fuel σ x hext]
  rw [canonicalFamilyTree, CommonTree.queryVars_commonRefineFin]
  ext v
  simp only [List.mem_toFinset]
  simp only [taggedRawWitSeq, taggedWitVar?, List.filterMap_flatten,
    List.filterMap_map, List.mem_flatten, List.mem_map, List.mem_ofFn,
    List.mem_filterMap]
  constructor
  · rintro ⟨w, ⟨segment, ⟨g, hg⟩, hfilter⟩, hv⟩
    subst segment
    subst w
    obtain ⟨e, he, hdec⟩ := List.mem_filterMap.mp hv
    obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp he
    refine ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, ?_⟩
    rw [← List.mem_toFinset, ← witDecode_runWitSeq,
      witDecode_eq_filterMap_toFinset]
    apply List.mem_toFinset.mpr
    apply List.mem_filterMap.mpr
    exact ⟨pc, hpc, by simpa [taggedWitVar?] using hdec⟩
  · rintro ⟨w, ⟨tree, ⟨g, hg⟩, hquery⟩, hv⟩
    subst tree
    subst w
    rw [← List.mem_toFinset, ← witDecode_runWitSeq,
      witDecode_eq_filterMap_toFinset] at hv
    obtain ⟨pc, hpc, hdec⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hv)
    refine ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, List.mem_filterMap.mpr ?_⟩
    exact ⟨(g, pc), List.mem_map.mpr ⟨pc, hpc, rfl⟩,
      by simpa [taggedWitVar?] using hdec⟩

/-- The fresh tagged witness length is exactly the normalized common-path length.  In particular,
the finite path label's existing length field also bounds and identifies the corrected position and
multiplicity streams; no extra length factor is needed in the count. -/
theorem freshTaggedWitSeq_length_eq_trace_readOnce {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    (x : Fin n → Bool) (hext : Rung4Restriction.Extends σ x) :
    (freshTaggedWitSeq gates fuel σ x).length =
      (CommonTree.trace
        (CommonTree.readOnce σ (canonicalFamilyTree gates fuel σ)) x).length := by
  rw [CommonTree.trace_length_eq_queryVars_length]
  rw [← List.toFinset_card_of_nodup
    (CommonTree.queryVars_readOnce_nodup σ (canonicalFamilyTree gates fuel σ) x hext)]
  change (freshTaggedWitSeq gates fuel σ x).length =
    (CommonTree.pathVars σ (canonicalFamilyTree gates fuel σ) x).card
  rw [← freshTaggedWitSeq_vars_eq_pathVars gates fuel σ x hext]
  rw [List.toFinset_card_of_nodup (freshTaggedWitSeq_vars_nodup gates fuel σ x)]
  exact (freshTaggedAux_filterMap_length gates ∅ _).symm

/-- Any coordinate on a raw canonical gate path is represented by a genuine active-term/literal
position entry in that gate's assignment-followed witness. -/
theorem mem_witDecode_runWitSeq_of_mem_queryVars {n : ℕ}
    (cs : List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    (x : Fin n → Bool) {v : Fin n}
    (hv : v ∈ CommonTree.queryVars (CommonTree.ofBool (canonicalDT cs fuel σ)) x) :
    v ∈ witDecode cs (runWitSeq cs fuel σ x) := by
  rw [witDecode_runWitSeq]
  exact List.mem_toFinset.mpr hv

/-- Every term index recorded later on an assignment-followed path belongs to the active suffix at
its current root. -/
theorem runWitSeq_index_mem_activeSuffix {n : ℕ} (cs : List (Clause n)) (hnd : cs.Nodup) :
    ∀ (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool) (pc : ℕ × ℕ),
      pc ∈ runWitSeq cs fuel σ x →
        ∃ T ∈ activeSuffix cs σ, pc.2 = cs.idxOf T := by
  intro fuel
  induction fuel with
  | zero => intro σ x pc hpc; simp [runWitSeq] at hpc
  | succ fuel ih =>
      intro σ x pc hpc
      by_cases hsat : anyTermSat cs σ = true
      · simp [runWitSeq, hsat] at hpc
      · cases hT : activeTerm cs σ with
        | none => simp [runWitSeq, hsat, hT] at hpc
        | some T =>
          cases hh : (freeLits σ T).head? with
          | none => simp [runWitSeq, hsat, hT, hh] at hpc
          | some ell =>
            have hellmem : ell ∈ freeLits σ T := List.mem_of_mem_head? hh
            have hv : σ (litVar ell) = none := by
              have hfree : litFree σ ell = true := (List.mem_filter.mp hellmem).2
              rw [litFree_var] at hfree
              cases hs : σ (litVar ell) with
              | none => rfl
              | some b => rw [hs] at hfree; simp at hfree
            have hTmem : T ∈ activeSuffix cs σ := by
              have hhead := head?_activeSuffix (cs := cs) (σ := σ)
                (Bool.eq_false_of_not_eq_true hsat)
              rw [hT] at hhead
              exact List.mem_of_mem_head? hhead
            have finish (b : Bool)
                (hp : pc = (freeLitPos σ T, activeTermIdx cs σ) ∨
                  pc ∈ runWitSeq cs fuel (fixVar σ (litVar ell) b) x) :
                ∃ U ∈ activeSuffix cs σ, pc.2 = cs.idxOf U := by
              rcases hp with rfl | hp
              · exact ⟨T, hTmem, activeTermIdx_eq_idxOf hnd hT⟩
              · obtain ⟨U, hU, hidx⟩ := ih (fixVar σ (litVar ell) b) x pc hp
                exact ⟨U, (activeSuffix_fixVar_suffix hv).subset hU, hidx⟩
            by_cases hx : x (litVar ell)
            · simp only [runWitSeq, hsat, Bool.false_eq_true, if_false, hT, hh,
                hx, if_true, List.mem_cons] at hpc
              exact finish true hpc
            · simp only [runWitSeq, hsat, Bool.false_eq_true, if_false, hT, hh,
                hx, if_false, List.mem_cons] at hpc
              exact finish false hpc

/-- Every term index in an assignment-followed witness is in range for its gate. -/
theorem runWitSeq_termIdx_lt_length {n : ℕ} (cs : List (Clause n)) (hnd : cs.Nodup)
    (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool) {pc : ℕ × ℕ}
    (hpc : pc ∈ runWitSeq cs fuel σ x) : pc.2 < cs.length := by
  obtain ⟨T, hT, hidx⟩ := runWitSeq_index_mem_activeSuffix cs hnd fuel σ x pc hpc
  rw [hidx]
  apply List.idxOf_lt_length_of_mem
  exact (List.dropWhile_suffix _).subset hT

/-- Every literal position in an assignment-followed witness respects a uniform width bound. -/
theorem runWitSeq_pos_lt {n w : ℕ} (cs : List (Clause n))
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) :
    ∀ (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool) (pc : ℕ × ℕ),
      pc ∈ runWitSeq cs fuel σ x → pc.1 < w := by
  intro fuel
  induction fuel with
  | zero => intro σ x pc hpc; simp [runWitSeq] at hpc
  | succ fuel ih =>
      intro σ x pc hpc
      by_cases hsat : anyTermSat cs σ = true
      · simp [runWitSeq, hsat] at hpc
      · cases hT : activeTerm cs σ with
        | none => simp [runWitSeq, hsat, hT] at hpc
        | some T =>
          cases hh : (freeLits σ T).head? with
          | none => simp [runWitSeq, hsat, hT, hh] at hpc
          | some ell =>
            by_cases hx : x (litVar ell)
            · simp only [runWitSeq, hsat, Bool.false_eq_true, if_false, hT, hh,
                hx, if_true, List.mem_cons] at hpc
              rcases hpc with rfl | hpc
              · exact (freeLitPos_lt hh).trans_le (hw T (Depth3.activeTerm_mem hT))
              · exact ih (fixVar σ (litVar ell) true) x pc hpc
            · simp only [runWitSeq, hsat, Bool.false_eq_true, if_false, hT, hh,
                hx, if_false, List.mem_cons] at hpc
              rcases hpc with rfl | hpc
              · exact (freeLitPos_lt hh).trans_le (hw T (Depth3.activeTerm_mem hT))
              · exact ih (fixVar σ (litVar ell) false) x pc hpc

/-- Assignment-followed canonical paths do not backtrack in the duplicate-free term order. -/
theorem runWitSeq_termIndices_pairwise {n : ℕ} (cs : List (Clause n)) (hnd : cs.Nodup) :
    ∀ (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool),
      List.Pairwise (· ≤ ·) ((runWitSeq cs fuel σ x).map Prod.snd) := by
  intro fuel
  induction fuel with
  | zero => intro σ x; simp [runWitSeq]
  | succ fuel ih =>
      intro σ x
      by_cases hsat : anyTermSat cs σ = true
      · simp [runWitSeq, hsat]
      · cases hT : activeTerm cs σ with
        | none => simp [runWitSeq, hsat, hT]
        | some T =>
          cases hh : (freeLits σ T).head? with
          | none => simp [runWitSeq, hsat, hT, hh]
          | some ell =>
            have hns : anyTermSat cs σ = false := Bool.eq_false_of_not_eq_true hsat
            have hhead : activeTermIdx cs σ = cs.idxOf T := activeTermIdx_eq_idxOf hnd hT
            have hellmem : ell ∈ freeLits σ T := List.mem_of_mem_head? hh
            have hv : σ (litVar ell) = none := by
              have hfree : litFree σ ell = true := (List.mem_filter.mp hellmem).2
              rw [litFree_var] at hfree
              cases hs : σ (litVar ell) with
              | none => rfl
              | some q => rw [hs] at hfree; simp at hfree
            have finish (b : Bool) :
                List.Pairwise (· ≤ ·)
                  (((freeLitPos σ T, activeTermIdx cs σ) ::
                    runWitSeq cs fuel (fixVar σ (litVar ell) b) x).map Prod.snd) := by
              simp only [List.map_cons]
              refine List.Pairwise.cons ?_ (ih (fixVar σ (litVar ell) b) x)
              intro i hi
              rw [List.mem_map] at hi
              obtain ⟨pc, hpc, rfl⟩ := hi
              obtain ⟨U, hU, hidx⟩ :=
                runWitSeq_index_mem_activeSuffix cs hnd fuel
                  (fixVar σ (litVar ell) b) x pc hpc
              have hU' : U ∈ activeSuffix cs σ :=
                (activeSuffix_fixVar_suffix hv).subset hU
              rw [hhead, hidx]
              exact idxOf_activeTerm_le_of_mem_activeSuffix hnd hns hT hU'
            by_cases hx : x (litVar ell)
            · rw [runWitSeq]
              simp only [hsat, Bool.false_eq_true, if_false, hT, hh, hx, if_true]
              exact finish true
            · rw [runWitSeq]
              simp only [hsat, Bool.false_eq_true, if_false, hT, hh, hx, if_false]
              exact finish false

/-- The raw family witness is block-monotone: gate indices increase strictly between blocks and
term indices are nondecreasing inside each gate. -/
theorem taggedRawWitSeq_keys_pairwise {n G : ℕ}
    (gates : Fin G → List (Clause n)) (hnd : ∀ g, (gates g).Nodup)
    (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool) :
    List.Pairwise (Prod.Lex (· < ·) (· ≤ ·))
      ((taggedRawWitSeq gates fuel σ x).map taggedWitKey) := by
  rw [taggedRawWitSeq, List.map_flatten, List.pairwise_flatten]
  constructor
  · intro block hblock
    obtain ⟨rawBlock, hrawBlock, rfl⟩ := List.mem_map.mp hblock
    obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hrawBlock
    simp only [List.map_map]
    have hpair := runWitSeq_termIndices_pairwise (gates g) (hnd g) fuel σ x
    rw [List.pairwise_map] at hpair ⊢
    simpa [taggedWitKey, Prod.lex_def] using hpair
  · rw [List.pairwise_map, List.pairwise_ofFn]
    intro i j hij left hleft right hright
    obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hleft
    obtain ⟨qc, hqc, rfl⟩ := List.mem_map.mp hright
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hqc
    simp [taggedWitKey, Prod.lex_def, hij]

/-- Stable global freshness filtering inherits raw block monotonicity. -/
theorem freshTaggedWitSeq_keys_pairwise {n G : ℕ}
    (gates : Fin G → List (Clause n)) (hnd : ∀ g, (gates g).Nodup)
    (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool) :
    List.Pairwise (Prod.Lex (· < ·) (· ≤ ·))
      ((freshTaggedWitSeq gates fuel σ x).map taggedWitKey) := by
  apply List.Pairwise.sublist (List.Sublist.map taggedWitKey
    (freshTaggedWitSeq_sublist gates fuel σ x))
  exact taggedRawWitSeq_keys_pairwise gates hnd fuel σ x

/-- Every fresh tagged entry has a term index below the declared uniform gate bound. -/
theorem freshTaggedWitSeq_termIdx_lt {n G m : ℕ}
    (gates : Fin G → List (Clause n)) (hnd : ∀ g, (gates g).Nodup)
    (hlen : ∀ g, (gates g).length ≤ m)
    (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool)
    {e : TaggedWitEntry G} (he : e ∈ freshTaggedWitSeq gates fuel σ x) : e.2.2 < m := by
  have heraw : e ∈ taggedRawWitSeq gates fuel σ x :=
    (freshTaggedWitSeq_sublist gates fuel σ x).subset he
  rw [taggedRawWitSeq] at heraw
  obtain ⟨block, hblock, heblock⟩ := List.mem_flatten.mp heraw
  obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hblock
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp heblock
  exact (runWitSeq_termIdx_lt_length (gates g) (hnd g) fuel σ x hpc).trans_le (hlen g)

/-- Every fresh tagged literal position respects the family width bound. -/
theorem freshTaggedWitSeq_pos_lt {n G w : ℕ}
    (gates : Fin G → List (Clause n))
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool)
    {e : TaggedWitEntry G} (he : e ∈ freshTaggedWitSeq gates fuel σ x) : e.2.1 < w := by
  have heraw : e ∈ taggedRawWitSeq gates fuel σ x :=
    (freshTaggedWitSeq_sublist gates fuel σ x).subset he
  rw [taggedRawWitSeq] at heraw
  obtain ⟨block, hblock, heblock⟩ := List.mem_flatten.mp heraw
  obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hblock
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp heblock
  exact runWitSeq_pos_lt (gates g) (hw g) fuel σ x pc hpc

/-- A block-monotone tagged key stream is uniquely determined by its multiplicities. -/
theorem taggedKeySeq_eq_of_count_eq {G : ℕ} {a b : List (Fin G × ℕ)}
    (ha : List.Pairwise (Prod.Lex (· < ·) (· ≤ ·)) a)
    (hb : List.Pairwise (Prod.Lex (· < ·) (· ≤ ·)) b)
    (hc : ∀ k, a.count k = b.count k) : a = b := by
  have hp : a.Perm b := List.perm_iff_count.mpr hc
  have hanti : ∀ p q : Fin G × ℕ,
      p ∈ a → q ∈ b →
      Prod.Lex (· < ·) (· ≤ ·) p q →
      Prod.Lex (· < ·) (· ≤ ·) q p → p = q := by
    intro p q _ _ hpq hqp
    rcases p with ⟨pg, pt⟩
    rcases q with ⟨qg, qt⟩
    simp only [Prod.lex_def] at hpq hqp
    rcases hpq with hpg | ⟨hgeq, hpt⟩
    · rcases hqp with hqg | ⟨hqeq, _⟩
      · exact (Fin.lt_asymm hpg hqg).elim
      · exact (hpg.ne hqeq.symm).elim
    · rcases hqp with hqg | ⟨_, hqt⟩
      · exact (hqg.ne hgeq.symm).elim
      · subst qg
        exact Prod.ext rfl (Nat.le_antisymm hpt hqt)
  exact List.Perm.eq_of_pairwise hanti ha hb hp

/-- Counting tagged keys after mapping is the same as the boolean predicate table used by the
compact label. -/
theorem count_map_taggedWitKey {G : ℕ} (es : List (TaggedWitEntry G))
    (g : Fin G) (j : ℕ) :
    (es.map taggedWitKey).count (g, j) =
      es.countP (fun e => e.1 = g && e.2.2 = j) := by
  induction es with
  | nil => simp
  | cons e es ih =>
      simp only [List.map_cons, List.count_cons, List.countP_cons, ih]
      by_cases hg : e.1 = g <;> by_cases hj : e.2.2 = j <;>
        simp [taggedWitKey, hg, hj]

/-- The fresh tagged key stream is recovered from its complete `(gate,term)` count table. -/
theorem freshTaggedWitSeq_keys_eq_of_count_eq {n G : ℕ}
    (gates : Fin G → List (Clause n)) (hnd : ∀ g, (gates g).Nodup)
    (fuel : ℕ) (ρ σ : Restriction n) (x y : Fin n → Bool)
    (hc : ∀ (g : Fin G) (j : ℕ),
      (freshTaggedWitSeq gates fuel ρ x).countP
          (fun e => e.1 = g && e.2.2 = j) =
        (freshTaggedWitSeq gates fuel σ y).countP
          (fun e => e.1 = g && e.2.2 = j)) :
    (freshTaggedWitSeq gates fuel ρ x).map taggedWitKey =
      (freshTaggedWitSeq gates fuel σ y).map taggedWitKey := by
  apply taggedKeySeq_eq_of_count_eq
    (freshTaggedWitSeq_keys_pairwise gates hnd fuel ρ x)
    (freshTaggedWitSeq_keys_pairwise gates hnd fuel σ y)
  rintro ⟨g, j⟩
  rw [count_map_taggedWitKey, count_map_taggedWitKey]
  exact hc g j

/-- Once keys and literal positions agree pointwise, the full tagged witnesses agree. -/
theorem taggedWitEntry_list_eq_of_key_pos {G : ℕ}
    {a b : List (TaggedWitEntry G)}
    (hkey : a.map taggedWitKey = b.map taggedWitKey)
    (hpos : a.map (fun e => e.2.1) = b.map (fun e => e.2.1)) : a = b := by
  induction a generalizing b with
  | nil => simpa using hkey
  | cons e es ih =>
      cases b with
      | nil => simp at hkey
      | cons f fs =>
          simp only [List.map_cons, List.cons.injEq] at hkey hpos
          obtain ⟨hkeyHead, hkeyTail⟩ := hkey
          obtain ⟨hposHead, hposTail⟩ := hpos
          have hef : e = f := by
            rcases e with ⟨eg, ep, et⟩
            rcases f with ⟨fg, fp, ft⟩
            simp only [taggedWitKey, Prod.mk.injEq] at hkeyHead
            simp only at hposHead
            rcases hkeyHead with ⟨rfl, rfl⟩
            subst fp
            rfl
          subst f
          simp [ih hkeyTail hposTail]

/-- Hence term multiplicities uniquely determine the assignment-followed term-index stream. -/
theorem runWitSeq_termIndices_eq_of_count_eq {n : ℕ}
    (cs : List (Clause n)) (hnd : cs.Nodup) (fuel : ℕ)
    (ρ σ : Restriction n) (x y : Fin n → Bool)
    (hc : ∀ i,
      ((runWitSeq cs fuel ρ x).map Prod.snd).count i =
        ((runWitSeq cs fuel σ y).map Prod.snd).count i) :
    (runWitSeq cs fuel ρ x).map Prod.snd =
      (runWitSeq cs fuel σ y).map Prod.snd :=
  pairwise_le_eq_of_count_eq
    (runWitSeq_termIndices_pairwise cs hnd fuel ρ x)
    (runWitSeq_termIndices_pairwise cs hnd fuel σ y) hc

/-- Literal positions together with term multiplicities recover the complete raw canonical witness
for a duplicate-free gate. -/
theorem runWitSeq_eq_of_positions_count {n : ℕ}
    (cs : List (Clause n)) (hnd : cs.Nodup) (fuel : ℕ)
    (ρ σ : Restriction n) (x y : Fin n → Bool)
    (hpos : (runWitSeq cs fuel ρ x).map Prod.fst =
      (runWitSeq cs fuel σ y).map Prod.fst)
    (hc : ∀ i,
      ((runWitSeq cs fuel ρ x).map Prod.snd).count i =
        ((runWitSeq cs fuel σ y).map Prod.snd).count i) :
    runWitSeq cs fuel ρ x = runWitSeq cs fuel σ y := by
  have hterm := runWitSeq_termIndices_eq_of_count_eq cs hnd fuel ρ σ x y hc
  have combine : ∀ (a b : List (ℕ × ℕ)),
      a.map Prod.fst = b.map Prod.fst → a.map Prod.snd = b.map Prod.snd → a = b := by
    intro a
    induction a with
    | nil => intro b hp _; simpa using hp
    | cons q qs ih =>
        intro b hp ht
        cases b with
        | nil => simp at hp
        | cons r rs =>
            simp only [List.map_cons, List.cons.injEq] at hp ht
            rw [show q = r from Prod.ext hp.1 ht.1, ih rs hp.2 ht.2]
  exact combine _ _ hpos hterm

/-- Consequently the same corrected per-gate data recovers the raw queried-variable set. -/
theorem rawQueryVars_toFinset_eq_of_positions_count {n : ℕ}
    (cs : List (Clause n)) (hnd : cs.Nodup) (fuel : ℕ)
    (ρ σ : Restriction n) (x y : Fin n → Bool)
    (hpos : (runWitSeq cs fuel ρ x).map Prod.fst =
      (runWitSeq cs fuel σ y).map Prod.fst)
    (hc : ∀ i,
      ((runWitSeq cs fuel ρ x).map Prod.snd).count i =
        ((runWitSeq cs fuel σ y).map Prod.snd).count i) :
    (CommonTree.queryVars (CommonTree.ofBool (canonicalDT cs fuel ρ)) x).toFinset =
      (CommonTree.queryVars (CommonTree.ofBool (canonicalDT cs fuel σ)) y).toFinset := by
  rw [← witDecode_runWitSeq, ← witDecode_runWitSeq,
    runWitSeq_eq_of_positions_count cs hnd fuel ρ σ x y hpos hc]

/-- Equality of every gate's raw queried-variable set splices to equality of the normalized global
common-path set.  Read-once normalization removes repetitions only; no explicit gate-origin stream
is needed. -/
theorem pathVars_canonicalFamily_eq_of_rawGate_eq {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ)
    (ρ σ : Restriction n) (x y : Fin n → Bool)
    (hx : Rung4Restriction.Extends ρ x) (hy : Rung4Restriction.Extends σ y)
    (hraw : ∀ g,
      (CommonTree.queryVars (CommonTree.ofBool (canonicalDT (gates g) fuel ρ)) x).toFinset =
        (CommonTree.queryVars (CommonTree.ofBool (canonicalDT (gates g) fuel σ)) y).toFinset) :
    CommonTree.pathVars ρ (canonicalFamilyTree gates fuel ρ) x =
      CommonTree.pathVars σ (canonicalFamilyTree gates fuel σ) y := by
  rw [pathVars_canonicalFamily_eq_raw gates fuel ρ x hx,
    pathVars_canonicalFamily_eq_raw gates fuel σ y hy]
  ext v
  simp only [canonicalFamilyTree, CommonTree.queryVars_commonRefineFin,
    List.mem_toFinset]
  constructor
  · intro hv
    obtain ⟨segment, hsegment, hvsegment⟩ := List.mem_flatten.mp hv
    obtain ⟨tree, htree, rfl⟩ := List.mem_map.mp hsegment
    obtain ⟨g, rfl⟩ := List.mem_ofFn.mp htree
    apply List.mem_flatten.mpr
    refine ⟨CommonTree.queryVars
      (CommonTree.ofBool (canonicalDT (gates g) fuel σ)) y, ?_, ?_⟩
    · apply List.mem_map.mpr
      exact ⟨canonicalDT (gates g) fuel σ, List.mem_ofFn.mpr ⟨g, rfl⟩, rfl⟩
    · exact List.mem_toFinset.mp ((hraw g) ▸ List.mem_toFinset.mpr hvsegment)
  · intro hv
    obtain ⟨segment, hsegment, hvsegment⟩ := List.mem_flatten.mp hv
    obtain ⟨tree, htree, rfl⟩ := List.mem_map.mp hsegment
    obtain ⟨g, rfl⟩ := List.mem_ofFn.mp htree
    apply List.mem_flatten.mpr
    refine ⟨CommonTree.queryVars
      (CommonTree.ofBool (canonicalDT (gates g) fuel ρ)) x, ?_, ?_⟩
    · apply List.mem_map.mpr
      exact ⟨canonicalDT (gates g) fuel ρ, List.mem_ofFn.mpr ⟨g, rfl⟩, rfl⟩
    · exact List.mem_toFinset.mp ((hraw g).symm ▸ List.mem_toFinset.mpr hvsegment)

/-- The complete multi-gate injectivity theorem at the raw-set interface.  Once the corrected
fresh-position encoding recovers each gate's raw query set, endpoint injectivity is automatic. -/
theorem canonicalFamily_endpoint_inj_of_rawGate_eq {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ)
    {ρ σ : Restriction n} {x y : Fin n → Bool}
    (hx : Rung4Restriction.Extends ρ x) (hy : Rung4Restriction.Extends σ y)
    (hE : CommonTree.pathEndpoint ρ (canonicalFamilyTree gates fuel ρ) x =
      CommonTree.pathEndpoint σ (canonicalFamilyTree gates fuel σ) y)
    (hraw : ∀ g,
      (CommonTree.queryVars (CommonTree.ofBool (canonicalDT (gates g) fuel ρ)) x).toFinset =
        (CommonTree.queryVars (CommonTree.ofBool (canonicalDT (gates g) fuel σ)) y).toFinset) :
    ρ = σ := by
  exact CommonTree.pathEndpoint_inj_of_pathVars_eq hx hy hE
    (pathVars_canonicalFamily_eq_of_rawGate_eq gates fuel ρ σ x y hx hy hraw)

/-- A fresh shared query together with the first raw canonical gate segment that contains it.
`none` is retained in the total definition until origin existence is proved. -/
abbrev FreshQueryAnnotation (n G : ℕ) := Fin n × Option (Fin G)

/-- First gate, in the canonical padded order, whose raw execution path queries `v`. -/
def firstGateOrigin? {n G : ℕ} (trees : Fin G → BoolDecisionTree n)
    (x : Fin n → Bool) (v : Fin n) : Option (Fin G) :=
  (List.finRange G).find? fun g => v ∈
    CommonTree.queryVars (CommonTree.ofBool (trees g)) x

/-- Annotate every genuinely fresh read-once query with its first raw gate of origin. -/
def annotatedFreshQueries {n G : ℕ} (σ : Restriction n)
    (trees : Fin G → BoolDecisionTree n) (x : Fin n → Bool) :
    List (FreshQueryAnnotation n G) :=
  (CommonTree.queryVars
    (CommonTree.readOnce σ (CommonTree.commonRefineFin trees)) x).map
      fun v => (v, firstGateOrigin? trees x v)

/-- Origin annotation does not alter, reorder, duplicate, or discard the fresh query path. -/
theorem annotatedFreshQueries_map_fst {n G : ℕ} (σ : Restriction n)
    (trees : Fin G → BoolDecisionTree n) (x : Fin n → Bool) :
    (annotatedFreshQueries σ trees x).map Prod.fst =
      CommonTree.queryVars
        (CommonTree.readOnce σ (CommonTree.commonRefineFin trees)) x := by
  simp [annotatedFreshQueries, List.map_map, Function.comp_def]

/-- The annotated fresh-variable stream remains duplicate-free. -/
theorem annotatedFreshQueries_vars_nodup {n G : ℕ} (σ : Restriction n)
    (trees : Fin G → BoolDecisionTree n) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) :
    ((annotatedFreshQueries σ trees x).map Prod.fst).Nodup := by
  rw [annotatedFreshQueries_map_fst]
  exact CommonTree.queryVars_readOnce_nodup σ _ x hext

/-- Every retained fresh query has a genuine raw gate segment of origin. -/
theorem firstGateOrigin_isSome_of_mem_readOnce {n G : ℕ} (σ : Restriction n)
    (trees : Fin G → BoolDecisionTree n) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) {v : Fin n}
    (hv : v ∈ CommonTree.queryVars
      (CommonTree.readOnce σ (CommonTree.commonRefineFin trees)) x) :
    (firstGateOrigin? trees x v).isSome = true := by
  have hraw := CommonTree.mem_queryVars_of_mem_readOnce σ
    (CommonTree.commonRefineFin trees) x hext hv
  rw [CommonTree.queryVars_commonRefineFin] at hraw
  obtain ⟨segment, hsegment, hvsegment⟩ := List.mem_flatten.mp hraw
  obtain ⟨tree, htree, rfl⟩ := List.mem_map.mp hsegment
  obtain ⟨g, hg⟩ := List.mem_ofFn.mp htree
  subst tree
  apply List.find?_isSome.mpr
  refine ⟨g, List.mem_finRange g, ?_⟩
  simpa using hvsegment

/-- Shared boundary bookkeeping: one run count per gate and one term multiplicity per gate/term. -/
abbrev CommonBoundaryLabel (d G m : ℕ) :=
  (Fin G → Fin (d + 1)) × (Fin G → Fin m → Fin (d + 1))

/-- The full finite common witness label: one shared bit transcript, one literal position per fresh
query, and polynomial boundary data.  The position component is necessary: without it, even the
single term `¬x₀ ∧ ¬x₁` has equal endpoint/transcript/boundary data from two different roots while
querying different variables (see `ComputationalDepthMultiSwitchingCompactLabelCounterexample`). -/
abbrev CommonBadPathLabel (w d G m : ℕ) :=
  CommonTree.FinitePathLabel d × (Fin d → Fin w) × CommonBoundaryLabel d G m

/-- Exact cardinality of the shared gate/term boundary bookkeeping. -/
theorem card_commonBoundaryLabel (d G m : ℕ) :
    Fintype.card (CommonBoundaryLabel d G m) =
      (d + 1) ^ G * ((d + 1) ^ m) ^ G := by
  simp [CommonBoundaryLabel, Fintype.card_prod]

/-- Exact common-witness label count.  The exponential transcript factor occurs once; all
gate/term identity information is in the displayed fixed-parameter polynomial factors. -/
theorem card_commonBadPathLabel (w d G m : ℕ) :
    Fintype.card (CommonBadPathLabel w d G m) =
      ((d + 1) * 2 ^ d) * w ^ d * ((d + 1) ^ G * ((d + 1) ^ m) ^ G) := by
  rw [Fintype.card_prod, CommonTree.card_finitePathLabel, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, card_commonBoundaryLabel]
  simp only [Fintype.card_fin]
  ring

/-- Assemble the shared transcript and boundary tables without duplicating path bits per gate. -/
def commonBadPathPack {w d G m : ℕ}
    (path : CommonTree.PathLabel d)
    (positions : Fin d → Fin w)
    (gateRuns : Fin G → Fin (d + 1))
    (termCounts : Fin G → Fin m → Fin (d + 1)) : CommonBadPathLabel w d G m :=
  (path.toFinite, positions, (gateRuns, termCounts))

/-- The common packing is injective once its three mathematical components agree. -/
theorem commonBadPathPack_eq_iff {w d G m : ℕ}
    {p q : CommonTree.PathLabel d}
    {pos₁ pos₂ : Fin d → Fin w}
    {gr₁ gr₂ : Fin G → Fin (d + 1)}
    {tc₁ tc₂ : Fin G → Fin m → Fin (d + 1)} :
    commonBadPathPack p pos₁ gr₁ tc₁ = commonBadPathPack q pos₂ gr₂ tc₂ ↔
      p = q ∧ pos₁ = pos₂ ∧ gr₁ = gr₂ ∧ tc₁ = tc₂ := by
  constructor
  · intro h
    exact ⟨CommonTree.PathLabel.toFinite_injective (congrArg Prod.fst h),
      congrArg (fun z => z.2.1) h, congrArg (fun z => z.2.2.1) h,
      congrArg (fun z => z.2.2.2) h⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

/-- Every real gate segment fits inside the total common-path depth. -/
theorem gateTrace_length_le_commonDepth {n G : ℕ}
    (trees : Fin G → BoolDecisionTree n) (x : Fin n → Bool) (g : Fin G) :
    (CommonTree.trace (CommonTree.ofBool (trees g)) x).length ≤
      CommonTree.depth (CommonTree.commonRefineFin trees) := by
  calc
    (CommonTree.trace (CommonTree.ofBool (trees g)) x).length
        ≤ ((List.ofFn trees).map fun t =>
            (CommonTree.trace (CommonTree.ofBool t) x).length).sum := by
          apply List.le_sum_of_mem
          simp
    _ = (CommonTree.trace (CommonTree.commonRefineFin trees) x).length :=
      (CommonTree.trace_commonRefineFin_length trees x).symm
    _ ≤ CommonTree.depth (CommonTree.commonRefineFin trees) :=
      CommonTree.trace_length_le_depth _ _

/-- The actual ordered common-refinement execution supplies the gate-run component of the label:
the `g`th entry is precisely the length of the `g`th canonical tree segment. -/
def commonGateRunCounts {n G : ℕ} (trees : Fin G → BoolDecisionTree n)
    (x : Fin n → Bool) :
    Fin G → Fin (CommonTree.depth (CommonTree.commonRefineFin trees) + 1) :=
  fun g => ⟨(CommonTree.trace (CommonTree.ofBool (trees g)) x).length,
    Nat.lt_succ_of_le (gateTrace_length_le_commonDepth trees x g)⟩

@[simp] theorem commonGateRunCounts_val {n G : ℕ}
    (trees : Fin G → BoolDecisionTree n) (x : Fin n → Bool) (g : Fin G) :
    (commonGateRunCounts trees x g).1 =
      (CommonTree.trace (CommonTree.ofBool (trees g)) x).length := rfl

/-- Per-gate term multiplicities along the actual assignment-followed canonical executions.
Every count is bounded by the shared (unnormalized) common-refinement depth, so the table is a
genuine inhabitant of the polynomial boundary-label space rather than a cardinality placeholder. -/
def commonTermCounts {n G m : ℕ} (gates : Fin G → List (Clause n))
    (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool) :
    Fin G → Fin m →
      Fin (CommonTree.depth
        (CommonTree.commonRefineFin (fun g => canonicalDT (gates g) fuel σ)) + 1) :=
  fun g j => ⟨((runWitSeq (gates g) fuel σ x).map Prod.snd).count j.1, by
    apply Nat.lt_succ_of_le
    calc
      ((runWitSeq (gates g) fuel σ x).map Prod.snd).count j.1
          ≤ ((runWitSeq (gates g) fuel σ x).map Prod.snd).length := List.count_le_length
      _ = (CommonTree.queryVars
          (CommonTree.ofBool (canonicalDT (gates g) fuel σ)) x).length := by
            simp only [List.length_map, runWitSeq_length_eq_queryVars]
      _ ≤ CommonTree.depth
          (CommonTree.commonRefineFin (fun g => canonicalDT (gates g) fuel σ)) :=
            by
              rw [← CommonTree.trace_length_eq_queryVars_length]
              exact gateTrace_length_le_commonDepth
                (fun g => canonicalDT (gates g) fuel σ) x g⟩

@[simp] theorem commonTermCounts_val {n G m : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    (x : Fin n → Bool) (g : Fin G) (j : Fin m) :
    (commonTermCounts gates fuel σ x g j).1 =
      ((runWitSeq (gates g) fuel σ x).map Prod.snd).count j.1 := rfl

/-- Corrected multiplicity table: count `(gate,term)` keys only on the globally fresh stream.
Unlike `commonTermCounts` (the raw diagnostic table), this is the component consumed by the compact
common label. -/
def freshTermCounts {n G m d : ℕ} (gates : Fin G → List (Clause n))
    (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool)
    (hlen : (freshTaggedWitSeq gates fuel σ x).length ≤ d) :
    Fin G → Fin m → Fin (d + 1) :=
  fun g j => ⟨(freshTaggedWitSeq gates fuel σ x).countP
      (fun e => e.1 = g && e.2.2 = j.1), by
    apply Nat.lt_succ_of_le
    exact (List.countP_le_length).trans hlen⟩

@[simp] theorem freshTermCounts_val {n G m d : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    (x : Fin n → Bool) (hlen : (freshTaggedWitSeq gates fuel σ x).length ≤ d)
    (g : Fin G) (j : Fin m) :
    (freshTermCounts gates fuel σ x hlen g j).1 =
      (freshTaggedWitSeq gates fuel σ x).countP
        (fun e => e.1 = g && e.2.2 = j.1) := rfl

/-- Equality of the actual finite compact-label table recovers the complete ordered key stream.
Indices outside `Fin m` contribute zero because every gate has at most `m` terms. -/
theorem freshTaggedWitSeq_keys_eq_of_freshTermCounts_eq {n G m d : ℕ}
    (gates : Fin G → List (Clause n)) (hnd : ∀ g, (gates g).Nodup)
    (hgate : ∀ g, (gates g).length ≤ m)
    (fuel : ℕ) (ρ σ : Restriction n) (x y : Fin n → Bool)
    (hlenρ : (freshTaggedWitSeq gates fuel ρ x).length ≤ d)
    (hlenσ : (freshTaggedWitSeq gates fuel σ y).length ≤ d)
    (htable : freshTermCounts (m := m) gates fuel ρ x hlenρ =
      freshTermCounts (m := m) gates fuel σ y hlenσ) :
    (freshTaggedWitSeq gates fuel ρ x).map taggedWitKey =
      (freshTaggedWitSeq gates fuel σ y).map taggedWitKey := by
  apply freshTaggedWitSeq_keys_eq_of_count_eq gates hnd fuel ρ σ x y
  intro g j
  by_cases hj : j < m
  · have hentry := congrFun (congrFun htable g) ⟨j, hj⟩
    exact congrArg Fin.val hentry
  · have zeroCount (τ : Restriction n) (z : Fin n → Bool)
        (e : TaggedWitEntry G)
        (he : e ∈ freshTaggedWitSeq gates fuel τ z) : e.2.2 ≠ j := by
      intro heq
      have hlt := freshTaggedWitSeq_termIdx_lt gates hnd hgate fuel τ z he
      exact hj (heq ▸ hlt)
    have hzρ : (freshTaggedWitSeq gates fuel ρ x).countP
        (fun e => e.1 = g && e.2.2 = j) = 0 := by
      rw [← count_map_taggedWitKey]
      apply List.count_eq_zero.mpr
      intro hk
      obtain ⟨e, he, heq⟩ := List.mem_map.mp hk
      have hterm := congrArg Prod.snd heq
      exact zeroCount ρ x e he hterm
    have hzσ : (freshTaggedWitSeq gates fuel σ y).countP
        (fun e => e.1 = g && e.2.2 = j) = 0 := by
      rw [← count_map_taggedWitKey]
      apply List.count_eq_zero.mpr
      intro hk
      obtain ⟨e, he, heq⟩ := List.mem_map.mp hk
      have hterm := congrArg Prod.snd heq
      exact zeroCount σ y e he hterm
    exact hzρ.trans hzσ.symm

/-- Pad the globally fresh literal-position stream to the fixed `Fin d → Fin w` label component. -/
def freshPositionCode {n G w d : ℕ} [NeZero w]
    (gates : Fin G → List (Clause n))
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool)
    (hlen : (freshTaggedWitSeq gates fuel σ x).length ≤ d) : Fin d → Fin w :=
  fun i =>
    if hi : i.1 < (freshTaggedWitSeq gates fuel σ x).length then
      ⟨(freshTaggedWitSeq gates fuel σ x)[i.1].2.1,
        freshTaggedWitSeq_pos_lt gates hw fuel σ x
          (List.getElem_mem hi)⟩
    else ⟨0, NeZero.pos w⟩

/-- Equal padded position codes and equal genuine lengths recover the unpadded position stream. -/
theorem freshPositions_eq_of_code_eq {n G w d : ℕ} [NeZero w]
    (gates : Fin G → List (Clause n))
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (fuel : ℕ) (ρ σ : Restriction n) (x y : Fin n → Bool)
    (hlenρ : (freshTaggedWitSeq gates fuel ρ x).length ≤ d)
    (hlenσ : (freshTaggedWitSeq gates fuel σ y).length ≤ d)
    (hsize : (freshTaggedWitSeq gates fuel ρ x).length =
      (freshTaggedWitSeq gates fuel σ y).length)
    (hcode : freshPositionCode gates hw fuel ρ x hlenρ =
      freshPositionCode gates hw fuel σ y hlenσ) :
    (freshTaggedWitSeq gates fuel ρ x).map (fun e => e.2.1) =
      (freshTaggedWitSeq gates fuel σ y).map (fun e => e.2.1) := by
  apply List.ext_get
  · simpa using hsize
  · intro i hiρ hiσ
    have hiρ' : i < (freshTaggedWitSeq gates fuel ρ x).length := by
      simpa using hiρ
    have hid : i < d := hiρ'.trans_le hlenρ
    have hentry := congrFun hcode ⟨i, hid⟩
    have hiσ' : i < (freshTaggedWitSeq gates fuel σ y).length := by
      simpa [hsize] using hiρ'
    simpa [freshPositionCode, hiρ', hiσ'] using congrArg Fin.val hentry

/-- The two finite corrected components recover the complete globally fresh tagged witness. -/
theorem freshTaggedWitSeq_eq_of_codes {n G w m d : ℕ} [NeZero w]
    (gates : Fin G → List (Clause n)) (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hgate : ∀ g, (gates g).length ≤ m)
    (fuel : ℕ) (ρ σ : Restriction n) (x y : Fin n → Bool)
    (hlenρ : (freshTaggedWitSeq gates fuel ρ x).length ≤ d)
    (hlenσ : (freshTaggedWitSeq gates fuel σ y).length ≤ d)
    (hsize : (freshTaggedWitSeq gates fuel ρ x).length =
      (freshTaggedWitSeq gates fuel σ y).length)
    (hpos : freshPositionCode gates hw fuel ρ x hlenρ =
      freshPositionCode gates hw fuel σ y hlenσ)
    (hcount : freshTermCounts (m := m) gates fuel ρ x hlenρ =
      freshTermCounts (m := m) gates fuel σ y hlenσ) :
    freshTaggedWitSeq gates fuel ρ x = freshTaggedWitSeq gates fuel σ y := by
  apply taggedWitEntry_list_eq_of_key_pos
  · exact freshTaggedWitSeq_keys_eq_of_freshTermCounts_eq gates hnd hgate fuel
      ρ σ x y hlenρ hlenσ hcount
  · exact freshPositions_eq_of_code_eq gates hw fuel ρ σ x y hlenρ hlenσ hsize hpos

/-- Corrected finite position/count data determines the normalized canonical-family query set. -/
theorem canonicalFamily_pathVars_eq_of_codes {n G w m d : ℕ} [NeZero w]
    (gates : Fin G → List (Clause n)) (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hgate : ∀ g, (gates g).length ≤ m)
    (fuel : ℕ) (ρ σ : Restriction n) (x y : Fin n → Bool)
    (hx : Rung4Restriction.Extends ρ x) (hy : Rung4Restriction.Extends σ y)
    (hlenρ : (freshTaggedWitSeq gates fuel ρ x).length ≤ d)
    (hlenσ : (freshTaggedWitSeq gates fuel σ y).length ≤ d)
    (hsize : (freshTaggedWitSeq gates fuel ρ x).length =
      (freshTaggedWitSeq gates fuel σ y).length)
    (hpos : freshPositionCode gates hw fuel ρ x hlenρ =
      freshPositionCode gates hw fuel σ y hlenσ)
    (hcount : freshTermCounts (m := m) gates fuel ρ x hlenρ =
      freshTermCounts (m := m) gates fuel σ y hlenσ) :
    CommonTree.pathVars ρ (canonicalFamilyTree gates fuel ρ) x =
      CommonTree.pathVars σ (canonicalFamilyTree gates fuel σ) y := by
  rw [← freshTaggedWitSeq_vars_eq_pathVars gates fuel ρ x hx,
    ← freshTaggedWitSeq_vars_eq_pathVars gates fuel σ y hy]
  exact congrArg (fun es => (es.filterMap (taggedWitVar? gates)).toFinset)
    (freshTaggedWitSeq_eq_of_codes gates hnd hw hgate fuel ρ σ x y
      hlenρ hlenσ hsize hpos hcount)

/-- Endpoint equality plus the corrected finite witness components recovers the root restriction. -/
theorem canonicalFamily_endpoint_inj_of_codes {n G w m d : ℕ} [NeZero w]
    (gates : Fin G → List (Clause n)) (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hgate : ∀ g, (gates g).length ≤ m)
    (fuel : ℕ) (ρ σ : Restriction n) (x y : Fin n → Bool)
    (hx : Rung4Restriction.Extends ρ x) (hy : Rung4Restriction.Extends σ y)
    (hlenρ : (freshTaggedWitSeq gates fuel ρ x).length ≤ d)
    (hlenσ : (freshTaggedWitSeq gates fuel σ y).length ≤ d)
    (hE : CommonTree.pathEndpoint ρ (canonicalFamilyTree gates fuel ρ) x =
      CommonTree.pathEndpoint σ (canonicalFamilyTree gates fuel σ) y)
    (hsize : (freshTaggedWitSeq gates fuel ρ x).length =
      (freshTaggedWitSeq gates fuel σ y).length)
    (hpos : freshPositionCode gates hw fuel ρ x hlenρ =
      freshPositionCode gates hw fuel σ y hlenσ)
    (hcount : freshTermCounts (m := m) gates fuel ρ x hlenρ =
      freshTermCounts (m := m) gates fuel σ y hlenσ) : ρ = σ := by
  exact CommonTree.pathEndpoint_inj_of_pathVars_eq hx hy hE
    (canonicalFamily_pathVars_eq_of_codes gates hnd hw hgate fuel ρ σ x y hx hy
      hlenρ hlenσ hsize hpos hcount)

/-- The actual finite label for a normalized canonical-family path.  The shared path component
stores the bit transcript and its genuine length, the position component stores the fresh literal
positions, and the term table stores fresh `(gate,term)` multiplicities.  Gate-run counts are set to
zero because reconstruction does not need them; retaining their slot keeps compatibility with the
earlier boundary-label API and only weakens the displayed cardinality bound. -/
def canonicalCommonBadPathLabel {n G w m d : ℕ} [NeZero w]
    (gates : Fin G → List (Clause n))
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x)
    (hdepth : (CommonTree.trace
      (CommonTree.readOnce σ (canonicalFamilyTree gates fuel σ)) x).length ≤ d) :
    CommonBadPathLabel w d G m :=
  let hlen : (freshTaggedWitSeq gates fuel σ x).length ≤ d :=
    (freshTaggedWitSeq_length_eq_trace_readOnce gates fuel σ x hext).trans_le hdepth
  commonBadPathPack
    ⟨CommonTree.trace
      (CommonTree.readOnce σ (canonicalFamilyTree gates fuel σ)) x, hdepth⟩
    (freshPositionCode gates hw fuel σ x hlen)
    (fun _ => 0)
    (freshTermCounts (m := m) gates fuel σ x hlen)

/-- Equality of concrete compact labels determines the root once the normalized endpoints agree.
This is the complete reconstruction theorem for the corrected label: no injectivity premise remains. -/
theorem canonicalFamily_endpoint_inj_of_label {n G w m d : ℕ} [NeZero w]
    (gates : Fin G → List (Clause n)) (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hgate : ∀ g, (gates g).length ≤ m)
    (fuel : ℕ) (ρ σ : Restriction n) (x y : Fin n → Bool)
    (hx : Rung4Restriction.Extends ρ x) (hy : Rung4Restriction.Extends σ y)
    (hdepthρ : (CommonTree.trace
      (CommonTree.readOnce ρ (canonicalFamilyTree gates fuel ρ)) x).length ≤ d)
    (hdepthσ : (CommonTree.trace
      (CommonTree.readOnce σ (canonicalFamilyTree gates fuel σ)) y).length ≤ d)
    (hE : CommonTree.pathEndpoint ρ (canonicalFamilyTree gates fuel ρ) x =
      CommonTree.pathEndpoint σ (canonicalFamilyTree gates fuel σ) y)
    (hlabel : canonicalCommonBadPathLabel (m := m) gates hw fuel ρ x hx hdepthρ =
      canonicalCommonBadPathLabel (m := m) gates hw fuel σ y hy hdepthσ) : ρ = σ := by
  let hlenρ : (freshTaggedWitSeq gates fuel ρ x).length ≤ d :=
    (freshTaggedWitSeq_length_eq_trace_readOnce gates fuel ρ x hx).trans_le hdepthρ
  let hlenσ : (freshTaggedWitSeq gates fuel σ y).length ≤ d :=
    (freshTaggedWitSeq_length_eq_trace_readOnce gates fuel σ y hy).trans_le hdepthσ
  have hpacked :
      commonBadPathPack
          ⟨CommonTree.trace
            (CommonTree.readOnce ρ (canonicalFamilyTree gates fuel ρ)) x, hdepthρ⟩
          (freshPositionCode gates hw fuel ρ x hlenρ)
          (fun _ => 0)
          (freshTermCounts (m := m) gates fuel ρ x hlenρ) =
        commonBadPathPack
          ⟨CommonTree.trace
            (CommonTree.readOnce σ (canonicalFamilyTree gates fuel σ)) y, hdepthσ⟩
          (freshPositionCode gates hw fuel σ y hlenσ)
          (fun _ => 0)
          (freshTermCounts (m := m) gates fuel σ y hlenσ) := by
    simpa [canonicalCommonBadPathLabel, hlenρ, hlenσ] using hlabel
  obtain ⟨hpath, hpos, _, hcount⟩ := commonBadPathPack_eq_iff.mp hpacked
  have hsize : (freshTaggedWitSeq gates fuel ρ x).length =
      (freshTaggedWitSeq gates fuel σ y).length := by
    rw [freshTaggedWitSeq_length_eq_trace_readOnce gates fuel ρ x hx,
      freshTaggedWitSeq_length_eq_trace_readOnce gates fuel σ y hy]
    exact congrArg (fun p : CommonTree.PathLabel d => p.1.length) hpath
  exact canonicalFamily_endpoint_inj_of_codes gates hnd hw hgate fuel ρ σ x y hx hy
    hlenρ hlenσ hE hsize hpos hcount

variable {n : ℕ}

/-- The finite-label count consumed by a genuine common bad-path encoder.  The sole remaining
semantic premise is injectivity of `(endpoint, shared witness label)` on the chosen bad set. -/
theorem commonBadPath_count {w d G m : ℕ}
    (endpoint : Restriction n → Restriction n)
    (label : Restriction n → CommonBadPathLabel w d G m)
    {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, endpoint ρ ∈ Short)
    (hrec : ∀ ρ ∈ Bad, ∀ σ ∈ Bad,
      endpoint ρ = endpoint σ → label ρ = label σ → ρ = σ) :
    Bad.card ≤ Short.card *
      (((d + 1) * 2 ^ d) * w ^ d * ((d + 1) ^ G * ((d + 1) ^ m) ^ G)) := by
  classical
  apply card_bad_le_label_card endpoint label
  · exact le_of_eq (card_commonBadPathLabel w d G m)
  · exact hmem
  · exact hrec

/-- Common bad-path count with endpoint injectivity discharged.

The common endpoint fixes exactly the fresh coordinates of the normalized path.  Consequently its
root is recovered by re-freeing those coordinates.  A compact label therefore need only determine
the selected coordinate set; endpoint injectivity is no longer a separate combinatorial premise. -/
theorem commonBadPath_count_of_pathVars {w d G m : ℕ} {α : Type}
    (tree : Restriction n → CommonTree n α)
    (assignment : Restriction n → (Fin n → Bool))
    (label : Restriction n → CommonBadPathLabel w d G m)
    {Bad Short : Finset (Restriction n)}
    (hext : ∀ ρ ∈ Bad, Rung4Restriction.Extends ρ (assignment ρ))
    (hmem : ∀ ρ ∈ Bad,
      CommonTree.pathEndpoint ρ (tree ρ) (assignment ρ) ∈ Short)
    (hvars : ∀ ρ ∈ Bad, ∀ σ ∈ Bad, label ρ = label σ →
      CommonTree.pathVars ρ (tree ρ) (assignment ρ) =
        CommonTree.pathVars σ (tree σ) (assignment σ)) :
    Bad.card ≤ Short.card *
      (((d + 1) * 2 ^ d) * w ^ d * ((d + 1) ^ G * ((d + 1) ^ m) ^ G)) := by
  apply commonBadPath_count
    (endpoint := fun ρ => CommonTree.pathEndpoint ρ (tree ρ) (assignment ρ))
    (label := label) hmem
  intro ρ hρ σ hσ hE hlabel
  exact CommonTree.pathEndpoint_inj_of_pathVars_eq
    (hext ρ hρ) (hext σ hσ) hE (hvars ρ hρ σ hσ hlabel)

/-- Concrete canonical-family counting theorem.  All reconstruction data is now supplied by the
explicit label, so the sole remaining combinatorial obligation is to map each bad root's normalized
endpoint into the proposed short set. -/
theorem canonicalCommonBadPath_count {w d G m : ℕ} [NeZero w]
    (gates : Fin G → List (Clause n)) (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hgate : ∀ g, (gates g).length ≤ m)
    (fuel : ℕ) (assignment : Restriction n → (Fin n → Bool))
    (hext : ∀ ρ, Rung4Restriction.Extends ρ (assignment ρ))
    (hdepth : ∀ ρ, (CommonTree.trace
      (CommonTree.readOnce ρ (canonicalFamilyTree gates fuel ρ))
        (assignment ρ)).length ≤ d)
    {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad,
      CommonTree.pathEndpoint ρ (canonicalFamilyTree gates fuel ρ) (assignment ρ) ∈ Short) :
    Bad.card ≤ Short.card *
      (((d + 1) * 2 ^ d) * w ^ d * ((d + 1) ^ G * ((d + 1) ^ m) ^ G)) := by
  apply commonBadPath_count
    (endpoint := fun ρ => CommonTree.pathEndpoint ρ
      (canonicalFamilyTree gates fuel ρ) (assignment ρ))
    (label := fun ρ => canonicalCommonBadPathLabel (m := m) gates hw fuel ρ
      (assignment ρ) (hext ρ) (hdepth ρ)) hmem
  intro ρ _ σ _ hE hlabel
  exact canonicalFamily_endpoint_inj_of_label gates hnd hw hgate fuel ρ σ
    (assignment ρ) (assignment σ) (hext ρ) (hext σ) (hdepth ρ) (hdepth σ)
    hE hlabel

end PallLean.Paper93.DeepMath.PathB.MultiSwitching

#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.card_commonBadPathLabel
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.runWitSeq_length_eq_queryVars
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.runWitSeq_termIndices_pairwise
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.runWitSeq_eq_of_positions_count
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.rawQueryVars_toFinset_eq_of_positions_count
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.pathVars_canonicalFamily_eq_of_rawGate_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalFamily_endpoint_inj_of_rawGate_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.witDecode_runWitSeq
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.mem_witDecode_runWitSeq_of_mem_queryVars
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.annotatedFreshQueries_map_fst
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.annotatedFreshQueries_vars_nodup
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.firstGateOrigin_isSome_of_mem_readOnce
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonBadPathPack_eq_iff
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.gateTrace_length_le_commonDepth
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonGateRunCounts_val
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonTermCounts_val
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.freshTermCounts_val
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.freshTaggedWitSeq_length_eq_trace_readOnce
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalFamily_endpoint_inj_of_label
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonBadPath_count
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonBadPath_count_of_pathVars
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalCommonBadPath_count
