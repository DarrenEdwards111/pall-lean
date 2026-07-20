import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATCircuitSeparationBridge

/-!
# First blood on the target: an unconditional `cbudget` floor for the SAT slices

The open target is `∀ k, ∃ n, n^k + k < cbudget (SATFamily n)`.  This file proves the
first **unconditional** lower bound on the exact target family — honestly scoped:

* **The dependency tool (proved).**  In the `CGate` model every input access costs a
  `.var` gate, so a circuit of `s` gates reads at most `s` distinct input coordinates:
  `depSet_card_le_cbudget : (depSet f).card ≤ cbudget f`.

* **The flip family (proved).**  `Φ_m := (x₀) ∧ (x₀) ∧ … ∧ (x₀)` (`m` singleton
  clauses) encodes to a word of length `7m+1` under the coordinate codec, with clause
  `j`'s sign bit at position `m + 6j + 6`.  Flipping that one bit yields **exactly** the
  encoding of the formula with clause `j` replaced by `(¬x₀)` — satisfiable flips to
  unsatisfiable (for `m ≥ 2`).  Hence `SATFamily (7m+1)` depends on at least `m`
  coordinates.

* **The floor (proved).**  `m ≤ cbudget (SATFamily (7m+1))` for all `m ≥ 2`; hence
  `cbudget (SATFamily n)` is unbounded in `n`, and the `k = 0` instance of the target
  holds: `∃ n, n^0 + 0 < cbudget (SATFamily n)`.

## Honest scope

The dependency method is structurally capped at `cbudget ≥ n` (a length-`n` slice has
only `n` coordinates), so it can never reach even the `k = 1` rung `n + 1 < cbudget`.
This file establishes the first rung and the first machine-checked engagement of a
lower-bound technique with the exact target object; the superpolynomial statement —
and already the superlinear one — remains the open wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit

variable {n : ℕ}

/-! ### The dependency tool: reading a coordinate costs a gate -/

open Classical in
/-- The coordinates a Boolean function genuinely depends on. -/
noncomputable def depSet (f : (Fin n → Bool) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ x b, f (Function.update x i b) ≠ f x

theorem mem_depSet {f : (Fin n → Bool) → Bool} {i : Fin n} :
    i ∈ depSet f ↔ ∃ x b, f (Function.update x i b) ≠ f x := by
  simp [depSet]

/-- The input variables a circuit reads. -/
def varsOf (c : List (CGate n)) : Finset (Fin n) :=
  (c.filterMap fun g => match g with | CGate.var i => some i | _ => none).toFinset

theorem mem_varsOf {c : List (CGate n)} {i : Fin n} :
    i ∈ varsOf c ↔ CGate.var i ∈ c := by
  simp only [varsOf, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨g, hg, he⟩
    cases g with
    | var j => simp only [Option.some.injEq] at he; rwa [← he]
    | cst b => simp at he
    | un op j => simp at he
    | bin op j k => simp at he
  · intro h
    exact ⟨CGate.var i, h, rfl⟩

theorem varsOf_card_le (c : List (CGate n)) : (varsOf c).card ≤ c.length :=
  le_trans (List.toFinset_card_le _) (List.length_filterMap_le _ _)

/-- A circuit not reading variable `i` is blind to it. -/
theorem runFrom_update (i : Fin n) (b : Bool) (x : Fin n → Bool) :
    ∀ (c : List (CGate n)) (vals : List Bool), CGate.var i ∉ c →
      runFrom (Function.update x i b) vals c = runFrom x vals c := by
  intro c
  induction c with
  | nil => intro vals _; rfl
  | cons g gs ih =>
    intro vals hvar
    have hev : evalGate (Function.update x i b) vals g = evalGate x vals g := by
      cases g with
      | var j =>
        have hne : j ≠ i := by
          intro he
          exact hvar (by rw [he]; exact List.mem_cons_self)
        simp only [evalGate]
        exact Function.update_of_ne hne b x
      | cst b' => rfl
      | un op j => rfl
      | bin op j k => rfl
    show runFrom (Function.update x i b) (vals ++ [evalGate (Function.update x i b) vals g]) gs
      = runFrom x (vals ++ [evalGate x vals g]) gs
    rw [hev, ih (vals ++ [evalGate x vals g]) (fun h => hvar (List.mem_cons_of_mem g h))]

/-- **The dependency floor (proved).**  Every genuinely-read coordinate costs a gate:
`(depSet f).card ≤ cbudget f`. -/
theorem depSet_card_le_cbudget (f : (Fin n → Bool) → Bool) :
    (depSet f).card ≤ cbudget f := by
  have hne : {s | ∃ c : List (CGate n), computes c f ∧ c.length = s}.Nonempty := by
    refine ⟨(compile 0 (dnfFor f)).length, compile 0 (dnfFor f), ?_, rfl⟩
    have h := compile_computes (dnfFor f)
    rwa [show (fun x => eval (dnfFor f) x) = f from funext fun x =>
      congrFun (eval_dnfFor f) x] at h
  obtain ⟨c, hcomp, hclen⟩ := Nat.sInf_mem hne
  have hsub : depSet f ⊆ varsOf c := by
    intro i hi
    obtain ⟨x, b, hxb⟩ := mem_depSet.mp hi
    by_contra hnv
    have hvar : CGate.var i ∉ c := fun h => hnv (mem_varsOf.mpr h)
    have hout : output c (Function.update x i b) = output c x := by
      unfold output
      rw [runFrom_update i b x c [] hvar]
    exact hxb (by rw [← hcomp, ← hcomp, hout])
  calc (depSet f).card ≤ (varsOf c).card := Finset.card_le_card hsub
    _ ≤ c.length := varsOf_card_le c
    _ = cbudget f := hclen

/-! ### The flip family: `m` satisfiability-critical bits in a length-`7m+1` slice -/

/-- The clause `(x₀)`. -/
def oneClause : Clause := [((0 : ℕ), true)]

/-- The clause `(¬x₀)`. -/
def zeroClause : Clause := [((0 : ℕ), false)]

/-- `Φ_m := (x₀) ∧ (x₀) ∧ … ∧ (x₀)`, `m` clauses. -/
def phiSat (m : ℕ) : Formula := List.replicate m oneClause

/-- `Φ_m` with clause `j` replaced by `(¬x₀)`. -/
def phiFlip (m j : ℕ) : Formula :=
  List.replicate j oneClause ++ zeroClause :: List.replicate (m - j - 1) oneClause

theorem satisfiable_phiSat (m : ℕ) : Satisfiable (phiSat m) := by
  refine ⟨fun _ => true, ?_⟩
  rw [evalFormula, List.all_eq_true]
  intro c hc
  rw [List.eq_of_mem_replicate hc]
  rfl

theorem unsat_phiFlip (m j : ℕ) (hm : 2 ≤ m) (hj : j < m) :
    ¬ Satisfiable (phiFlip m j) := by
  rintro ⟨a, ha⟩
  rw [evalFormula, List.all_eq_true] at ha
  have hzero : evalClause a zeroClause = true :=
    ha zeroClause (by
      rw [phiFlip]
      exact List.mem_append_right _ List.mem_cons_self)
  have hone : evalClause a oneClause = true := by
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · refine ha oneClause (List.mem_append_right _ (List.mem_cons_of_mem _ ?_))
      rw [List.mem_replicate]
      exact ⟨by omega, rfl⟩
    · refine ha oneClause (List.mem_append_left _ ?_)
      rw [List.mem_replicate]
      exact ⟨by omega, rfl⟩
  simp only [evalClause, oneClause, zeroClause, List.any_cons, List.any_nil, evalLit,
    Bool.or_false] at hone hzero
  rw [beq_iff_eq] at hone hzero
  rw [hone] at hzero
  simp at hzero

/-- The encoded `(x₀)` clause block: six bits, sign bit last. -/
theorem encodeClause'_one :
    encodeClause' oneClause = [true, false, false, false, false, true] := by
  rfl

/-- The encoded `(¬x₀)` clause block: same first five bits, sign bit last. -/
theorem encodeClause'_zero :
    encodeClause' zeroClause = [true, false, false, false, false, false] := by
  rfl

/-- The five sign-independent bits of a singleton `x₀` clause block. -/
def cPre : List Bool := [true, false, false, false, false]

theorem length_flatten_replicate {α : Type} (l : List α) :
    ∀ k, ((List.replicate k l).flatten).length = k * l.length := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, List.length_append, ih, Nat.succ_mul]
    omega

/-- The sign-bit position of clause `j`. -/
def signPos (m j : ℕ) : ℕ := m + 6 * j + 6

/-- The shared prefix up to (excluding) clause `j`'s sign bit. -/
def flipPre (m j : ℕ) : List Bool :=
  encodeNat m ++ (List.replicate j (encodeClause' oneClause)).flatten ++ cPre

theorem flipPre_length (m j : ℕ) : (flipPre m j).length = signPos m j := by
  rw [flipPre, signPos, List.length_append, List.length_append, encodeNat_length,
    length_flatten_replicate, encodeClause'_one]
  show m + 1 + j * 6 + 5 = m + 6 * j + 6
  omega

/-- Splitting a replicate at position `j`. -/
theorem replicate_split {α : Type} (a : α) {m j : ℕ} (hj : j < m) :
    List.replicate m a = List.replicate j a ++ a :: List.replicate (m - j - 1) a := by
  conv_rhs => rw [← List.replicate_succ, ← List.replicate_add]
  rw [show j + (m - j - 1 + 1) = m from by omega]

/-- The encoding of `Φ_m`, split at clause `j`'s sign bit. -/
theorem encode_phiSat_split (m j : ℕ) (hj : j < m) :
    encodeFormula' (phiSat m)
      = flipPre m j
        ++ true :: (List.replicate (m - j - 1) (encodeClause' oneClause)).flatten := by
  rw [encodeFormula', phiSat, List.length_replicate, List.map_replicate,
    replicate_split (encodeClause' oneClause) hj, List.flatten_append, List.flatten_cons,
    encodeClause'_one, flipPre, encodeClause'_one]
  simp [cPre, List.append_assoc]

/-- The encoding of the flipped formula: identical except the one sign bit. -/
theorem encode_phiFlip_split (m j : ℕ) (hj : j < m) :
    encodeFormula' (phiFlip m j)
      = flipPre m j
        ++ false :: (List.replicate (m - j - 1) (encodeClause' oneClause)).flatten := by
  rw [encodeFormula', phiFlip,
    show (List.replicate j oneClause
        ++ zeroClause :: List.replicate (m - j - 1) oneClause).length = m from by
      simp
      omega]
  rw [List.map_append, List.map_cons, List.map_replicate, List.map_replicate,
    List.flatten_append, List.flatten_cons,
    encodeClause'_one, encodeClause'_zero, flipPre, encodeClause'_one]
  simp [cPre, List.append_assoc]

/-- Setting the element right after a prefix. -/
theorem set_append_cons {α : Type} (A : List α) (x y : α) (B : List α) :
    (A ++ x :: B).set A.length y = A ++ y :: B := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    show a :: ((A ++ x :: B).set A.length y) = a :: (A ++ y :: B)
    rw [ih]

/-- **The one-bit flip identity**: flipping clause `j`'s sign bit in the encoding of
`Φ_m` yields exactly the encoding of the flipped formula. -/
theorem word_flip (m j : ℕ) (hj : j < m) :
    (encodeFormula' (phiSat m)).set (signPos m j) false
      = encodeFormula' (phiFlip m j) := by
  rw [encode_phiSat_split m j hj, encode_phiFlip_split m j hj, ← flipPre_length m j,
    set_append_cons]

theorem encode_phiSat_length (m : ℕ) :
    (encodeFormula' (phiSat m)).length = 7 * m + 1 := by
  rw [encodeFormula', phiSat, List.length_replicate, List.map_replicate,
    List.length_append, encodeNat_length, length_flatten_replicate, encodeClause'_one]
  show m + 1 + m * 6 = 7 * m + 1
  omega

/-! ### The word/vector flip correspondence -/

theorem wordOfFin_getElem (x : Fin n → Bool) (k : ℕ) (h : k < (wordOfFin x).length)
    (hk : k < n) : (wordOfFin x)[k] = x ⟨k, hk⟩ := by
  simp [wordOfFin]

theorem wordOfFin_update (x : Fin n → Bool) (i : Fin n) (b : Bool) :
    wordOfFin (Function.update x i b) = (wordOfFin x).set i.val b := by
  apply List.ext_getElem
  · simp [wordOfFin_length]
  · intro k h1 h2
    have hk : k < n := by
      have := h1
      rwa [wordOfFin_length] at this
    rw [wordOfFin_getElem _ k h1 hk, List.getElem_set]
    by_cases hik : i.val = k
    · rw [if_pos hik]
      have he : (⟨k, hk⟩ : Fin n) = i := Fin.ext hik.symm
      rw [he, Function.update_self]
    · rw [if_neg hik,
        wordOfFin_getElem _ k (by simpa using h2) hk]
      have hne : (⟨k, hk⟩ : Fin n) ≠ i := fun he => hik (by rw [← he])
      rw [Function.update_of_ne hne]

/-! ### The SAT slices depend on every sign bit -/

theorem SATLang_phiSat (m : ℕ) : SATLang (encodeFormula' (phiSat m)) = true := by
  rw [SATLang, decodeFormula'_encodeFormula', if_pos (satisfiable_phiSat m)]

theorem SATLang_phiFlip (m j : ℕ) (hm : 2 ≤ m) (hj : j < m) :
    SATLang (encodeFormula' (phiFlip m j)) = false := by
  rw [SATLang, decodeFormula'_encodeFormula', if_neg (unsat_phiFlip m j hm hj)]

/-- Each sign bit is a genuine dependence of the SAT slice. -/
theorem signPos_mem_depSet (m j : ℕ) (hm : 2 ≤ m) (hj : j < m)
    (hlt : signPos m j < (encodeFormula' (phiSat m)).length) :
    (⟨signPos m j, hlt⟩ : Fin (encodeFormula' (phiSat m)).length)
      ∈ depSet (SATFamily (encodeFormula' (phiSat m)).length) := by
  rw [mem_depSet]
  refine ⟨finOfWord (encodeFormula' (phiSat m)), false, ?_⟩
  rw [SATFamily_apply, SATFamily_apply, wordOfFin_update, wordOfFin_finOfWord]
  show SATLang ((encodeFormula' (phiSat m)).set (signPos m j) false)
      ≠ SATLang (encodeFormula' (phiSat m))
  rw [word_flip m j hj, SATLang_phiSat, SATLang_phiFlip m j hm hj]
  simp

/-- The `m` sign bits give `m` distinct dependent coordinates. -/
theorem depSet_card_ge (m : ℕ) (hm : 2 ≤ m) :
    m ≤ (depSet (SATFamily (encodeFormula' (phiSat m)).length)).card := by
  have hbound : ∀ v ∈ (Finset.range m).image (signPos m),
      v < (encodeFormula' (phiSat m)).length := by
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    rw [Finset.mem_range] at hj
    rw [encode_phiSat_length, signPos]
    omega
  have hsub : Finset.attachFin ((Finset.range m).image (signPos m)) hbound
      ⊆ depSet (SATFamily (encodeFormula' (phiSat m)).length) := by
    intro i hi
    rw [Finset.mem_attachFin, Finset.mem_image] at hi
    obtain ⟨j, hj, hji⟩ := hi
    rw [Finset.mem_range] at hj
    have := signPos_mem_depSet m j hm hj (hji ▸ i.isLt)
    have he : (⟨signPos m j, hji ▸ i.isLt⟩ : Fin (encodeFormula' (phiSat m)).length) = i :=
      Fin.ext hji
    rwa [he] at this
  calc m = (Finset.range m).card := (Finset.card_range m).symm
    _ = ((Finset.range m).image (signPos m)).card :=
        (Finset.card_image_of_injective _ (fun a b hab => by
          simp only [signPos] at hab; omega)).symm
    _ = (Finset.attachFin ((Finset.range m).image (signPos m)) hbound).card :=
        (Finset.card_attachFin _ _).symm
    _ ≤ _ := Finset.card_le_card hsub

/-! ### THE FLOOR: the first unconditional lower bound on the target family -/

/-- **Unconditional linear floor on the exact target.**  For every `m ≥ 2`,
`cbudget (SATFamily (7m+1)) ≥ m`. -/
theorem cbudget_SATFamily_ge (m : ℕ) (hm : 2 ≤ m) :
    m ≤ cbudget (SATFamily (7 * m + 1)) := by
  rw [← encode_phiSat_length m]
  exact le_trans (depSet_card_ge m hm) (depSet_card_le_cbudget _)

/-- `cbudget` of the SAT slices is unbounded. -/
theorem cbudget_SATFamily_unbounded (B : ℕ) : ∃ n, B < cbudget (SATFamily n) :=
  ⟨7 * (B + 2) + 1, lt_of_lt_of_le (by omega) (cbudget_SATFamily_ge (B + 2) (by omega))⟩

/-- The `k = 0` instance of the open target holds. -/
theorem target_k_zero : ∃ n, n ^ 0 + 0 < cbudget (SATFamily n) := by
  obtain ⟨n, hn⟩ := cbudget_SATFamily_unbounded 1
  exact ⟨n, by simpa using hn⟩

end PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor

#print axioms PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor.depSet_card_le_cbudget
#print axioms PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor.cbudget_SATFamily_ge
#print axioms PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor.cbudget_SATFamily_unbounded
#print axioms PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor.target_k_zero
