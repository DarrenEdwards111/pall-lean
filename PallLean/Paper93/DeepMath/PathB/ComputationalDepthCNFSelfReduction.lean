import Mathlib

/-!
# Round-4 REPAIR: encoded CNF, restriction size bound, self-reducibility, and the CONDITIONAL obstruction

The round-4 abstraction (`SelfReductionPolarity`) used a truth-table `BF`, which is insufficient — it hides the
encoding size that the whole obstruction is about, and my memo overreached by presenting a size↔polarity "duality"
as *the reason* the fixed-polynomial circuit lower bound sits at `Σ₂ᵖ`.  Classical work (Kannan 1982;
Cai–Watanabe 2004) places it at `Σ₂ᵖ` but does **not** establish that duality as the cause.  This file is the
crisp repair, on **encoded CNF**:

* `restrict` / `restrict_descLen_le` — restriction with a proved encoding-size bound (it never grows the encoding);
* `restrict_correct` / `sat_iff_restrict` — self-reducibility on the encoded objects (not truth tables);
* `wrap` / `wrap_sound` — the greedy verify-wrapper: no false positives (every accept carries a witness);
* `hardwire_needs_length` / `hardwire_conditional` — the **conditional** obstruction ONLY: if a formula literally
  hardwires a circuit description of length `> N`, it cannot itself have length `≤ N`.  We do **not** infer
  `descLen C > N` from any `P/poly` upper bound, and we claim **no** separation.

What this file is: the honest encoded-object version of the round-4 mechanisms plus the conditional size
obstruction.  What it is NOT: a proof about `P/poly`, a claim that the duality explains the `Σ₂ᵖ` placement, or any
progress on `P ≠ NP`.  The uniform target `∃ L ∈ NP, L ∉ P` and its load-bearing lower-bound lemma remain the
undiscovered content; Lean can only verify that after discovery.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CNFSelfReduction

variable {n : ℕ}

/-- A literal: a variable index with a polarity (`true` = positive, `false` = negated). -/
abbrev Lit (n : ℕ) := Fin n × Bool

/-- A clause (disjunction of literals). -/
abbrev Clause (n : ℕ) := List (Lit n)

/-- A CNF formula (conjunction of clauses) — the encoded object. -/
abbrev CNF (n : ℕ) := List (Clause n)

/-- Literal semantics: `(i, b)` is satisfied by `a` iff `a i = b`. -/
def litSat (a : Fin n → Bool) (l : Lit n) : Bool := a l.1 == l.2

/-- Clause semantics (disjunction). -/
def clauseSat (a : Fin n → Bool) (c : Clause n) : Bool := c.any (litSat a)

/-- CNF semantics (conjunction). -/
def eval (φ : CNF n) (a : Fin n → Bool) : Bool := φ.all (clauseSat a)

theorem clauseSat_cons (a : Fin n → Bool) (l : Lit n) (ls : Clause n) :
    clauseSat a (l :: ls) = (litSat a l || clauseSat a ls) := List.any_cons

theorem eval_cons (a : Fin n → Bool) (c : Clause n) (cs : CNF n) :
    eval (c :: cs) a = (clauseSat a c && eval cs a) := List.all_cons

/-- Satisfiability. -/
def Sat (φ : CNF n) : Prop := ∃ a, eval φ a = true

/-- Encoding length: total literal count (an honest size measure that restriction cannot grow). -/
def descLen (φ : CNF n) : ℕ := (φ.map List.length).sum

/-- Restriction: fix variable `i` to `val` — drop clauses satisfied by `(i, val)`, drop the falsified `(i, !val)`
literals from the rest. -/
def restrict (φ : CNF n) (i : Fin n) (val : Bool) : CNF n :=
  (φ.filter (fun c => decide ((i, val) ∉ c))).map (fun c => c.filter (fun l => decide (l.1 ≠ i)))

/-- **Restriction never grows the encoding.** -/
theorem restrict_descLen_le (φ : CNF n) (i : Fin n) (val : Bool) :
    descLen (restrict φ i val) ≤ descLen φ := by
  induction φ with
  | nil => exact le_refl 0
  | cons c cs ih =>
    have hcs : descLen (c :: cs) = c.length + descLen cs := by
      unfold descLen; rw [List.map_cons, List.sum_cons]
    by_cases hc : (i, val) ∈ c
    · have hr : restrict (c :: cs) i val = restrict cs i val := by
        unfold restrict; simp [List.filter_cons, hc]
      rw [hr, hcs]; omega
    · have hr : restrict (c :: cs) i val
          = (c.filter (fun l => decide (l.1 ≠ i))) :: restrict cs i val := by
        unfold restrict; simp [List.filter_cons, hc]
      have hd : descLen ((c.filter (fun l => decide (l.1 ≠ i))) :: restrict cs i val)
          = (c.filter (fun l => decide (l.1 ≠ i))).length + descLen (restrict cs i val) := by
        unfold descLen; rw [List.map_cons, List.sum_cons]
      have h1 : (c.filter (fun l => decide (l.1 ≠ i))).length ≤ c.length := List.length_filter_le _ _
      rw [hr, hd, hcs]; omega

/-- Per-clause restriction correctness. -/
theorem clause_restrict (c : Clause n) (i : Fin n) (val : Bool) (a : Fin n → Bool)
    (hc : (i, val) ∉ c) :
    clauseSat a (c.filter (fun l => decide (l.1 ≠ i))) = clauseSat (Function.update a i val) c := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
    have hls : (i, val) ∉ ls := fun h => hc (List.mem_cons_of_mem l h)
    obtain ⟨j, b⟩ := l
    by_cases hji : j = i
    · subst hji
      have hbv : b ≠ val := fun h => hc (by rw [h]; exact List.mem_cons_self)
      have hfilt : (((j, b) :: ls).filter (fun l => decide (l.1 ≠ j)))
          = ls.filter (fun l => decide (l.1 ≠ j)) := by simp [List.filter_cons]
      rw [hfilt, ih hls, clauseSat_cons]
      have hlit : litSat (Function.update a j val) (j, b) = false := by
        simp only [litSat, Function.update_self]
        cases hb : b <;> cases hv : val <;> simp_all
      rw [hlit, Bool.false_or]
    · have hfilt : (((j, b) :: ls).filter (fun l => decide (l.1 ≠ i)))
          = (j, b) :: ls.filter (fun l => decide (l.1 ≠ i)) := by
        simp [List.filter_cons, hji]
      rw [hfilt, clauseSat_cons, clauseSat_cons, ih hls]
      congr 1
      simp only [litSat, Function.update_of_ne hji]

/-- **Restriction correctness**: evaluating the restriction equals evaluating the original with `x_i := val`. -/
theorem restrict_correct (φ : CNF n) (i : Fin n) (val : Bool) (a : Fin n → Bool) :
    eval (restrict φ i val) a = eval φ (Function.update a i val) := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    unfold eval restrict at *
    by_cases hc : (i, val) ∈ c
    · have hfilter : ((c :: cs).filter (fun c => decide ((i, val) ∉ c)))
          = cs.filter (fun c => decide ((i, val) ∉ c)) := by
        simp [List.filter_cons, hc]
      rw [hfilter]
      have hcsat : clauseSat (Function.update a i val) c = true := by
        unfold clauseSat
        rw [List.any_eq_true]
        exact ⟨(i, val), hc, by simp [litSat, Function.update_self]⟩
      rw [List.all_cons, hcsat, Bool.true_and]
      exact ih
    · have hfilter : ((c :: cs).filter (fun c => decide ((i, val) ∉ c)))
          = c :: cs.filter (fun c => decide ((i, val) ∉ c)) := by
        simp [List.filter_cons, hc]
      rw [hfilter, List.map_cons, List.all_cons, List.all_cons, ih, clause_restrict c i val a hc]

/-- **Self-reducibility on the encoded CNF**: `φ` is satisfiable iff a coordinate-`i` restriction is. -/
theorem sat_iff_restrict (φ : CNF n) (i : Fin n) :
    Sat φ ↔ Sat (restrict φ i false) ∨ Sat (restrict φ i true) := by
  constructor
  · rintro ⟨a, ha⟩
    have hkey : eval (restrict φ i (a i)) a = true := by
      rw [restrict_correct, Function.update_eq_self]; exact ha
    cases hb : a i with
    | false => exact Or.inl ⟨a, by rw [hb] at hkey; exact hkey⟩
    | true => exact Or.inr ⟨a, by rw [hb] at hkey; exact hkey⟩
  · rintro (⟨a, ha⟩ | ⟨a, ha⟩)
    · exact ⟨Function.update a i false, by rw [← restrict_correct]; exact ha⟩
    · exact ⟨Function.update a i true, by rw [← restrict_correct]; exact ha⟩

/-! ## The verify-wrapper (false-negative-only conversion) -/

/-- A purported decider on encoded formulas (a circuit computing a `CNF → Bool`). -/
abbrev Decider (n : ℕ) := CNF n → Bool

/-- The verify-wrapper of a search: run the search, then check the candidate assignment. -/
def wrap (search : CNF n → (Fin n → Bool)) (φ : CNF n) : Bool := eval φ (search φ)

/-- **No false positives.**  Every accepted formula is genuinely satisfiable, with the witness in hand
(NP-checkable) — the polarity-converting property, on encoded objects. -/
theorem wrap_sound (search : CNF n → (Fin n → Bool)) (φ : CNF n) (h : wrap search φ = true) : Sat φ :=
  ⟨search φ, h⟩

/-! ## The CONDITIONAL size obstruction (literal hardwiring only) -/

/-- A formula *literally hardwires* a description of length `s` if its own encoding is at least `s` long
(it contains the description as a component). -/
def Hardwires (φ : CNF n) (s : ℕ) : Prop := s ≤ descLen φ

/-- **The conditional obstruction.**  If a formula literally hardwires a circuit description of length `s > N`,
then its own length exceeds `N`.  (Contrapositive: a length-`≤ N` formula cannot literally hardwire a longer
description.)  This is the ONLY obstruction claimed — it does not infer `s > N` from any `P/poly` upper bound and
proves nothing about `P/poly`. -/
theorem hardwire_needs_length {φ : CNF n} {s N : ℕ} (hs : N < s) (hh : Hardwires φ s) : N < descLen φ :=
  lt_of_lt_of_le hs hh

/-- The same, contrapositive: no length-`≤ N` formula literally hardwires a description longer than `N`. -/
theorem hardwire_conditional {φ : CNF n} {s N : ℕ} (hs : N < s) (hlen : descLen φ ≤ N) :
    ¬ Hardwires φ s := fun hh => absurd (hardwire_needs_length hs hh) (by omega)

end PallLean.Paper93.DeepMath.PathB.CNFSelfReduction

#print axioms PallLean.Paper93.DeepMath.PathB.CNFSelfReduction.sat_iff_restrict
#print axioms PallLean.Paper93.DeepMath.PathB.CNFSelfReduction.wrap_sound
#print axioms PallLean.Paper93.DeepMath.PathB.CNFSelfReduction.hardwire_conditional
#print axioms PallLean.Paper93.DeepMath.PathB.CNFSelfReduction.restrict_descLen_le
