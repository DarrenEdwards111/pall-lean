import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingFixStable

/-!
# Read-once active-clause identification

For **read-once** clause families (each variable in at most one clause) the active-clause
identification — open in general — is *complete*: the clauses falsified at the end-state
`replayPath cs ρ s` are **exactly** the active clauses `{activeTerm (replayPath cs ρ k) : k < s}`.

The general obstruction was over-counting: with shared literals, a non-active clause containing some
active literal `ℓ_j` is also falsified.  Read-once removes it — a falsified clause's false literal
lies on a path-fixed variable, that variable belongs to a *unique* clause, and that clause is
forced to be the active clause whose step fixed the variable.

* `ReadOnce` — each variable lies in at most one clause;
* `falsified_clause_is_active` — **the ⟹ direction** (the read-once core): a clause falsified at the
  end-state is the active clause of some step `< s`.  Uses fix-stability + "ρ falsifies nothing" to
  locate the false literal's variable in `replaySel`, then read-once to pin its clause;
* `falsified_iff_active` — combined with `termFalsified_of_active_lit_mem` (the ⟸ direction), the
  **complete characterization**: under read-once and "ρ falsifies nothing", a clause is falsified at
  the end-state iff it is active at some step `< s`.

So a decoder reading the end-state can recover the active clauses (the falsified ones) and, via the
position label (`clauseLitAt`/`pivotPosOf`), the active literals — closing `hdec` for the read-once
class.  (Tseitin is *not* read-once, so this does not close the general switching count; it is the
honest tractable case where active-clause identification is provable.)
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- A clause family is **read-once** if each variable lies in at most one clause. -/
def ReadOnce (cs : List (Clause n)) : Prop :=
  ∀ (i : Fin n) (C D : Clause n), C ∈ cs → D ∈ cs →
    (∃ ℓ ∈ C.lits, litVar ℓ = i) → (∃ ℓ ∈ D.lits, litVar ℓ = i) → C = D

/-- `litFalse` depends only on the literal's variable value. -/
theorem litFalse_eq_of_litVar_val {σ τ : Restriction n} {m : Rung4Literal n}
    (h : σ (litVar m) = τ (litVar m)) : litFalse σ m = litFalse τ m := by
  cases m with
  | pos i => simp only [litFalse, Depth3.litFixedVal]; rw [show σ i = τ i from h]
  | neg i => simp only [litFalse, Depth3.litFixedVal]; rw [show σ i = τ i from h]

/-- A variable selected by the replay is the active literal's variable at some step `< s`. -/
theorem mem_replaySel {cs : List (Clause n)} {ρ : Restriction n} {v : Fin n} :
    ∀ s, v ∈ replaySel cs ρ s →
      ∃ k, k < s ∧ ∃ ℓ, activeTermLit cs (replayPath cs ρ k) = some ℓ ∧ litVar ℓ = v := by
  intro s
  induction s with
  | zero => intro h; simp [replaySel] at h
  | succ s ih =>
    intro h
    rw [replaySel, Finset.mem_union] at h
    rcases h with h | h
    · obtain ⟨k, hk, hℓ⟩ := ih h
      exact ⟨k, by omega, hℓ⟩
    · cases hs : activeTermLit cs (replayPath cs ρ s) with
      | none => rw [hs] at h; simp at h
      | some ℓ =>
        rw [hs, Finset.mem_singleton] at h
        exact ⟨s, by omega, ℓ, hs, h.symm⟩

/-- The active term is a member of the clause list. -/
theorem activeTerm_mem {cs : List (Clause n)} {σ : Restriction n} {T : Clause n}
    (h : activeTerm cs σ = some T) : T ∈ cs := by
  have hns := activeTerm_anyTermSat_false h
  have hfind : cs.find? (fun T => !termFalsified σ T && decide (0 < (freeLits σ T).length)) = some T :=
    activeTerm_eq_find hns ▸ h
  exact List.mem_of_find?_eq_some hfind

/-- **Read-once core (⟹).**  A clause falsified at the end-state is the active clause of some step
`< s`.  The false literal's variable was fixed by the path (not by `ρ`, which falsifies nothing), so
it lies in `replaySel`; read-once forces its unique clause to be that step's active clause. -/
theorem falsified_clause_is_active {cs : List (Clause n)} {ρ : Restriction n} (hro : ReadOnce cs)
    (hnf : ∀ T ∈ cs, termFalsified ρ T = false) {C : Clause n} (hC : C ∈ cs) {s : ℕ}
    (hfals : termFalsified (replayPath cs ρ s) C = true) :
    ∃ k, k < s ∧ activeTerm cs (replayPath cs ρ k) = some C := by
  rw [termFalsified, List.any_eq_true] at hfals
  obtain ⟨m, hmC, hmf⟩ := hfals
  -- ρ does not fix litVar m (else m would be false under ρ, falsifying C)
  have hρnone : ρ (litVar m) = none := by
    by_contra hne
    obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.mp hne
    have hstab : replayPath cs ρ s (litVar m) = some b' := by
      have hh := replayPath_fixed_stable (cs := cs) (ρ := ρ) (v := litVar m) (b := b') 0 s
      rw [show replayPath cs ρ 0 = ρ from rfl, Nat.zero_add] at hh
      exact hh hb'
    have heq : ρ (litVar m) = replayPath cs ρ s (litVar m) := by rw [hb', hstab]
    have hfρ : litFalse ρ m = true := by rw [litFalse_eq_of_litVar_val heq]; exact hmf
    have hcf : termFalsified ρ C = true := by
      rw [termFalsified, List.any_eq_true]; exact ⟨m, hmC, hfρ⟩
    rw [hnf C hC] at hcf; exact absurd hcf (by simp)
  -- so litVar m is path-selected
  have hmem : litVar m ∈ replaySel cs ρ s := by
    by_contra hnotin
    have heqo := replayPath_eq_outside cs ρ s hnotin
    rw [hρnone] at heqo
    exact litFalse_litVar_fixed hmf heqo
  obtain ⟨k, hk, ℓ, hℓ, hℓv⟩ := mem_replaySel s hmem
  -- recover the active clause at step k and its literal ℓ
  obtain ⟨T, hTactive, hℓT⟩ : ∃ T, activeTerm cs (replayPath cs ρ k) = some T ∧ ℓ ∈ T.lits := by
    unfold activeTermLit at hℓ
    cases hat : activeTerm cs (replayPath cs ρ k) with
    | none => rw [hat] at hℓ; simp at hℓ
    | some T =>
      rw [hat] at hℓ
      exact ⟨T, rfl, (List.mem_filter.mp (List.mem_of_mem_head? hℓ)).1⟩
  -- read-once: C and T share variable litVar m, so C = T
  have hCT : C = T :=
    hro (litVar m) C T hC (activeTerm_mem hTactive) ⟨m, hmC, rfl⟩ ⟨ℓ, hℓT, hℓv⟩
  exact ⟨k, hk, hCT ▸ hTactive⟩

/-- **Complete read-once characterization.**  Under read-once and "ρ falsifies nothing", a clause is
falsified at the end-state iff it is the active clause of some step `< s`.  This identifies the
active clauses from the end-state — the active-clause identification, for the read-once class. -/
theorem falsified_iff_active {cs : List (Clause n)} {ρ : Restriction n} (hro : ReadOnce cs)
    (hnf : ∀ T ∈ cs, termFalsified ρ T = false) {C : Clause n} (hC : C ∈ cs) {s : ℕ} :
    termFalsified (replayPath cs ρ s) C = true ↔
      ∃ k, k < s ∧ activeTerm cs (replayPath cs ρ k) = some C := by
  constructor
  · exact falsified_clause_is_active hro hnf hC
  · rintro ⟨k, hk, hactive⟩
    obtain ⟨_, hlen⟩ := activeTerm_pred hactive
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, (freeLits (replayPath cs ρ k) C).head? = some ℓ := by
      cases hh : freeLits (replayPath cs ρ k) C with
      | nil => rw [hh] at hlen; simp at hlen
      | cons a _ => exact ⟨a, rfl⟩
    have hatl : activeTermLit cs (replayPath cs ρ k) = some ℓ := by
      unfold activeTermLit; rw [hactive]; exact hℓ
    have hℓC : ℓ ∈ C.lits := (List.mem_filter.mp (List.mem_of_mem_head? hℓ)).1
    exact termFalsified_of_active_lit_mem hk hatl hℓC

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.falsified_clause_is_active
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.falsified_iff_active
