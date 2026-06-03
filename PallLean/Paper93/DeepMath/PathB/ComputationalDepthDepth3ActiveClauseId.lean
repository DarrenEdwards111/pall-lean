import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestDecoder

/-!
# The active-clause identifier: what it is, and the irreducible lift

The decoder needs, at each step, the active clause (to turn a `(position, bit)` label into the
queried variable `litVar ℓ`).  The identifier **from a state** is exactly `activeTermLit` — the
canonical first free literal of the first live (non-falsified, has-free-literal) clause — and it is
fully sound:

* `deepestPath_follows_identifier` — the deepest path's step *is* the identifier: at a branching
  state with `activeTermLit cs σ = some ℓ`, `deepestPath cs (fuel+1) σ = (litVar ℓ, b) :: rest`.  So
  the path follows `activeTermLit` exactly, by construction.
* `freeOn_fixVar_active` (from `…DeepestDecoder`) — given the identifier's `ℓ`, re-freeing `litVar ℓ`
  recovers the prior state.

So *given the intermediate state* `σ_k`, identification + recovery are immediate: `ℓ_k =
activeTermLit cs σ_k`, then re-free.

## The irreducible lift (honest)

The decoder does **not** have the intermediate states — only the *end-state* `σ_s` and the `(2w)^s`
label.  Lifting "identifier from a state" to "identifier from the end-state" is the forward-scan
invariant of Håstad's switching lemma: scanning clauses in order, the *first live clause in the
restriction reconstructed so far* equals the active clause at the corresponding step, so freeing its
labelled path-variables advances the reconstruction one step toward `ρ`.

Proving that invariant — for general (non-falsify) branches, where a `true` step satisfies and so the
queried variable carries no false literal to read off — is the genuine research core.  It is **not**
discharged here and **not** faked.  Everything *around* it is proved: the identifier from a state
(`activeTermLit`), the path following it (`deepestPath_follows_identifier`), the recovery
(`freeOn_fixVar_active`), and the special cases where the lift *is* free — the falsify path
(`decodedSel_eq_replaySel`) and read-once (`falsified_iff_active`).
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The deepest path follows the identifier.**  At a branching state (no satisfied term, an active
literal `ℓ`), the deepest path's next step queries exactly `litVar ℓ = litVar (activeTermLit cs σ)` —
the path is driven by the active-clause identifier `activeTermLit`, by construction. -/
theorem deepestPath_follows_identifier {cs : List (Clause n)} {σ : Fin n → Option Bool}
    {ℓ : Rung4Literal n} {fuel : ℕ}
    (hany : SwitchingCounting.anyTermSat cs σ = false)
    (hatl : SwitchingCounting.activeTermLit cs σ = some ℓ) :
    ∃ (b : Bool) (rest : List (Fin n × Bool)),
      deepestPath cs (fuel + 1) σ = (litVar ℓ, b) :: rest := by
  unfold SwitchingCounting.activeTermLit at hatl
  cases hact : SwitchingCounting.activeTerm cs σ with
  | none => rw [hact] at hatl; simp at hatl
  | some T =>
    rw [hact] at hatl
    rw [deepestPath]
    simp only [hany, Bool.false_eq_true, if_false, hact, hatl]
    split
    · exact ⟨false, _, rfl⟩
    · exact ⟨true, _, rfl⟩

/-- **Identification + recovery from a state.**  Given the intermediate state `σ` with active literal
`ℓ`, the next-state relation inverts: re-freeing `litVar ℓ` recovers `σ` (any bit).  So if the
intermediate states were available, the decoder would be immediate; the missing ingredient is
recovering the states from the end-state (the forward-scan invariant). -/
theorem identifier_recovers {cs : List (Clause n)} {σ : Fin n → Option Bool}
    {ℓ : Rung4Literal n} (h : SwitchingCounting.activeTermLit cs σ = some ℓ) (b : Bool) :
    SwitchingCounting.freeOn (fixVar σ (litVar ℓ) b) {litVar ℓ} = σ :=
  freeOn_fixVar_active h b

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestPath_follows_identifier
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.identifier_recovers
