import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceDistinctRowsRecoding

/-!
# The blank-traversal bound, machine-checked (empty-input case)

The head-as-data settlement rested on a "no computation in empty space" fact I argued but did not
check.  This file checks its cleanest complete instance: **a write-free machine on empty input
halts within `|State|` steps or never halts.**

On the all-blank tape (`init M []`) a write-free machine reads `false` at every step and writes
nothing, so its *state* evolves by pure iteration of `blankNext s = (δ s false).1`, independent of
the head (`run_st_tracks`).  Iterating a function on a finite type is eventually periodic within
`|State|` steps (`orbit_bounded`), so the state either reaches a halt state within `|State|` steps
or cycles through non-halt states forever.  Hence `writeFree_empty_halts_fast`: on empty input the
machine's halting is decided by step `|State|` — it cannot compute for longer in empty space.

This is the pure mechanism behind the head-as-data obstruction, checked.  The **general** bound
(arbitrary input, `time ≤ poly(distinctTapes, |x|)`) extends this to a *moving* blank frontier via
crossing sequences — each frontier extension is a distinct tape — which is a larger Hennie-machine
formalization not attempted here.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  This file proves no SAT lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.EmptySpaceHennie

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.TraceDistinctRowsRecoding (WriteFree run_tp_const)

variable {M : Machine}

/-! ## Iterating a function on a finite type is eventually periodic -/

theorem iter_shift {α : Type} (f : α → α) (s : α) {i p : ℕ} (h : f^[i + p] s = f^[i] s) (k : ℕ) :
    f^[i + p + k] s = f^[i + k] s := by
  rw [show i + p + k = k + (i + p) from by ring, Function.iterate_add_apply, h,
    ← Function.iterate_add_apply, show k + i = i + k from by ring]

theorem iter_mod {α : Type} (f : α → α) {i p : ℕ} (hp : 0 < p) {s : α}
    (h : f^[i + p] s = f^[i] s) : ∀ t, f^[i + t] s = f^[i + t % p] s := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rcases lt_or_ge t p with ht | ht
    · rw [Nat.mod_eq_of_lt ht]
    · have key : f^[i + t] s = f^[i + (t - p)] s := by
        rw [show i + t = i + p + (t - p) from by omega]; exact iter_shift f s h (t - p)
      have hmod : t % p = (t - p) % p := by
        conv_lhs => rw [← Nat.sub_add_cancel ht]; rw [Nat.add_mod_right]
      rw [key, ih (t - p) (by omega), hmod]

/-- **The orbit is confined to its first `|α|` iterates.**  For a finite type, every iterate equals
one of the first `Fintype.card α` iterates. -/
theorem orbit_bounded {α : Type} [Fintype α] (f : α → α) (s : α) (t : ℕ) :
    ∃ t' ≤ Fintype.card α, f^[t] s = f^[t'] s := by
  by_cases ht : t ≤ Fintype.card α
  · exact ⟨t, ht, rfl⟩
  · push_neg at ht
    have key : ∀ a b : Fin (Fintype.card α + 1), a.val < b.val → f^[a.val] s = f^[b.val] s →
        ∃ t' ≤ Fintype.card α, f^[t] s = f^[t'] s := by
      intro a b hab hfab
      have hp : 0 < b.val - a.val := by omega
      have hper : f^[a.val + (b.val - a.val)] s = f^[a.val] s := by
        rw [show a.val + (b.val - a.val) = b.val from by omega]; exact hfab.symm
      refine ⟨a.val + (t - a.val) % (b.val - a.val), ?_, ?_⟩
      · have h1 := Nat.mod_lt (t - a.val) hp
        have h2 : b.val ≤ Fintype.card α := by omega
        omega
      · rw [← iter_mod f hp hper (t - a.val), show a.val + (t - a.val) = t from by omega]
    obtain ⟨a, b, hne, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (Fintype.card α + 1) => f^[i.val] s) (by rw [Fintype.card_fin]; omega)
    rcases lt_or_gt_of_ne (fun heq => hne (Fin.val_injective heq)) with hlt | hgt
    · exact key a b hlt hfab
    · exact key b a hgt hfab.symm

/-! ## On empty input a write-free machine's state iterates `blankNext` -/

/-- The next state on reading `false`. -/
def blankNext (M : Machine) (s : M.State) : M.State := (M.δ s false).1

theorem step_st_blank {c : Cfg M} (hnh : M.halt c.st = false)
    (hf : c.tp.getD c.hd false = false) : (step M c).st = blankNext M c.st := by
  have h1 : ¬ M.halt c.st = true := by rw [hnh]; simp
  unfold step blankNext
  rw [if_neg h1, hf]

/-- While `blankNext` has not yet halted, a write-free machine's state on empty input is exactly the
`blankNext`-iterate. -/
theorem run_st_tracks (hW : WriteFree M) (t : ℕ)
    (hpre : ∀ k, k < t → M.halt ((blankNext M)^[k] M.start) = false) :
    (run M t (init M [])).st = (blankNext M)^[t] M.start := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ihv := ih (fun k hk => hpre k (by omega))
    have hnh : M.halt (run M t (init M [])).st = false := by rw [ihv]; exact hpre t (by omega)
    have htp : (run M t (init M [])).tp = [] := run_tp_const hW (init M []) t
    rw [run_succ, step_st_blank hnh (by simp [htp]), ihv, Function.iterate_succ_apply']

/-! ## No computation in empty space -/

/-- **The blank-traversal bound (empty input).**  A write-free machine on empty input either halts
within `|State|` steps or never halts: it cannot compute for longer than its state count in empty
space. -/
theorem writeFree_empty_halts_fast (hW : WriteFree M) :
    (∃ t ≤ Fintype.card M.State, M.halt (run M t (init M [])).st = true)
      ∨ (∀ t, M.halt (run M t (init M [])).st = false) := by
  by_cases h : ∀ t, M.halt ((blankNext M)^[t] M.start) = false
  · right
    intro t
    rw [run_st_tracks hW t (fun k _ => h k)]
    exact h t
  · left
    have hex : ∃ t, M.halt ((blankNext M)^[t] M.start) = true := by
      push_neg at h
      obtain ⟨t0, ht0⟩ := h
      exact ⟨t0, by cases hh : M.halt ((blankNext M)^[t0] M.start) <;> simp_all⟩
    have hpre : ∀ k, k < Nat.find hex → M.halt ((blankNext M)^[k] M.start) = false := by
      intro k hk
      have hm := Nat.find_min hex hk
      cases hb : M.halt ((blankNext M)^[k] M.start) <;> simp_all
    have hT0card : Nat.find hex ≤ Fintype.card M.State := by
      obtain ⟨t', ht'le, ht'eq⟩ := orbit_bounded (blankNext M) M.start (Nat.find hex)
      by_contra hgt
      push_neg at hgt
      have hlt : t' < Nat.find hex := by omega
      have hf := hpre t' hlt
      rw [← ht'eq, Nat.find_spec hex] at hf
      simp at hf
    exact ⟨Nat.find hex, hT0card, by rw [run_st_tracks hW _ hpre]; exact Nat.find_spec hex⟩

end PallLean.Paper93.DeepMath.PathB.EmptySpaceHennie
