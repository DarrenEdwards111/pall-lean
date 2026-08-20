import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3WitnessSeqProps

/-!
# Compact deepest-witness labels

The unconditional deepest witness previously stored a term index at every depth step.  Since the
term stream is now proved nondecreasing, it is uniquely determined by its `m` multiplicities.  This
file packages positions and multiplicities into a finite label of cardinality
`w^s * (s+1)^m`, replacing the repeated `m^s` term component.
-/

namespace PallLean.Paper93.DeepMath.PathB
namespace Depth3

open SwitchingCounting

/-- One position per path step, and one multiplicity (between `0` and `s`) per term. -/
abbrev CompactWitLabel (w s m : ℕ) := (Fin s → Fin w) × (Fin m → Fin (s + 1))

theorem card_compactWitLabel (w s m : ℕ) :
    Fintype.card (CompactWitLabel w s m) = w ^ s * (s + 1) ^ m := by
  simp [CompactWitLabel, Fintype.card_prod]

/-- Total packing function.  Modulo is used only outside the certified fixed-length/range regime. -/
def compactWitPack (w s m : ℕ) [NeZero w]
    (l : List (ℕ × ℕ)) : CompactWitLabel w s m :=
  (fun i => ⟨(l.getD i (0, 0)).1 % w,
      Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne w))⟩,
   fun j => ⟨((l.map Prod.snd).count j.val) % (s + 1),
      Nat.mod_lt _ (Nat.succ_pos s)⟩)

/-- **Compact-label injectivity on monotone witness streams.** -/
theorem compactWitPack_inj {w s m : ℕ} [NeZero w]
    {a b : List (ℕ × ℕ)}
    (hal : a.length = s) (hbl : b.length = s)
    (haw : ∀ p ∈ a, p.1 < w) (hbw : ∀ p ∈ b, p.1 < w)
    (ham : ∀ p ∈ a, p.2 < m) (hbm : ∀ p ∈ b, p.2 < m)
    (has : List.Pairwise (· ≤ ·) (a.map Prod.snd))
    (hbs : List.Pairwise (· ≤ ·) (b.map Prod.snd))
    (heq : compactWitPack w s m a = compactWitPack w s m b) : a = b := by
  have hpos : a.map Prod.fst = b.map Prod.fst := by
    apply List.ext_getElem
    · simp [hal, hbl]
    · intro i hia hib
      have hi : i < s := by simpa [hal] using hia
      have h := congrFun (congrArg Prod.fst heq) ⟨i, hi⟩
      simp only [compactWitPack] at h
      have hai : i < a.length := by simpa [hal] using hi
      have hbi : i < b.length := by simpa [hbl] using hi
      simp only [List.getElem_map]
      simpa [List.getElem?_eq_getElem hai, List.getElem?_eq_getElem hbi,
        Nat.mod_eq_of_lt (haw a[i] (List.getElem_mem hai)),
        Nat.mod_eq_of_lt (hbw b[i] (List.getElem_mem hbi))] using congrArg Fin.val h
  have hcount : ∀ i, (a.map Prod.snd).count i = (b.map Prod.snd).count i := by
    intro i
    by_cases hi : i < m
    · have h := congrFun (congrArg Prod.snd heq) ⟨i, hi⟩
      have hac : (a.map Prod.snd).count i < s + 1 := by
        have hc := List.count_le_length (a := i) (l := a.map Prod.snd)
        simp only [List.length_map, hal] at hc
        omega
      have hbc : (b.map Prod.snd).count i < s + 1 := by
        have hc := List.count_le_length (a := i) (l := b.map Prod.snd)
        simp only [List.length_map, hbl] at hc
        omega
      simpa [compactWitPack, Nat.mod_eq_of_lt hac, Nat.mod_eq_of_lt hbc] using congrArg Fin.val h
    · have hna : i ∉ a.map Prod.snd := by
        intro hmem
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
        exact hi (ham p hp)
      have hnb : i ∉ b.map Prod.snd := by
        intro hmem
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
        exact hi (hbm p hp)
      simp [List.count_eq_zero.mpr hna, List.count_eq_zero.mpr hnb]
  have hterm : a.map Prod.snd = b.map Prod.snd :=
    pairwise_le_eq_of_count_eq has hbs hcount
  have combine : ∀ (x y : List (ℕ × ℕ)),
      x.map Prod.fst = y.map Prod.fst → x.map Prod.snd = y.map Prod.snd → x = y := by
    intro x
    induction x with
    | nil => intro y hp _; simpa using hp
    | cons q qs ih =>
        intro y hp ht
        cases y with
        | nil => simp at hp
        | cons r rs =>
            simp only [List.map_cons, List.cons.injEq] at hp ht
            rw [show q = r from Prod.ext hp.1 ht.1, ih rs hp.2 ht.2]
  exact combine a b hpos hterm

end Depth3
end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.card_compactWitLabel
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.compactWitPack_inj
