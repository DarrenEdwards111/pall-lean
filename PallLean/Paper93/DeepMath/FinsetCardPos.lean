import Mathlib.Data.Finset.Card

namespace PallLean.Paper93.DeepMath

theorem finset_card_pos_iff : ∀ {ι : Type*} (s : Finset ι), 0 < s.card ↔ s.Nonempty :=
  fun {_} s => Finset.card_pos (s := s)

end PallLean.Paper93.DeepMath
