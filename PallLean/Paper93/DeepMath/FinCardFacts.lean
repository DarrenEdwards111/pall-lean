import Mathlib.Data.Fintype.Card

namespace PallLean.Paper93.DeepMath

theorem fin_card (N : ℕ) : Fintype.card (Fin N) = N := Fintype.card_fin N
