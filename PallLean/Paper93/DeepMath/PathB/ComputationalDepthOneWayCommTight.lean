import PallLean.Paper93.DeepMath.PathB.ComputationalDepthOneWayCommLB

/-!
# One-way communication complexity is exactly the subfunction count

`OneWayCommLB` proved the lower bound: a one-way protocol computing `f` needs `≥ #subfunctions`
messages.  This file adds the matching upper bound — a protocol with *exactly* `#subfunctions`
messages (Alice names her subfunction) — giving the **fundamental theorem of one-way
deterministic communication complexity**: the minimum message count is exactly the number of
distinct subfunctions.

* `subfunProtocol` — Alice sends the index of her subfunction; Bob evaluates it.  Computes `f`
  with `(subfuns f).card` messages (`subfunProtocol_computes`).
* `oneWay_exact` — combining with `oneWay_card_ge`: `(subfuns f).card` messages both suffice and
  are necessary; it is the exact one-way message complexity.
* `dIndex_oneWay_exact` — the doubled-INDEX middle-cut split has one-way complexity *exactly*
  its subfunction count, which is `≥ 2^m` — tight against `OneWayCommLB`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.OneWayCommTight

open PallLean.Paper93.DeepMath.PathB.OneWayCommLB
open PallLean.Paper93.DeepMath.PathB.LangRankKill (dIndexLang subfunCountAt)

/-- The optimal protocol: Alice sends the index of her subfunction (its position among the
distinct subfunctions), and Bob evaluates that subfunction at his input. -/
noncomputable def subfunProtocol {α β : Type} [Fintype α] [Fintype β] (f : α → β → Bool) :
    OneWayProtocol α β (subfuns f).card where
  msg u := (subfuns f).equivFin
    ⟨fun v => f u v, by
      simp only [subfuns, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨u, rfl⟩⟩
  out m v := ((subfuns f).equivFin.symm m).1 v

/-- The optimal protocol computes `f`. -/
theorem subfunProtocol_computes {α β : Type} [Fintype α] [Fintype β] (f : α → β → Bool) :
    Computes (subfunProtocol f) f := by
  intro u v
  show ((subfuns f).equivFin.symm ((subfuns f).equivFin
      ⟨fun v => f u v, _⟩)).1 v = f u v
  rw [Equiv.symm_apply_apply]

/-- **The exact one-way complexity.**  `(subfuns f).card` messages both suffice
(`subfunProtocol`) and are necessary (`oneWay_card_ge`) — it is exactly the one-way
deterministic message complexity of `f`. -/
theorem oneWay_exact {α β : Type} [Fintype α] [Fintype β] (f : α → β → Bool) :
    (∃ P : OneWayProtocol α β (subfuns f).card, Computes P f)
      ∧ ∀ k (P : OneWayProtocol α β k), Computes P f → (subfuns f).card ≤ k :=
  ⟨⟨subfunProtocol f, subfunProtocol_computes f⟩, fun _ P hP => oneWay_card_ge f P hP⟩

/-! ## Instantiation: doubled INDEX -/

/-- **Doubled INDEX has one-way complexity exactly its subfunction count** (`≥ 2^m`): the
optimal protocol uses `subfunCountAt` messages, and no protocol uses fewer. -/
theorem dIndex_oneWay_exact (m : ℕ) :
    (∃ P : OneWayProtocol _ _ (subfunCountAt dIndexLang (3 * m + 3) (3 * m + 3)),
        Computes P (dIndexComm m))
      ∧ ∀ k (P : OneWayProtocol _ _ k), Computes P (dIndexComm m)
          → subfunCountAt dIndexLang (3 * m + 3) (3 * m + 3) ≤ k := by
  obtain ⟨hup, hlo⟩ := oneWay_exact (dIndexComm m)
  rw [subfuns_dIndexComm] at hup hlo
  exact ⟨hup, hlo⟩

end PallLean.Paper93.DeepMath.PathB.OneWayCommTight
