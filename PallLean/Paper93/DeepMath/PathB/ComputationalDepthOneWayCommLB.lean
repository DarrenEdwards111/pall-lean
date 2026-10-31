import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLangRankKill

/-!
# One-way communication complexity: a lower bound for doubled INDEX

Communication complexity lower bounds are a core separation tool (formula size, branching
programs, streaming, data structures).  This file gives the clean one-way deterministic bound
and instantiates it for the doubled-INDEX function `dIndexLang` of `LangRankKill`, whose
subfunction count was already shown to be `≥ 2^m`.

* `OneWayProtocol α β k` — Alice (input `α`) sends one of `k` messages; Bob (input `β`) then
  outputs.  It *computes* `f : α → β → Bool` if Bob's output always matches `f`.
* `oneWay_card_ge` — **the fooling bound**: a `k`-message protocol computing `f` has
  `k ≥ #{ distinct subfunctions v ↦ f u v }`.  Each message determines Bob's whole output
  function, so the messages surject onto the subfunctions.
* `oneWay_bits_ge` — hence the message length `⌈log₂ k⌉ ≥ log₂(#subfunctions)`.
* `dIndexComm`, `dIndex_oneWay_card_ge`, `dIndex_oneWay_bits_ge` — the doubled-INDEX split at
  the middle cut needs `≥ 2^m` messages, i.e. `≥ m` bits of one-way communication (from
  `two_pow_le_subfunCountAt_dIndex`).  A concrete, unconditional `Ω(m)` one-way lower bound.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.OneWayCommLB

open PallLean.Paper93.DeepMath.PathB.LangRankKill (dIndexLang subfunCountAt
  two_pow_le_subfunCountAt_dIndex)

/-- A one-way deterministic protocol: Alice maps her input to one of `k` messages; Bob maps
`(message, his input)` to an output bit. -/
structure OneWayProtocol (α β : Type) (k : ℕ) where
  /-- Alice's message. -/
  msg : α → Fin k
  /-- Bob's output, given the message and his input. -/
  out : Fin k → β → Bool

/-- The protocol *computes* `f` if Bob's output always matches. -/
def Computes {α β : Type} {k : ℕ} (P : OneWayProtocol α β k) (f : α → β → Bool) : Prop :=
  ∀ u v, P.out (P.msg u) v = f u v

/-- The set of distinct subfunctions `v ↦ f u v` (the rows of the communication matrix). -/
noncomputable def subfuns {α β : Type} [Fintype α] [Fintype β] (f : α → β → Bool) :
    Finset (β → Bool) :=
  Finset.univ.image fun u => fun v => f u v

/-- **The fooling bound.**  A one-way protocol computing `f` needs at least as many messages as
`f` has distinct subfunctions: each message determines Bob's entire output function, so the
messages surject onto the subfunctions. -/
theorem oneWay_card_ge {α β : Type} [Fintype α] [Fintype β] {k : ℕ}
    (f : α → β → Bool) (P : OneWayProtocol α β k) (hP : Computes P f) :
    (subfuns f).card ≤ k := by
  have hsub : subfuns f ⊆ Finset.univ.image fun m : Fin k => fun v => P.out m v := by
    intro g hg
    simp only [subfuns, Finset.mem_image, Finset.mem_univ, true_and] at hg ⊢
    obtain ⟨u, rfl⟩ := hg
    refine ⟨P.msg u, ?_⟩
    funext v
    exact hP u v
  calc (subfuns f).card
      ≤ (Finset.univ.image fun m : Fin k => fun v => P.out m v).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
    _ = k := by simp

/-- **The bit bound.**  A protocol computing `f` uses messages of length `⌈log₂ k⌉`, at least
`log₂` of the subfunction count: `2 ^ b < #subfuns ⇒ 2 ^ b < k`, so `k` exceeds every power of
two below the subfunction count. -/
theorem oneWay_bits_ge {α β : Type} [Fintype α] [Fintype β] {k : ℕ}
    (f : α → β → Bool) (P : OneWayProtocol α β k) (hP : Computes P f)
    (b : ℕ) (hb : 2 ^ b ≤ (subfuns f).card) : 2 ^ b ≤ k :=
  le_trans hb (oneWay_card_ge f P hP)

/-! ## Instantiation: doubled INDEX -/

/-- The doubled-INDEX communication problem at the middle cut of slice `6m+6`: Alice holds the
data-block half, Bob holds the address half. -/
def dIndexComm (m : ℕ) : (Fin (3 * m + 3) → Bool) → (Fin (3 * m + 3) → Bool) → Bool :=
  fun u v => dIndexLang (List.ofFn u ++ List.ofFn v)

/-- Its subfunction set has exactly the `subfunCountAt` cardinality. -/
theorem subfuns_dIndexComm (m : ℕ) :
    (subfuns (dIndexComm m)).card = subfunCountAt dIndexLang (3 * m + 3) (3 * m + 3) := by
  unfold subfuns subfunCountAt
  rfl

/-- **Doubled INDEX needs `≥ 2^m` one-way messages.**  Any one-way protocol computing the
middle-cut split of doubled INDEX uses at least `2^m` messages. -/
theorem dIndex_oneWay_card_ge (m k : ℕ) (P : OneWayProtocol _ _ k)
    (hP : Computes P (dIndexComm m)) : 2 ^ m ≤ k := by
  refine oneWay_bits_ge (dIndexComm m) P hP m ?_
  rw [subfuns_dIndexComm]
  exact two_pow_le_subfunCountAt_dIndex m

/-- **Doubled INDEX has one-way communication complexity `≥ m`.**  Any one-way protocol needs
messages of length at least `m`: with `k < 2^m` messages no correct protocol exists. -/
theorem dIndex_oneWay_bits_ge (m k : ℕ) (P : OneWayProtocol _ _ k)
    (hP : Computes P (dIndexComm m)) : m ≤ Nat.log 2 k := by
  have hk : 2 ^ m ≤ k := dIndex_oneWay_card_ge m k P hP
  calc m = Nat.log 2 (2 ^ m) := (Nat.log_pow (by norm_num : 1 < 2) m).symm
    _ ≤ Nat.log 2 k := Nat.log_mono_right hk

end PallLean.Paper93.DeepMath.PathB.OneWayCommLB
