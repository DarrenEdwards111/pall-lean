import PallLean.Paper93.DeepMath.PathB.ComputationalDepthOneWayCommLB

/-!
# VC-dimension communication lower bound (a sixth technique)

A *sixth* communication-complexity technique: **VC-dimension**.  Viewing `f x y` as the set system
`{ S_x : x }` with `S_x = { y : f x y }`, a set `T ⊆ Y` is **shattered** when every subset of `T`
is realized as some row's trace on `T`.  The largest shattered set is the VC-dimension.

The key fact (`shatters_subfun_ge`) is a Sauer–Shelah-flavored injection: a shattered set of size
`d` forces `≥ 2^d` distinct subfunctions, because the `2^d` subsets of `T` each pin down a distinct
row.  Feeding the one-way subfunction bound (`oneWay_card_ge`) gives `vc_oneWay_ge`: any protocol
needs `≥ 2^d` messages, i.e. `≥ d` bits — the **VC lower bound** `CC(f) ≥ VC(f)`.

The witness is the membership/subset function `memFn`: Alice holds a subset `S : Fin n → Bool`, Bob
an index `i`, output `S i`.  The whole universe is shattered (`memFn_shatters`), so `VC = n` and its
one-way complexity is `≥ n` (`memFn_oneWay_ge`) — a new combinatorial parameter giving the bound.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.VCDimComm

open Finset
open PallLean.Paper93.DeepMath.PathB.OneWayCommLB (subfuns OneWayProtocol Computes oneWay_card_ge)

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]

/-- `T` is **shattered** by the rows of `f`: every subset of `T` is the trace on `T` of some row. -/
def Shatters (f : α → β → Bool) (T : Finset β) : Prop :=
  ∀ U ⊆ T, ∃ a : α, ∀ b ∈ T, (f a b = true ↔ b ∈ U)

/-- **The VC → subfunction bound (Sauer–Shelah flavor).**  A shattered set of size `d` forces
`≥ 2^d` distinct subfunctions: the `2^d` subsets of `T` inject into the rows, since distinct subsets
give rows with distinct traces on `T`. -/
theorem shatters_subfun_ge (f : α → β → Bool) (T : Finset β) (h : Shatters f T) :
    2 ^ T.card ≤ (subfuns f).card := by
  classical
  haveI : Nonempty α := ⟨(h ∅ (Finset.empty_subset T)).choose⟩
  set a : Finset β → α :=
    fun U => if hU : U ⊆ T then (h U hU).choose else Classical.arbitrary α with ha_def
  have ha_spec : ∀ U, U ⊆ T → ∀ b ∈ T, (f (a U) b = true ↔ b ∈ U) := by
    intro U hU b hb
    have haU : a U = (h U hU).choose := by rw [ha_def]; simp only [dif_pos hU]
    rw [haU]
    exact (h U hU).choose_spec b hb
  rw [← Finset.card_powerset T]
  apply Finset.card_le_card_of_injOn (fun U => fun b => f (a U) b)
  · intro U _
    show (fun b => f (a U) b) ∈ Finset.univ.image (fun u => fun v => f u v)
    exact Finset.mem_image.mpr ⟨a U, Finset.mem_univ _, rfl⟩
  · intro U hU U' hU' hgg
    rw [Finset.mem_coe, Finset.mem_powerset] at hU hU'
    ext b
    by_cases hbT : b ∈ T
    · have e1 := ha_spec U hU b hbT
      have e2 := ha_spec U' hU' b hbT
      have hfe : f (a U) b = f (a U') b := congrFun hgg b
      rw [← e1, ← e2, hfe]
    · constructor
      · intro hb; exact absurd (hU hb) hbT
      · intro hb; exact absurd (hU' hb) hbT

/-- **The VC one-way lower bound.**  A one-way protocol computing `f` needs `≥ 2^d` messages when
`f` shatters a set of size `d`. -/
theorem vc_oneWay_ge (f : α → β → Bool) (T : Finset β) (h : Shatters f T)
    (k : ℕ) (P : OneWayProtocol α β k) (hP : Computes P f) : 2 ^ T.card ≤ k :=
  le_trans (shatters_subfun_ge f T h) (oneWay_card_ge f P hP)

/-! ## The membership function -/

/-- The membership/subset function: Alice holds a subset `S`, Bob an index `i`, output `S i`. -/
def memFn (n : ℕ) : (Fin n → Bool) → Fin n → Bool := fun S i => S i

/-- **The whole universe is shattered**, so `memFn` has VC-dimension `n`. -/
theorem memFn_shatters (n : ℕ) : Shatters (memFn n) (Finset.univ) := by
  intro U _
  exact ⟨fun i => decide (i ∈ U), fun b _ => by simp [memFn]⟩

/-- `memFn` has `≥ 2^n` subfunctions, by VC-dimension `n`. -/
theorem memFn_vc (n : ℕ) : 2 ^ n ≤ (subfuns (memFn n)).card := by
  have := shatters_subfun_ge (memFn n) Finset.univ (memFn_shatters n)
  rwa [Finset.card_univ, Fintype.card_fin] at this

/-- **The membership function has one-way complexity `≥ n`, by VC-dimension.**  A sixth technique:
the VC-dimension is `n`, forcing `≥ 2^n` messages / `≥ n` bits. -/
theorem memFn_oneWay_ge (n k : ℕ) (P : OneWayProtocol (Fin n → Bool) (Fin n) k)
    (hP : Computes P (memFn n)) : 2 ^ n ≤ k :=
  le_trans (memFn_vc n) (oneWay_card_ge (memFn n) P hP)

/-- **The VC bound in bits.** -/
theorem memFn_bits_ge (n k : ℕ) (P : OneWayProtocol (Fin n → Bool) (Fin n) k)
    (hP : Computes P (memFn n)) : n ≤ Nat.log 2 k := by
  have hk : 2 ^ n ≤ k := memFn_oneWay_ge n k P hP
  calc n = Nat.log 2 (2 ^ n) := (Nat.log_pow Nat.one_lt_two n).symm
    _ ≤ Nat.log 2 k := Nat.log_mono_right hk

end PallLean.Paper93.DeepMath.PathB.VCDimComm
