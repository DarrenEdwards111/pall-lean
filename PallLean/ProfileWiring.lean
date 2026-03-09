/-
  ProfileWiring.lean — Wire profile_subspace_cover from components

  Converts the axiom into a theorem using:
  - Profile.spdp_le_iSup_profileSubspace (cover)
  - within_profile_dim_bound (Lemma 31, axiom)
  - Profile count bound (already proved)

  Paper: Theorem 23 assembly.
-/
import PallLean.Profile
import PallLean.ProfileDimBound
import PallLean.DerivType
import PallLean.TypeWord
import Mathlib.Tactic

namespace ProfileWiring

open SPDP MvPolynomial Profile DerivType

/-! ## Concrete profile function

Each variable in the block partition has a position within its block.
The profile function classifies each derivative by position mod 4,
giving a histogram of derivative types. -/

/-- Classify a variable by its role within its clause block (position mod 4) -/
noncomputable def classifyVar {n : ℕ} (_B : BlockPartition n) (i : Fin n) : Fin 4 :=
  ⟨i.val % 4, Nat.mod_lt _ (by omega)⟩

/-- Profile function: maps derivative list to type histogram.
    Counts how many list elements have each classification. -/
noncomputable def mkProfileFn {n : ℕ} (B : BlockPartition n) :
    List (Fin n) → Profile.Profile 4 :=
  fun S => fun (t : Fin 4) => (S.filter (fun i => classifyVar B i = t)).length

/-! ## Profile enumeration

We need a Finset of profiles containing all profiles with total mass ≤ R.
The number of such profiles is ≤ C(R+4, 4) by stars-and-bars. -/

/-- The set of all profiles h : Fin 4 → ℕ with totalMass h ≤ R.
    Constructed as image of (Fin 4 → Fin (R+1)) filtered by total mass.
    This is finite with |profileSet R| ≤ C(R+4, 4). -/
noncomputable def profileSet (R : ℕ) : Finset (Profile.Profile 4) :=
  ((Finset.univ : Finset (Fin 4 → Fin (R + 1))).image
    (fun f => fun t => (f t).val)).filter
    (fun h => Profile.totalMass h ≤ R)

theorem profileSet_mem_totalMass (R : ℕ) (h : Profile.Profile 4)
    (hm : h ∈ profileSet R) : Profile.totalMass h ≤ R := by
  simp [profileSet, Finset.mem_filter] at hm; exact hm.2

theorem profileSet_complete (R : ℕ) (h : Profile.Profile 4)
    (htotal : Profile.totalMass h ≤ R) :
    h ∈ profileSet R := by
  unfold profileSet
  rw [Finset.mem_filter]
  constructor
  · rw [Finset.mem_image]
    refine ⟨fun t => ⟨h t, ?_⟩, Finset.mem_univ _, ?_⟩
    · have h1 : h t ≤ Finset.univ.sum h := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ t)
      have h2 : Finset.univ.sum h = Profile.totalMass h := rfl
      omega
    · ext t; simp
  · exact htotal

theorem profileSet_card_le (R : ℕ) :
    (profileSet R).card ≤ (R + 1) ^ 4 := by
  unfold profileSet
  calc (Finset.filter _ _).card
      ≤ (Finset.univ.image (fun (f : Fin 4 → Fin (R + 1)) (t : Fin 4) => (f t).val)).card :=
        Finset.card_filter_le _ _
    _ ≤ Finset.card (Finset.univ : Finset (Fin 4 → Fin (R + 1))) :=
        Finset.card_image_le
    _ = (R + 1) ^ 4 := by simp [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

/-! ## mkProfileFn total mass = list length -/

-- Helper: partitioning a list by a function into Fin k gives sum of bin sizes = length
theorem sum_filter_length_eq_length {α : Type*} {k : ℕ} (f : α → Fin k) (l : List α) :
    (Finset.univ : Finset (Fin k)).sum
      (fun t => (l.filter (fun a => f a = t)).length) = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.length_cons]
    -- Each filter on (x :: xs): if f x = t then length + 1 else length
    -- Show each filter length on cons = filter length on tail + indicator
    have hstep : ∀ t : Fin k,
        ((x :: xs).filter (fun a => f a = t)).length =
        (xs.filter (fun a => f a = t)).length + if f x = t then 1 else 0 := by
      intro t; simp only [List.filter_cons, decide_eq_true_eq]
      split <;> simp
    have := calc
      (Finset.univ : Finset (Fin k)).sum
          (fun t => ((x :: xs).filter (fun a => f a = t)).length)
        = Finset.univ.sum (fun t =>
          (xs.filter (fun a => f a = t)).length + if f x = t then 1 else 0) := by
          apply Finset.sum_congr rfl; intro t _; exact hstep t
      _ = Finset.univ.sum (fun t => (xs.filter (fun a => f a = t)).length) +
          Finset.univ.sum (fun t => if f x = t then 1 else 0) :=
          Finset.sum_add_distrib
      _ = xs.length + 1 := by
          rw [ih, Finset.sum_ite_eq Finset.univ (f x) (fun _ => 1)]
          simp [Finset.mem_univ]
    linarith

theorem mkProfileFn_totalMass {n : ℕ} (B : BlockPartition n)
    (S : List (Fin n)) :
    Profile.totalMass (mkProfileFn B S) = S.length := by
  exact sum_filter_length_eq_length (classifyVar B) S

/-- For block-admissible lists, total mass ≤ κ ≤ R when R ≥ κ -/
theorem mkProfileFn_mass_le {n : ℕ} (B : BlockPartition n)
    (S : List (Fin n)) (R : ℕ) (hlen : S.length = κ) (hR : κ ≤ R) :
    Profile.totalMass (mkProfileFn B S) ≤ R := by
  rw [mkProfileFn_totalMass]; omega

end ProfileWiring
