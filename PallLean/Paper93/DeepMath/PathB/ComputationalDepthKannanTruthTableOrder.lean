import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKannanNaming

/-!
# The Kannan arc, stage 3: the explicit truth-table order — the enumeration becomes algorithmic

Stage 2 named the first hard function against a *definitional* enumeration (`Fintype.equivFin`,
choice-based).  Stage 3 replaces it with the **explicit truth-table order**: a computable encoding
`ttNat` of Boolean functions by their truth tables, with injectivity proved by structural induction —
no choice, no `noncomputable`, kernel-evaluable.  The named object becomes *the* canonical
least-truth-table hard function — Kannan's actual function.

## What is proved

* **`natOfBools` / `natOfBools_inj`** — binary reading of a Bool list; injective on equal lengths
  (head by parity, tail by halving — pure `omega`).
* **`allAsg` / `allAsg_complete` / `allAsg_length`** — the explicit assignment enumeration: all
  length-`n` Bool lists, complete, of size `2^n`.
* **`ttNat` / `ttNat_inj`** — the truth-table number of `f : BF n`, computable, injective (via
  completeness + the `ofFn` roundtrip).  Concrete kernel evaluations: `ttNat_const_false`,
  `ttNat_id_one` — the order is *algorithmic*, not definitional.
* **`named_of_exists_tt` / `named_hard_function_tt`** — the naming re-run on the explicit order:
  a unique **truth-table-first** hard function exists (below the Shannon threshold, and concretely at
  `(10,10)`: `named_ten_tt`).
* **`isFirstHardTT_pi2`** — the Π₂ prenex shape carries over verbatim to the explicit order.

## Honest scope — the enumeration is now algorithmic; uniformity and altitude remain

Stage 3 removes the choice from the name: the order is a computable function of truth tables, and the
named object is the standard Kannan function.  The naming machinery is order-generic (the stage-2
proofs re-run verbatim), so the *content* added here is exactly the explicitness.  Remaining stages,
unchanged: per-input-length **uniformity** (the family `n ↦ f_n`), **Σ₂ machine semantics** over
`ComposableMachine` (relating the Π₂ circuit-space shape to machine alternation), **Karp–Lipton**,
and assembly.  Ceiling unchanged and stated up front: fixed-polynomial bounds at Σ₂ altitude — not
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KannanTT

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.SharingModelShannon
open PallLean.Paper93.DeepMath.PathB.KannanNaming

/-! ### Binary reading of Bool lists -/

/-- Read a Bool list as a natural number, little-endian. -/
def natOfBools : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * natOfBools bs

theorem natOfBools_cons_mod (b : Bool) (bs : List Bool) :
    natOfBools (b :: bs) % 2 = if b then 1 else 0 := by
  cases b
  · show (0 + 2 * natOfBools bs) % 2 = 0
    omega
  · show (1 + 2 * natOfBools bs) % 2 = 1
    omega

theorem natOfBools_cons_div (b : Bool) (bs : List Bool) :
    natOfBools (b :: bs) / 2 = natOfBools bs := by
  cases b
  · show (0 + 2 * natOfBools bs) / 2 = natOfBools bs
    omega
  · show (1 + 2 * natOfBools bs) / 2 = natOfBools bs
    omega

/-- **Binary reading is injective on equal lengths (proved).**  Head by parity, tail by halving. -/
theorem natOfBools_inj : ∀ (l₁ l₂ : List Bool), l₁.length = l₂.length →
    natOfBools l₁ = natOfBools l₂ → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ hlen _
    cases l₂ with
    | nil => rfl
    | cons b bs => simp at hlen
  | cons b bs ih =>
    intro l₂ hlen heq
    cases l₂ with
    | nil => simp at hlen
    | cons b' bs' =>
      have hmod : (if b then 1 else 0 : ℕ) = if b' then 1 else 0 := by
        rw [← natOfBools_cons_mod b bs, ← natOfBools_cons_mod b' bs', heq]
      have hb : b = b' := by
        cases b <;> cases b' <;> first | rfl | exact absurd hmod (by decide)
      have htail : natOfBools bs = natOfBools bs' := by
        rw [← natOfBools_cons_div b bs, ← natOfBools_cons_div b' bs', heq]
      have hlen' : bs.length = bs'.length := by
        simp only [List.length_cons] at hlen; omega
      rw [hb, ih bs' hlen' htail]

/-! ### The explicit assignment enumeration -/

/-- All length-`n` Bool lists, in canonical (false-first) order. -/
def allAsg : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allAsg n).map (false :: ·) ++ (allAsg n).map (true :: ·)

/-- **Completeness (proved).**  Every length-`n` list appears. -/
theorem allAsg_complete : ∀ (n : ℕ) (l : List Bool), l.length = n → l ∈ allAsg n := by
  intro n
  induction n with
  | zero =>
    intro l hl
    have h0 : l = [] := List.eq_nil_of_length_eq_zero hl
    rw [h0]
    exact List.mem_cons_self
  | succ n ih =>
    intro l hl
    cases l with
    | nil => simp at hl
    | cons b bs =>
      have hbs : bs ∈ allAsg n := ih bs (by simpa using hl)
      show b :: bs ∈ (allAsg n).map (false :: ·) ++ (allAsg n).map (true :: ·)
      cases b
      · exact List.mem_append_left _ (List.mem_map.mpr ⟨bs, hbs, rfl⟩)
      · exact List.mem_append_right _ (List.mem_map.mpr ⟨bs, hbs, rfl⟩)

/-- The enumeration has exactly `2^n` rows. -/
theorem allAsg_length (n : ℕ) : (allAsg n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show ((allAsg n).map (false :: ·) ++ (allAsg n).map (true :: ·)).length = 2 ^ (n + 1)
    rw [List.length_append, List.length_map, List.length_map, ih, Nat.pow_succ]
    omega

/-! ### The truth-table number -/

/-- The assignment a Bool list denotes. -/
def asFn {n : ℕ} (l : List Bool) : Fin n → Bool := fun i => l.getD i.val false

/-- The truth table of `f`. -/
def ttList (n : ℕ) (f : BF n) : List Bool := (allAsg n).map (fun l => f (asFn l))

/-- **The truth-table number** — computable, no choice. -/
def ttNat (n : ℕ) (f : BF n) : ℕ := natOfBools (ttList n f)

/-- Equal maps over the same list agree on members. -/
theorem map_congr_of_eq {α β : Type} : ∀ (l : List α) (f g : α → β),
    l.map f = l.map g → ∀ a ∈ l, f a = g a := by
  intro l f g
  induction l with
  | nil => intro _ a ha; exact (List.not_mem_nil ha).elim
  | cons x xs ih =>
    intro h a ha
    simp only [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact h.1
    · exact ih h.2 a ha'

/-- **The truth-table number is injective (proved).**  Via completeness and the `ofFn` roundtrip. -/
theorem ttNat_inj (n : ℕ) : Function.Injective (ttNat n) := by
  intro f g h
  have hlen : (ttList n f).length = (ttList n g).length := by
    simp [ttList]
  have hlist : ttList n f = ttList n g := natOfBools_inj _ _ hlen h
  have hpt : ∀ l ∈ allAsg n, f (asFn l) = g (asFn l) :=
    map_congr_of_eq (allAsg n) _ _ hlist
  funext x
  have hx : List.ofFn x ∈ allAsg n := allAsg_complete n (List.ofFn x) (by simp)
  have hfx : asFn (n := n) (List.ofFn x) = x := by
    funext i
    show (List.ofFn x).getD i.val false = x i
    rw [getD_ofFn false n x i.val i.isLt]
  have hval := hpt (List.ofFn x) hx
  rw [hfx] at hval
  exact hval

/-- **The order is algorithmic (kernel-checked).**  The constant-false function has table `0`. -/
theorem ttNat_const_false : ttNat 1 (fun _ => false) = 0 := by decide

/-- **The order is algorithmic (kernel-checked).**  The identity on one input has table `2`. -/
theorem ttNat_id_one : ttNat 1 (fun x => x 0) = 2 := by decide

/-! ### The naming, re-run on the explicit order -/

/-- `f` is the **truth-table-first hard function**: hard, and least in the truth-table order. -/
def IsFirstHardTT (n L : ℕ) (f : BF n) : Prop :=
  IsHard n L f ∧ ∀ g : BF n, IsHard n L g → ttNat n f ≤ ttNat n g

/-- **Naming on the explicit order (proved).**  If a hard function exists, the truth-table-first hard
function exists and is unique. -/
theorem named_of_exists_tt (n L : ℕ) (hex : ∃ f : BF n, IsHard n L f) :
    ∃! f : BF n, IsFirstHardTT n L f := by
  classical
  obtain ⟨f₀, hf₀⟩ := hex
  have hne : (Finset.univ.filter (fun f : BF n => IsHard n L f)).Nonempty :=
    ⟨f₀, Finset.mem_filter.mpr ⟨Finset.mem_univ f₀, hf₀⟩⟩
  obtain ⟨f, hf_mem, hf_min⟩ := Finset.exists_min_image _ (ttNat n) hne
  rw [Finset.mem_filter] at hf_mem
  refine ⟨f, ⟨hf_mem.2, fun g hg => hf_min g (Finset.mem_filter.mpr ⟨Finset.mem_univ g, hg⟩)⟩, ?_⟩
  rintro f' ⟨hf'h, hf'min⟩
  exact ttNat_inj n (le_antisymm (hf'min f hf_mem.2)
    (hf_min f' (Finset.mem_filter.mpr ⟨Finset.mem_univ f', hf'h⟩)))

/-- Naming below the Shannon threshold, explicit order. -/
theorem named_hard_function_tt (n L : ℕ) (hcard : Fintype.card (Code n L) < 2 ^ 2 ^ n) :
    ∃! f : BF n, IsFirstHardTT n L f :=
  named_of_exists_tt n L (shannon_exists n L hcard)

/-- **The Π₂ shape, explicit order (proved).**  Carries over verbatim: hardness is `∀c`, firstness
costs one alternation. -/
theorem isFirstHardTT_pi2 (n L : ℕ) (f : BF n) :
    IsFirstHardTT n L f ↔
      ∀ (c : List (CGate n)) (g : BF n),
        (computes c f → L < c.length) ∧
        (ttNat n f ≤ ttNat n g ∨ ∃ c' : List (CGate n), computes c' g ∧ c'.length ≤ L) := by
  constructor
  · rintro ⟨h1, h2⟩ c g
    refine ⟨h1 c, ?_⟩
    by_cases hg : IsHard n L g
    · exact Or.inl (h2 g hg)
    · right
      unfold IsHard at hg
      push_neg at hg
      exact hg
  · intro h
    constructor
    · intro c hc
      exact (h c f).1 hc
    · intro g hg
      rcases (h [] g).2 with hle | ⟨c', hc', hlen⟩
      · exact hle
      · exact absurd (hg c' hc') (by omega)

/-- **Concrete (proved).**  There is a unique truth-table-first hard 10-input function. -/
theorem named_ten_tt : ∃! f : BF 10, IsFirstHardTT 10 10 f :=
  named_of_exists_tt 10 10 hard_function_exists_ten

end PallLean.Paper93.DeepMath.PathB.KannanTT

#print axioms PallLean.Paper93.DeepMath.PathB.KannanTT.ttNat_inj
#print axioms PallLean.Paper93.DeepMath.PathB.KannanTT.named_of_exists_tt
#print axioms PallLean.Paper93.DeepMath.PathB.KannanTT.isFirstHardTT_pi2
#print axioms PallLean.Paper93.DeepMath.PathB.KannanTT.named_ten_tt
