import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA5b

/-!
# Shrinkage brick A6a: serialization and computability

The counting-brick substrate: an injective serialization of formulas and a DNF
construction giving universal computability (so `dmsizeC` is always attained):

* `ser` — prefix serialization into a finite token alphabet `Tok k`;
* **`ser_injective` (proved)** — via the append-cancellation lemma
  `ser_append_inj` (structural induction, no fuel/parser);
* `totalNodes`/`ser_length`/`canonical_ser_len` — the length of a canonical
  (constant or constant-free) formula's serialization is `≤ 2·L₀ + 1`;
* `dnfC`/`dnfC_eval` — every Boolean function is computed by a formula;
* **`dmsizeC_set_nonempty` (proved)** — so `dmsizeC` is a genuine minimum;
* `wit` — the canonical minimal-size witness formula of a function.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-! ### The token alphabet and serialization -/

/-- The serialization alphabet: `inl false` = AND, `inl true` = OR,
`inr (inl b)` = constant, `inr (inr (i,b))` = literal. -/
abbrev Tok (k : ℕ) := Bool ⊕ Bool ⊕ (Fin k × Bool)

def ser {k : ℕ} : DMTreeC k → List (Tok k)
  | .lit i b => [Sum.inr (Sum.inr (i, b))]
  | .cst b => [Sum.inr (Sum.inl b)]
  | .and l r => Sum.inl false :: (ser l ++ ser r)
  | .or l r => Sum.inl true :: (ser l ++ ser r)

/-- **Append-cancellation of the serialization (proved).** -/
theorem ser_append_inj {k : ℕ} (t1 : DMTreeC k) :
    ∀ (s1 : List (Tok k)) (t2 : DMTreeC k) (s2 : List (Tok k)),
      ser t1 ++ s1 = ser t2 ++ s2 → t1 = t2 ∧ s1 = s2 := by
  induction t1 with
  | lit i b =>
    intro s1 t2 s2 h
    cases t2 with
    | lit j c =>
      simp only [ser, List.singleton_append, List.cons.injEq, Sum.inr.injEq,
        Prod.mk.injEq] at h
      obtain ⟨⟨hi, hb⟩, hs⟩ := h
      subst hi; subst hb; subst hs
      exact ⟨rfl, rfl⟩
    | cst c => simp [ser] at h
    | and l r => simp [ser] at h
    | or l r => simp [ser] at h
  | cst b =>
    intro s1 t2 s2 h
    cases t2 with
    | lit j c => simp [ser] at h
    | cst c =>
      simp only [ser, List.singleton_append, List.cons.injEq, Sum.inr.injEq,
        Sum.inl.injEq] at h
      obtain ⟨hb, hs⟩ := h
      subst hb; subst hs
      exact ⟨rfl, rfl⟩
    | and l r => simp [ser] at h
    | or l r => simp [ser] at h
  | and l1 r1 ihl ihr =>
    intro s1 t2 s2 h
    cases t2 with
    | lit j c => simp [ser] at h
    | cst c => simp [ser] at h
    | and l2 r2 =>
      rw [ser, ser, List.cons_append, List.cons_append, List.append_assoc,
        List.append_assoc] at h
      simp only [List.cons.injEq, true_and] at h
      obtain ⟨hl, hrest⟩ := ihl (ser r1 ++ s1) l2 (ser r2 ++ s2) h
      obtain ⟨hr, hs⟩ := ihr s1 r2 s2 hrest
      subst hl; subst hr; subst hs
      exact ⟨rfl, rfl⟩
    | or l2 r2 =>
      rw [ser, ser, List.cons_append, List.cons_append] at h
      simp only [List.cons.injEq, Sum.inl.injEq] at h
      exact absurd h.1 (by decide)
  | or l1 r1 ihl ihr =>
    intro s1 t2 s2 h
    cases t2 with
    | lit j c => simp [ser] at h
    | cst c => simp [ser] at h
    | and l2 r2 =>
      rw [ser, ser, List.cons_append, List.cons_append] at h
      simp only [List.cons.injEq, Sum.inl.injEq] at h
      exact absurd h.1 (by decide)
    | or l2 r2 =>
      rw [ser, ser, List.cons_append, List.cons_append, List.append_assoc,
        List.append_assoc] at h
      simp only [List.cons.injEq, true_and] at h
      obtain ⟨hl, hrest⟩ := ihl (ser r1 ++ s1) l2 (ser r2 ++ s2) h
      obtain ⟨hr, hs⟩ := ihr s1 r2 s2 hrest
      subst hl; subst hr; subst hs
      exact ⟨rfl, rfl⟩

theorem ser_injective {k : ℕ} : Function.Injective (ser (k := k)) := by
  intro t1 t2 h
  have h' : ser t1 ++ [] = ser t2 ++ [] := by rw [List.append_nil, List.append_nil, h]
  exact (ser_append_inj t1 [] t2 [] h').1

/-! ### Length -/

def totalNodes {k : ℕ} : DMTreeC k → ℕ
  | .lit _ _ => 1
  | .cst _ => 1
  | .and l r => 1 + totalNodes l + totalNodes r
  | .or l r => 1 + totalNodes l + totalNodes r

theorem ser_length {k : ℕ} (t : DMTreeC k) : (ser t).length = totalNodes t := by
  induction t with
  | lit i b => rfl
  | cst b => rfl
  | and l r ihl ihr =>
    rw [ser, List.length_cons, List.length_append, ihl, ihr]
    show totalNodes l + totalNodes r + 1 = 1 + totalNodes l + totalNodes r
    omega
  | or l r ihl ihr =>
    rw [ser, List.length_cons, List.length_append, ihl, ihr]
    show totalNodes l + totalNodes r + 1 = 1 + totalNodes l + totalNodes r
    omega

theorem totalNodes_cstfree {k : ℕ} (t : DMTreeC k) (h : CstFree t) :
    totalNodes t + 1 = 2 * t.lsize0 := by
  induction t with
  | lit i b => rfl
  | cst b => exact h.elim
  | and l r ihl ihr =>
    have h1 := ihl h.1
    have h2 := ihr h.2
    show (1 + totalNodes l + totalNodes r) + 1 = 2 * (l.lsize0 + r.lsize0)
    omega
  | or l r ihl ihr =>
    have h1 := ihl h.1
    have h2 := ihr h.2
    show (1 + totalNodes l + totalNodes r) + 1 = 2 * (l.lsize0 + r.lsize0)
    omega

theorem canonical_ser_len {k : ℕ} (t : DMTreeC k)
    (h : (∃ v, t = .cst v) ∨ CstFree t) : (ser t).length ≤ 2 * t.lsize0 + 1 := by
  rw [ser_length]
  rcases h with ⟨v, hv⟩ | hcf
  · subst hv; exact Nat.le_refl _
  · have := totalNodes_cstfree t hcf
    omega

/-! ### DNF: every function is computable -/

def minterm {k : ℕ} (y : Fin k → Bool) : DMTreeC k :=
  (List.finRange k).foldr (fun i acc => DMTreeC.and (.lit i (y i)) acc) (.cst true)

theorem minterm_foldr_true {k : ℕ} (y x : Fin k → Bool) (L : List (Fin k)) :
    (L.foldr (fun i acc => DMTreeC.and (.lit i (y i)) acc) (.cst true)).eval x = true
      ↔ ∀ i ∈ L, x i = y i := by
  induction L with
  | nil => simp [DMTreeC.eval]
  | cons a L ih =>
    rw [List.foldr_cons]
    show ((DMTreeC.lit a (y a)).eval x
      && (L.foldr (fun i acc => DMTreeC.and (.lit i (y i)) acc) (.cst true)).eval x)
      = true ↔ _
    rw [Bool.and_eq_true, ih]
    show ((x a == y a) = true ∧ _) ↔ _
    rw [beq_iff_eq, List.forall_mem_cons]

theorem minterm_true {k : ℕ} (y x : Fin k → Bool) :
    (minterm y).eval x = true ↔ x = y := by
  rw [minterm, minterm_foldr_true]
  constructor
  · intro h
    funext i
    exact h i (by simp)
  · rintro rfl i _
    rfl

noncomputable def dnfC {k : ℕ} (f : (Fin k → Bool) → Bool) : DMTreeC k :=
  (Finset.univ.filter (fun y => f y = true)).toList.foldr
    (fun y acc => DMTreeC.or (minterm y) acc) (.cst false)

theorem dnf_foldr_true {k : ℕ} (x : Fin k → Bool) (L : List (Fin k → Bool)) :
    (L.foldr (fun y acc => DMTreeC.or (minterm y) acc) (.cst false)).eval x = true
      ↔ ∃ y ∈ L, x = y := by
  induction L with
  | nil => simp [DMTreeC.eval]
  | cons a L ih =>
    rw [List.foldr_cons]
    show ((minterm a).eval x
      || (L.foldr (fun y acc => DMTreeC.or (minterm y) acc) (.cst false)).eval x)
      = true ↔ _
    rw [Bool.or_eq_true, minterm_true, ih]
    simp [List.mem_cons]

theorem dnfC_eval {k : ℕ} (f : (Fin k → Bool) → Bool) (x : Fin k → Bool) :
    (dnfC f).eval x = f x := by
  have key : (dnfC f).eval x = true ↔ f x = true := by
    rw [dnfC, dnf_foldr_true]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Finset.mem_toList, Finset.mem_filter] at hy
      exact hy.2
    · intro hfx
      refine ⟨x, ?_, rfl⟩
      rw [Finset.mem_toList, Finset.mem_filter]
      exact ⟨Finset.mem_univ x, hfx⟩
  cases hd : (dnfC f).eval x <;> cases hf : f x <;> simp_all

theorem dmsizeC_set_nonempty {k : ℕ} (f : (Fin k → Bool) → Bool) :
    {L | ∃ t : DMTreeC k, (∀ x, t.eval x = f x) ∧ t.lsize0 = L}.Nonempty :=
  ⟨(dnfC f).lsize0, dnfC f, dnfC_eval f, rfl⟩

/-! ### The canonical witness -/

/-- The canonical minimal-size formula of `f`. -/
noncomputable def wit {k : ℕ} (f : (Fin k → Bool) → Bool) : DMTreeC k :=
  simpC (Nat.sInf_mem (dmsizeC_set_nonempty f)).choose

theorem wit_eval {k : ℕ} (f : (Fin k → Bool) → Bool) (x : Fin k → Bool) :
    (wit f).eval x = f x := by
  rw [wit, simpC_eval]
  exact (Nat.sInf_mem (dmsizeC_set_nonempty f)).choose_spec.1 x

theorem wit_lsize0_le {k : ℕ} (f : (Fin k → Bool) → Bool) :
    (wit f).lsize0 ≤ dmsizeC f := by
  have h1 : (Nat.sInf_mem (dmsizeC_set_nonempty f)).choose.lsize0 = dmsizeC f :=
    (Nat.sInf_mem (dmsizeC_set_nonempty f)).choose_spec.2
  rw [wit]
  calc (simpC (Nat.sInf_mem (dmsizeC_set_nonempty f)).choose).lsize0
      ≤ (Nat.sInf_mem (dmsizeC_set_nonempty f)).choose.lsize0 := simpC_lsize0 _
    _ = dmsizeC f := h1

theorem wit_canonical {k : ℕ} (f : (Fin k → Bool) → Bool) :
    (∃ v, wit f = .cst v) ∨ CstFree (wit f) :=
  simpC_cstFree _

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.ser_injective
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.dnfC_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.wit_eval
