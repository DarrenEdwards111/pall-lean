import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameRootShape

/-!
# N-Frame: the no-bipartite-split engine — two honest rows overflow any split

The last rung of the read-once kill, delivered as engine + frame + conditional cash-out.

  `no_split_two_rows` — **PROVED, the engine (pure logic)**: if `f = op (g, h)` with `g` reading only `S`
        and `h` only its complement, then every "row" (the `S`-function induced by freezing the complement)
        lies in the four-element family `{0, 1, G, ¬G}` — so **two rows that differ somewhere, agree
        somewhere, and are each non-constant** are a contradiction.  Six evaluations of `f` refute the
        split; no classification of `op` is needed.
  `sat3_split_frame` — **PROVED, the frame**: a minimal SAT circuit with `coneExcess = 0` yields exactly
        the engine's hypothesis — `sat3 = op (g, h)` with `g` blind off a variable set `S`, `h` blind on
        `S` (root-shape reduction + top split + read-uniqueness for the sides' disjointness).
  `Sat3NoBipartiteSplit` / `sat3_cbudget_2mD_of_no_split` — **the conditional cash-out**: if SAT admits no
        bipartite split (the named witness-production hypothesis, NOT discharged), then every minimal
        circuit has `coneExcess ≥ 1` and `2·m·D ≤ cbudget` — the first record beyond connectivity.

## Honest scope

The engine and the frame are theorems; the witness production is not.  `Sat3NoBipartiteSplit` is carried as
an explicit hypothesis, never an axiom: discharging it means, for an arbitrary cut `(S, Sᶜ)`, producing two
complement-side settings whose rows differ, agree, and are non-constant — six `f`-evaluations at mixed
points.  The mixed points are controllable only through coordinates of known side, so the discharge needs
per-coordinate-type eval lemmas (the pair (designated sign, pin sign) gives XOR-rows via
`sat3Context_probe_eval`; the agree-witness there needs the two-literal AND-context; selector coordinates
are monotone, so their clashes must route through sign fields).  That per-type sweep is the honest wall.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- Combine the `S`-part of `x` with the complement part of `y`. -/
def mixOn {n : ℕ} (S : Finset (Fin n)) (x y : Fin n → Bool) : Fin n → Bool :=
  fun i => if i ∈ S then x i else y i

/-- Two injective unary Bool maps that agree somewhere agree everywhere — the row-capacity core. -/
theorem two_injective_unaries (u v : Bool → Bool) (ad aa a1 a1' a2 a2' : Bool)
    (hxd : u ad ≠ v ad) (hxa : u aa = v aa)
    (hx1 : u a1 ≠ u a1') (hx2 : v a2 ≠ v a2') : False := by
  have huinj : u true ≠ u false := by
    cases h1 : a1 <;> cases h1' : a1' <;> rw [h1, h1'] at hx1
    · exact absurd rfl hx1
    · exact fun h => hx1 h.symm
    · exact hx1
    · exact absurd rfl hx1
  have hvinj : v true ≠ v false := by
    cases h2 : a2 <;> cases h2' : a2' <;> rw [h2, h2'] at hx2
    · exact absurd rfl hx2
    · exact fun h => hx2 h.symm
    · exact hx2
    · exact absurd rfl hx2
  have hunot : u true = !(u false) := by
    cases h : u false <;> cases h' : u true <;> simp_all
  have hvnot : v true = !(v false) := by
    cases h : v false <;> cases h' : v true <;> simp_all
  have hall : ∀ b, u b = v b := by
    intro b
    cases hb : b <;> cases ha : aa <;> rw [ha] at hxa
    · exact hxa
    · rw [show u false = !(u true) from by rw [hunot]; cases u false <;> rfl,
        show v false = !(v true) from by rw [hvnot]; cases v false <;> rfl, hxa]
    · rw [hunot, hvnot, hxa]
    · exact hxa
  exact hxd (hall ad)

/-- **THE ENGINE (proved)**: two rows that differ somewhere, agree somewhere, and are each non-constant
overflow every bipartite decomposition. -/
theorem no_split_two_rows {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n))
    (op : Bool → Bool → Bool) (g h : (Fin n → Bool) → Bool)
    (hg : ∀ x y : Fin n → Bool, (∀ i, i ∈ S → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin n → Bool, (∀ i, i ∉ S → x i = y i) → h x = h y)
    (hf : ∀ x, f x = op (g x) (h x))
    (y₁ y₂ : Fin n → Bool)
    (hdiff : ∃ x, f (mixOn S x y₁) ≠ f (mixOn S x y₂))
    (hagree : ∃ x, f (mixOn S x y₁) = f (mixOn S x y₂))
    (hnc₁ : ∃ x x', f (mixOn S x y₁) ≠ f (mixOn S x' y₁))
    (hnc₂ : ∃ x x', f (mixOn S x y₂) ≠ f (mixOn S x' y₂)) : False := by
  have hrow : ∀ x y : Fin n → Bool,
      f (mixOn S x y) = op (g (mixOn S x y₁)) (h (mixOn S y₁ y)) := by
    intro x y
    rw [hf]
    congr 1
    · apply hg
      intro i hi
      show (if i ∈ S then x i else y i) = (if i ∈ S then x i else y₁ i)
      rw [if_pos hi, if_pos hi]
    · apply hh
      intro i hi
      show (if i ∈ S then x i else y i) = (if i ∈ S then y₁ i else y i)
      rw [if_neg hi, if_neg hi]
  obtain ⟨xd, hxd⟩ := hdiff
  obtain ⟨xa, hxa⟩ := hagree
  obtain ⟨x1, x1', hx1⟩ := hnc₁
  obtain ⟨x2, x2', hx2⟩ := hnc₂
  rw [hrow xd y₁, hrow xd y₂] at hxd
  rw [hrow xa y₁, hrow xa y₂] at hxa
  rw [hrow x1 y₁, hrow x1' y₁] at hx1
  rw [hrow x2 y₂, hrow x2' y₂] at hx2
  exact two_injective_unaries
    (fun b => op b (h (mixOn S y₁ y₁))) (fun b => op b (h (mixOn S y₁ y₂)))
    (g (mixOn S xd y₁)) (g (mixOn S xa y₁)) (g (mixOn S x1 y₁)) (g (mixOn S x1' y₁))
    (g (mixOn S x2 y₁)) (g (mixOn S x2' y₁)) hxd hxa hx1 hx2

/-- **THE FRAME (proved)**: a minimal SAT circuit at excess zero yields the engine's hypothesis exactly. -/
theorem sat3_split_frame (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N))
    (hex : coneExcess c (c.length - 1) = 0) :
    ∃ (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (S : Finset (Fin N)),
      (∀ x y : Fin N → Bool, (∀ i, i ∈ S → x i = y i) → g x = g y) ∧
      (∀ x y : Fin N → Bool, (∀ i, i ∉ S → x i = y i) → h x = h y) ∧
      (∀ x, sat3Family N x = op (g x) (h x)) := by
  classical
  obtain ⟨op, L, R, hroot, hL, hR, hLR⟩ := sat3_root_shape N hv hm3 hk c hcomp hmin
  obtain ⟨hdisj, hsplit⟩ := excess_zero_top_split (sat3Family N) c hcomp hex op L R
    hroot hL hR hLR
  refine ⟨op, fun x => (runFrom x [] c).getD L false,
    fun x => (runFrom x [] c).getD R false,
    Finset.univ.filter (fun i => ∃ p ∈ coneOf c L,
      c.getD p (CGate.cst false) = CGate.var i), ?_, ?_, hsplit⟩
  · -- the L-wire reads only S
    intro x y hxy
    apply cone_val_agree c L x y ?_ L (cone_self c L)
    intro p hp i hgate
    apply hxy
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ i, p, hp, hgate⟩
  · -- the R-wire reads only the complement: its cone variables never lie in S
    intro x y hxy
    apply cone_val_agree c R x y ?_ R (cone_self c R)
    intro p hp i hgate
    apply hxy
    rw [Finset.mem_filter]
    rintro ⟨-, q, hq, hgate'⟩
    -- two var-gates for i, one in each cone: they coincide (read-uniqueness), but cones are disjoint
    have hplt : p < c.length - 1 := by
      have h1 := cone_le c R p hp
      omega
    have hqlt : q < c.length - 1 := by
      have h1 := cone_le c L q hq
      omega
    have hpq : p = q := by
      rcases Nat.lt_trichotomy p q with hlt | heq | hgt
      · exact absurd (var_gate_unique (sat3Family N) c hcomp hmin i p q hlt hqlt
          hgate hgate') (fun h => h)
      · exact heq
      · exact absurd (var_gate_unique (sat3Family N) c hcomp hmin i q p hgt hplt
          hgate' hgate) (fun h => h)
    rw [Finset.disjoint_left] at hdisj
    exact hdisj hq (hpq ▸ hp)

/-- The named witness-production hypothesis — **NOT discharged**: SAT admits no bipartite split.  For every
decomposition `sat3 = op (g|_S, h|_Sᶜ)` there is a refutation. -/
def Sat3NoBipartiteSplit (N : ℕ) : Prop :=
  ∀ (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (S : Finset (Fin N)),
    (∀ x y : Fin N → Bool, (∀ i, i ∈ S → x i = y i) → g x = g y) →
    (∀ x y : Fin N → Bool, (∀ i, i ∉ S → x i = y i) → h x = h y) →
    (∀ x, sat3Family N x = op (g x) (h x)) → False

/-- **CONDITIONAL (hypothesis named, not claimed)**: no bipartite split ⇒ every minimal circuit pays
excess ≥ 1. -/
theorem sat3_excess_pos_of_no_split (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hW : Sat3NoBipartiteSplit N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N)) :
    1 ≤ coneExcess c (c.length - 1) := by
  by_contra hcon
  push_neg at hcon
  have hex : coneExcess c (c.length - 1) = 0 := by omega
  obtain ⟨op, g, h, S, hg, hh, hf⟩ := sat3_split_frame N hv hm3 hk c hcomp hmin hex
  exact hW op g h S hg hh hf

/-- **CONDITIONAL CASH-OUT (hypothesis named, not claimed)**: no bipartite split ⇒ `2·m·D ≤ cbudget` —
one gate past the connectivity record. -/
theorem sat3_cbudget_2mD_of_no_split (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hW : Sat3NoBipartiteSplit N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N)) :
    2 * (sat3M N * sat3D N) ≤ cbudget (sat3Family N) := by
  have h1 := sat3_excess_priced N hv (by omega) c hcomp hmin
  have h2 := sat3_excess_pos_of_no_split N hv hm3 hk hW c hcomp hmin
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.no_split_two_rows
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_split_frame
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cbudget_2mD_of_no_split
