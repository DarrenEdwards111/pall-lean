import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTraceExtraction

/-!
# N-Frame: the exit-set instantiation — trace width is priced by cone excess

Rung (1) of the extraction: minimal circuits produce trace-interfaced factorizations whose trace is
the **exit set** of the shared cone region, and the exit set is charged to `coneExcess`.

  `sep_frontier_val_agree` — **PROVED, the separated frontier**: if every entry into a region `T`
        from outside passes through `F ⊆ T`, then agreement on `F`-wire values plus agreement on
        the variables of out-of-`T` gates determines every out-of-`T` cone value.  (Sharpens
        `frontier_val_agree`: variables of gates *inside* `T \ F` are never consulted.)
  `exitSet` — the wires of `coneL ∩ coneR` read from outside the intersection (plus `L`, `R`
        themselves when shared).
  `exitSet_card_le_coneExcess` — **PROVED, the charge**: every exit wire has two distinct cone
        readers — one from each side, distinct because one of them avoids the intersection — so
        `|exitSet| ≤ coneExcess` via the multi-reader bound.
  `sat3_top_cut_trace_extraction` — **PROVED, the extraction**: every minimal SAT circuit yields
        `TraceInterfacedFactorization (sat3Family N) (varsOf L \ varsOf R) j` with
        `j ≤ coneExcess` — the wire-frontier → trace-interface bridge, instantiated.  `G` is the
        `L`-wire value, determined by the exclusive-left variables plus the exit trace
        (`sep_frontier_val_agree` + `var_gate_unique` to keep out-of-region variables exclusive);
        `H` and the trace are blind on the exclusive-left side.

## Honest scope

With this, `rows_force_trace` converts row families over `varsOf L \ varsOf R` into `coneExcess`
lower bounds.  Remaining, named: (2) the **swallowed-side recursion** — when one cone's variable
support contains the other's, the top cut is degenerate and the argument must descend; the descent
target (which node, what invariant survives) is a genuine design problem, not bookkeeping; (3) the
**trace upgrade of the counting arc** — the row-capacity family (propagations) upgrades through the
trace engine; the coordinate-interning counts (sign graph, escape counts, menus) do **not**, and
replacing them at trace strength is the remaining semantic work.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE SEPARATED FRONTIER (proved)**: if every entry into `T` passes through `F`, agreement on
`F`-values plus out-of-`T` variables determines every out-of-`T` cone value. -/
theorem sep_frontier_val_agree {n : ℕ} (c : List (CGate n)) (root : ℕ)
    (T F : Finset ℕ)
    (hsep : ∀ q ∈ coneOf c root, q ∉ T → ∀ w ∈ childrenOf c q, w ∈ T → w ∈ F)
    (x x' : Fin n → Bool)
    (hFval : ∀ p ∈ F, (runFrom x [] c).getD p false = (runFrom x' [] c).getD p false)
    (hfront : ∀ q ∈ coneOf c root, q ∉ T →
      ∀ i, c.getD q (CGate.cst false) = CGate.var i → x i = x' i) :
    ∀ q, q ∈ coneOf c root → q ∉ T →
      (runFrom x [] c).getD q false = (runFrom x' [] c).getD q false := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq hqT
    by_cases hlen : q < c.length
    · rw [output_getD_at x c q hlen, output_getD_at x' c q hlen]
      cases hg : c.getD q (CGate.cst false) with
      | var i =>
        show x i = x' i
        exact hfront q hq hqT i hg
      | cst b => rfl
      | un op j =>
        show op ((runFrom x [] (c.take q)).getD j false)
            = op ((runFrom x' [] (c.take q)).getD j false)
        by_cases hj : j < q
        · rw [takeRun_getD x c q j hj (le_of_lt hlen),
            takeRun_getD x' c q j hj (le_of_lt hlen)]
          have hjc : j ∈ childrenOf c q := by
            rw [childrenOf_eq_un c q op j hg, if_pos hj]
            exact Finset.mem_singleton_self j
          have hjcone : j ∈ coneOf c root := cone_child c root q hq j hjc
          by_cases hjT : j ∈ T
          · rw [hFval j (hsep q hq hqT j hjc hjT)]
          · rw [ih j hj hjcone hjT]
        · have hxlen : (runFrom x [] (c.take q)).length ≤ j := by
            rw [runFrom_length x (c.take q) [], List.length_take]
            show ([] : List Bool).length + min q c.length ≤ j
            simp only [List.length_nil]
            omega
          have hxlen' : (runFrom x' [] (c.take q)).length ≤ j := by
            rw [runFrom_length x' (c.take q) [], List.length_take]
            show ([] : List Bool).length + min q c.length ≤ j
            simp only [List.length_nil]
            omega
          rw [List.getD_eq_default _ false hxlen, List.getD_eq_default _ false hxlen']
      | bin op j k =>
        show op ((runFrom x [] (c.take q)).getD j false)
              ((runFrom x [] (c.take q)).getD k false)
            = op ((runFrom x' [] (c.take q)).getD j false)
              ((runFrom x' [] (c.take q)).getD k false)
        have hjv : (runFrom x [] (c.take q)).getD j false
            = (runFrom x' [] (c.take q)).getD j false := by
          by_cases hj : j < q
          · rw [takeRun_getD x c q j hj (le_of_lt hlen),
              takeRun_getD x' c q j hj (le_of_lt hlen)]
            have hjc : j ∈ childrenOf c q := by
              rw [childrenOf_eq_bin c q op j k hg]
              apply Finset.mem_union_left
              rw [if_pos hj]
              exact Finset.mem_singleton_self j
            have hjcone : j ∈ coneOf c root := cone_child c root q hq j hjc
            by_cases hjT : j ∈ T
            · exact hFval j (hsep q hq hqT j hjc hjT)
            · exact ih j hj hjcone hjT
          · have hxlen : (runFrom x [] (c.take q)).length ≤ j := by
              rw [runFrom_length x (c.take q) [], List.length_take]
              show ([] : List Bool).length + min q c.length ≤ j
              simp only [List.length_nil]
              omega
            have hxlen' : (runFrom x' [] (c.take q)).length ≤ j := by
              rw [runFrom_length x' (c.take q) [], List.length_take]
              show ([] : List Bool).length + min q c.length ≤ j
              simp only [List.length_nil]
              omega
            rw [List.getD_eq_default _ false hxlen, List.getD_eq_default _ false hxlen']
        have hkv : (runFrom x [] (c.take q)).getD k false
            = (runFrom x' [] (c.take q)).getD k false := by
          by_cases hkq : k < q
          · rw [takeRun_getD x c q k hkq (le_of_lt hlen),
              takeRun_getD x' c q k hkq (le_of_lt hlen)]
            have hkc : k ∈ childrenOf c q := by
              rw [childrenOf_eq_bin c q op j k hg]
              apply Finset.mem_union_right
              rw [if_pos hkq]
              exact Finset.mem_singleton_self k
            have hkcone : k ∈ coneOf c root := cone_child c root q hq k hkc
            by_cases hkT : k ∈ T
            · exact hFval k (hsep q hq hqT k hkc hkT)
            · exact ih k hkq hkcone hkT
          · have hxlen : (runFrom x [] (c.take q)).length ≤ k := by
              rw [runFrom_length x (c.take q) [], List.length_take]
              show ([] : List Bool).length + min q c.length ≤ k
              simp only [List.length_nil]
              omega
            have hxlen' : (runFrom x' [] (c.take q)).length ≤ k := by
              rw [runFrom_length x' (c.take q) [], List.length_take]
              show ([] : List Bool).length + min q c.length ≤ k
              simp only [List.length_nil]
              omega
            rw [List.getD_eq_default _ false hxlen, List.getD_eq_default _ false hxlen']
        rw [hjv, hkv]
    · have hLn : (runFrom x [] c).length ≤ q := by
        rw [runFrom_length x c []]
        show ([] : List Bool).length + c.length ≤ q
        simp only [List.length_nil]
        omega
      have hLn' : (runFrom x' [] c).length ≤ q := by
        rw [runFrom_length x' c []]
        show ([] : List Bool).length + c.length ≤ q
        simp only [List.length_nil]
        omega
      rw [List.getD_eq_default _ false hLn, List.getD_eq_default _ false hLn']

open Classical in
/-- The exit set of the shared cone region: its wires read from outside, plus the tops. -/
noncomputable def exitSet {n : ℕ} (c : List (CGate n)) (L R : ℕ) : Finset ℕ :=
  (coneOf c L ∩ coneOf c R).filter (fun w => w = L ∨ w = R ∨
    ∃ r ∈ coneOf c L ∪ coneOf c R, r ∉ coneOf c L ∩ coneOf c R ∧ w ∈ childrenOf c r)

/-- Cone variable supports are monotone along cone membership. -/
theorem varsOf_mono {n : ℕ} (c : List (CGate n)) (r s : ℕ)
    (hrs : r ∈ coneOf c s) : varsOf c r ⊆ varsOf c s := by
  classical
  intro i hi
  obtain ⟨-, p, hp, hgate⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, p, cone_trans c s r hrs p hp, hgate⟩

/-- **THE CHARGE (proved)**: every exit wire has two distinct readers in the root cone, so the exit
set is priced by `coneExcess`. -/
theorem exitSet_card_le_coneExcess {n : ℕ} (c : List (CGate n))
    (op : Bool → Bool → Bool) (L R : ℕ)
    (hroot : c.getD (c.length - 1) (CGate.cst false) = CGate.bin op L R)
    (hL : L < c.length - 1) (hR : R < c.length - 1) (hLR : L ≠ R) :
    (exitSet c L R).card ≤ coneExcess c (c.length - 1) := by
  classical
  have hLch : L ∈ childrenOf c (c.length - 1) := by
    rw [childrenOf_eq_bin c (c.length - 1) op L R hroot]
    exact Finset.mem_union_left _
      (by rw [if_pos hL]; exact Finset.mem_singleton_self L)
  have hRch : R ∈ childrenOf c (c.length - 1) := by
    rw [childrenOf_eq_bin c (c.length - 1) op L R hroot]
    exact Finset.mem_union_right _
      (by rw [if_pos hR]; exact Finset.mem_singleton_self R)
  have hLroot : L ∈ coneOf c (c.length - 1) :=
    cone_child c _ _ (cone_self c (c.length - 1)) L hLch
  have hRroot : R ∈ coneOf c (c.length - 1) :=
    cone_child c _ _ (cone_self c (c.length - 1)) R hRch
  refine le_trans (Finset.card_le_card ?_)
    (coneExcess_ge_multiReader c (c.length - 1))
  intro w hw
  obtain ⟨hwI, hcase⟩ := Finset.mem_filter.mp hw
  have hwL : w ∈ coneOf c L := (Finset.mem_inter.mp hwI).1
  have hwR : w ∈ coneOf c R := (Finset.mem_inter.mp hwI).2
  have hwle : w ≤ L := cone_le c L w hwL
  have hwroot : w ∈ coneOf c (c.length - 1) := cone_trans c _ L hLroot w hwL
  have h2 : ∃ r₁ ∈ coneOf c (c.length - 1), ∃ r₂ ∈ coneOf c (c.length - 1),
      r₁ ≠ r₂ ∧ w ∈ childrenOf c r₁ ∧ w ∈ childrenOf c r₂ := by
    rcases hcase with hwL' | hwR' | ⟨r, hrmem, hrI, hrch⟩
    · subst hwL'
      rcases cone_parent c R w hwR with heq | ⟨r₂, hr₂, hch₂⟩
      · exact absurd heq hLR
      · have hr₂le : r₂ ≤ R := cone_le c R r₂ hr₂
        exact ⟨c.length - 1, cone_self c _, r₂,
          cone_trans c _ R hRroot r₂ hr₂, by omega, hLch, hch₂⟩
    · subst hwR'
      rcases cone_parent c L w hwL with heq | ⟨r₁, hr₁, hch₁⟩
      · exact absurd heq.symm hLR
      · have hr₁le : r₁ ≤ L := cone_le c L r₁ hr₁
        exact ⟨r₁, cone_trans c _ L hLroot r₁ hr₁, c.length - 1,
          cone_self c _, by omega, hch₁, hRch⟩
    · have hrnotI : ¬(r ∈ coneOf c L ∧ r ∈ coneOf c R) := by
        intro hcon
        exact hrI (Finset.mem_inter.mpr hcon)
      rw [Finset.mem_union] at hrmem
      rcases hrmem with hrL | hrR
      · have hrnR : r ∉ coneOf c R := fun hc => hrnotI ⟨hrL, hc⟩
        rcases cone_parent c R w hwR with heq | ⟨r₂, hr₂, hch₂⟩
        · subst heq
          exact ⟨r, cone_trans c _ L hLroot r hrL, c.length - 1,
            cone_self c _, (by have := cone_le c L r hrL; omega), hrch, hRch⟩
        · refine ⟨r, cone_trans c _ L hLroot r hrL, r₂,
            cone_trans c _ R hRroot r₂ hr₂, ?_, hrch, hch₂⟩
          intro hcon
          rw [hcon] at hrnR
          exact hrnR hr₂
      · have hrnL : r ∉ coneOf c L := fun hc => hrnotI ⟨hc, hrR⟩
        rcases cone_parent c L w hwL with heq | ⟨r₁, hr₁, hch₁⟩
        · subst heq
          exact ⟨c.length - 1, cone_self c _, r,
            cone_trans c _ R hRroot r hrR,
            (by have := cone_le c R r hrR; omega), hLch, hrch⟩
        · refine ⟨r₁, cone_trans c _ L hLroot r₁ hr₁, r,
            cone_trans c _ R hRroot r hrR, ?_, hch₁, hrch⟩
          intro hcon
          rw [← hcon] at hrnL
          exact hrnL hr₁
  obtain ⟨r₁, hr₁c, r₂, hr₂c, hne, hch₁, hch₂⟩ := h2
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_erase.mpr ⟨by omega, hwroot⟩, ?_⟩
  have h1lt : 1 < ((coneOf c (c.length - 1)).filter
      (fun q => w ∈ childrenOf c q)).card :=
    Finset.one_lt_card.mpr ⟨r₁, Finset.mem_filter.mpr ⟨hr₁c, hch₁⟩,
      r₂, Finset.mem_filter.mpr ⟨hr₂c, hch₂⟩, hne⟩
  omega

/-- **THE EXIT-SET EXTRACTION (proved)**: every minimal SAT circuit yields a trace-interfaced
factorization over its exclusive-left variables whose trace width is at most its cone excess. -/
theorem sat3_top_cut_trace_extraction (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N)) :
    ∃ L R j : ℕ, j ≤ coneExcess c (c.length - 1) ∧
      TraceInterfacedFactorization (sat3Family N) (varsOf c L \ varsOf c R) j := by
  classical
  obtain ⟨op, L, R, hroot, hL, hR, hLR⟩ := sat3_root_shape N hv hm3 hk c hcomp hmin
  refine ⟨L, R, (exitSet c L R).card,
    exitSet_card_le_coneExcess c op L R hroot hL hR hLR, op,
    fun x => (runFrom x [] c).getD L false,
    fun x => (runFrom x [] c).getD R false,
    fun x e => (runFrom x [] c).getD (((exitSet c L R).equivFin.symm e).val) false,
    ?_, ?_, ?_,
    top_split_eval (sat3Family N) c hcomp op L R hroot hL hR⟩
  · -- the trace is blind on the exclusive-left side
    intro x y hxy
    funext e
    apply varsOf_agree_wire c (((exitSet c L R).equivFin.symm e).val) x y
    intro i hi
    apply hxy
    intro hiS
    have hprop := ((exitSet c L R).equivFin.symm e).2
    have hweR : (((exitSet c L R).equivFin.symm e).val) ∈ coneOf c R :=
      (Finset.mem_inter.mp (Finset.mem_filter.mp hprop).1).2
    have hiR : i ∈ varsOf c R := varsOf_mono c _ R hweR hi
    exact (Finset.mem_sdiff.mp hiS).2 hiR
  · -- G: the L-wire, determined by the exclusive-left variables plus the trace
    intro x y hxy hφxy
    have hFval : ∀ p ∈ exitSet c L R,
        (runFrom x [] c).getD p false = (runFrom y [] c).getD p false := by
      intro p hp
      have hidx := congrFun hφxy ((exitSet c L R).equivFin ⟨p, hp⟩)
      simp only [Equiv.symm_apply_apply] at hidx
      exact hidx
    by_cases hLI : L ∈ coneOf c R
    · exact hFval L (Finset.mem_filter.mpr
        ⟨Finset.mem_inter.mpr ⟨cone_self c L, hLI⟩, Or.inl rfl⟩)
    · have hsepPf : ∀ q ∈ coneOf c L, q ∉ coneOf c L ∩ coneOf c R →
          ∀ w ∈ childrenOf c q, w ∈ coneOf c L ∩ coneOf c R →
          w ∈ exitSet c L R := by
        intro q hq hqT w hwch hwT
        exact Finset.mem_filter.mpr ⟨hwT, Or.inr (Or.inr
          ⟨q, Finset.mem_union_left _ hq, hqT, hwch⟩)⟩
      have hfrontPf : ∀ q ∈ coneOf c L, q ∉ coneOf c L ∩ coneOf c R →
          ∀ i, c.getD q (CGate.cst false) = CGate.var i → x i = y i := by
        intro q hq hqT i hgate
        apply hxy
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ i, q, hq, hgate⟩, ?_⟩
        intro hiR
        obtain ⟨-, p, hpR, hgate'⟩ := Finset.mem_filter.mp hiR
        have hqle : q ≤ L := cone_le c L q hq
        have hple : p ≤ R := cone_le c R p hpR
        have hpq : p = q := by
          rcases Nat.lt_trichotomy p q with hlt | heq | hgt
          · exact (var_gate_unique (sat3Family N) c hcomp hmin i p q hlt
              (by omega) hgate' hgate).elim
          · exact heq
          · exact (var_gate_unique (sat3Family N) c hcomp hmin i q p hgt
              (by omega) hgate hgate').elim
        apply hqT
        refine Finset.mem_inter.mpr ⟨hq, ?_⟩
        rw [← hpq]
        exact hpR
      exact sep_frontier_val_agree c L (coneOf c L ∩ coneOf c R) (exitSet c L R)
        hsepPf x y hFval hfrontPf L (cone_self c L)
        (fun hc => hLI (Finset.mem_inter.mp hc).2)
  · -- H: the R-wire, blind on the exclusive-left side
    intro x y hxy
    apply varsOf_agree_wire c R x y
    intro i hiR
    apply hxy
    intro hiS
    exact (Finset.mem_sdiff.mp hiS).2 hiR

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sep_frontier_val_agree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.exitSet_card_le_coneExcess
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_top_cut_trace_extraction
