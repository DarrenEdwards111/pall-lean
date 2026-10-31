import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameKPortCounting

/-!
# N-Frame: context uniformity — the determination identity, and the honest fate of the block bound

The uniformity step, done honestly.  The naive block statement — "a fixed selector-blind top over `p` ports
must have `p ≥ m−2` to realize `2^(m−2)` context subfunctions" — is **false**: `passthrough_mediates` gives a
*one-port* selector-blind top for every function, servicing every context, because the top reads the context
raw and absorbs all its dependence.  What survives, and is proved here, is the identity that any winning
count must route through:

  `eq_of_agree_off` — insensitivity at a list of coordinates propagates to full agreement off them.
  `joint_top_map_full` — the joint top map with all three clauses: reconstruction, joint selector-blindness,
        and port-locality.
  `joint_cube_factor` — **PROVED, the determination identity**: for a simultaneously mediated family, the
        port values together with the off-selector context **determine** `f` — two inputs agreeing off the
        mediated selectors and on the mediator wires have equal output.  All of `K` selectors' influence
        passes through `≥ K/2, ≤ K` port bits: the compression is real and exact.

## Honest scope — the irreducible core

The determination identity is the whole provable content of context uniformity.  Why it does not yet count:
the ports are *unconstrained wire functions* — a port may compute anything, including `f` itself — so any
bound on what `p` ports can realize is a bound on circuit-computable functions, i.e. the lower bound being
sought.  The face's core is exactly this circularity, now isolated: to make the determination identity count,
one must charge the ports' own circuit cost inside the same budget — a self-referential accounting no local
reduction removes.  That is the mountain; it is open and not claimed.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Insensitivity propagates to agreement -/

theorem eq_of_agree_off {n : ℕ} (g : (Fin n → Bool) → Bool) (T : List (Fin n))
    (hg : ∀ (x : Fin n → Bool), ∀ i ∈ T, ∀ b : Bool, g (Function.update x i b) = g x) :
    ∀ (D : Finset (Fin n)) (x x' : Fin n → Bool),
      (∀ i', x i' ≠ x' i' → i' ∈ D) → (∀ i' ∈ D, i' ∈ T) → g x = g x' := by
  classical
  intro D
  induction D using Finset.strongInduction with
  | _ D ih =>
    intro x x' hD hDT
    by_cases hall : ∀ i', x i' = x' i'
    · exact congrArg g (funext hall)
    · push_neg at hall
      obtain ⟨i₀, hi₀⟩ := hall
      have hi₀D : i₀ ∈ D := hD i₀ hi₀
      have hstep : g x = g (Function.update x i₀ (x' i₀)) :=
        (hg x i₀ (hDT i₀ hi₀D) (x' i₀)).symm
      rw [hstep]
      apply ih (D.erase i₀) (Finset.erase_ssubset hi₀D)
      · intro i' hne
        rw [Finset.mem_erase]
        by_cases hii : i' = i₀
        · exfalso
          apply hne
          rw [hii, Function.update_self]
        · refine ⟨hii, ?_⟩
          apply hD
          rwa [Function.update_of_ne hii] at hne
      · intro i' hi'
        exact hDT i' (Finset.mem_of_mem_erase hi')

/-! ### The joint top map with all three clauses -/

/-- **The full joint top map (proved)**: reconstruction, joint selector-blindness, and port-locality. -/
theorem joint_top_map_full {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (S : List (Fin n × ℕ × ℕ))
    (hS : ∀ t ∈ S, MediatedAt c t.1 t.2.1 t.2.2) :
    ∃ H : (ℕ → Bool) → (Fin n → Bool) → Bool,
      (∀ x, f x = H (fun r => (runFrom x [] c).getD r false) x) ∧
      (∀ (v : ℕ → Bool) (x : Fin n → Bool) (t : Fin n × ℕ × ℕ), t ∈ S → ∀ b : Bool,
        H v (Function.update x t.1 b) = H v x) ∧
      (∀ (v v' : ℕ → Bool) (x : Fin n → Bool),
        (∀ t ∈ S, v t.2.2 = v' t.2.2) → H v x = H v' x) := by
  obtain ⟨H₀, h1, h2⟩ := joint_top_map f c hcomp S hS
  -- the constructed witness is the pinned-circuit output; rebuild it explicitly for port-locality
  have hSlen : ∀ t ∈ S, t.2.2 < c.length := by
    intro t ht
    have h := (hS t ht).2.2.2.1
    omega
  refine ⟨fun v x => output (pinAll v S c) x, ?_, ?_, ?_⟩
  · intro x
    have hrun := pinAll_run_eq x (runFrom x [] c) S c hSlen rfl (fun t _ => rfl)
      (fun r => (runFrom x [] c).getD r false) (fun t _ => rfl)
    show f x = (runFrom x [] (pinAll (fun r => (runFrom x [] c).getD r false) S c)).getD
        ((pinAll (fun r => (runFrom x [] c).getD r false) S c).length - 1) false
    rw [hrun, pinAll_length _ S c hSlen]
    exact (hcomp x).symm
  · intro v x t ht b
    have hmed := hS t ht
    have hdlen : (pinAll v S c).length = c.length := pinAll_length v S c hSlen
    show output (pinAll v S c) (Function.update x t.1 b) = output (pinAll v S c) x
    show (runFrom (Function.update x t.1 b) [] (pinAll v S c)).getD
        ((pinAll v S c).length - 1) false
      = (runFrom x [] (pinAll v S c)).getD ((pinAll v S c).length - 1) false
    apply cone_val_agree (pinAll v S c) ((pinAll v S c).length - 1)
      (Function.update x t.1 b) x ?_ _ (cone_self _ _)
    intro q hq i' hgate
    have hii : i' ≠ t.1 := by
      intro hii'
      rw [hii'] at hgate
      obtain ⟨hgc, hqpins⟩ := pinAll_getD_var v S c q t.1 hSlen hgate
      have hqp : q = t.2.1 := hmed.2.1 q hgc
      have hrint := hmed.2.2.2.1
      have hplr : t.2.1 < t.2.2 := children_lt c t.2.2 t.2.1 hmed.2.2.1
      rcases cone_parent _ _ q hq with h' | ⟨r', hr'cone, hr'child⟩
      · rw [hdlen] at h'
        omega
      · by_cases hr'pin : ∃ t' ∈ S, r' = t'.2.2
        · obtain ⟨t', ht', rfl⟩ := hr'pin
          rw [pinAll_children_pinned v S c t' ht' hSlen] at hr'child
          exact absurd hr'child (Finset.notMem_empty q)
        · push_neg at hr'pin
          rw [pinAll_children v S c r' hSlen (fun t' ht' => hr'pin t' ht')] at hr'child
          rw [hqp] at hr'child
          have hr'r := hmed.2.2.2.2 r' hr'child
          exact (hr'pin t ht) hr'r
    rw [Function.update_of_ne hii]
  · intro v v' x hvv
    exact jointH_ports c S v v' x hvv

/-! ### The determination identity -/

/-- **THE DETERMINATION IDENTITY (proved)**: for a simultaneously mediated family, port values together with
the off-selector context determine `f` — all of the selectors' influence passes through the ports. -/
theorem joint_cube_factor {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (S : List (Fin n × ℕ × ℕ))
    (hS : ∀ t ∈ S, MediatedAt c t.1 t.2.1 t.2.2)
    (x x' : Fin n → Bool)
    (hoff : ∀ i' : Fin n, (∀ t ∈ S, i' ≠ t.1) → x i' = x' i')
    (hports : ∀ t ∈ S,
      (runFrom x [] c).getD t.2.2 false = (runFrom x' [] c).getD t.2.2 false) :
    f x = f x' := by
  classical
  obtain ⟨H, h1, h2, h3⟩ := joint_top_map_full f c hcomp S hS
  rw [h1 x, h1 x']
  have hHagree : H (fun r => (runFrom x [] c).getD r false) x
      = H (fun r => (runFrom x [] c).getD r false) x' := by
    apply eq_of_agree_off (H (fun r => (runFrom x [] c).getD r false)) (S.map (·.1))
      (by
        intro y i hi b
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hi
        exact h2 _ y t ht b)
      (Finset.univ.filter (fun i' => x i' ≠ x' i')) x x'
    · intro i' hne
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i', hne⟩
    · intro i' hi'
      rw [Finset.mem_filter] at hi'
      by_contra hmem
      apply hi'.2
      apply hoff
      intro t ht
      intro hii
      apply hmem
      rw [hii]
      exact List.mem_map_of_mem ht
  rw [hHagree]
  exact h3 _ _ x' (fun t ht => hports t ht)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.eq_of_agree_off
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.joint_top_map_full
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.joint_cube_factor
