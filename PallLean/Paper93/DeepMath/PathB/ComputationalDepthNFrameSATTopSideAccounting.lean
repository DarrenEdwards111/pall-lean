import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSATMediationFace

/-!
# N-Frame: top-side accounting — re-entry remainders, port rigidity, and the SAT contrast

The top side, opened with definitions and its first exact boundary.  For each selector the canonical
remainder is `reentry f i v x := f (x[i := v])` — the function the shared top must compute once the
mediator bit `v` re-enters.  The first structural question about a shared top is **port rigidity**: does the
port act on the remainder through one fixed operation, `G v x = op v (h x)` with `h` blind to the selector?

  `reentry` / `reentry_self` / `reentry_indep` — **the object**: the canonical remainder, its
        reconstruction identity, and its selector-freeness.
  `rigid_iff_topDecomp` — **PROVED, the bridge**: the canonical remainder is port-rigid *iff* the function is
        top-decomposable at the selector — rigidity is exactly the boundary already mapped.
  `and_reentry_rigid` — **PROVED, calibration**: AND's remainders are rigid — a shared top services them
        with one fixed port operation, cheaply, as it must.
  `sat3_reentry_not_rigid` — **PROVED, the SAT contrast**: at every slot-2 selector, SAT's remainder is
        **not** port-rigid — the shared top must consult the context to know what the re-entering bit means.
        The behavior triple (identity / constant-true / constant-false) is irreducibly context-dependent.

## Honest scope — what the top-side face still needs

Single-port incompatibility is settled: it is non-rigidity, and SAT has it at all `m·v` slot-2 selectors.
But per-selector mediation does **not** compose into a joint factorization `f = H((vᵢ)_{i∈S}, x_{off S})` —
each remainder `G_i` may read the *other* selectors raw, and the pass-through/xor exceptions show pairwise
joint forms are free.  The open face is therefore *K-port compression*: extracting a joint bottleneck from
the circuit's **positional order** (mediators are wires in one DAG, computed in sequence) — the one resource
not yet exploited — and then counting SAT's remainders against it.  The cash-out pipeline
(`unmediated_dup_or_reuse` → `cbudget_fanout_kill` → `2N + Ω(K)`) stands ready.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The re-entry remainder -/

/-- The canonical top-side remainder: the function once the mediator bit re-enters at the selector. -/
def reentry {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n)
    (v : Bool) (x : Fin n → Bool) : Bool :=
  f (Function.update x i v)

theorem reentry_self {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) (x : Fin n → Bool) :
    reentry f i (x i) x = f x := by
  show f (Function.update x i (x i)) = f x
  rw [Function.update_eq_self]

theorem reentry_indep {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n)
    (v : Bool) (x : Fin n → Bool) (b' : Bool) :
    reentry f i v (Function.update x i b') = reentry f i v x := by
  show f (Function.update (Function.update x i b') i v) = f (Function.update x i v)
  rw [Function.update_idem]

/-! ### Port rigidity and the bridge -/

/-- A remainder is port-rigid when the port acts through one fixed operation, blind to context. -/
def RigidPort {n : ℕ} (G : Bool → (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  ∃ (op : Bool → Bool → Bool) (h : (Fin n → Bool) → Bool),
    (∀ v x, G v x = op v (h x)) ∧ (∀ x b, h (Function.update x i b) = h x)

/-- **THE BRIDGE (proved)**: the canonical remainder is port-rigid iff the function is top-decomposable at
the selector — single-port incompatibility is exactly the boundary already mapped. -/
theorem rigid_iff_topDecomp {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) :
    RigidPort (reentry f i) i ↔ TopDecomp f i := by
  constructor
  · rintro ⟨op, h, hfeq, hfree⟩
    refine ⟨op, h, ?_, hfree⟩
    intro x
    rw [← reentry_self f i x, hfeq (x i) x]
  · rintro ⟨op, h, hfeq, hfree⟩
    refine ⟨op, h, ?_, hfree⟩
    intro v x
    show f (Function.update x i v) = op v (h x)
    rw [hfeq (Function.update x i v)]
    rw [Function.update_self, hfree x v]

/-! ### Calibration and the SAT contrast -/

/-- **Calibration (proved)**: AND's remainders are port-rigid — a shared top services them with one fixed
port operation. -/
theorem and_reentry_rigid {n : ℕ} (i : Fin n) :
    RigidPort (reentry (fun x : Fin n → Bool => decide (∀ j, x j = true)) i) i :=
  (rigid_iff_topDecomp _ i).mpr (and_topDecomp i)

/-- **THE SAT CONTRAST (proved)**: at every slot-2 selector, SAT's remainder is not port-rigid — the shared
top must consult the context to know what the re-entering bit means. -/
theorem sat3_reentry_not_rigid (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (j : Fin (sat3V N)) :
    ¬RigidPort (reentry (sat3Family N) (sat3S2Sel N cIdx j)) (sat3S2Sel N cIdx j) := by
  intro hrig
  exact sat3_selector_notTopDecomp N hv hm2 cIdx j
    ((rigid_iff_topDecomp (sat3Family N) (sat3S2Sel N cIdx j)).mp hrig)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.rigid_iff_topDecomp
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.and_reentry_rigid
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_reentry_not_rigid
