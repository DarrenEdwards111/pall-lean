import PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposableMachine

/-!
# Head-move construction, brick 9: the two-track marker seek (`scanMarker`)

To read the simulated symbol at the marked head, the data bits and the head-marker have to coexist on
one Bool tape.  With a Bool alphabet there is no third symbol, so the honest layout is **two-track**:
simulated cell `i` occupies physical cells `2i` (data) and `2i+1` (marker).  The marker track holds a
single `true`, at `2·hd+1`; the data track (even cells) is arbitrary.

Seeking to the head therefore cannot be `scanToTrue` (brick 4) — that would stop at a data `true`.  It
must be a **scan-by-2** that inspects only the marker cells.  This brick builds that machine,
`scanMarker`, and proves it lands on the marker regardless of the data bits.

## What is proved

* **`scanMarker`** — a three-state machine (`atData → atMarker → found`): at a data cell, step right to
  its marker cell (ignoring data); at a marker cell, halt if `true`, else step right to the next data
  cell.  No writes.
* **`scanMarker_partial`** — the two-step-cycle invariant: for `k ≤ m`, after `2k` steps the machine is
  back at a data cell, `run scanMarker (2*k) c = ⟨atData, c.hd + 2*k, c.tp⟩` (still scanning).
* **`scanMarker_run`** — if marker cells `0..m-1` are `false` and cell `m` is `true`, then after
  `2m + 2` steps the machine halts on the marker: `⟨found, c.hd + 2*m + 1, c.tp⟩`.  The data bits are
  never inspected — this is a pure marker-track seek.
* **`scanMarker_seeks`** — the concrete payoff on `replicate (2*m+1) false ++ (true :: post)`, head `0`.

The head cell's data bit then sits at `c.hd + 2*m` — one cell left of where `scanMarker` halts — which
is what the read phase reads.

## Honest scope

`scanMarker` is the two-track seek: the data-aware analog of brick 4.  What remains for `uStepOnTape`:
read the data cell adjacent to the marker (brick 3's `readBit`, one step left), the rule-lookup scan,
and the reset-to-0 per-step wrapper; then the lazy-delay diagonal.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineScanMarker

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- Control states of `scanMarker`: at a data cell, at a marker cell, or found. -/
inductive Mark2 where
  | atData : Mark2
  | atMarker : Mark2
  | found : Mark2
  deriving DecidableEq

instance : Fintype Mark2 := ⟨{.atData, .atMarker, .found}, fun x => by cases x <;> decide⟩

/-- **The two-track marker seek.**  At a data cell: step right to the marker cell (ignore data).  At a
marker cell: halt if `true`, else step right to the next data cell.  No writes. -/
def scanMarker : Machine where
  State := Mark2
  fin := inferInstance
  dec := inferInstance
  start := Mark2.atData
  halt := fun s => match s with | .found => true | _ => false
  δ := fun s b => match s with
    | .atData => (Mark2.atMarker, none, (1 : Move))
    | .atMarker => if b then (Mark2.found, none, (2 : Move)) else (Mark2.atData, none, (1 : Move))
    | .found => (Mark2.found, none, (2 : Move))
  accept := fun _ => false

theorem scanMarker_step_active {c : Cfg scanMarker} (hne : scanMarker.halt c.st = false) :
    step scanMarker c = ⟨(scanMarker.δ c.st (c.tp.getD c.hd false)).1,
                    moveHead c.hd (scanMarker.δ c.st (c.tp.getD c.hd false)).2.2,
                    (match (scanMarker.δ c.st (c.tp.getD c.hd false)).2.1 with
                      | none => c.tp | some w => writeAt c.tp c.hd w)⟩ := by
  unfold step; rw [hne]; rfl

theorem scanMarker_step_data {c : Cfg scanMarker} (hs : c.st = Mark2.atData) :
    step scanMarker c = ⟨Mark2.atMarker, c.hd + 1, c.tp⟩ := by
  rw [scanMarker_step_active (by rw [hs]; rfl), hs]; rfl

theorem scanMarker_step_marker_false {c : Cfg scanMarker} (hs : c.st = Mark2.atMarker)
    (hb : c.tp.getD c.hd false = false) : step scanMarker c = ⟨Mark2.atData, c.hd + 1, c.tp⟩ := by
  rw [scanMarker_step_active (by rw [hs]; rfl), hs, hb]; rfl

theorem scanMarker_step_marker_true {c : Cfg scanMarker} (hs : c.st = Mark2.atMarker)
    (hb : c.tp.getD c.hd false = true) : step scanMarker c = ⟨Mark2.found, c.hd, c.tp⟩ := by
  rw [scanMarker_step_active (by rw [hs]; rfl), hs, hb]; rfl

/-- **The two-step-cycle invariant (proved).**  While the first `m` marker cells are `false`, after
`2k` steps (`k ≤ m`) the machine is back at a data cell, still scanning. -/
theorem scanMarker_partial (m : ℕ) (c : Cfg scanMarker) (hstart : c.st = Mark2.atData)
    (hfalse : ∀ k, k < m → c.tp.getD (c.hd + 2 * k + 1) false = false) :
    ∀ k, k ≤ m → run scanMarker (2 * k) c = ⟨Mark2.atData, c.hd + 2 * k, c.tp⟩ := by
  intro k
  induction k with
  | zero => intro _; obtain ⟨st, hd', tp⟩ := c; subst hstart; rfl
  | succ k ih =>
    intro hle
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add, ih (by omega)]
    show step scanMarker (step scanMarker ⟨Mark2.atData, c.hd + 2 * k, c.tp⟩) = _
    rw [scanMarker_step_data (c := ⟨Mark2.atData, c.hd + 2 * k, c.tp⟩) rfl,
      scanMarker_step_marker_false (c := ⟨Mark2.atMarker, c.hd + 2 * k + 1, c.tp⟩) rfl
        (hfalse k (by omega))]
    show (⟨Mark2.atData, c.hd + 2 * k + 1 + 1, c.tp⟩ : Cfg scanMarker)
        = ⟨Mark2.atData, c.hd + 2 * (k + 1), c.tp⟩
    rw [show c.hd + 2 * k + 1 + 1 = c.hd + 2 * (k + 1) from by ring]

/-- **The seek is correct (proved).**  Marker cells `0..m-1` false and cell `m` true ⇒ after `2m + 2`
steps `scanMarker` halts on the marker at `c.hd + 2*m + 1`, tape unchanged, data never inspected. -/
theorem scanMarker_run (m : ℕ) (c : Cfg scanMarker) (hstart : c.st = Mark2.atData)
    (hfalse : ∀ k, k < m → c.tp.getD (c.hd + 2 * k + 1) false = false)
    (htrue : c.tp.getD (c.hd + 2 * m + 1) false = true) :
    run scanMarker (2 * m + 2) c = ⟨Mark2.found, c.hd + 2 * m + 1, c.tp⟩ := by
  rw [run_add, scanMarker_partial m c hstart hfalse m (le_refl m)]
  show step scanMarker (step scanMarker ⟨Mark2.atData, c.hd + 2 * m, c.tp⟩) = _
  rw [scanMarker_step_data (c := ⟨Mark2.atData, c.hd + 2 * m, c.tp⟩) rfl,
    scanMarker_step_marker_true (c := ⟨Mark2.atMarker, c.hd + 2 * m + 1, c.tp⟩) rfl htrue]

/-- **Concrete payoff (proved).**  On `replicate (2*m+1) false ++ (true :: post)` with the head at `0`
(marker at physical cell `2m+1`), `scanMarker` seeks to it in `2m + 2` steps. -/
theorem scanMarker_seeks (m : ℕ) (post : List Bool) :
    run scanMarker (2 * m + 2)
        ⟨Mark2.atData, 0, List.replicate (2 * m + 1) false ++ (true :: post)⟩
      = ⟨Mark2.found, 2 * m + 1, List.replicate (2 * m + 1) false ++ (true :: post)⟩ := by
  rw [scanMarker_run m ⟨Mark2.atData, 0, List.replicate (2 * m + 1) false ++ (true :: post)⟩ rfl
    (fun k hk => by
      show (List.replicate (2 * m + 1) false ++ (true :: post)).getD (0 + 2 * k + 1) false = false
      rw [Nat.zero_add, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [List.length_replicate]; omega),
        List.getElem?_replicate_of_lt (by omega)]
      rfl)
    (by
      show (List.replicate (2 * m + 1) false ++ (true :: post)).getD (0 + 2 * m + 1) false = true
      rw [Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp),
        List.length_replicate, Nat.sub_self]
      rfl)]
  show (⟨Mark2.found, 0 + 2 * m + 1, _⟩ : Cfg scanMarker) = ⟨Mark2.found, 2 * m + 1, _⟩
  rw [Nat.zero_add]

end PallLean.Paper93.DeepMath.PathB.UniversalMachineScanMarker

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineScanMarker.scanMarker_run
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineScanMarker.scanMarker_seeks
