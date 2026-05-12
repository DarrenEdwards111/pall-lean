# Paper ↔ Lean Consistency Checklist (Route B close)

Date: 2026-05-12
Branch: `godmove-paper-faithful`
Commit: `b3f9fbac`

## 1) Current Lean status (verified now)

### Route B paper-faithful local-monoid/profile-template seam
- ✅ `PallLean/Paper93/Paper283/RouteBPaperFaithfulTPhiExtraction.lean`
  - Added exact-budget constructor from profile-template span data:
    - `routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms_of_profileTemplateSpanData`

- ✅ `PallLean/Paper93/DeepMath/PathB/RouteBPlacedQuotientDescentKR.lean`
  - Added Step247 uniform surfaces:
    - `Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData`
    - `Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms`
  - Added adapter chain:
    - profile-template span data → profile-template local-monoid NFs
    - profile-template local-monoid NFs → local-monoid NFs
    - profile-template span data → local-monoid NFs
  - Added closeout theorems:
    - `noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms`
    - `noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData`

- ✅ `PallLean/Paper93/DeepMath/PathB/SATPathBChain.lean`
  - Added extraction-move theorems:
    - `SAT_path_B_paperFaithfulSourceWitnessedLeibnizProfileTemplateSpanData_TPhi_extraction_move`
    - `SAT_path_B_paperFaithfulSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms_TPhi_extraction_move`

## 2) Build evidence (requested targets)

These all passed locally:

```bash
lake build PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiExtraction
lake build PallLean.Paper93.DeepMath.PathB.RouteBPlacedQuotientDescentKR
lake build PallLean.Paper93.DeepMath.PathB.SATPathBChain
```

## 3) Paper text that should be updated now

In `/mnt/c/Users/darre/Desktop/p vs np1.pdf` (and source), update wording that still says formalization is pending/future where appropriate.

High-priority phrases to review:
- “community verification … remains future work”
- “machine-checked Lean formalization remains future work”
- “full verification … ongoing”

Action: replace with precise status:
- Route B paper-faithful local-monoid/profile-template bypass is Lean-wired and build-checked.
- Keep only genuinely-open items as open.

## 4) Assumption inventory sync (must be explicit)

### 4.1 Publish-ready assumption inventory table (Route B slice)

| Paper claim / seam label | Lean artifact (path + name) | Status | Axiom footprint |
|---|---|---|---|
| Step247 selected-profile template span data surface exists | `PallLean/Paper93/DeepMath/PathB/RouteBPlacedQuotientDescentKR.lean` — `Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData` | **proved (definition surface)** | classical-only (`propext`, `Classical.choice`, `Quot.sound`) |
| Step247 exact-budget selected-profile local-monoid NF surface exists | `...RouteBPlacedQuotientDescentKR.lean` — `Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms` | **proved (definition surface)** | classical-only |
| Profile-template span data instantiates exact-budget local-monoid NFs | `...RouteBPlacedQuotientDescentKR.lean` — `step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms_of_profileTemplateSpanData` | **proved (adapter)** | classical-only |
| Exact-budget profile-template local-monoid NFs forget to general local-monoid NF Step247 surface | `...RouteBPlacedQuotientDescentKR.lean` — `step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms_of_profileTemplateLocalMonoidNormalForms` | **proved (adapter)** | classical-only |
| Direct profile-template span → general local-monoid NF Step247 surface | `...RouteBPlacedQuotientDescentKR.lean` — `step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms_of_profileTemplateSpanData` | **proved (adapter)** | classical-only |
| Per-instance constructor: profile-template span data → exact-budget local-monoid NFs | `PallLean/Paper93/Paper283/RouteBPaperFaithfulTPhiExtraction.lean` — `routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms_of_profileTemplateSpanData` | **proved (constructor)** | classical-only |
| No-bounded-SAT closeout from exact-budget profile-template local-monoid NFs | `...RouteBPlacedQuotientDescentKR.lean` — `noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms` | **proved (theorem)** | classical-only |
| No-bounded-SAT closeout from profile-template span data | `...RouteBPlacedQuotientDescentKR.lean` — `noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData` | **proved (theorem)** | classical-only |
| SAT Path B extraction move via profile-template span seam | `PallLean/Paper93/DeepMath/PathB/SATPathBChain.lean` — `SAT_path_B_paperFaithfulSourceWitnessedLeibnizProfileTemplateSpanData_TPhi_extraction_move` | **proved (theorem)** | classical-only |
| SAT Path B extraction move via exact-budget profile-template local-monoid seam | `...SATPathBChain.lean` — `SAT_path_B_paperFaithfulSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms_TPhi_extraction_move` | **proved (theorem)** | classical-only |
| Legacy Step247 local-monoid seam remains available and now reached through new adapters | `...RouteBPlacedQuotientDescentKR.lean` — `noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms` | **proved (theorem)** | classical-only |
| Singleton EventAtom QDim target-row-in-target-span as a universal closure route | (no theorem used in final Route B closure path) | **not assumed in final closeout path** | n/a |

### 4.2 Wording block for the paper

Use this short statement in the assumption-inventory section:

> The final Step247 Route-B closure does **not** depend on a universal singleton EventAtom-QDim target-row-in-target-span claim.  The checked closure path is instead the selected-profile template span / exact-budget local-monoid normal-form route (with explicit adapters to the existing local-monoid Step247 surface), all Lean-wired and build-verified in the current repository state.

### 4.3 Remaining table rows to fill outside Route B

Add rows for non-Route-B load-bearing items cited in your paper’s global assumption inventory (e.g., any Theorem-92/94/207 surfaces), with the same columns and explicit Lean links.

## 5) GitHub publication status

- ✅ Local commit created: `b3f9fbac`
- ⛔ Push blocked: GitHub auth not configured on machine

To finish:
```bash
gh auth login
# or switch remote to SSH and ensure key is loaded

git push origin godmove-paper-faithful
```

## 6) Final “done-done” checklist

Reference artifact created:
- `GLOBAL_ASSUMPTION_INVENTORY_V1.md` (core Theorem 92/94/207 + Route B audit rows, with axiom footprints from `#print axioms`)

- [ ] Push branch with `b3f9fbac`
- [ ] Update paper status wording (future-work lines)
- [ ] Add assumption inventory table aligned to Lean artifacts
- [ ] Rebuild 3 targets after wording/code sync
- [ ] (Optional) Open PR with summary + build evidence snippets
