# ComplexLieGroups Module TODO

## Sorry Status

### MatrixLieGroup.lean — 0 sorrys ✓
GL(n;ℂ) and SL(n;ℂ) path-connectedness fully proved.

### SOConnected.lean — 0 sorrys ✓
SO(n;ℂ) path-connectedness fully proved via:
- Exponential map infrastructure (skew-symmetric → orthogonal)
- Givens rotation algebra (P, Q projection matrices)
- Complex rotation elements with `c² + s² = 1`
- Column reduction by induction on n (Givens rotations zero out column entries)
- Block decomposition: first column = e₀ implies block-diagonal form

### Complexification.lean — 0 sorrys ✓
Complex Lorentz group SO⁺(1,d;ℂ) fully defined and path-connected:
- `ComplexLorentzGroup` structure with complex Minkowski metric preservation
- Group/topology instances
- Lie algebra exponential infrastructure
- Wick rotation homeomorphism: `toSOComplex` / `fromSOComplex`
- `isPathConnected` proved by transferring from `SOComplex.isPathConnected`

### LorentzLieGroup.lean — 1 sorry
| # | Line | Name | Status |
|---|------|------|--------|
| 1 | 1039 | `RestrictedLorentzGroup.isPathConnected` | **sorry** (deferred) |

### Connectedness.lean — 3 sorrys (down from 7)
| # | Line | Name | Status |
|---|------|------|--------|
| 1 | 1108 | `orbitSet_isPreconnected` | **sorry** — O_w connected |
| 2 | 1530 | `F_permutation_invariance` | **sorry** — edge-of-the-wedge (core BHW content) |
| 3 | 1776 | BHW uniqueness | **sorry** — identity theorem + PET connected |

**PROVED (previously sorry):**
- `fullExtendF_well_defined` — reduced to `F_permutation_invariance`
- BHW Property 1 (holomorphicity) — inverse chart argument with EventuallyEq
- BHW Property 2 (F_ext = F on FT) — well-definedness + identity preimage
- BHW Property 3 (Lorentz invariance) — Lorentz group composition
- BHW Property 4 (permutation symmetry) — permutation composition + well-definedness

Note: `nonemptyDomain_isPreconnected` is PROVED from `orbitSet_isPreconnected`
using `isPreconnected_sUnion`. `complex_lorentz_invariance` is proved modulo
`orbitSet_isPreconnected`.

Proved infrastructure:
- ForwardTube, complexLorentzAction, PermutedExtendedTube definitions
- `near_identity_invariance` — F(Λ·z₀) = F(z₀) for Λ near 1 in SO⁺(1,d;ℂ)
- `uniform_near_identity_invariance` — uniform version over a nhd of z₀
- `eq_zero_on_convex_of_eventuallyEq_zero` — identity theorem on open convex domains
- `complex_lorentz_invariance` — PROVED modulo `orbitSet_isPreconnected`
- `fullExtendF_well_defined` — PROVED from `F_permutation_invariance`
- `fullExtendF` definition + all BHW properties except uniqueness PROVED
- `extendF`, `extendF_eq_on_forwardTube`, `extendF_preimage_eq`, etc.
- BHW theorem statement with all hypotheses

**Total: 4 sorrys across 2 files**

---

## Remaining Sorrys — Analysis

### `orbitSet_isPreconnected` (geometric)

**Goal:** O_w = {Λ ∈ G : Λ·w ∈ FT} is preconnected for each w ∈ FT.

**Why needed:** `nonemptyDomain_isPreconnected` reduces to this via
`isPreconnected_sUnion`, and `complex_lorentz_invariance` needs it.

**Why `domain_nonempty` (∀ Λ, D_Λ ≠ ∅) is FALSE:** boost(iπ) gives Λ with D_Λ = ∅.

**Approaches:** See Proofideas/complex_lorentz_invariance.lean for detailed analysis.

### `F_permutation_invariance` (edge-of-the-wedge — CORE BHW content)

**Goal:** For w ∈ FT, τ ∈ S_n, Γ ∈ SO⁺(1,d;ℂ) with Γ·(τ·w) ∈ FT:
  F(Γ·(τ·w)) = F(w).

**Analysis:**
- For τ = id: this is `complex_lorentz_invariance` (proved modulo orbitSet sorry).
- For τ ≠ id: uses local commutativity (hF_local) at Jost points + edge-of-the-wedge.
- FT and τ·FT have opposite imaginary parts for permuted differences,
  so FT ∩ τ·FT = ∅ for τ ≠ id. But their closures share Jost points
  (real configs with spacelike separations).
- Edge-of-the-wedge (SCV.edge_of_the_wedge_theorem) glues F on FT with
  F∘σ on σ·FT into a holomorphic function on FT ∪ σ·FT ∪ (Jost neighborhood).
- Iterate over adjacent transpositions for general τ.

### BHW uniqueness (identity theorem)

**Goal:** G holomorphic on PET + G = F on FT ⟹ G = fullExtendF on PET.

**Dependencies:**
- PET connected (follows from edge-of-the-wedge connecting permutation sectors)
- Multi-variable identity theorem (DifferentiableOn → AnalyticOnNhd for
  Fin n → Fin (d+1) → ℂ, available via SCV.differentiableOn_analyticAt + type equiv)
- Alternative: 1D exponential path argument avoids multi-variable identity theorem
  for the extended tube ET, but still needs PET connected for full PET.

---

## Dependency Graph

```
MatrixLieGroup.lean ✓ ──────────────────────────────────────────┐
                                                                 │
SOConnected.lean ✓ ──────────────────────────────────┐           │
   SO(n;ℂ) path-connected                           │           │
                                                     ▼           │
LorentzLieGroup.lean (1 sorry, deferred)     Complexification.lean ✓
   RestrictedLorentzGroup                    ComplexLorentzGroup
   isPathConnected [deferred]                isPathConnected ✓
            │                                        │
            │                                        │
            ▼                                        ▼
          Connectedness.lean (3 sorrys)
            orbitSet_isPreconnected [geometric]
            F_permutation_invariance [edge-of-the-wedge]
            BHW uniqueness [identity theorem + PET connected]
                     │
                     ▼
          (bridges to Wightman/AnalyticContinuation.lean)
```

## Execution Order

1. **Connectedness.lean** — prove `orbitSet_isPreconnected` (geometric analysis)
2. **Connectedness.lean** — prove `F_permutation_invariance` (edge-of-the-wedge)
3. **Connectedness.lean** — prove BHW uniqueness (follows from 2 + identity theorem)
4. Build: `lake build OSReconstruction.ComplexLieGroups`
5. **LorentzLieGroup.lean** — prove `isPathConnected` (Phase 3, when convenient)
