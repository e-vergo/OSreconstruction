# vNA Module TODO

## Overview

This module develops von Neumann algebra foundations for rigorous QFT, including:
- Unbounded self-adjoint operators
- Spectral theory via Riesz-Markov-Kakutani (RMK)
- Stone's theorem for one-parameter unitary groups
- Modular theory (Tomita-Takesaki)

## Current Status

### Spectral Theory via RMK (Primary Approach) — Sorry-Free Chain

| File | Status | Sorrys |
|------|--------|--------|
| `Spectral/SpectralFunctionalViaRMK.lean` | Complete | 0 |
| `Spectral/SpectralMeasurePolarizedViaRMK.lean` | Complete | 0 |
| `Spectral/SpectralTheoremViaRMK.lean` | Complete | 0 |
| `Spectral/CayleyTransform.lean` | Complete | 0 |
| `Spectral/SpectralViaCayleyRMK.lean` | **Complete** | 0 |
| `Spectral/SigmaAdditivity.lean` | **Complete** | 0 |
| `Spectral/SpectralProjectionLemmas.lean` | Complete | 0 |
| `Spectral/JensenLinearity.lean` | Complete | 0 |

### Unbounded Operators — Fully Proven

| File | Status | Sorrys |
|------|--------|--------|
| `Unbounded/Basic.lean` | Complete | 0 |
| `Unbounded/Graph.lean` | Complete | 0 |

### Measure Theory Infrastructure — Mostly Proven

| File | Status | Sorrys |
|------|--------|--------|
| `MeasureTheory/SpectralIntegral.lean` | Complete | 0 |
| `MeasureTheory/CaratheodoryExtension.lean` | Complete | 0 |
| `MeasureTheory/SpectralStieltjes.lean` | Nearly Complete | 1 (`complexMeasure_eq_inner`) |

### Spectral Theorem & Functional Calculus

| File | Status | Sorrys |
|------|--------|--------|
| `Unbounded/Spectral.lean` | **Nearly Complete** | 2 (spectral_theorem + FC + unitary group fully sorry-free!) |

**Sorry-free results:**
- `spectral_theorem_pvm`: PVM existence — **sorry-free**
- `spectral_theorem`: `⟨x, f(T)y⟩ = P.spectralIntegral f x y` — **sorry-free**
- `functionalCalculus_star`: `(f(T))* = f̄(T)` — **sorry-free**
- `functionalCalculus_mul`: `f(T)g(T) = (fg)(T)` — **sorry-free**
- `functionalCalculus_inner`: `⟨x, f(T)y⟩ = Bform P f x y` — **sorry-free**
- `power_add`: `T^(s+t) = T^s ∘ T^t` — **sorry-free** (via `functionalCalculus_mul`)
- `unitaryGroup`: `U(t) = e^{itA} = ∫ exp(itλ) dP(λ)` — **redefined using exp(itλ) directly**
- `unitaryGroup_zero`: `U(0) = 1` — **sorry-free** (no positivity needed!)
- `unitaryGroup_mul`: `U(s) ∘ U(t) = U(s+t)` — **sorry-free**
- `unitaryGroup_inv`: `U(t)* = U(-t)` — **sorry-free**
- `unitaryGroup_neg_comp`/`unitaryGroup_comp_neg` — **sorry-free**
- `unitaryGroup_continuous`: `t ↦ U(t)x` is continuous — **sorry-free** (DCT + weak→strong via isometry)
- `power` integrability/boundedness — **sorry-free** (uses `Re(s) = 0` hypothesis)

**Key change:** `unitaryGroup` no longer uses `power` (λ^{it}). It uses `exp(itλ)` directly,
which removes the positivity requirement and makes U(0)=1 trivially true.

**Remaining sorrys in Spectral.lean (2):**
- `power_zero` — requires spectral support argument: P((-∞,0]) = 0 for positive T (isolated, not on critical path)
- `power_imaginary_unitary` — depends on `power_zero` (isolated, not on critical path)

### Stone's Theorem

| File | Status | Sorrys |
|------|--------|--------|
| `Unbounded/StoneTheorem.lean` | In Progress | ~9 |

### Deprecated Files (moved to `/backup_deprecated_vNA/`)

The following files used `UnboundedCFC` which is broken for unbounded T
(returns 0 by Mathlib CFC convention). They have been moved out of the
source tree but backed up for reference:
- `TPConnection.lean` — T-P connection via UnboundedCFC
- `FunctionalCalculusFromCFC.lean` — spectral projections via CFC bump operators
- `FunctionalCalculusFromCFC/Basic.lean` — UnboundedCFC definition, proven infrastructure
- `SpectralIntegralCauchy.lean` — Cauchy sequence approach to spectral integrals

## Critical Issue: UnboundedCFC is Broken

**Problem**: `UnboundedCFC T f = cfc (cfcViaInverseCayley f) U` where U is the Cayley
transform. For unbounded T, `1 ∈ σ(U)` and `cfcViaInverseCayley f` is discontinuous
at 1 for most f (since `inverseCayley(w) → ∞` as `w → 1`). By Mathlib's CFC convention,
`cfc g U = 0` when g is not continuous on σ(U). Therefore `UnboundedCFC T f = 0` for most f.

**Fix**: Use `functionalCalculus P f` from `Unbounded/Spectral.lean` which is defined via
the sesquilinear form `Bform P f x y = polarized spectral integral`. This works correctly
for all bounded measurable f and does not depend on the Cayley transform.

**Affected definitions/theorems** (all in `FunctionalCalculusFromCFC/` and `TPConnection.lean`):
- `UnboundedCFC` — returns junk for unbounded T
- `unboundedSpectralFunctional` — uses UnboundedCFC
- `spectralFunctionalCalculus` — uses UnboundedCFC
- `TP_connection` — LHS is UnboundedCFC (= 0 for most f)
- `TP_connection_diagonal` — same issue

## Action Plan

### ✅ Step 1: Fix SpectralMeasure definition — DONE
### ✅ Step 2: Complete σ-additivity — DONE
### ✅ Step 2.5: Refactor spectral_theorem (sorry-free PVM) — DONE
### ✅ Step 3: Prove spectral_theorem — DONE
- Uses `functionalCalculus` (sesquilinear form) instead of `UnboundedCFC`
- Proof: `functionalCalculus_inner` + definitional equality of Bform and spectralIntegral

### ✅ Step 4: Complete functionalCalculus properties — MOSTLY DONE
**File:** `Unbounded/Spectral.lean`

- ✅ `functionalCalculus_mul`: **sorry-free** (SimpleFunc.induction + DCT + adjoint trick)
- ✅ `power` integrability/boundedness: **sorry-free** (added `Re(s) = 0` hypothesis)
- `power_zero`: needs spectral support argument for positive T
- `power_add`: now easy from `functionalCalculus_mul`
- `unitaryGroup_continuous`: dominated convergence

### ✅ Step 5: Stone's Theorem — Forward Direction — DONE
**File:** `Unbounded/Spectral.lean`

All properties of the one-parameter unitary group are **sorry-free**:
- `unitaryGroup_zero`: `U(0) = 1` — **sorry-free**
- `unitaryGroup_mul`: `U(s)U(t) = U(s+t)` — **sorry-free**
- `unitaryGroup_inv`: `U(t)* = U(-t)` — **sorry-free**
- `unitaryGroup_continuous`: `t ↦ U(t)x` is continuous — **sorry-free** (DCT + weak→strong)

### Step 6: Stone's Theorem — Inverse Direction (HARDEST)
**File:** `Unbounded/StoneTheorem.lean`

1. `generator_densely_defined` — needs mollification
2. `generator_selfadjoint` — the hardest sorry

## Priority/Dependency Order

```
[Steps 1-3]  PVM + spectral_theorem                    ✅ ALL DONE (sorry-free!)
    ↓
[Step 4]     functionalCalculus_mul + power             ✅ MOSTLY DONE (FC mul sorry-free!)
    ↓
[Step 5]     Stone forward direction                    ✅ DONE (all unitary group properties sorry-free!)
    ↓
[Step 6]     Stone inverse direction                    ← NEXT/HARDEST (mollification)
```

## Full Module Dependency Chart

```
Spectral Theory (sorry-free chain)
│
│  SpectralFunctionalViaRMK ✅
│  SpectralMeasurePolarizedViaRMK ✅
│  SpectralTheoremViaRMK ✅
│  CayleyTransform ✅ → SpectralViaCayleyRMK ✅ → SigmaAdditivity ✅
│  SpectralProjectionLemmas ✅, JensenLinearity ✅
│
├── MeasureTheory
│   ├── SpectralIntegral ✅
│   ├── CaratheodoryExtension (~14 sorrys, measure extension infrastructure)
│   └── SpectralStieltjes (1 sorry: complexMeasure_eq_inner)
│
├── Unbounded Operators
│   ├── Basic ✅, Graph ✅
│   ├── Spectral (2 sorrys: power_zero, power_imaginary_unitary — isolated)
│   └── StoneTheorem (~4 sorrys: generator_densely_defined, generator_selfadjoint, generates, timeEvolution_generator)
│       │
│       ▼
├── Modular Theory (depends on Δ^{it} from spectral/Stone)
│   ├── Basic (1 sorry: cyclic_iff_separating)
│   ├── Predual (2 sorrys: sigmaWeak_convergence_iff, kaplansky_density)
│   ├── ModularTheory (9 sorrys: Ω_in_domain, fixed point, JΔJ=Δ⁻¹, J reverses flow,
│   │                            conjugation maps M→M', σ_t preserves M, positive cone, uniqueness)
│   ├── ModularAutomorphism (13 sorrys: preserves_algebra, multiplicativity, star,
│   │                        continuity, state_invariant, cocycle properties, Radon-Nikodym)
│   └── KMS (9 sorrys: strip_boundary, modular_state_is_KMS, uniqueness,
│            invariance, factor uniqueness, temperature limits, passivity)
│
└── Bochner Integration (sorry-free helper infrastructure)
    ├── CfcInfrastructure ✅
    ├── OperatorBochner ✅
    ├── Convergence ✅
    ├── FunctionalCalculusLinearity ✅
    └── Applications ✅
```

### Critical Chain

```
Spectral (sorry-free) → StoneTheorem (~4 sorrys) → ModularTheory (9) → ModularAutomorphism (13) → KMS (9)
```

Stone's inverse direction is the **single bottleneck**: everything in the modular theory chain
ultimately depends on `Δ^{it}` being a strongly continuous unitary group generated by `log Δ`.

### Parallel Work Streams

- **Group A** (spectral): power_zero + power_imaginary_unitary (isolated, 2 sorrys)
- **Group B** (Stone inverse): generator_densely_defined → generator_selfadjoint (4 sorrys, hardest)
- **Group C** (measure theory): CaratheodoryExtension sorrys (~14, infrastructure)
- **Group D** (modular theory): 31 sorrys, but blocked by Group B

Groups A and C are independent of each other and of Group B.
Group D becomes unblocked once Group B is complete.

## Sorry Summary by File

| File | Sorrys | Category |
|------|--------|----------|
| `Unbounded/Spectral.lean` | 2 | power_zero + power_imaginary_unitary — isolated |
| `Unbounded/StoneTheorem.lean` | ~4 | Stone inverse (hardest) |
| `MeasureTheory/SpectralStieltjes.lean` | 1 | `complexMeasure_eq_inner` |
| `MeasureTheory/CaratheodoryExtension.lean` | ~14 | Measure extension infrastructure |
| `Basic.lean` | 1 | `cyclic_iff_separating` |
| `Predual.lean` | 2 | σ-weak topology + Kaplansky density |
| `ModularTheory.lean` | 9 | Tomita-Takesaki fundamentals |
| `ModularAutomorphism.lean` | 13 | Automorphism group + Connes cocycle |
| `KMS.lean` | 9 | KMS states + passivity |
| **Total** | **~55** | |

### Sorry-Free Key Results
- `spectral_theorem_pvm`: PVM existence
- `spectral_theorem`: spectral representation ⟨x, f(T)y⟩ = ∫ f d⟨x, P y⟩
- `functionalCalculus_star`: (f(T))* = f̄(T)
- `functionalCalculus_mul`: f(T)g(T) = (fg)(T)
- `functionalCalculus_inner`: ⟨x, f(T)y⟩ = Bform P f x y
- `unitaryGroup_zero`: U(0) = 1
- `unitaryGroup_mul`: U(s)U(t) = U(s+t)
- `unitaryGroup_inv`: U(t)* = U(-t)
- `unitaryGroup_continuous`: t ↦ U(t)x is continuous (DCT + weak→strong)
- `UnboundedOperator.spectralMeasure`: spectral measure definition
- `UnboundedOperator.spectralCayley`: Cayley transform definition
- `UnboundedOperator.spectralMeasure_eq_RMK`: agreement with RMK

## What NOT to Pursue

All deprecated files have been moved to `/backup_deprecated_vNA/`:
- **UnboundedCFC**: Broken for unbounded T (returns 0)
- **CFC approach**: Superseded by sesquilinear form
- **TP_connection**: Used broken UnboundedCFC

## Key Technical Notes

### Why RMK?

The traditional approach creates circularity:
1. CFC for bounded normal operators → spectral projections
2. Cayley transform to reduce unbounded to bounded
3. But CFC itself uses spectral theory

The RMK approach breaks this by:
1. Defining spectral functional Λ_z(f) = Re⟨z, cfc(f, U) z⟩
2. Using RMK to get a measure μ_z from Λ_z
3. Extending to polarized measure μ_{x,y} via polarization
4. Defining P(E) via sesquilinear form: ⟨x, P(E) y⟩ = μ_{x,y}(E)

### Why Sesquilinear Form for Functional Calculus?

The `functionalCalculus P f` is defined via:
1. Diagonal measure: `μ_z(E) = ‖P(E)z‖²`
2. Quadratic form: `Q(z) = ∫ f dμ_z`
3. Polarization: `B(x,y) = (1/4)[Q(x+y) - Q(x-y) - iQ(x+iy) + iQ(x-iy)]`
4. Riesz representation: unique T with `⟨x, Ty⟩ = B(x,y)` (sesquilinearToOperator)

This works for ALL bounded measurable f and ANY self-adjoint operator (bounded or unbounded).

### Key Lemmas Available (Sorry-Free)

**From RMK chain:**
- `spectralFunctionalAux_tendsto_of_pointwise_general`: Dominated convergence
- `spectralProjection_polarized_product_closed`: P(E)P(F) product formula
- `spectralProjection_idempotent_closed`: P(F)² = P(F)
- `spectralMeasurePolarized_univ`: μ_{x,y}(Circle) = ⟨x, y⟩
- `spectralMeasurePolarized_integral`: U-P connection for compactly supported
- `one_not_eigenvalue`: U x = x ⟹ x = 0

**From TPConnection.lean:**
- `spectralMeasureDiagonalOnR`: Pullback measure on ℝ
- `TP_connection_indicator`: ⟨x, P(E) y⟩ = μ^ℝ_{x,y}(E)
- `spectralMeasureDiagonal_singleton_one_eq_zero`: μ_z({1}) = 0
- `integral_circle_eq_integral_minus_one`: ∫ g dμ = ∫_{Circle\{1}} g dμ

## References

- Reed-Simon, "Methods of Modern Mathematical Physics I", Ch. VII-VIII
- Rudin, "Functional Analysis", Ch. 13
- Kato, "Perturbation Theory for Linear Operators", Ch. V
