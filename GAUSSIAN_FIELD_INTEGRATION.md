# Gaussian-Field Integration into OSReconstruction

This document describes the changes made to wire the
[gaussian-field](https://github.com/mdouglas/gaussian-field) library into
OSReconstruction, eliminating the sorry in `SchwartzNuclear.lean`.

## Problem

The original `SchwartzNuclear.lean` proved that S(ℝⁿ, ℝ) is nuclear via a
`NuclearFrechet` intermediate structure. The `nuclear_step` field — the core
"nuclearity" condition — was left as `sorry`. This was the last sorry in the
nuclearity path.

## Solution

### 1. Add gaussian-field as a dependency

**Files:** `lakefile.toml`, `lake-manifest.json`

The gaussian-field library provides sorry-free proofs of:
- Hermite function properties (orthonormality, Schwartz membership, seminorm bounds)
- `GaussianField.NuclearSpace` instance for `SchwartzMap D ℝ` (Dynin-Mityagin characterization)
- Gaussian measure construction and characteristic functional identities

### 2. GaussianFieldBridge

**File:** `OSReconstruction/Wightman/NuclearSpaces/GaussianFieldBridge.lean` (new)

Re-exports gaussian-field results into the OSReconstruction namespace:
- `gfHermiteFunction`, `gfHermiteFunction_schwartz`, `gfHermiteFunction_orthonormal`, etc.
- `gfMeasure`, `gfCharFun`, `gfMeasureCentered`, `gfCrossMomentEqCovariance`
- `gfCompactSelfAdjointSpectral` (spectral theorem for compact self-adjoint operators)

Also contains the bridge from Dynin-Mityagin to Pietsch nuclearity:
- `exists_CLF_le_seminorm` — Hahn-Banach for continuous seminorms
- `seminorm_le_nuclear_expansion` — triangle inequality bound from Schauder expansion
- `GaussianField.NuclearSpace.toPietschNuclearSpace` — the main bridge theorem

### 3. SchwartzNuclear.lean changes

**File:** `OSReconstruction/Wightman/NuclearSpaces/SchwartzNuclear.lean` (modified)

The old approach used `NuclearFrechet` with a sorry in `nuclear_step`.
The new approach splits into two cases:

**n = 0** (`schwartz_nuclearSpace_fin0`): Direct proof. The domain
`EuclideanSpace ℝ (Fin 0)` is a single point, so the Schwartz space is
one-dimensional. All seminorms except `seminorm ℝ 0 0` vanish. Nuclear
dominance holds with the evaluation functional as the single component.

Helper lemmas:
- `seminorm_eq_zero_of_fin0` — seminorms with (a,b) ≠ (0,0) vanish on Fin 0
- `sup_schwartz_le_00` — any finset sup of Schwartz seminorms ≤ seminorm 0 0
- `evalLM₀` / `evalCLM₀` — evaluation at default as a CLM
- `seminorm_00_eq` — seminorm 0 0 f = ‖f default‖

**n > 0** (`GaussianField.NuclearSpace.toPietschNuclearSpace`): Uses the
gaussian-field bridge. The Dynin-Mityagin `GaussianField.NuclearSpace`
instance (Hermite basis with polynomial growth/decay) is converted to
Pietsch `NuclearSpace` (nuclear dominance by seminorms) via Hahn-Banach.

### 4. Downstream updates

**Files:** `BochnerMinlos.lean`, `EuclideanMeasure.lean`

Updated to use `GaussianField.NuclearSpace` where appropriate, since the
gaussian-field library provides the Gaussian measure construction directly.

## Sorry status

After these changes, `SchwartzNuclear.lean` has **0 functional sorries**.
The 3 remaining sorries are in `SchwartzHermiteLegacy` — a legacy namespace
containing the original (physicists' convention) Hermite function stubs.
These are fully superseded by the sorry-free gaussian-field versions and
are retained only for reference.

## Two NuclearSpace definitions

OSReconstruction defines `NuclearSpace` via the **Pietsch characterization**
(nuclear dominance by seminorms). The gaussian-field library defines
`GaussianField.NuclearSpace` via the **Dynin-Mityagin characterization**
(Schauder basis with rapid decay). Both are valid characterizations of
nuclear Fréchet spaces and coexist in separate namespaces.

The bridge `toPietschNuclearSpace` proves Dynin-Mityagin → Pietsch,
so `SchwartzMap.instNuclearSpace` provides the Pietsch instance.
