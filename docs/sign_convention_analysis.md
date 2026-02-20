# Sign Convention Analysis: Forward Tube and Boundary Values

## The Problem

In `wightman_to_os_full` (WickRotation.lean), the last remaining sorry asks us to prove that the BHW extension `F_ext` has the same distributional boundary values as the Wightman distribution `W_n`. This reduces to showing that points of the form `x - iεη` (with η in the forward cone) lie in a region where `F_ext` agrees with `W_analytic`. They don't — and understanding why requires tracing the sign conventions through the codebase.

## Definitions in the Codebase

### Minkowski signature (LorentzLieGroup.lean:51)
```
η = diag(-1, +1, ..., +1)    (mostly-plus convention)
```

### Forward light cone (Connectedness.lean:58)
```
InOpenForwardCone d η  :=  η₀ > 0  ∧  -η₀² + Σᵢ ηᵢ² < 0
```
This is the standard future-pointing timelike cone: positive time component, timelike norm.

### Forward tube (Connectedness.lean:63)
```
ForwardTube d n  :=  { z : (Fin n → Fin (d+1) → ℂ) |
    ∀ k, InOpenForwardCone d (fun μ => Im(zₖ μ - z_{k-1} μ)) }
```
where `z_{-1} := 0`. So the forward tube requires that **successive imaginary-part differences** lie in the forward light cone. In particular for k = 0:
```
Im(z₀ μ) ∈ V⁺     (i.e., Im(z₀)₀ > 0)
```

### Wick rotation (WightmanAxioms.lean:333)
```
wickRotatePoint(x) μ  =  if μ = 0 then i · x₀ else xμ
```
So a Euclidean point (τ, x⃗) maps to the complex spacetime point (iτ, x⃗) with:
- Re = (0, x⃗),  Im = (τ, 0⃗)

### Boundary value formula (Reconstruction.lean:527, IsWickRotationPair:1362)
Both `spectrum_condition` and `IsWickRotationPair` use:
```
lim_{ε→0⁺}  ∫ W_analytic(x - iεη) · f(x) dx  =  Wₙ(f)
```
where η ranges over `∀ k, InOpenForwardCone d (η k)`.

## The Sign Issue

Consider the point `z k μ = (x k μ : ℂ) - ε · (η k μ : ℂ) · I`:
```
Re(z k μ) = x k μ
Im(z k μ) = -ε · η k μ
```

For k = 0 (where prev = 0), the forward tube requires:
```
Im(z₀)₀ > 0
```
But we get:
```
Im(z₀)₀ = -ε · η₀ ₀
```
Since `InOpenForwardCone d (η 0)` gives `η₀ ₀ > 0` and `ε > 0`:
```
Im(z₀)₀ = -ε · η₀ ₀ < 0
```

**The points `x - iεη` lie in the backward tube (Im₀ < 0), not the forward tube.**

## What the Physics Says

In the standard Wightman formalism (Streater-Wightman, Jost), the boundary value theorem states:

> W(x) = lim_{ε→0⁺} W_analytic(ξ + iεη)   where ξ = difference variables, η ∈ V⁺

The approach is from **above** — the imaginary part is **positive** and shrinks to zero. Written in absolute (non-difference) coordinates with approach direction η_k ∈ V⁺:

```
z k μ = x k μ + i ε η k μ        (physics convention)
```

This gives `Im(z₀)₀ = +ε η₀ ₀ > 0`, placing the point in the **forward** tube. ✓

The codebase uses `x - iεη` instead of `x + iεη`. This places the approach points in the backward tube.

## Why It Matters

The BHW theorem gives `F_ext` agreeing with `W_analytic` on the **forward tube**:
```
∀ z ∈ ForwardTube, F_ext(z) = W_analytic(z)
```

To prove the boundary value sorry, we need:
```
F_ext(x - iεη) = W_analytic(x - iεη)     for all x, small ε > 0
```

Since `x - iεη` is in the **backward** tube, not the forward tube, the agreement lemma doesn't apply. The values of `W_analytic` (which is a total function from `Exists.choose`) outside the forward tube are **arbitrary** — they have no analytic meaning.

## Comparison: Euclidean Restriction (the part that works)

The Euclidean restriction `S_n(f) = ∫ F_ext(Wick(x)) · f(x) dx` works because:

For `wickRotatePoint(x)`: Im = (x₀, 0, ..., 0). Successive differences have Im = (x_k₀ - x_{k-1}₀, 0, ..., 0). This is in the forward cone when:
```
x_k₀ - x_{k-1}₀ > 0   (strictly increasing Euclidean times)
```

For a.e. configuration (measure-zero excluded), times are distinct, and after permutation the Wick-rotated point lies in the **permuted** extended tube. Since `constructSchwingerFunctions` uses `F_ext` directly, the Euclidean restriction is proved by `rfl` without needing any tube membership argument.

## Options for Resolution

### Option 1: Fix the sign in `spectrum_condition` and `IsWickRotationPair`

Change `x - iεη` to `x + iεη` everywhere:
```lean
-- In spectrum_condition and IsWickRotationPair:
fun ε => ∫ x, F_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x
```

Then `Im(z k μ) = +ε η k μ`, and for k = 0: `Im(z₀)₀ = ε η₀ ₀ > 0` ✓.
The approach points are in the forward tube, and `F_ext = W_analytic` applies directly.

**Impact**: Need to update `spectrum_condition` in WightmanAxioms.lean, `IsWickRotationPair` in Reconstruction.lean, `boundary_values_tempered` in WickRotation.lean, and any downstream references.

### Option 2: Use `W_analytic` as the `IsWickRotationPair` witness

Instead of `F_ext`, provide `W_analytic = (Wfn.spectrum_condition n).choose` as the witness:
- Holomorphicity: direct from `spectrum_condition`
- Boundary values: direct from `spectrum_condition`
- Euclidean restriction: needs `∫ F_ext(Wick(x)) f(x) = ∫ W_analytic(Wick(x)) f(x)`, which requires showing `F_ext = W_analytic` at Wick-rotated points for a.e. x (measure-theoretic argument: ordered-time configurations are in ForwardTube, and disordered-time configurations have measure zero)

### Option 3: Keep the sorry

The boundary value property is morally correct — `F_ext` is the unique holomorphic extension of `W_analytic`, so it has the same boundary values. The sorry marks a genuine gap that would require either option 1 or 2 to close.

## Recommendation

**Option 1 (fix the sign)** is the cleanest. The sign `x - iεη` appears to be a typo or convention error. Changing to `x + iεη` makes the boundary value proof essentially trivial:

```lean
-- After sign fix, the proof would be:
intro f η hη
-- For ε > 0, the point x + iεη is in ForwardTube
-- So F_ext(x + iεη) = W_analytic(x + iεη)
-- Therefore ∫ F_ext(x + iεη) f(x) = ∫ W_analytic(x + iεη) f(x)
-- And the limit is W_n(f) by spectrum_condition
```
