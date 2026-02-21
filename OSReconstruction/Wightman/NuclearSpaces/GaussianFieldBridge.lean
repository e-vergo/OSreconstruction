/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import SchwartzNuclear
import GaussianField
import OSReconstruction.Wightman.NuclearSpaces.NuclearSpace

/-!
# Bridge: GaussianField → OSReconstruction

This file imports results from the `gaussian-field` library and re-exports
them for use in the OS reconstruction project.

## What we get from gaussian-field

### SchwartzNuclear (all sorry-free)
- Hermite functions: definition, orthonormality, Schwartz membership
- Schwartz-Hermite expansion: `f = ∑ₙ cₙ(f) ψₙ` in Schwartz topology
- Tensor product Hermite basis for S(ℝⁿ)
- `GaussianField.NuclearSpace (SchwartzMap D ℝ)` instance (Dynin-Mityagin)

### GaussianField (all sorry-free)
- Spectral theorem for compact self-adjoint operators
- Nuclear SVD: singular value decomposition for nuclear operators
- Gaussian measure construction on `WeakDual ℝ E`
- Characteristic functional: `∫ exp(i⟨ω,f⟩) dμ = exp(-½ ‖T(f)‖²)`
- Moment identities: E[ω(f)] = 0, E[ω(f)ω(g)] = ⟨Tf,Tg⟩
- Pietsch nuclear space definition and DM → Pietsch bridge

## Two NuclearSpace definitions

This project (OSReconstruction) defines `NuclearSpace` via the Pietsch
characterization (nuclear dominance by seminorms). The gaussian-field project
defines `GaussianField.NuclearSpace` via the Dynin-Mityagin characterization
(Schauder basis with rapid decay) and `GaussianField.PietschNuclearSpace`
via the Pietsch characterization.

The DM → Pietsch bridge is proved in gaussian-field
(`GaussianField.NuclearSpace.toPietschNuclearSpace`). This file provides
the final conversion from `GaussianField.PietschNuclearSpace` to the
OSReconstruction `NuclearSpace`.

## References

- Dynin, Mityagin, "Criterion for nuclearity in terms of approximative dimension"
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4
- Pietsch, "Nuclear Locally Convex Spaces" (1972)
-/

noncomputable section

open GaussianField
open scoped NNReal

/-! ### Schwartz NuclearSpace instance

The `schwartz_nuclearSpace` axiom from gaussian-field provides a
`GaussianField.NuclearSpace` instance for `SchwartzMap D ℝ` whenever
`D` is a nontrivial finite-dimensional normed space with a Borel σ-algebra.

This instance is registered globally, so once this file is imported,
typeclass synthesis will automatically find it. -/

-- Verify the instance is available
example : GaussianField.NuclearSpace (SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℝ) :=
  inferInstance

/-! ### Hermite function results

The gaussian-field library provides sorry-free proofs of the fundamental
properties of Hermite functions. These are at the top-level namespace. -/

/-- Hermite functions from gaussian-field. These are ψₙ(x) = cₙ · Hₙ(x√2) · exp(-x²/2)
    using probabilist Hermite polynomials. -/
abbrev gfHermiteFunction := hermiteFunction

/-- Hermite functions are in the Schwartz space (sorry-free from gaussian-field). -/
abbrev gfHermiteFunction_schwartz := hermiteFunction_schwartz

/-- Hermite functions are orthonormal in L²(ℝ) (sorry-free from gaussian-field). -/
abbrev gfHermiteFunction_orthonormal := hermiteFunction_orthonormal

/-- Hermite functions are complete in L² (sorry-free from gaussian-field). -/
abbrev gfHermiteFunction_complete := hermiteFunction_complete

/-- Seminorm bounds on Hermite functions (sorry-free from gaussian-field). -/
abbrev gfHermiteFunction_seminorm_bound := hermiteFunction_seminorm_bound

/-! ### Spectral theorem -/

/-- Spectral theorem for compact self-adjoint operators on a real Hilbert space.
    Sorry-free from gaussian-field.

    For a compact self-adjoint T ≠ 0, there exist eigenvectors forming a
    HilbertBasis, with eigenvalues μ and T(x) = ∑ μᵢ ⟨eᵢ, x⟩ eᵢ. -/
abbrev gfCompactSelfAdjointSpectral := @compact_selfAdjoint_spectral

/-! ### Gaussian measure construction -/

/-- The configuration space (space of distributions). -/
abbrev gfConfiguration := @Configuration

/-- The Gaussian measure on Configuration E with covariance ⟨T·, T·⟩. -/
abbrev gfMeasure := @GaussianField.measure

/-- Characteristic functional: ∫ exp(i⟨ω,f⟩) dμ = exp(-½ ‖T(f)‖²).
    Sorry-free from gaussian-field. -/
abbrev gfCharFun := @charFun

/-! ### Moment identities -/

/-- The Gaussian measure is centered: E[ω(f)] = 0 (sorry-free). -/
abbrev gfMeasureCentered := @measure_centered

/-- Cross-moment equals covariance: E[ω(f)ω(g)] = ⟨Tf, Tg⟩ (sorry-free). -/
abbrev gfCrossMomentEqCovariance := @cross_moment_eq_covariance

/-- The pairing ω(f) is Gaussian-distributed (sorry-free). -/
abbrev gfPairingIsGaussian := @pairing_is_gaussian

/-! ### Bridge: GaussianField.PietschNuclearSpace → NuclearSpace

The two Pietsch definitions (`GaussianField.PietschNuclearSpace` from gaussian-field
and `NuclearSpace` from OSReconstruction) are structurally identical. This trivial
conversion connects them. -/

/-- Convert `GaussianField.PietschNuclearSpace` to the OSReconstruction `NuclearSpace`.

The two definitions have identical `nuclear_dominance` fields, so the
conversion is just field extraction. -/
theorem GaussianField.PietschNuclearSpace.toNuclearSpace (E : Type*)
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [h : GaussianField.PietschNuclearSpace E] : _root_.NuclearSpace E where
  nuclear_dominance := h.nuclear_dominance

/-- **Dynin-Mityagin implies OSReconstruction Pietsch nuclearity.**

Composes the gaussian-field bridge (`NuclearSpace.toPietschNuclearSpace`)
with the trivial conversion to the OSReconstruction `NuclearSpace`. -/
theorem GaussianField.NuclearSpace.toOSNuclearSpace (E : Type*)
    [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [GaussianField.NuclearSpace E] : _root_.NuclearSpace E :=
  letI := GaussianField.NuclearSpace.toPietschNuclearSpace E
  GaussianField.PietschNuclearSpace.toNuclearSpace E

end
