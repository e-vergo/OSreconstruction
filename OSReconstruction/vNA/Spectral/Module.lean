/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.vNA.Spectral.CayleyTransform
import OSReconstruction.vNA.Spectral.SpectralViaCayleyRMK
import OSReconstruction.vNA.Spectral.SigmaAdditivity

/-!
# Spectral Theory Module (vNA/Spectral/)

This module re-exports the spectral theory infrastructure.
Note: This is separate from `vNA/Unbounded/Spectral.lean` which contains
the main `SpectralMeasure` structure and theorems. This folder contains
supporting infrastructure for the RMK-based spectral construction.

1. **CayleyTransform** - The bijection between unbounded self-adjoint operators and
   unitary operators. Key definitions:
   - `CayleyTransform` - U = (T-i)(T+i)⁻¹
   - `cayleyMap` - The map λ ↦ (λ-i)/(λ+i) from ℝ to S¹

2. **SpectralViaCayleyRMK** - Spectral measure construction via Riesz-Markov-Kakutani
   (sorry-free). Key definitions:
   - `spectralMeasureFromRMK` - P(E) for Borel sets E

3. **SigmaAdditivity** - σ-additivity of spectral projections (sorry-free)

## Mathematical Background

The spectral theorem for unbounded self-adjoint operators states that every
self-adjoint operator T has a unique spectral decomposition T = ∫ λ dP(λ)
where P is a projection-valued measure.

Our approach uses:
1. The Cayley transform to reduce to bounded (unitary) operators
2. Riesz-Markov-Kakutani representation theorem for spectral measures
3. Sesquilinear form approach for functional calculus f(T)

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I", Chapter VIII
* Rudin, "Functional Analysis", Chapter 13
-/
