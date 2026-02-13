/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/

import OSReconstruction.vNA.Basic
import OSReconstruction.vNA.Predual
import OSReconstruction.vNA.ModularTheory
import OSReconstruction.vNA.ModularAutomorphism
import OSReconstruction.vNA.KMS

/-!
# Von Neumann Algebras and Tomita-Takesaki Theory

This module develops the theory of von Neumann algebras with a focus on
Tomita-Takesaki modular theory.

## Contents

* `Basic` - Cyclic and separating vectors, standard form
* `Predual` - Normal functionals, predual theory, σ-weak topology
* `ModularTheory` - Tomita operator S, modular operator Δ, modular conjugation J
* `ModularAutomorphism` - Modular automorphism group σ_t, Connes cocycle
* `KMS` - KMS condition, equilibrium states

## Mathematical Overview

### Von Neumann Algebras

A von Neumann algebra M on a Hilbert space H is a *-subalgebra of B(H) that
equals its double commutant: M = M''. Equivalently (by the bicommutant theorem),
it is a *-subalgebra that is closed in the weak (or strong) operator topology.

### Tomita-Takesaki Theory

Given a von Neumann algebra M with a cyclic-separating vector Ω:

1. **Tomita operator**: S₀ : aΩ ↦ a*Ω (antilinear, closable)
2. **Polar decomposition**: S̄ = JΔ^{1/2} where
   - Δ = S̄*S̄ is the **modular operator** (positive, self-adjoint)
   - J is the **modular conjugation** (antiunitary involution)

3. **Fundamental theorem**: JMJ = M' (the commutant)

4. **Modular automorphism group**: σ_t(a) = Δ^{it} a Δ^{-it}
   - σ_t preserves M
   - Forms a one-parameter group of *-automorphisms

### KMS Condition

A state φ is (σ, β)-KMS if for all a, b ∈ M, the function
  F(t) = φ(σ_t(a)b)
extends analytically to the strip {z : 0 < Im(z) < β} with
  F(t + iβ) = φ(bσ_t(a))

The modular state φ_Ω is (σ^Ω, 1)-KMS, and this uniquely characterizes
the modular automorphism group.

## References

* Tomita, "On canonical forms of von Neumann algebras" (1967)
* Takesaki, "Tomita's theory of modular Hilbert algebras" (1970)
* Takesaki, "Theory of Operator Algebras" I, II, III
* Bratteli-Robinson, "Operator Algebras and Quantum Statistical Mechanics"
* Connes, "Noncommutative Geometry"

## Future Directions

- Type classification (I, II, III) of factors
- Connes' classification of type III factors
- Relative modular theory
- Jones index theory
- Subfactor theory
-/
