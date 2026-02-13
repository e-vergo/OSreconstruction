/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/

import OSReconstruction.vNA.Unbounded.Basic
import OSReconstruction.vNA.Unbounded.Spectral

/-!
# Unbounded Operator Theory

This module collects all the unbounded operator theory needed for
Tomita-Takesaki modular theory.

## Contents

* `Basic` - Basic definitions: unbounded operators, domains, graphs, adjoints
* `Spectral` - Spectral theory: spectral measures, functional calculus, powers

## Applications to Modular Theory

The key applications are:
1. The Tomita operator S₀ : aΩ ↦ a*Ω is an unbounded closable antilinear operator
2. Its closure S has polar decomposition S = JΔ^{1/2}
3. The modular operator Δ = S*S is positive self-adjoint
4. The modular conjugation J is antiunitary
5. The modular automorphism group σ_t(a) = Δ^{it} a Δ^{-it} uses functional calculus
-/
