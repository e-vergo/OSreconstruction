/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Spacetime.Metric
import OSReconstruction.Wightman.Groups.Lorentz
import OSReconstruction.Wightman.Groups.Poincare

/-!
# Wightman QFT: Basic Structures

This module aggregates the basic mathematical structures needed for the rigorous
formulation of Wightman quantum field theory in general dimension.

## Contents

### Spacetime (`Spacetime/`)
* `Metric` - Minkowski space ℝ^{1,d} with the mostly positive metric η = diag(-1,+1,...,+1)

### Groups (`Groups/`)
* `Lorentz` - The Lorentz group O(1,d) preserving the Minkowski metric
* `Poincare` - The Poincaré group ISO(1,d) = ℝ^{d+1} ⋊ O(1,d)

## Dimension Convention

We use general spatial dimension d ≥ 1, so spacetime has dimension d+1.
- d = 1: 1+1 dimensional QFT (exactly solvable models)
- d = 2: 2+1 dimensional QFT (φ⁴₃ theory)
- d = 3: 3+1 dimensional QFT (physical spacetime)

For spinor fields, one would need the spin group Spin(1,d) (the universal cover of SO⁺(1,d)).
This infrastructure focuses on scalar fields where the ordinary Poincaré group suffices.

## Signature Convention

We use the **mostly positive** (particle physics) convention throughout:
  η = diag(-1, +1, +1, ..., +1)

This means:
- Timelike vectors have η(x,x) < 0
- Spacelike vectors have η(x,x) > 0
- Lightlike vectors have η(x,x) = 0
- The mass-shell condition is p² = -m²

The index 0 corresponds to time, indices 1,...,d correspond to spatial dimensions.

## References

* Streater-Wightman, "PCT, Spin and Statistics, and All That"
* Weinberg, "The Quantum Theory of Fields", Vol. I
* Glimm-Jaffe, "Quantum Physics: A Functional Integral Point of View"
* Haag, "Local Quantum Physics"
-/

-- Re-export key definitions
namespace Wightman

export MinkowskiSpace (metricSignature minkowskiInner minkowskiNormSq)
export MinkowskiSpace (IsTimelike IsSpacelike IsLightlike AreSpacelikeSeparated)
export MinkowskiSpace (ForwardLightCone OpenForwardLightCone ClosedForwardLightCone)

end Wightman

