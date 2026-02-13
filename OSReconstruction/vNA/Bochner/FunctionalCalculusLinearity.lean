/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.vNA.Unbounded.Spectral
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Linearity of the Spectral Functional Calculus

This file proves that the functional calculus `functionalCalculus P f` is linear in `f`:
* `functionalCalculus_add`: `(f₁+f₂)(T) = f₁(T) + f₂(T)`
* `functionalCalculus_sub`: `(f₁-f₂)(T) = f₁(T) - f₂(T)`
* `functionalCalculus_neg`: `(-f)(T) = -f(T)`

The proofs use the polarization identity for complex Hilbert spaces
(`ext_inner_map`): if `⟪Ax, x⟫ = ⟪Bx, x⟫` for all x, then A = B.
Combined with `functionalCalculus_inner_self` (which gives
`⟪x, f(T)x⟫ = ∫ f dμ_x`), this reduces linearity to
the linearity of the Bochner integral.

## Mathematical idea

To prove `(f₁+f₂)(T) = f₁(T) + f₂(T)`, it suffices to show that
the diagonal inner products agree. Using `functionalCalculus_inner_self`:
```
  ⟪x, (f₁+f₂)(T)x⟫ = ∫ (f₁+f₂) dμ_x
                      = ∫ f₁ dμ_x + ∫ f₂ dμ_x
                      = ⟪x, f₁(T)x⟫ + ⟪x, f₂(T)x⟫
                      = ⟪x, (f₁(T) + f₂(T))x⟫
```
By `ext_inner_map` (polarization for complex inner product spaces),
this implies equality of the operators.
-/

noncomputable section

open MeasureTheory Complex Filter Topology SpectralMeasure
open scoped InnerProduct ComplexConjugate

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Extension lemma for continuous linear maps -/

omit [CompleteSpace H] in
/-- Two continuous linear maps on a complex inner product space are equal if their
    diagonal inner products agree: `⟪Sx, x⟫ = ⟪Tx, x⟫` for all x.
    Lifts `ext_inner_map` from `→ₗ[ℂ]` to `→L[ℂ]`. -/
theorem ContinuousLinearMap.ext_inner_self {S T : H →L[ℂ] H}
    (h : ∀ x, @inner ℂ H _ (S x) x = @inner ℂ H _ (T x) x) : S = T := by
  have h_lin : S.toLinearMap = T.toLinearMap := (ext_inner_map _ _).mp h
  exact ContinuousLinearMap.ext fun x => by
    change S.toLinearMap x = T.toLinearMap x; rw [h_lin]

/-! ### Helper: flipped inner product formula -/

/-- `⟪f(T)x, x⟫ = conj(∫ f dμ_x)`. Flipped version of `functionalCalculus_inner_self`. -/
theorem functionalCalculus_inner_self_flip (P : SpectralMeasure H) (f : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    (x : H) :
    @inner ℂ H _ (functionalCalculus P f hf_int hf_bdd x) x =
    starRingEnd ℂ (∫ t, f t ∂(P.diagonalMeasure x)) := by
  conv_lhs => rw [show @inner ℂ H _ (functionalCalculus P f hf_int hf_bdd x) x =
      starRingEnd ℂ (@inner ℂ H _ x (functionalCalculus P f hf_int hf_bdd x))
      from (inner_conj_symm _ _).symm]
  congr 1
  exact functionalCalculus_inner_self P f hf_int hf_bdd x

/-! ### Linearity theorems -/

/-- The functional calculus is additive: `(f₁+f₂)(T) = f₁(T) + f₂(T)`.

    Proof uses polarization: show diagonal inner products agree via
    `functionalCalculus_inner_self` + `integral_add`, then apply `ext_inner_map`. -/
theorem SpectralMeasure.functionalCalculus_add (P : SpectralMeasure H) (f₁ f₂ : ℝ → ℂ)
    (h1_int : ∀ z : H, Integrable f₁ (P.diagonalMeasure z))
    (h1_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f₁ t‖ ≤ M)
    (h2_int : ∀ z : H, Integrable f₂ (P.diagonalMeasure z))
    (h2_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f₂ t‖ ≤ M)
    (h12_int : ∀ z : H, Integrable (f₁ + f₂) (P.diagonalMeasure z))
    (h12_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖(f₁ + f₂) t‖ ≤ M) :
    functionalCalculus P (f₁ + f₂) h12_int h12_bdd =
    functionalCalculus P f₁ h1_int h1_bdd + functionalCalculus P f₂ h2_int h2_bdd := by
  apply ContinuousLinearMap.ext_inner_self
  intro x
  -- ⟪(f₁+f₂)(T)x, x⟫ = ⟪(f₁(T)+f₂(T))x, x⟫
  simp only [ContinuousLinearMap.add_apply]
  rw [inner_add_left]
  -- ⟪(f₁+f₂)(T)x, x⟫ = ⟪f₁(T)x, x⟫ + ⟪f₂(T)x, x⟫
  rw [functionalCalculus_inner_self_flip P (f₁ + f₂) h12_int h12_bdd x,
      functionalCalculus_inner_self_flip P f₁ h1_int h1_bdd x,
      functionalCalculus_inner_self_flip P f₂ h2_int h2_bdd x]
  -- conj(∫(f₁+f₂)dμ_x) = conj(∫f₁dμ_x) + conj(∫f₂dμ_x)
  rw [← map_add (starRingEnd ℂ)]
  congr 1
  simp_rw [Pi.add_apply]
  exact integral_add (h1_int x) (h2_int x)

/-- The functional calculus preserves negation: `(-f)(T) = -f(T)`. -/
theorem SpectralMeasure.functionalCalculus_neg (P : SpectralMeasure H) (f : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    (hnf_int : ∀ z : H, Integrable (-f) (P.diagonalMeasure z))
    (hnf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖(-f) t‖ ≤ M) :
    functionalCalculus P (-f) hnf_int hnf_bdd =
    -functionalCalculus P f hf_int hf_bdd := by
  apply ContinuousLinearMap.ext_inner_self
  intro x
  simp only [ContinuousLinearMap.neg_apply]
  rw [inner_neg_left]
  rw [functionalCalculus_inner_self_flip P (-f) hnf_int hnf_bdd x,
      functionalCalculus_inner_self_flip P f hf_int hf_bdd x]
  rw [← map_neg (starRingEnd ℂ)]
  congr 1
  simp_rw [Pi.neg_apply, integral_neg]

/-- The functional calculus is subtractive: `(f₁-f₂)(T) = f₁(T) - f₂(T)`. -/
theorem SpectralMeasure.functionalCalculus_sub (P : SpectralMeasure H) (f₁ f₂ : ℝ → ℂ)
    (h1_int : ∀ z : H, Integrable f₁ (P.diagonalMeasure z))
    (h1_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f₁ t‖ ≤ M)
    (h2_int : ∀ z : H, Integrable f₂ (P.diagonalMeasure z))
    (h2_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f₂ t‖ ≤ M)
    (h12_int : ∀ z : H, Integrable (f₁ - f₂) (P.diagonalMeasure z))
    (h12_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖(f₁ - f₂) t‖ ≤ M) :
    functionalCalculus P (f₁ - f₂) h12_int h12_bdd =
    functionalCalculus P f₁ h1_int h1_bdd - functionalCalculus P f₂ h2_int h2_bdd := by
  apply ContinuousLinearMap.ext_inner_self
  intro x
  simp only [ContinuousLinearMap.sub_apply]
  rw [inner_sub_left]
  rw [functionalCalculus_inner_self_flip P (f₁ - f₂) h12_int h12_bdd x,
      functionalCalculus_inner_self_flip P f₁ h1_int h1_bdd x,
      functionalCalculus_inner_self_flip P f₂ h2_int h2_bdd x]
  rw [← map_sub (starRingEnd ℂ)]
  congr 1
  simp_rw [Pi.sub_apply]
  exact integral_sub (h1_int x) (h2_int x)

end
