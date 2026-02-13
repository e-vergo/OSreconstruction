/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Bochner Integration of Operator-Valued Functions

This file provides infrastructure for Bochner integration of `H →L[ℂ] H`-valued functions
with respect to scalar measures. This is "Type A" integration: the integrand is an
operator-valued function and the measure is scalar.

The key results are:
* `operatorIntegral_apply`: evaluation commutes with integration
  (from Mathlib's `ContinuousLinearMap.integral_apply`)
* `operatorIntegral_norm_le`: norm bound
* `operatorIntegral_adjoint`: adjoint commutes with integration
* `operatorIntegral_comp_left`, `operatorIntegral_comp_right`: composition commutes
  with integration
* `operatorIntegral_inner_left`, `operatorIntegral_inner_right`: inner product formulas
* `operatorIntegral_tendsto_SOT`: dominated convergence in SOT
* `operatorIntegral_tendsto_norm`: dominated convergence in operator norm

## Mathematical Context

For the spectral theorem, we ultimately need "Type B" integration:
  `∫ f(λ) dP(λ)` where `P` is a projection-valued measure (PVM)
This is more subtle and is handled via the existing `functionalCalculus` in
`vNA/Unbounded/Spectral.lean` and the convergence infrastructure in `Convergence.lean`.

Type A integration appears naturally when:
- Computing resolvents as contour integrals
- Defining operator semigroups
- Bochner integral representations of operator functions

## Coordination with existing infrastructure

- `vNA/MeasureTheory/SpectralIntegral.lean`: `sesquilinearToOperator`, `ComplexSpectralMeasure`
- `vNA/MeasureTheory/SpectralStieltjes.lean`: `ProjectionValuedMeasure`, `diagonalMeasure`
- `vNA/Unbounded/Spectral.lean`: `SpectralMeasure`, `functionalCalculus`

## References

* Mathlib `Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap`
* Reed-Simon, "Methods of Modern Mathematical Physics I", Chapter VI
-/

noncomputable section

open MeasureTheory Complex Filter Topology
open scoped InnerProduct

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {X : Type*} [MeasurableSpace X]

/-! ### Basic operator integral -/

/-- The Bochner integral of an operator-valued function.
    This is simply the Mathlib Bochner integral, with a convenient name. -/
def operatorIntegral (μ : Measure X) (T : X → (H →L[ℂ] H)) : H →L[ℂ] H :=
  ∫ t, T t ∂μ

/-- Evaluation commutes with integration: `(∫ T(t) dμ) v = ∫ T(t)v dμ`.

    This is the fundamental property of operator-valued Bochner integrals.
    It follows directly from Mathlib's `ContinuousLinearMap.integral_apply`. -/
theorem operatorIntegral_apply (μ : Measure X) (T : X → (H →L[ℂ] H))
    (hT : Integrable T μ) (v : H) :
    (operatorIntegral μ T) v = ∫ t, T t v ∂μ :=
  ContinuousLinearMap.integral_apply hT v

/-- Norm bound: `‖∫ T dμ‖ ≤ ∫ ‖T‖ dμ`. -/
theorem operatorIntegral_norm_le (μ : Measure X) (T : X → (H →L[ℂ] H))
    (_hT : Integrable T μ) :
    ‖operatorIntegral μ T‖ ≤ ∫ t, ‖T t‖ ∂μ :=
  norm_integral_le_integral_norm _

/-- The integral of the zero function is zero. -/
theorem operatorIntegral_zero (μ : Measure X) :
    operatorIntegral μ (fun _ : X => (0 : H →L[ℂ] H)) = 0 := by
  simp [operatorIntegral]

/-- Linearity: scalar multiplication commutes with integration. -/
theorem operatorIntegral_smul (μ : Measure X) (c : ℂ) (T : X → (H →L[ℂ] H)) :
    operatorIntegral μ (fun t => c • T t) = c • operatorIntegral μ T := by
  simp [operatorIntegral, integral_smul]

/-- Linearity: addition commutes with integration. -/
theorem operatorIntegral_add (μ : Measure X) (S T : X → (H →L[ℂ] H))
    (hS : Integrable S μ) (hT : Integrable T μ) :
    operatorIntegral μ (fun t => S t + T t) = operatorIntegral μ S + operatorIntegral μ T := by
  simp [operatorIntegral, integral_add hS hT]

/-- Linearity: subtraction commutes with integration. -/
theorem operatorIntegral_sub (μ : Measure X) (S T : X → (H →L[ℂ] H))
    (hS : Integrable S μ) (hT : Integrable T μ) :
    operatorIntegral μ (fun t => S t - T t) = operatorIntegral μ S - operatorIntegral μ T := by
  simp [operatorIntegral, integral_sub hS hT]

/-! ### Composition with operators -/

/-- Left composition: `A((∫ T dμ) v) = ∫ A(T(t)v) dμ` for bounded A and all v. -/
theorem operatorIntegral_comp_left_apply (μ : Measure X) (A : H →L[ℂ] H)
    (T : X → (H →L[ℂ] H)) (hT : Integrable T μ) (v : H) :
    A ((operatorIntegral μ T) v) = ∫ t, A (T t v) ∂μ := by
  rw [operatorIntegral_apply μ T hT v]
  exact (ContinuousLinearMap.integral_comp_comm A (hT.apply_continuousLinearMap _)).symm

/-- Right composition: `(∫ T dμ)(Av) = ∫ T(t)(Av) dμ` for bounded A. -/
theorem operatorIntegral_comp_right_apply (μ : Measure X) (A : H →L[ℂ] H)
    (T : X → (H →L[ℂ] H)) (hT : Integrable T μ) (v : H) :
    (operatorIntegral μ T) (A v) = ∫ t, T t (A v) ∂μ :=
  operatorIntegral_apply μ T hT (A v)

/-! ### Inner product formulas -/

/-- Inner product formula (right): `⟨w, (∫ T dμ) v⟩ = ∫ ⟨w, T(t)v⟩ dμ`.

    This follows directly from Mathlib's `integral_inner`. -/
theorem operatorIntegral_inner_right (μ : Measure X) (T : X → (H →L[ℂ] H))
    (hT : Integrable T μ) (v w : H) :
    @inner ℂ H _ w ((operatorIntegral μ T) v) =
    ∫ t, @inner ℂ H _ w (T t v) ∂μ := by
  rw [operatorIntegral_apply μ T hT v]
  exact (integral_inner (hT.apply_continuousLinearMap v) w).symm

/-- Inner product formula (left): `⟨(∫ T dμ) v, w⟩ = ∫ ⟨T(t)v, w⟩ dμ`.

    Proved by conjugating `operatorIntegral_inner_right` using
    `inner_conj_symm` and `integral_conj`. -/
theorem operatorIntegral_inner_left (μ : Measure X) (T : X → (H →L[ℂ] H))
    (hT : Integrable T μ) (v w : H) :
    @inner ℂ H _ ((operatorIntegral μ T) v) w =
    ∫ t, @inner ℂ H _ (T t v) w ∂μ := by
  rw [operatorIntegral_apply μ T hT v]
  -- Goal: ⟪∫ T(t)v dμ, w⟩ = ∫ ⟪T(t)v, w⟩ dμ
  -- Strategy: ⟪a,b⟩ = star ⟪b,a⟩ (inner_conj_symm), pull star through integral
  -- inner_conj_symm x y : starRingEnd ℂ ⟪y, x⟩ = ⟪x, y⟩
  -- So (inner_conj_symm (∫..) w).symm : ⟪∫.., w⟩ = starRingEnd ℂ ⟪w, ∫..⟩
  calc @inner ℂ H _ (∫ t, T t v ∂μ) w
      = starRingEnd ℂ (@inner ℂ H _ w (∫ t, T t v ∂μ)) :=
        (inner_conj_symm (𝕜 := ℂ) (∫ t, T t v ∂μ) w).symm
    _ = starRingEnd ℂ (∫ t, @inner ℂ H _ w (T t v) ∂μ) := by
        congr 1; exact (integral_inner (𝕜 := ℂ) (hT.apply_continuousLinearMap v) w).symm
    _ = ∫ t, starRingEnd ℂ (@inner ℂ H _ w (T t v)) ∂μ := (integral_conj (𝕜 := ℂ)).symm
    _ = ∫ t, @inner ℂ H _ (T t v) w ∂μ := by
        congr 1; ext t; exact inner_conj_symm (𝕜 := ℂ) (T t v) w

/-! ### Adjoint interchange -/

/-- Adjoint commutes with integration: `(∫ T dμ)* = ∫ T(t)* dμ`. -/
theorem operatorIntegral_adjoint (μ : Measure X) (T : X → (H →L[ℂ] H))
    (hT : Integrable T μ) (hTadj : Integrable (fun t => (T t).adjoint) μ) :
    (operatorIntegral μ T).adjoint = operatorIntegral μ (fun t => (T t).adjoint) := by
  apply ContinuousLinearMap.ext; intro v
  apply ext_inner_left ℂ; intro w
  rw [ContinuousLinearMap.adjoint_inner_right]
  -- Goal: ⟪(operatorIntegral μ T) w, v⟩ = ⟪w, operatorIntegral μ (fun t => (T t).adjoint) v⟩
  rw [operatorIntegral_inner_left μ T hT w v]
  rw [operatorIntegral_inner_right μ (fun t => (T t).adjoint) hTadj v w]
  -- Goal: ∫ ⟪T(t)w, v⟩ = ∫ ⟪w, (T t).adjoint v⟩
  congr 1; ext t
  exact (ContinuousLinearMap.adjoint_inner_right (T t) w v).symm

/-! ### Dominated convergence for operator integrals -/

/-- Dominated convergence in the strong operator topology:
    If Tₙ(t) → T(t) pointwise in operator norm, and ‖Tₙ(t)‖ ≤ g(t) with g integrable,
    then (∫ Tₙ dμ)v → (∫ T dμ)v for all v. -/
theorem operatorIntegral_tendsto_SOT
    (μ : Measure X) [SigmaFinite μ]
    (T : ℕ → X → (H →L[ℂ] H)) (Tlim : X → (H →L[ℂ] H))
    (hT_meas : ∀ n, AEStronglyMeasurable (T n) μ)
    (hTlim_meas : AEStronglyMeasurable Tlim μ)
    (g : X → ℝ) (hg_int : Integrable g μ)
    (hT_bound : ∀ n, ∀ᵐ t ∂μ, ‖T n t‖ ≤ g t)
    (hT_tend : ∀ᵐ t ∂μ, Tendsto (fun n => T n t) atTop (nhds (Tlim t)))
    (v : H) :
    Tendsto (fun n => (operatorIntegral μ (T n)) v) atTop
      (nhds ((operatorIntegral μ Tlim) v)) := by
  have hT_int : ∀ n, Integrable (T n) μ := by
    intro n
    exact hg_int.mono' (hT_meas n) (hT_bound n)
  have hTlim_int : Integrable Tlim μ := by
    have hTlim_bound : ∀ᵐ t ∂μ, ‖Tlim t‖ ≤ g t := by
      have hbdall : ∀ᵐ t ∂μ, ∀ n, ‖T n t‖ ≤ g t := ae_all_iff.mpr hT_bound
      filter_upwards [hT_tend, hbdall] with t hconv hbd
      exact le_of_tendsto (continuous_norm.continuousAt.tendsto.comp hconv)
        (Filter.Eventually.of_forall fun n => hbd n)
    exact hg_int.mono' hTlim_meas hTlim_bound
  rw [operatorIntegral_apply μ Tlim hTlim_int v]
  have : ∀ n, (operatorIntegral μ (T n)) v = ∫ t, T n t v ∂μ :=
    fun n => operatorIntegral_apply μ (T n) (hT_int n) v
  simp_rw [this]
  apply tendsto_integral_of_dominated_convergence (fun t => g t * ‖v‖)
  · intro n
    exact (hT_meas n).apply_continuousLinearMap _
  · exact hg_int.mul_const _
  · intro n
    filter_upwards [hT_bound n] with t ht
    calc ‖T n t v‖ ≤ ‖T n t‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ g t * ‖v‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
  · filter_upwards [hT_tend] with t ht
    exact (ContinuousLinearMap.apply ℂ H v).continuous.continuousAt.tendsto.comp ht

/-- Dominated convergence in operator norm:
    If Tₙ(t) → T(t) pointwise in operator norm, ‖Tₙ(t)‖ ≤ g(t) with g integrable,
    then ∫ Tₙ dμ → ∫ T dμ in operator norm. -/
theorem operatorIntegral_tendsto_norm
    (μ : Measure X) [SigmaFinite μ]
    (T : ℕ → X → (H →L[ℂ] H)) (Tlim : X → (H →L[ℂ] H))
    (hT_meas : ∀ n, AEStronglyMeasurable (T n) μ)
    (hTlim_meas : AEStronglyMeasurable Tlim μ)
    (g : X → ℝ) (hg_int : Integrable g μ)
    (hT_bound : ∀ n, ∀ᵐ t ∂μ, ‖T n t‖ ≤ g t)
    (hT_tend : ∀ᵐ t ∂μ, Tendsto (fun n => T n t) atTop (nhds (Tlim t))) :
    Tendsto (fun n => operatorIntegral μ (T n)) atTop (nhds (operatorIntegral μ Tlim)) := by
  simp only [operatorIntegral]
  apply tendsto_integral_of_dominated_convergence g hT_meas hg_int hT_bound hT_tend

end
