/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.vNA.Bochner.Convergence
import OSReconstruction.vNA.Bochner.FunctionalCalculusLinearity

/-!
# Applications of the Spectral Functional Calculus

This file provides useful corollaries of the spectral functional calculus
infrastructure built in `Convergence.lean` and `FunctionalCalculusLinearity.lean`.

## Main Results

* `functionalCalculus_congr`: Proof irrelevance — if `f = g` pointwise then
  `f(T) = g(T)` regardless of integrability/boundedness proofs.

* `functionalCalculus_opNorm_le`: Tight operator norm bound `‖f(T)‖ ≤ M`.

* `functionalCalculus_isSelfAdjoint`: If `f` is real-valued then `f(T)` is self-adjoint.

* `functionalCalculus_inner_self_nonneg`: If `f ≥ 0` then `f(T)` is positive.

* `functionalCalculus_smul`: Scalar multiplication `(c • f)(T) = c • f(T)`.
-/

noncomputable section

open MeasureTheory Complex Filter Topology SpectralMeasure
open scoped InnerProduct ComplexConjugate

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Proof irrelevance (congr) -/

/-- The functional calculus depends only on `f`, not on the proofs of integrability
    and boundedness. If `f = g` pointwise, then `f(T) = g(T)`.

    Proof: By polarization, it suffices to show `⟨f(T)x, x⟩ = ⟨g(T)x, x⟩`.
    Using `functionalCalculus_inner_self_flip`:
    `⟨f(T)x, x⟩ = conj(∫ f dμ_x) = conj(∫ g dμ_x) = ⟨g(T)x, x⟩`. -/
theorem functionalCalculus_congr (P : SpectralMeasure H) (f g : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    (hg_int : ∀ z : H, Integrable g (P.diagonalMeasure z))
    (hg_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖g t‖ ≤ M)
    (hfg : ∀ t, f t = g t) :
    functionalCalculus P f hf_int hf_bdd = functionalCalculus P g hg_int hg_bdd := by
  apply ContinuousLinearMap.ext_inner_self
  intro x
  rw [functionalCalculus_inner_self_flip P f hf_int hf_bdd x,
      functionalCalculus_inner_self_flip P g hg_int hg_bdd x]
  congr 1
  exact integral_congr_ae (Eventually.of_forall hfg)

/-! ### Operator norm bound -/

/-- Tight operator norm bound: `‖f(T)‖ ≤ M` where `∀ t, ‖f t‖ ≤ M`.

    This is tighter than the `2M` bound from the sesquilinear form construction.
    Proof: `‖f(T)x‖² = ∫ |f|² dμ_x ≤ M² · μ_x(ℝ) = M² ‖x‖²`. -/
theorem functionalCalculus_opNorm_le (P : SpectralMeasure H) (f : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    (hf_meas : Measurable f) (M : ℝ) (hM_nn : 0 ≤ M) (hM : ∀ t, ‖f t‖ ≤ M) :
    ‖functionalCalculus P f hf_int hf_bdd‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM_nn
  intro x
  by_cases hx : x = 0
  · simp [hx]
  -- ‖f(T)x‖² = ∫ |f|² dμ_x ≤ M² · ‖x‖²
  have hnorm_sq := functionalCalculus_norm_sq' P f hf_int hf_bdd hf_meas x
  -- ∫ |f|² dμ_x ≤ M² · ‖x‖²
  have h_int_le : ∫ t, ‖f t‖ ^ 2 ∂(P.diagonalMeasure x) ≤ M ^ 2 * ‖x‖ ^ 2 := by
    calc ∫ t, ‖f t‖ ^ 2 ∂(P.diagonalMeasure x)
        ≤ ∫ _, M ^ 2 ∂(P.diagonalMeasure x) := by
          apply integral_mono_of_nonneg
          · exact Eventually.of_forall fun _ => sq_nonneg _
          · exact integrable_const _
          · exact Eventually.of_forall fun t =>
              sq_le_sq' (by linarith [norm_nonneg (f t)]) (hM t)
      _ = (P.diagonalMeasure x).real Set.univ * M ^ 2 := by
          rw [integral_const, smul_eq_mul]
      _ ≤ ‖x‖ ^ 2 * M ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          rw [P.diagonalMeasure_real_univ]
      _ = M ^ 2 * ‖x‖ ^ 2 := by ring
  -- ‖f(T)x‖² ≤ (M ‖x‖)² implies ‖f(T)x‖ ≤ M ‖x‖
  have h_sq : ‖functionalCalculus P f hf_int hf_bdd x‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
    rw [mul_pow]; linarith
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rwa [Real.sqrt_sq (norm_nonneg _),
       Real.sqrt_sq (mul_nonneg hM_nn (norm_nonneg x))] at h_sqrt

/-! ### Self-adjointness -/

/-- If `f` is real-valued (i.e., `star ∘ f = f`), then `f(T)` is self-adjoint.

    Proof: By `functionalCalculus_star`, `f(T)* = (star ∘ f)(T)`.
    Since `star ∘ f = f` pointwise, `functionalCalculus_congr` gives
    `(star ∘ f)(T) = f(T)`. -/
theorem functionalCalculus_isSelfAdjoint (P : SpectralMeasure H) (f : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    (hf_real : ∀ t, starRingEnd ℂ (f t) = f t)
    (hsf_int : ∀ z : H, Integrable (star ∘ f) (P.diagonalMeasure z))
    (hsf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖(star ∘ f) t‖ ≤ M) :
    IsSelfAdjoint (functionalCalculus P f hf_int hf_bdd) := by
  rw [isSelfAdjoint_iff]
  -- star = adjoint for CLMs
  rw [ContinuousLinearMap.star_eq_adjoint]
  -- adjoint(f(T)) = (star ∘ f)(T) by functionalCalculus_star
  rw [functionalCalculus_star P f hf_int hf_bdd hsf_int hsf_bdd]
  -- (star ∘ f)(T) = f(T) since star ∘ f = f
  exact functionalCalculus_congr P (star ∘ f) f hsf_int hsf_bdd hf_int hf_bdd
    (fun t => hf_real t)

/-! ### Positivity -/

/-- If `f(t) ≥ 0` as a real number for all `t`, then `re⟨x, f(T)x⟩ ≥ 0`.

    This means `f(T)` is a positive operator.

    Proof: `⟨x, f(T)x⟩ = ∫ f dμ_x`. Since f takes nonneg real values,
    `∫ f dμ_x = ↑(∫ r dμ_x)` where `r ≥ 0`, so `re(⟨x, f(T)x⟩) ≥ 0`. -/
theorem functionalCalculus_inner_self_nonneg (P : SpectralMeasure H) (f : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    -- f takes nonneg real values: f(t) = ↑(r(t)) with r(t) ≥ 0
    (r : ℝ → ℝ) (hr_nonneg : ∀ t, 0 ≤ r t) (hr_eq : ∀ t, f t = ↑(r t))
    (x : H) :
    0 ≤ RCLike.re (@inner ℂ H _ x (functionalCalculus P f hf_int hf_bdd x)) := by
  rw [functionalCalculus_inner_self P f hf_int hf_bdd x]
  -- Goal: 0 ≤ re(∫ f dμ_x)
  rw [← integral_re (hf_int x)]
  apply integral_nonneg fun t => ?_
  simp only [Pi.zero_apply]
  rw [hr_eq t]; simp [hr_nonneg t]

/-! ### Scalar multiplication -/

/-- Scalar multiplication: `(c • f)(T) = c • f(T)`.

    Proof: By polarization, it suffices to show diagonal inner products agree.
    Uses `functionalCalculus_inner_self_flip` + `integral_smul`. -/
theorem SpectralMeasure.functionalCalculus_smul (P : SpectralMeasure H) (c : ℂ) (f : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    (hcf_int : ∀ z : H, Integrable (c • f) (P.diagonalMeasure z))
    (hcf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖(c • f) t‖ ≤ M) :
    functionalCalculus P (c • f) hcf_int hcf_bdd =
    c • functionalCalculus P f hf_int hf_bdd := by
  apply ContinuousLinearMap.ext_inner_self
  intro x
  rw [ContinuousLinearMap.smul_apply, inner_smul_left]
  rw [functionalCalculus_inner_self_flip P (c • f) hcf_int hcf_bdd x,
      functionalCalculus_inner_self_flip P f hf_int hf_bdd x]
  rw [← map_mul (starRingEnd ℂ)]
  congr 1
  simp_rw [Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

end
