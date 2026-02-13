/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Osgood's Lemma and Holomorphic Extension Infrastructure

This file develops infrastructure for the multi-dimensional edge-of-the-wedge theorem:

1. **Osgood's Lemma**: A continuous function of several complex variables that is
   holomorphic in each variable separately is jointly holomorphic.

2. **1D extension across real line**: A continuous function on an open set in ℂ that
   is holomorphic off the real line is holomorphic everywhere (via Morera's theorem).

3. **Holomorphic extension across totally real boundaries**: A continuous function
   that is holomorphic on two open sets separated by a real boundary is holomorphic
   on the union.

These are needed for the Bargmann-Hall-Wightman theorem.

## Mathematical Background

Osgood's Lemma (1899): Let U ⊂ ℂⁿ be open and f : U → ℂ continuous. If f is
holomorphic in each variable z_i (with the others fixed), then f is holomorphic
(jointly, in the sense of Fréchet differentiability over ℂ).

The proof uses: for each pair of variables (z₁, z₂), the Cauchy integral formula
in z₁ gives a representation of f that is visibly holomorphic in z₂ by
differentiation under the integral sign.

## References

* Osgood, "Note über analytische Functionen mehrerer Veränderlichen" (1899)
* Krantz-Parks, "A Primer of Real Analytic Functions", §2.2
* Streater-Wightman, "PCT, Spin and Statistics, and All That", Ch. 2
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory intervalIntegral
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Cauchy Integral with Holomorphic Parameter -/

/-- **Cauchy integral with holomorphic parameter**: If f(ζ, x) is continuous on
    (sphere z₀ r) × V and holomorphic in x for each ζ on the sphere, then
    G(z, x) = (2πi)⁻¹ · ∮ f(ζ, x) / (ζ - z) dζ is jointly holomorphic
    on (ball z₀ r) × V. -/
theorem differentiableOn_cauchyIntegral_param [CompleteSpace E]
    {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    {V : Set E} (hV : IsOpen V)
    (f : ℂ → E → ℂ)
    (hf_cont : ContinuousOn (fun p : ℂ × E => f p.1 p.2)
      (Metric.closedBall z₀ r ×ˢ V))
    (hf_x_holo : ∀ ζ ∈ Metric.closedBall z₀ r, DifferentiableOn ℂ (f ζ) V) :
    DifferentiableOn ℂ
      (fun p : ℂ × E =>
        (2 * ↑Real.pi * I)⁻¹ • ∮ ζ in C(z₀, r), (ζ - p.1)⁻¹ • f ζ p.2)
      (Metric.ball z₀ r ×ˢ V) := by
  sorry

/-! ### Osgood's Lemma Infrastructure -/

/-- The z-derivative of f(z,x) at z₀ varies continuously in x, when f is jointly
    continuous and separately holomorphic in z.

    Proof: By Cauchy integral formula,
      deriv(z ↦ f(z,x))(z₀) = (2πI)⁻¹ ∮ f(ζ,x)/(ζ-z₀)² dζ
    The integrand is continuous in x (from joint continuity of f) and uniformly
    bounded on the circle, so the integral is continuous in x. -/
lemma continuousAt_deriv_of_continuousOn [CompleteSpace E]
    {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {V : Set E} (hV : IsOpen V)
    (f : ℂ × E → ℂ)
    (hf_cont : ContinuousOn f (Metric.closedBall z₀ ρ ×ˢ V))
    (hf_z : ∀ x ∈ V, DifferentiableOn ℂ (fun z => f (z, x)) (Metric.closedBall z₀ ρ))
    {x₀ : E} (hx₀ : x₀ ∈ V) :
    ContinuousAt (fun x => deriv (fun z => f (z, x)) z₀) x₀ := by
  -- By Cauchy integral formula:
  -- deriv(z ↦ f(z,x))(z₀) is a Cauchy integral, hence continuous in x
  -- We express deriv via DifferentiableOn.deriv_eq_smul_circleIntegral
  -- and show the resulting circle integral is continuous in x
  sorry

/-- Uniform Taylor remainder bound for a family of holomorphic functions.

    If f is continuous on closedBall z₀ ρ × V and holomorphic in z for each x ∈ V,
    then the first-order Taylor remainder in z is uniformly O(|h|²):
      |f(z₀+h, x) - f(z₀, x) - deriv_z f(z₀, x) · h| ≤ C · |h|²
    for |h| ≤ ρ/2 and x in a neighborhood of x₀.

    Proof: Power series expansion gives remainder = Σ_{n≥2} aₙ(x)hⁿ.
    Cauchy estimates: |aₙ(x)| ≤ M/ρⁿ where M = sup|f| on the compact set.
    Geometric series: |remainder| ≤ 2M|h|²/ρ² for |h| ≤ ρ/2. -/
lemma taylor_remainder_bound [CompleteSpace E]
    {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {V : Set E} (hV : IsOpen V)
    (f : ℂ × E → ℂ)
    (hf_cont : ContinuousOn f (Metric.closedBall z₀ ρ ×ˢ V))
    (hf_z : ∀ x ∈ V, DifferentiableOn ℂ (fun z => f (z, x)) (Metric.closedBall z₀ ρ))
    {x₀ : E} (hx₀ : x₀ ∈ V) :
    ∃ (C : ℝ) (δ : ℝ), C ≥ 0 ∧ δ > 0 ∧
      ∀ (h : ℂ) (x : E), x ∈ V → ‖x - x₀‖ < δ → ‖h‖ < ρ / 2 →
      ‖f (z₀ + h, x) - f (z₀, x) - deriv (fun z => f (z, x)) z₀ * h‖ ≤ C * ‖h‖ ^ 2 := by
  sorry

/-! ### Osgood's Lemma -/

/-- **Osgood's Lemma (product form)**: A continuous function f : ℂ × E → ℂ on an
    open product U₁ × U₂ that is holomorphic in each factor separately is jointly
    holomorphic.

    The proof constructs the joint Fréchet derivative L(h,k) = a·h + B(k) where
    a = ∂f/∂z(z₀,x₀) and B = D_x f(z₀,x₀), then shows the remainder is o(‖(h,k)‖)
    using three estimates:
    1. Taylor remainder in z: O(|h|²) uniformly in x (Cauchy estimates)
    2. Derivative variation: [a(x₀+k) - a(x₀)]·h → 0 (continuity of z-derivative)
    3. Fréchet remainder in x: o(‖k‖) (from x-holomorphicity) -/
theorem osgood_lemma_prod [CompleteSpace E]
    {U₁ : Set ℂ} {U₂ : Set E} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (f : ℂ × E → ℂ)
    (hf_cont : ContinuousOn f (U₁ ×ˢ U₂))
    (hf_z : ∀ x ∈ U₂, DifferentiableOn ℂ (fun z => f (z, x)) U₁)
    (hf_x : ∀ z ∈ U₁, DifferentiableOn ℂ (fun x => f (z, x)) U₂) :
    DifferentiableOn ℂ f (U₁ ×ˢ U₂) := by
  intro ⟨z₀, x₀⟩ ⟨hz₀, hx₀⟩
  -- Step 1: Find neighborhoods inside U₁ and U₂
  obtain ⟨ρ₀, hρ₀, hball_z⟩ := Metric.isOpen_iff.mp hU₁ z₀ hz₀
  obtain ⟨r_x, hr_x, hball_x⟩ := Metric.isOpen_iff.mp hU₂ x₀ hx₀
  set ρ := ρ₀ / 2
  have hρ : 0 < ρ := by positivity
  have hρ_lt : ρ < ρ₀ := by change ρ₀ / 2 < ρ₀; linarith
  have hcball_sub : Metric.closedBall z₀ ρ ⊆ U₁ :=
    fun w hw => hball_z (lt_of_le_of_lt (Metric.mem_closedBall.mp hw) hρ_lt)
  -- Step 2: DifferentiableAt in each variable
  have h_z_at : DifferentiableAt ℂ (fun z => f (z, x₀)) z₀ :=
    (hf_z x₀ hx₀ z₀ hz₀).differentiableAt (hU₁.mem_nhds hz₀)
  have h_x_at : DifferentiableAt ℂ (fun x => f (z₀, x)) x₀ :=
    (hf_x z₀ hz₀ x₀ hx₀).differentiableAt (hU₂.mem_nhds hx₀)
  -- Step 3: Candidate Fréchet derivative L(h,k) = a·h + B(k)
  -- a_of x = ∂f/∂z(z₀, x), the z-derivative as a function of x
  set a_of : E → ℂ := fun x => deriv (fun z => f (z, x)) z₀
  set B : E →L[ℂ] ℂ := fderiv ℂ (fun x => f (z₀, x)) x₀
  set L : ℂ × E →L[ℂ] ℂ :=
    ContinuousLinearMap.coprod (a_of x₀ • ContinuousLinearMap.id ℂ ℂ) B
  suffices HasFDerivAt f L (z₀, x₀) from this.differentiableAt.differentiableWithinAt
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  -- Step 4: Infrastructure for helper lemmas
  have hf_z_ball : ∀ x ∈ U₂, DifferentiableOn ℂ (fun z => f (z, x))
      (Metric.closedBall z₀ ρ) :=
    fun x hx => (hf_z x hx).mono hcball_sub
  have hf_cont_ball : ContinuousOn f (Metric.closedBall z₀ ρ ×ˢ U₂) :=
    hf_cont.mono (Set.prod_mono hcball_sub Subset.rfl)
  -- (i) Continuity of z-derivative in x
  have h_a_cont : ContinuousAt a_of x₀ :=
    continuousAt_deriv_of_continuousOn hρ hU₂ f hf_cont_ball hf_z_ball hx₀
  -- (ii) Taylor remainder bound
  obtain ⟨C_t, δ_t, hCt, hδt, h_taylor⟩ :=
    taylor_remainder_bound hρ hU₂ f hf_cont_ball hf_z_ball hx₀
  -- (iii) HasFDerivAt for x-part
  have h_x_fderiv : HasFDerivAt (fun x => f (z₀, x)) B x₀ := h_x_at.hasFDerivAt
  -- Step 5: ε-δ proof of isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  -- Get δ₂ from continuity of a_of at x₀
  obtain ⟨δ₂, hδ₂, h_a_near⟩ := Metric.continuousAt_iff.mp h_a_cont (c / 3) (by positivity)
  -- Get δ₃ from HasFDerivAt of x-part
  have h_x_fderiv' := h_x_fderiv
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff] at h_x_fderiv'
  obtain ⟨δ₃, hδ₃, h_x_bound⟩ :=
    Metric.eventually_nhds_iff.mp (h_x_fderiv' (show (0 : ℝ) < c / 3 from by positivity))
  -- Choose overall δ
  have hCt1 : (0 : ℝ) < C_t + 1 := by linarith
  refine Metric.eventually_nhds_iff.mpr
    ⟨min (min (ρ / 2) (c / (3 * (C_t + 1)))) (min (min δ₂ δ₃) (min δ_t r_x)),
     by positivity, fun p hp => ?_⟩
  rw [dist_zero_right] at hp
  -- Extract individual bounds from the nested min
  simp only [lt_min_iff] at hp
  obtain ⟨⟨hp_ρ, hp_ct⟩, ⟨hp_δ₂, hp_δ₃⟩, hp_δt, hp_rx⟩ := hp
  -- Component norm bounds
  have h_fst : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
  have h_snd : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
  -- Membership: x₀ + p.2 ∈ U₂
  have hx_mem : x₀ + p.2 ∈ U₂ :=
    hball_x (show dist (x₀ + p.2) x₀ < r_x by
      simp [dist_eq_norm]; exact lt_of_le_of_lt h_snd hp_rx)
  -- Step 6: Decompose remainder into three terms
  -- T₁ = Taylor remainder in z, T₂ = derivative variation, T₃ = Fréchet in x
  set T₁ := f (z₀ + p.1, x₀ + p.2) - f (z₀, x₀ + p.2) - a_of (x₀ + p.2) * p.1
  set T₂ := (a_of (x₀ + p.2) - a_of x₀) * p.1
  set T₃ := f (z₀, x₀ + p.2) - f (z₀, x₀) - B p.2
  -- Show the remainder equals T₁ + T₂ + T₃
  have h_decomp : f ((z₀, x₀) + p) - f (z₀, x₀) - L p = T₁ + T₂ + T₃ := by
    -- Unfold L p and use definitional equality (z₀, x₀) + p = (z₀ + p.1, x₀ + p.2)
    have hLp : L p = a_of x₀ * p.1 + B p.2 := by
      simp [L, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul]
    have hfp : f ((z₀, x₀) + p) = f (z₀ + p.1, x₀ + p.2) := rfl
    rw [hfp, hLp]; simp only [T₁, T₂, T₃]; ring
  rw [h_decomp]
  -- Step 7: Bound each term by (c/3) * ‖p‖
  -- T₁ bound: Taylor remainder ≤ C_t * ‖p.1‖² ≤ (c/3) * ‖p‖
  have hT₁ : ‖T₁‖ ≤ c / 3 * ‖p‖ := by
    have h_tay := h_taylor p.1 (x₀ + p.2) hx_mem
      (show ‖x₀ + p.2 - x₀‖ < δ_t by simp [add_sub_cancel_left]; exact lt_of_le_of_lt h_snd hp_δt)
      (show ‖p.1‖ < ρ / 2 from lt_of_le_of_lt h_fst hp_ρ)
    -- h_tay : ‖T₁‖ ≤ C_t * ‖p.1‖ ^ 2
    have hCt_mul : C_t * ‖p‖ ≤ c / 3 := by
      have h1 : (C_t + 1) * ‖p‖ < (C_t + 1) * (c / (3 * (C_t + 1))) :=
        mul_lt_mul_of_pos_left hp_ct hCt1
      have h2 : (C_t + 1) * (c / (3 * (C_t + 1))) = c / 3 := by field_simp
      nlinarith [norm_nonneg p]
    have hsq : ‖p.1‖ ^ 2 ≤ ‖p‖ ^ 2 :=
      sq_le_sq' (by linarith [norm_nonneg p.1, norm_nonneg p]) h_fst
    calc ‖T₁‖ ≤ C_t * ‖p.1‖ ^ 2 := h_tay
      _ ≤ C_t * ‖p‖ ^ 2 := by nlinarith
      _ = C_t * ‖p‖ * ‖p‖ := by ring
      _ ≤ c / 3 * ‖p‖ := by nlinarith [norm_nonneg p]
  -- T₂ bound: derivative variation * h ≤ (c/3) * ‖p‖
  have hT₂ : ‖T₂‖ ≤ c / 3 * ‖p‖ := by
    have h_an := h_a_near (show dist (x₀ + p.2) x₀ < δ₂ by
      simp [dist_eq_norm]; exact lt_of_le_of_lt h_snd hp_δ₂)
    -- h_an : dist (a_of (x₀ + p.2)) (a_of x₀) < c / 3
    rw [dist_eq_norm] at h_an
    calc ‖T₂‖ = ‖(a_of (x₀ + p.2) - a_of x₀) * p.1‖ := rfl
      _ = ‖a_of (x₀ + p.2) - a_of x₀‖ * ‖p.1‖ := norm_mul _ _
      _ ≤ ‖a_of (x₀ + p.2) - a_of x₀‖ * ‖p‖ := by nlinarith [norm_nonneg (a_of (x₀ + p.2) - a_of x₀)]
      _ ≤ c / 3 * ‖p‖ := by nlinarith [norm_nonneg p]
  -- T₃ bound: Fréchet remainder ≤ (c/3) * ‖p‖
  have hT₃ : ‖T₃‖ ≤ c / 3 * ‖p‖ := by
    have h_xb := h_x_bound (show dist p.2 0 < δ₃ by
      simp [dist_zero_right]; exact lt_of_le_of_lt h_snd hp_δ₃)
    -- h_xb : ‖f (z₀, x₀ + p.2) - f (z₀, x₀) - B p.2‖ ≤ c / 3 * ‖p.2‖
    calc ‖T₃‖ ≤ c / 3 * ‖p.2‖ := h_xb
      _ ≤ c / 3 * ‖p‖ := by nlinarith [norm_nonneg p.2, norm_nonneg p]
  -- Step 8: Combine via triangle inequality
  calc ‖T₁ + T₂ + T₃‖ ≤ ‖T₁ + T₂‖ + ‖T₃‖ := norm_add_le _ _
    _ ≤ (‖T₁‖ + ‖T₂‖) + ‖T₃‖ := by linarith [norm_add_le T₁ T₂]
    _ ≤ c / 3 * ‖p‖ + c / 3 * ‖p‖ + c / 3 * ‖p‖ := by linarith
    _ = c * ‖p‖ := by ring

/-- **Osgood's Lemma (Fin m → ℂ version)**: A continuous function on an open
    subset of ℂᵐ that is holomorphic in each coordinate separately (with the
    others fixed) is jointly holomorphic. -/
theorem osgood_lemma {m : ℕ} {U : Set (Fin m → ℂ)} (hU : IsOpen U)
    (f : (Fin m → ℂ) → ℂ)
    (hf_cont : ContinuousOn f U)
    (hf_sep : ∀ z ∈ U, ∀ i : Fin m,
      DifferentiableAt ℂ (fun w => f (Function.update z i w)) (z i)) :
    DifferentiableOn ℂ f U := by
  induction m with
  | zero =>
    -- Fin 0 → ℂ is a singleton type, so U is a subsingleton set
    have : Subsingleton (Fin 0 → ℂ) := inferInstance
    have hUsub : U.Subsingleton := fun a _ b _ => Subsingleton.elim a b
    exact hUsub.differentiableOn
  | succ n ih =>
    -- At each point z, show DifferentiableWithinAt ℂ f U z
    intro z hz
    -- Find a ball inside U
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z hz
    -- Use @Fin.cons with explicit non-dependent type to avoid elaboration issues
    -- Define g(a, b) = f(Fin.cons a b) on ℂ × (Fin n → ℂ)
    set cons' : ℂ → (Fin n → ℂ) → (Fin (n + 1) → ℂ) :=
      @Fin.cons n (fun _ => ℂ) with hcons'_def
    set g : ℂ × (Fin n → ℂ) → ℂ := fun p => f (cons' p.1 p.2) with hg_def
    -- Helper: cons' maps the product ball into ball(z, ε)
    have hcons_in_ball : ∀ a ∈ Metric.ball (z 0) ε,
        ∀ b ∈ Metric.ball (Fin.tail z) ε,
        cons' a b ∈ Metric.ball z ε := by
      intro a ha b hb
      rw [Metric.mem_ball] at ha hb ⊢
      rw [dist_pi_lt_iff hε]
      intro i
      cases i using Fin.cases with
      | zero => simp only [hcons'_def, Fin.cons_zero]; exact ha
      | succ j =>
        simp only [hcons'_def, Fin.cons_succ]
        exact lt_of_le_of_lt (dist_le_pi_dist b (Fin.tail z) j) hb
    -- cons' as a map from the product is continuous
    have hcons_cont : Continuous (fun p : ℂ × (Fin n → ℂ) => cons' p.1 p.2) := by
      apply continuous_pi; intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · show Continuous (fun p : ℂ × (Fin n → ℂ) => cons' p.1 p.2 0)
        simp_rw [hcons'_def, Fin.cons_zero]; exact continuous_fst
      · show Continuous (fun p : ℂ × (Fin n → ℂ) => cons' p.1 p.2 j.succ)
        simp_rw [hcons'_def, Fin.cons_succ]; exact (continuous_apply j).comp continuous_snd
    -- g is continuous on the product ball
    have hg_cont : ContinuousOn g
        (Metric.ball (z 0) ε ×ˢ Metric.ball (Fin.tail z) ε) :=
      (hf_cont.mono (fun w hw => hball hw)).comp hcons_cont.continuousOn
        (fun ⟨a, b⟩ ⟨ha, hb⟩ => hcons_in_ball a ha b hb)
    -- g is holomorphic in the first variable (from hf_sep for i = 0)
    have hg_z : ∀ b ∈ Metric.ball (Fin.tail z) ε,
        DifferentiableOn ℂ (fun a => g (a, b)) (Metric.ball (z 0) ε) := by
      intro b hb a ha
      have hmem : cons' a b ∈ U := hball (hcons_in_ball a ha b hb)
      have hsep := hf_sep (cons' a b) hmem 0
      have hupd : (fun w => f (Function.update (cons' a b) 0 w)) =
          (fun w => g (w, b)) := by
        ext w; simp only [hg_def, hcons'_def, Fin.update_cons_zero]
      have hcons0 : cons' a b 0 = a := by simp [hcons'_def, Fin.cons_zero]
      rw [hupd, hcons0] at hsep
      exact hsep.differentiableWithinAt
    -- g is holomorphic in the second variable (by induction hypothesis)
    have hg_x : ∀ a ∈ Metric.ball (z 0) ε,
        DifferentiableOn ℂ (fun b => g (a, b)) (Metric.ball (Fin.tail z) ε) := by
      intro a ha
      -- Explicitly show the function to avoid unification timeout with g
      show DifferentiableOn ℂ (fun b => f (cons' a b)) (Metric.ball (Fin.tail z) ε)
      apply ih Metric.isOpen_ball (fun b => f (cons' a b))
      · exact (hf_cont.mono (fun w hw => hball hw)).comp
          (hcons_cont.comp (continuous_const.prodMk continuous_id)).continuousOn
          (fun b hb => hcons_in_ball a ha b hb)
      · intro b hb j
        have hmem : cons' a b ∈ U := hball (hcons_in_ball a ha b hb)
        have hsep := hf_sep (cons' a b) hmem j.succ
        have hupd : (fun w => f (Function.update (cons' a b) j.succ w)) =
            (fun w => f (cons' a (Function.update b j w))) := by
          ext w; simp only [hcons'_def]; congr 1; rw [← Fin.cons_update]
        have hconsj : cons' a b j.succ = b j := by simp [hcons'_def, Fin.cons_succ]
        rw [hupd, hconsj] at hsep
        exact hsep
    -- Apply osgood_lemma_prod to g
    have hg_diff : DifferentiableOn ℂ g
        (Metric.ball (z 0) ε ×ˢ Metric.ball (Fin.tail z) ε) :=
      osgood_lemma_prod Metric.isOpen_ball Metric.isOpen_ball g hg_cont hg_z hg_x
    -- g is DifferentiableAt at (z 0, Fin.tail z)
    have hg_at : DifferentiableAt ℂ g (z 0, Fin.tail z) := by
      have hmem : (z 0, Fin.tail z) ∈ Metric.ball (z 0) ε ×ˢ Metric.ball (Fin.tail z) ε :=
        ⟨Metric.mem_ball_self hε, Metric.mem_ball_self hε⟩
      exact (hg_diff _ hmem).differentiableAt
        ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hmem)
    -- f(w) = g(w 0, Fin.tail w) by Fin.cons_self_tail
    have hfg : ∀ w, f w = g (w 0, Fin.tail w) := by
      intro w; simp only [hg_def, hcons'_def, Fin.cons_self_tail]
    -- ψ(w) = (w 0, Fin.tail w) is differentiable
    have hψ_diff : DifferentiableAt ℂ (fun w : Fin (n+1) → ℂ => (w 0, Fin.tail w)) z := by
      exact DifferentiableAt.prodMk (differentiableAt_apply (𝕜 := ℂ) 0 z)
        (differentiableAt_pi.mpr (fun j => by
          show DifferentiableAt ℂ (fun w : Fin (n+1) → ℂ => w j.succ) z
          exact differentiableAt_apply (𝕜 := ℂ) j.succ z))
    -- f = g ∘ ψ is DifferentiableAt at z
    have hf_at : DifferentiableAt ℂ f z := by
      have : f = g ∘ (fun w => (w 0, Fin.tail w)) := by ext w; exact hfg w
      rw [this]; exact hg_at.comp z hψ_diff
    exact hf_at.differentiableWithinAt

/-! ### 1D Extension Across the Real Line

A continuous function on an open set V ⊂ ℂ that is holomorphic on V \ {Im = 0}
is holomorphic on all of V. This is proved via Morera's theorem: the rectangle
integrals vanish because crossing rectangles split into sub-rectangles in the
upper and lower half-planes. -/

/-- A continuous function on an open set in ℂ that is holomorphic away from the
    real line is holomorphic everywhere. Uses Morera's theorem. -/
theorem differentiableOn_of_continuous_off_real_1d
    {V : Set ℂ} (hV : IsOpen V)
    (f : ℂ → ℂ) (hf_cont : ContinuousOn f V)
    (hf_holo : DifferentiableOn ℂ f (V \ {z : ℂ | z.im = 0})) :
    DifferentiableOn ℂ f V := by
  -- At each point z ∈ V, show DifferentiableWithinAt
  intro z₀ hz₀
  -- If z₀ is not on the real line, f is already holomorphic near z₀
  by_cases hzim : z₀.im ≠ 0
  · have : z₀ ∈ V \ {z | z.im = 0} := ⟨hz₀, hzim⟩
    have hopen : IsOpen (V \ {z : ℂ | z.im = 0}) :=
      hV.sdiff (isClosed_eq Complex.continuous_im continuous_const)
    exact ((hf_holo z₀ this).differentiableAt (hopen.mem_nhds this)).differentiableWithinAt
  · -- z₀ is on the real line. Use Morera's theorem.
    push_neg at hzim -- hzim : z₀.im = 0
    -- Find a ball around z₀ inside V
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV z₀ hz₀
    -- Prove DifferentiableOn on ball, then extract DifferentiableAt at z₀
    suffices h : DifferentiableOn ℂ f (Metric.ball z₀ r) from
      ((h z₀ (Metric.mem_ball_self hr)).differentiableAt
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableWithinAt
    apply (isConservativeOn_and_continuousOn_iff_isDifferentiableOn
      Metric.isOpen_ball).mp
    constructor
    · -- IsConservativeOn f (ball z₀ r)
      -- Helper: continuity on ball
      have hf_cont_ball : ContinuousOn f (Metric.ball z₀ r) :=
        hf_cont.mono (fun _ hw => hball hw)
      -- Helper: DifferentiableAt for points off the real line in the ball
      have hf_diff_at : ∀ c : ℂ, c.im ≠ 0 → c ∈ Metric.ball z₀ r →
          DifferentiableAt ℂ f c := by
        intro c hc hcball
        have hmem : c ∈ V \ {z | z.im = 0} := ⟨hball hcball, hc⟩
        exact (hf_holo c hmem).differentiableAt
          ((hV.sdiff (isClosed_eq Complex.continuous_im continuous_const)).mem_nhds hmem)
      intro z w hrect
      apply eq_neg_of_add_eq_zero_left
      rw [wedgeIntegral_add_wedgeIntegral_eq]
      by_cases hcross : min z.im w.im < 0 ∧ 0 < max z.im w.im
      · -- CROSSING case: rectangle straddles the real line
        obtain ⟨hmin_neg, hmax_pos⟩ := hcross
        let z₁ : ℂ := ⟨z.re, 0⟩
        let w₁ : ℂ := ⟨w.re, 0⟩
        have h0_mem : (0 : ℝ) ∈ [[z.im, w.im]] := by
          rcases le_total z.im w.im with h | h
          · rw [Set.mem_uIcc]; left
            exact ⟨le_of_lt (by rwa [min_eq_left h] at hmin_neg),
                   le_of_lt (by rwa [max_eq_right h] at hmax_pos)⟩
          · rw [Set.mem_uIcc]; right
            exact ⟨le_of_lt (by rwa [min_eq_right h] at hmin_neg),
                   le_of_lt (by rwa [max_eq_left h] at hmax_pos)⟩
        have hzim_ne : z.im ≠ 0 := by
          intro heq; rw [heq] at hmin_neg hmax_pos
          rcases le_or_gt w.im 0 with h | h
          · linarith [max_eq_left h (a := (0 : ℝ))]
          · linarith [min_eq_left (le_of_lt h) (a := (0 : ℝ))]
        have hwim_ne : w.im ≠ 0 := by
          intro heq; rw [heq] at hmin_neg hmax_pos
          rcases le_or_gt z.im 0 with h | h
          · linarith [max_eq_right h (a := z.im) (b := (0 : ℝ))]
          · linarith [min_eq_right (le_of_lt h) (a := z.im) (b := (0 : ℝ))]
        -- Sub-rectangle continuity (following EdgeOfWedge.lean pattern)
        have hcont_sub1 : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, (0 : ℝ)]]) :=
          hf_cont_ball.mono (fun c hc => hrect
            (show c ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] from by
              rw [mem_reProdIm] at hc ⊢
              exact ⟨hc.1, Set.uIcc_subset_uIcc_left h0_mem hc.2⟩))
        have hcont_sub2 : ContinuousOn f ([[z.re, w.re]] ×ℂ [[(0 : ℝ), w.im]]) :=
          hf_cont_ball.mono (fun c hc => hrect
            (show c ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] from by
              rw [mem_reProdIm] at hc ⊢
              exact ⟨hc.1, Set.uIcc_subset_uIcc_right h0_mem hc.2⟩))
        -- DifferentiableOn for sub-rectangles
        have hdiff_sub1 : DifferentiableOn ℂ f
            (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im 0) (max z.im 0)) := by
          intro c hc; rw [mem_reProdIm] at hc
          have hcim := mem_Ioo.mp hc.2
          have hc_ne : c.im ≠ 0 := by
            rcases lt_or_gt_of_ne hzim_ne with hz | hz
            · exact ne_of_lt (lt_of_lt_of_le hcim.2 (by rw [max_eq_right (le_of_lt hz)]))
            · exact ne_of_gt (lt_of_le_of_lt (by rw [min_eq_right (le_of_lt hz)]) hcim.1)
          exact (hf_diff_at c hc_ne (hrect
            (show c ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] from by
              rw [mem_reProdIm]; exact ⟨Ioo_subset_Icc_self hc.1,
              Set.uIcc_subset_uIcc_left h0_mem (Ioo_subset_Icc_self hc.2)⟩))).differentiableWithinAt
        have hdiff_sub2 : DifferentiableOn ℂ f
            (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min 0 w.im) (max 0 w.im)) := by
          intro c hc; rw [mem_reProdIm] at hc
          have hcim := mem_Ioo.mp hc.2
          have hc_ne : c.im ≠ 0 := by
            rcases lt_or_gt_of_ne hwim_ne with hw | hw
            · exact ne_of_lt (lt_of_lt_of_le hcim.2 (by rw [max_eq_left (le_of_lt hw)]))
            · exact ne_of_gt (lt_of_le_of_lt (by rw [min_eq_left (le_of_lt hw)]) hcim.1)
          exact (hf_diff_at c hc_ne (hrect
            (show c ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] from by
              rw [mem_reProdIm]; exact ⟨Ioo_subset_Icc_self hc.1,
              Set.uIcc_subset_uIcc_right h0_mem (Ioo_subset_Icc_self hc.2)⟩))).differentiableWithinAt
        -- Sub-rectangle integrals vanish by Cauchy-Goursat
        have h_sub1 := integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
          f z w₁ (by convert hcont_sub1 using 2) (by convert hdiff_sub1 using 2)
        have h_sub2 := integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
          f z₁ w (by convert hcont_sub2 using 2) (by convert hdiff_sub2 using 2)
        simp only [show (z₁.im : ℝ) = 0 from rfl, show (w₁.im : ℝ) = 0 from rfl,
          show re z₁ = z.re from rfl, show re w₁ = w.re from rfl,
          Complex.ofReal_zero, zero_mul, add_zero] at h_sub1 h_sub2
        simp only [smul_eq_mul] at h_sub1 h_sub2 ⊢
        -- IntervalIntegrable for splitting
        have hint : ∀ (ρ : ℝ), ρ ∈ [[z.re, w.re]] →
            ∀ a' b', [[a', b']] ⊆ [[z.im, w.im]] →
            IntervalIntegrable (fun y => f (↑ρ + ↑y * I)) volume a' b' := by
          intro ρ hρ a' b' hab'
          apply ContinuousOn.intervalIntegrable
          apply hf_cont_ball.comp ((continuousOn_const).add
            ((Complex.continuous_ofReal.continuousOn).mul continuousOn_const))
          intro y hy
          apply hrect
          show (↑ρ + ↑(y : ℝ) * I) ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]]
          rw [mem_reProdIm]
          constructor
          · simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
              Complex.ofReal_im, Complex.I_re, Complex.I_im]; exact hρ
          · simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
              Complex.ofReal_re, Complex.I_re, Complex.I_im]; exact hab' hy
        have hw_mem : w.re ∈ [[z.re, w.re]] := Set.right_mem_uIcc
        have hz_mem : z.re ∈ [[z.re, w.re]] := Set.left_mem_uIcc
        have hsub1 : [[z.im, (0 : ℝ)]] ⊆ [[z.im, w.im]] :=
          Set.uIcc_subset_uIcc_left h0_mem
        have hsub2 : [[(0 : ℝ), w.im]] ⊆ [[z.im, w.im]] :=
          Set.uIcc_subset_uIcc_right h0_mem
        rw [← integral_add_adjacent_intervals (hint w.re hw_mem z.im 0 hsub1)
              (hint w.re hw_mem 0 w.im hsub2),
            ← integral_add_adjacent_intervals (hint z.re hz_mem z.im 0 hsub1)
              (hint z.re hz_mem 0 w.im hsub2)]
        linear_combination h_sub1 + h_sub2
      · -- NON-CROSSING: f holomorphic on open interior, direct Cauchy-Goursat
        push_neg at hcross
        exact integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w
          (hf_cont_ball.mono hrect) (by
          intro c hc; rw [mem_reProdIm] at hc
          rcases le_or_gt 0 (min z.im w.im) with hge | hlt
          · exact (hf_diff_at c (ne_of_gt
              (lt_of_le_of_lt hge (mem_Ioo.mp hc.2).1)) (hrect
              (show c ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] from by
                rw [mem_reProdIm]; exact ⟨Ioo_subset_Icc_self hc.1,
                Ioo_subset_Icc_self hc.2⟩))).differentiableWithinAt
          · exact (hf_diff_at c (ne_of_lt
              (lt_of_lt_of_le (mem_Ioo.mp hc.2).2 (hcross hlt))) (hrect
              (show c ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] from by
                rw [mem_reProdIm]; exact ⟨Ioo_subset_Icc_self hc.1,
                Ioo_subset_Icc_self hc.2⟩))).differentiableWithinAt)
    · -- ContinuousOn
      exact hf_cont.mono (fun _ hw => hball hw)

/-! ### Holomorphic Extension Across Real Boundaries -/

/-- A continuous function on an open set in ℂᵐ that is holomorphic on the
    complement of the "real slice" {z : Im(z) = 0} is holomorphic everywhere.

    For each coordinate direction, the function restricted to a complex line
    is continuous and holomorphic off the real line. By
    `differentiableOn_of_continuous_off_real_1d`, it is holomorphic in that
    direction. Osgood's lemma then gives joint holomorphicity. -/
theorem holomorphic_extension_across_real {m : ℕ}
    {U : Set (Fin m → ℂ)} (hU : IsOpen U)
    (f : (Fin m → ℂ) → ℂ)
    (hf_cont : ContinuousOn f U)
    (hf_holo_off : DifferentiableOn ℂ f
      (U \ { z : Fin m → ℂ | ∀ i : Fin m, (z i).im = 0 })) :
    DifferentiableOn ℂ f U := by
  -- Apply Osgood's lemma
  apply osgood_lemma hU f hf_cont
  -- Show f is separately holomorphic at each point
  -- Helper: Function.update z i is continuous and differentiable
  -- Use update_apply to reduce to if/then/else on each component
  have hupdate_cont : ∀ (z₀ : Fin m → ℂ) (k : Fin m),
      Continuous (Function.update z₀ k) := by
    intro z₀ k; apply continuous_pi; intro j
    simp_rw [Function.update_apply]
    exact continuous_if_const _ (fun _ => continuous_id) (fun _ => continuous_const)
  have hupdate_diff : ∀ (z₀ : Fin m → ℂ) (k : Fin m) (w : ℂ),
      DifferentiableAt ℂ (Function.update z₀ k) w := by
    intro z₀ k w; rw [differentiableAt_pi]; intro j
    simp_rw [Function.update_apply]
    split <;> simp_all
  -- Helper: {z | ∀ j, (z j).im = 0} is closed
  have hreal_closed : IsClosed {z : Fin m → ℂ | ∀ j, (z j).im = 0} := by
    have : {z : Fin m → ℂ | ∀ j, (z j).im = 0} = ⋂ j, {z | (z j).im = 0} := by
      ext z; simp
    rw [this]
    exact isClosed_iInter (fun j => isClosed_eq
      (Complex.continuous_im.comp (continuous_apply j)) continuous_const)
  intro z hz i
  by_cases hreal : ∀ j : Fin m, (z j).im = 0
  · -- z IS on the real slice. Use 1D extension.
    set V : Set ℂ := (Function.update z i) ⁻¹' U with hV_def
    have hV_open : IsOpen V := hU.preimage (hupdate_cont z i)
    have hV_mem : z i ∈ V := by
      show Function.update z i (z i) ∈ U
      rw [Function.update_eq_self]; exact hz
    -- g = f ∘ (Function.update z i) is continuous on V
    have hg_cont : ContinuousOn (fun w => f (Function.update z i w)) V :=
      hf_cont.comp (hupdate_cont z i).continuousOn (fun _ hw => hw)
    -- g is holomorphic on V \ {Im = 0}
    have hg_holo : DifferentiableOn ℂ (fun w => f (Function.update z i w))
        (V \ {w : ℂ | w.im = 0}) := by
      intro w ⟨hwV, hwim⟩
      have hwim' : ¬w.im = 0 := hwim
      have hnotreal : ¬(∀ j, (Function.update z i w j).im = 0) := by
        push_neg; exact ⟨i, by simp [Function.update_self, hwim']⟩
      have hmem : Function.update z i w ∈ U \ {z | ∀ j, (z j).im = 0} :=
        ⟨hwV, hnotreal⟩
      have hopen := hU.sdiff hreal_closed
      have hf_at := (hf_holo_off _ hmem).differentiableAt (hopen.mem_nhds hmem)
      exact (hf_at.comp w ((hupdate_diff z i) w)).differentiableWithinAt
    -- By 1D extension, g is holomorphic on V
    have hg_diff : DifferentiableOn ℂ (fun w => f (Function.update z i w)) V :=
      differentiableOn_of_continuous_off_real_1d hV_open _ hg_cont hg_holo
    exact (hg_diff (z i) hV_mem).differentiableAt (hV_open.mem_nhds hV_mem)
  · -- z is NOT on the real slice. f is directly differentiable near z.
    -- hreal : ¬∀ j, (z j).im = 0, which is exactly z ∉ {z | ∀ j, ...}
    have hmem : z ∈ U \ {z | ∀ j, (z j).im = 0} := ⟨hz, hreal⟩
    have hopen := hU.sdiff hreal_closed
    have hf_at : DifferentiableAt ℂ f z :=
      (hf_holo_off z hmem).differentiableAt (hopen.mem_nhds hmem)
    -- f ∘ (Function.update z i) is differentiable at z i
    have hf_at' : DifferentiableAt ℂ f (Function.update z i (z i)) := by
      rwa [Function.update_eq_self]
    exact hf_at'.comp (z i) ((hupdate_diff z i) (z i))

/-! ### Gluing Lemma for Tube Domains -/

/-- Given a function F that is continuous on an open ball in ℂᵐ and holomorphic away
    from the real slice `{z : ∀ i, (z i).im = 0}`, F is holomorphic on the entire ball.

    This is a direct application of `holomorphic_extension_across_real`.

    **Limitation**: This only helps prove the edge-of-the-wedge theorem when the cone C
    satisfies `C ∪ (-C) ∪ {0} = ℝᵐ` (e.g., m = 1 with C = (0,∞)), because otherwise
    `TubeDomain(C) ∪ TubeDomain(-C)` does not cover all non-real points, and
    the `hF_holo_off` hypothesis cannot be established from the tube domain holomorphicity
    of f₊ and f₋ alone. For general convex cones (including the forward light cone),
    the multi-dimensional edge-of-the-wedge requires iterated 1D extensions. -/
theorem tube_domain_gluing {m : ℕ}
    (x₀ : Fin m → ℝ) (r : ℝ)
    (F : (Fin m → ℂ) → ℂ)
    -- F is continuous on the ball
    (hF_cont : ContinuousOn F (Metric.ball (fun i => (x₀ i : ℂ)) r))
    -- F is holomorphic away from the real slice
    (hF_holo_off : DifferentiableOn ℂ F
      (Metric.ball (fun i => (x₀ i : ℂ)) r \
       { z : Fin m → ℂ | ∀ i : Fin m, (z i).im = 0 })) :
    -- Conclusion: F is holomorphic on the ball
    DifferentiableOn ℂ F (Metric.ball (fun i => (x₀ i : ℂ)) r) :=
  holomorphic_extension_across_real Metric.isOpen_ball F hF_cont hF_holo_off

end
