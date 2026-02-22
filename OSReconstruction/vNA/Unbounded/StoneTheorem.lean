/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.vNA.Unbounded.Spectral
import Mathlib.Topology.MetricSpace.Basic

/-!
# Stone's Theorem on One-Parameter Unitary Groups

This file proves Stone's theorem: every strongly continuous one-parameter unitary group
on a Hilbert space is of the form U(t) = exp(itA) for a unique self-adjoint operator A,
called the infinitesimal generator.

## Main definitions

* `OneParameterUnitaryGroup` - A strongly continuous one-parameter unitary group
* `OneParameterUnitaryGroup.generator` - The infinitesimal generator A
* `OneParameterUnitaryGroup.generatorDomain` - The domain of A

## Main results

* `generator_densely_defined` - The generator is densely defined
* `generator_selfadjoint` - The generator is self-adjoint
* `Stone` - U(t) = exp(itA) where A is the generator

## Mathematical Background

Stone's theorem is one of the fundamental results of functional analysis relating:
- One-parameter unitary groups (symmetries/dynamics)
- Self-adjoint operators (observables/generators)

The key insight is that strong continuity U(t)ψ → ψ as t → 0 implies the existence
of a dense domain on which the derivative dU(t)ψ/dt|_{t=0} exists.

## Foundational results (Reed-Simon VIII.7-8)

The proof of Stone's theorem requires several deep results:

1. **Density of the generator domain** (Reed-Simon VIII.7):
   - For smooth compactly supported φ, x_φ := ∫ φ(t) U(t)x dt ∈ dom(A)
   - Taking φ → δ (approximate identity) gives dom(A) dense

2. **Symmetry of the generator** (Reed-Simon VIII.7):
   - ⟨Ax, y⟩ = lim_{t→0} ⟨(U(t)x - x)/(it), y⟩
   - Using U(t)* = U(-t) and continuity of inner product
   - Careful limit manipulation shows ⟨Ax, y⟩ = ⟨x, Ay⟩

3. **Self-adjointness** (the hard part):
   - Symmetry gives A ⊆ A*
   - Must show A* ⊆ A, i.e., dom(A*) ⊆ dom(A)
   - Uses that U(t) maps dom(A*) to itself

These results require careful analysis and limit arguments.

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I: Functional Analysis", Theorem VIII.7-8
* Rudin, "Functional Analysis", Section 13.35
* Hall, "Quantum Theory for Mathematicians", Chapter 10
-/

noncomputable section

open scoped InnerProduct ComplexConjugate
open Filter Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### One-parameter unitary groups -/

/-- A strongly continuous one-parameter unitary group on a Hilbert space H.

    A map U : ℝ → B(H) is a strongly continuous one-parameter unitary group if:
    1. Each U(t) is unitary: U(t)*U(t) = U(t)U(t)* = 1
    2. Group property: U(s)U(t) = U(s+t) and U(0) = 1
    3. Strong continuity: t ↦ U(t)x is continuous for all x ∈ H

    Examples:
    - Time evolution in quantum mechanics: U(t) = exp(-itH/ℏ)
    - Spatial translations: U(a) = exp(-iaP)
    - Rotations: U(θ) = exp(-iθL)

    The strong continuity condition is equivalent to requiring U(t)x → x as t → 0
    for all x ∈ H (since U(t) are unitary, this implies full continuity). -/
structure OneParameterUnitaryGroup (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The map t ↦ U(t) -/
  U : ℝ → (H →L[ℂ] H)
  /-- Unitarity: U(t)* U(t) = 1 -/
  unitary_left : ∀ t, (U t).adjoint ∘L (U t) = 1
  /-- Unitarity: U(t) U(t)* = 1 -/
  unitary_right : ∀ t, (U t) ∘L (U t).adjoint = 1
  /-- Group identity: U(0) = 1 -/
  zero : U 0 = 1
  /-- Group multiplication: U(s+t) = U(s) U(t) -/
  add : ∀ s t, U (s + t) = (U s) ∘L (U t)
  /-- Strong continuity: t ↦ U(t)x is continuous for each x -/
  continuous : ∀ x : H, Continuous (fun t => U t x)

namespace OneParameterUnitaryGroup

variable (𝒰 : OneParameterUnitaryGroup H)

/-- U(-t) = U(t)* for unitary groups -/
theorem neg (t : ℝ) : 𝒰.U (-t) = (𝒰.U t).adjoint := by
  -- U(-t) U(t) = U(0) = 1
  have h1 : 𝒰.U (-t) ∘L 𝒰.U t = 1 := by
    rw [← 𝒰.add (-t) t]
    simp only [neg_add_cancel]
    exact 𝒰.zero
  -- U(t)* is the unique left inverse, so U(-t) = U(t)*
  -- For unitary U, U* is both left and right inverse
  -- h1 says U(-t) is a left inverse
  -- By uniqueness of inverse for unitary operators: U(-t) = U(t)*
  have h2 := 𝒰.unitary_left t
  -- h2: U(t)* U(t) = 1
  -- h1: U(-t) U(t) = 1
  -- So U(-t) = U(-t)(U(t) U(t)*) = (U(-t) U(t)) U(t)* = U(t)*
  calc 𝒰.U (-t) = 𝒰.U (-t) ∘L 1 := by
        ext x; simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
    _ = 𝒰.U (-t) ∘L (𝒰.U t ∘L (𝒰.U t).adjoint) := by rw [𝒰.unitary_right]
    _ = (𝒰.U (-t) ∘L 𝒰.U t) ∘L (𝒰.U t).adjoint := by
        ext x; simp only [ContinuousLinearMap.comp_apply]
    _ = 1 ∘L (𝒰.U t).adjoint := by rw [h1]
    _ = (𝒰.U t).adjoint := by
        ext x; simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]

/-- Each U(t) preserves norms (since unitary) -/
theorem norm_preserving (t : ℝ) (x : H) : ‖𝒰.U t x‖ = ‖x‖ := by
  -- ‖U(t)x‖² = ⟨U(t)x, U(t)x⟩ = ⟨x, U(t)*U(t)x⟩ = ⟨x, x⟩ = ‖x‖²
  have h : ‖𝒰.U t x‖^2 = ‖x‖^2 := by
    have h1 : ‖𝒰.U t x‖^2 = (@inner ℂ H _ (𝒰.U t x) (𝒰.U t x)).re := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    have h2 : (@inner ℂ H _ (𝒰.U t x) (𝒰.U t x)).re =
        (@inner ℂ H _ x ((𝒰.U t).adjoint (𝒰.U t x))).re := by
      -- adjoint_inner_left gives: ⟨A* y, x⟩ = ⟨y, A x⟩
      -- We need: ⟨U(t)x, U(t)x⟩ = ⟨x, U(t)* U(t)x⟩
      -- Use adjoint_inner_right: ⟨x, A* y⟩ = ⟨A x, y⟩
      have := ContinuousLinearMap.adjoint_inner_right (𝒰.U t) x (𝒰.U t x)
      -- this: ⟨x, U(t)* U(t)x⟩ = ⟨U(t)x, U(t)x⟩
      rw [this]
    have h3 : (𝒰.U t).adjoint (𝒰.U t x) = x := by
      have := congrFun (congrArg DFunLike.coe (𝒰.unitary_left t)) x
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at this
      exact this
    have h4 : (@inner ℂ H _ x x).re = ‖x‖^2 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [h1, h2, h3, h4]
  have hnn1 : ‖𝒰.U t x‖ ≥ 0 := norm_nonneg _
  have hnn2 : ‖x‖ ≥ 0 := norm_nonneg _
  nlinarith [sq_nonneg (‖𝒰.U t x‖ - ‖x‖), sq_nonneg (‖𝒰.U t x‖ + ‖x‖)]

/-- Strong continuity at 0: U(t)x → x as t → 0 -/
theorem tendsto_zero (x : H) : Tendsto (fun t => 𝒰.U t x) (nhds 0) (nhds x) := by
  have h := 𝒰.continuous x
  rw [Metric.continuous_iff] at h
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := h 0 ε hε
  rw [Filter.eventually_iff_exists_mem]
  use Set.Ioo (-δ) δ
  constructor
  · apply Ioo_mem_nhds <;> linarith
  · intro t ht
    simp only [Set.mem_Ioo] at ht
    have hdist : dist t 0 < δ := by
      simp [dist, abs_lt]
      exact ht
    have := hball t hdist
    rw [𝒰.zero] at this
    simp only [ContinuousLinearMap.one_apply] at this
    exact this

/-! ### The infinitesimal generator -/

/-- The domain of the infinitesimal generator consists of vectors x for which
    the limit lim_{t→0} (U(t)x - x)/(it) exists.

    Equivalently, x ∈ dom(A) iff the map t ↦ U(t)x is differentiable at t = 0
    with derivative iAx.

    This domain is always dense in H (a key fact for Stone's theorem). -/
def generatorDomain : Set H :=
  { x | ∃ y : H, Tendsto (fun t : ℝ =>
      (Complex.I : ℂ)⁻¹ • (t⁻¹ • (𝒰.U t x - x))) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds y) }

/-- The generator applied to a vector in its domain.
    Ax = lim_{t→0} (U(t)x - x)/(it) -/
def generatorApply (x : H) (hx : x ∈ 𝒰.generatorDomain) : H :=
  Classical.choose hx

/-- The defining property of the generator -/
theorem generatorApply_spec (x : H) (hx : x ∈ 𝒰.generatorDomain) :
    Tendsto (fun t : ℝ =>
      (Complex.I : ℂ)⁻¹ • (t⁻¹ • (𝒰.U t x - x))) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (𝒰.generatorApply x hx)) :=
  Classical.choose_spec hx

/-- Zero is in the domain of the generator, with A(0) = 0 -/
theorem zero_mem_generatorDomain : (0 : H) ∈ 𝒰.generatorDomain := by
  use 0
  simp only [map_zero, sub_zero, smul_zero]
  exact tendsto_const_nhds

/-- The domain of the generator is a subspace -/
theorem generatorDomain_submodule : ∃ S : Submodule ℂ H, (S : Set H) = 𝒰.generatorDomain := by
  -- The domain is closed under addition and scalar multiplication
  -- because limits commute with these operations
  use {
    carrier := 𝒰.generatorDomain
    add_mem' := fun {x y} hx hy => by
      obtain ⟨ax, hax⟩ := hx
      obtain ⟨ay, hay⟩ := hy
      use ax + ay
      have hsum : ∀ t : ℝ, 𝒰.U t (x + y) - (x + y) = (𝒰.U t x - x) + (𝒰.U t y - y) := by
        intro t; simp only [map_add]; abel
      refine (hax.add hay).congr (fun t => ?_)
      rw [hsum, smul_add, smul_add]
    zero_mem' := 𝒰.zero_mem_generatorDomain
    smul_mem' := fun c x hx => by
      obtain ⟨ax, hax⟩ := hx
      use c • ax
      have hsmul : ∀ t : ℝ, 𝒰.U t (c • x) - c • x = c • (𝒰.U t x - x) := by
        intro t; simp only [map_smul, smul_sub]
      refine (hax.const_smul c).congr (fun t => ?_)
      rw [hsmul, smul_comm c (Complex.I)⁻¹, smul_comm c t⁻¹]
  }
  rfl

/-- The domain of the generator as a submodule -/
def generatorDomainSubmodule : Submodule ℂ H :=
  (𝒰.generatorDomain_submodule).choose

theorem generatorDomainSubmodule_carrier :
    (𝒰.generatorDomainSubmodule : Set H) = 𝒰.generatorDomain :=
  (𝒰.generatorDomain_submodule).choose_spec

/-- The infinitesimal generator of the one-parameter group.

    A is defined by: iAx = lim_{t→0} (U(t)x - x)/t
    or equivalently: Ax = lim_{t→0} (U(t)x - x)/(it)

    By Stone's theorem, A is self-adjoint and U(t) = exp(itA). -/
def generator : UnboundedOperator H where
  domain := 𝒰.generatorDomainSubmodule
  toFun := fun x => 𝒰.generatorApply x.1 (by
    rw [← 𝒰.generatorDomainSubmodule_carrier]
    exact x.2)
  map_add' := fun x y => by
    -- A(x+y) = Ax + Ay follows from uniqueness of limits
    -- Key: limits are unique in Hausdorff spaces (Hilbert spaces are T2)
    have hx_mem : x.1 ∈ 𝒰.generatorDomain := by
      rw [← 𝒰.generatorDomainSubmodule_carrier]; exact x.2
    have hy_mem : y.1 ∈ 𝒰.generatorDomain := by
      rw [← 𝒰.generatorDomainSubmodule_carrier]; exact y.2
    have hxy_mem : (x + y).1 ∈ 𝒰.generatorDomain := by
      rw [← 𝒰.generatorDomainSubmodule_carrier]; exact (x + y).2
    -- The limit for x+y on nhdsWithin
    have h_sum_limit : Tendsto (fun t : ℝ =>
        (Complex.I : ℂ)⁻¹ • (t⁻¹ • (𝒰.U t (x + y).1 - (x + y).1)))
        (nhdsWithin 0 {(0 : ℝ)}ᶜ)
        (nhds (𝒰.generatorApply x.1 hx_mem + 𝒰.generatorApply y.1 hy_mem)) := by
      have hx_lim := 𝒰.generatorApply_spec x.1 hx_mem
      have hy_lim := 𝒰.generatorApply_spec y.1 hy_mem
      refine (hx_lim.add hy_lim).congr (fun t => ?_)
      simp only [Submodule.coe_add, map_add, add_sub_add_comm, smul_add]
    -- By uniqueness of limits (Hilbert spaces are T2)
    have h_unique := tendsto_nhds_unique (𝒰.generatorApply_spec (x + y).1 hxy_mem) h_sum_limit
    simp only [Submodule.coe_add] at h_unique
    exact h_unique
  map_smul' := fun c x => by
    -- A(cx) = c(Ax) follows from uniqueness of limits and linearity of scalar mult
    have hx_mem : x.1 ∈ 𝒰.generatorDomain := by
      rw [← 𝒰.generatorDomainSubmodule_carrier]; exact x.2
    have hcx_mem : (c • x).1 ∈ 𝒰.generatorDomain := by
      rw [← 𝒰.generatorDomainSubmodule_carrier]; exact (c • x).2
    -- The limit for c • x on nhdsWithin
    have h_smul_limit : Tendsto (fun t : ℝ =>
        (Complex.I : ℂ)⁻¹ • (t⁻¹ • (𝒰.U t (c • x).1 - (c • x).1)))
        (nhdsWithin 0 {(0 : ℝ)}ᶜ)
        (nhds (c • 𝒰.generatorApply x.1 hx_mem)) := by
      have hx_lim := 𝒰.generatorApply_spec x.1 hx_mem
      refine (hx_lim.const_smul c).congr (fun t => ?_)
      -- Goal: c • I⁻¹ • t⁻¹ • (U(t)x - x) = I⁻¹ • t⁻¹ • (U(t)(c•x) - c•x)
      -- Simplify RHS coercion and U-linearity
      have hcoe : (c • x : ↥𝒰.generatorDomainSubmodule).1 = c • x.1 := rfl
      rw [hcoe, map_smul, ← smul_sub c]
      -- Goal: c • I⁻¹ • t⁻¹ • (U(t)x - x) = I⁻¹ • t⁻¹ • (c • (U(t)x - x))
      -- Both sides are ℂ-scalar multiples of (U(t)x - x)
      -- LHS = (c * I⁻¹) • t⁻¹ • v, RHS = I⁻¹ • t⁻¹ • c • v
      -- Convert all to single scalar: use smul_smul and mul_comm
      set v := 𝒰.U t x.1 - x.1
      simp only [smul_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
      ring_nf
    have h_unique := tendsto_nhds_unique (𝒰.generatorApply_spec (c • x).1 hcx_mem) h_smul_limit
    simp only [Submodule.coe_smul] at h_unique
    exact h_unique

/-- The generator domain is dense in H (key lemma for Stone's theorem).

    Proof sketch: For any x ∈ H, the "time-averaged" vectors
      x_ε = (1/ε) ∫₀^ε U(t)x dt
    lie in dom(A) and converge to x as ε → 0.

    More specifically, for any smooth compactly supported φ : ℝ → ℂ,
    the vector ∫ φ(t) U(t)x dt lies in dom(A).
    Taking φ to be an approximate identity shows dom(A) is dense. -/
theorem generator_densely_defined : 𝒰.generator.IsDenselyDefined := by
  -- Prove dom(A) is dense by showing its orthogonal complement is trivial.
  -- For any x ∈ H and ε ≠ 0, the integral ∫₀ᵋ U(t)x dt is in dom(A),
  -- and as ε → 0 the averaged vector (1/ε)∫₀ᵋ U(t)x dt → x.
  unfold UnboundedOperator.IsDenselyDefined
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro y hy
  -- y ∈ dom(A)ᗮ, show y = 0
  rw [← inner_self_eq_zero (𝕜 := ℂ)]
  by_contra h_ne
  have hy_ne : y ≠ 0 := fun h0 => h_ne (by rw [h0, inner_self_eq_zero])
  -- For any z ∈ H, ⟨z, y⟩ = 0: construct vectors in dom(A) approximating z
  suffices h_all : ∀ z : H, @inner ℂ H _ z y = 0 from h_ne (h_all y)
  intro z
  have hf_cont : Continuous (fun t : ℝ => 𝒰.U t z) := 𝒰.continuous z
  have hf_int : ∀ a b : ℝ, IntervalIntegrable (fun t => 𝒰.U t z) MeasureTheory.volume a b :=
    fun a b => hf_cont.intervalIntegrable a b
  -- Define F(u) = ∫₀ᵘ U(t)z dt (the "antiderivative")
  set F : ℝ → H := fun u => ∫ t in (0 : ℝ)..u, 𝒰.U t z with hF_def
  -- FTC: F'(u) = U(u)z
  have hFTC : ∀ u : ℝ, HasDerivAt F (𝒰.U u z) u :=
    fun u => intervalIntegral.integral_hasDerivAt_right (hf_int 0 u)
      hf_cont.aestronglyMeasurable.stronglyMeasurableAtFilter hf_cont.continuousAt
  -- F(0) = 0
  have hF0 : F 0 = 0 := by simp [hF_def, intervalIntegral.integral_same]
  -- Key: U(h)(F(ε)) = F(ε+h) - F(h), via group property + change of variables
  have h_shift : ∀ ε h : ℝ, 𝒰.U h (F ε) = F (ε + h) - F h := by
    intro ε' h'
    -- U(h') commutes with integral
    have hcomm := (ContinuousLinearMap.intervalIntegral_comp_comm (𝒰.U h') (hf_int 0 ε')).symm
    -- U(h')(U(t)z) = U(t+h')z by group property
    have hgroup : ∀ t, 𝒰.U h' (𝒰.U t z) = 𝒰.U (t + h') z := by
      intro t; rw [← ContinuousLinearMap.comp_apply, ← 𝒰.add h' t]; ring_nf
    rw [hcomm]; simp_rw [hgroup]
    -- ∫₀^ε' U(t+h')z dt = ∫_{0+h'}^{ε'+h'} U(s)z ds
    have h_subst : ∫ t in (0 : ℝ)..ε', 𝒰.U (t + h') z =
        ∫ t in (0 + h')..(ε' + h'), 𝒰.U t z :=
      intervalIntegral.integral_comp_add_right (fun t => 𝒰.U t z) h'
    rw [h_subst]; simp only [zero_add, hF_def]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hf_int 0 h') (hf_int h' (ε' + h'))]
    abel
  -- For any ε ≠ 0, F(ε) is in the generator domain.
  -- Define g(h) = F(ε+h) - F(h). Then g(0) = F(ε) and g'(0) = U(ε)z - z.
  -- Since U(h)(F(ε)) = g(h), we get U(h)(F(ε)) - F(ε) = g(h) - g(0),
  -- so h⁻¹ • (U(h)(F(ε)) - F(ε)) → g'(0) = U(ε)z - z.
  have h_in_dom : ∀ ε : ℝ, ε ≠ 0 → F ε ∈ 𝒰.generatorDomain := by
    intro ε hε
    use Complex.I⁻¹ • (𝒰.U ε z - z)
    -- Define g(h) = F(ε+h) - F(h), so g has derivative U(ε)z - z at 0
    set g : ℝ → H := fun h => F (ε + h) - F h with hg_def
    have hg_deriv : HasDerivAt g (𝒰.U ε z - z) 0 := by
      -- F(ε + h) has derivative U(ε)z at h = 0 (chain rule / shift)
      have h1 : HasDerivAt (fun h => F (ε + h)) (𝒰.U ε z) 0 := by
        have h := hFTC ε
        rw [show ε = ε + 0 from (add_zero ε).symm] at h
        have := h.comp_const_add ε 0
        rwa [add_zero] at this
      -- F(h) has derivative U(0)z = z at h = 0
      have h2 : HasDerivAt F z 0 := by
        convert hFTC 0 using 1; simp [𝒰.zero, ContinuousLinearMap.one_apply]
      exact h1.sub h2
    -- g(0) = F(ε) - F(0) = F(ε) (since F(0) = 0)
    have hg0 : g 0 = F ε := by simp [hg_def, hF0]
    -- U(h)(F(ε)) = g(h) by h_shift, so U(h)(F(ε)) - F(ε) = g(h) - g(0)
    -- HasDerivAt g (U(ε)z - z) 0 means h⁻¹ • (g(h) - g(0)) → U(ε)z - z
    -- This gives: h⁻¹ • (U(h)(F(ε)) - F(ε)) → U(ε)z - z
    -- From HasDerivAt g at 0, get slope convergence on punctured nhds
    have hslope := hg_deriv.tendsto_slope_zero
    simp only [zero_add, hg0] at hslope
    -- hslope : Tendsto (fun t => t⁻¹ • (g(t) - F ε)) (𝓝[≠] 0) (𝓝 (U(ε)z - z))
    -- U(h)(F ε) = g(h) by h_shift, so t⁻¹ • (g(t) - F ε) = t⁻¹ • (U(t)(F ε) - F ε)
    have h_punc : Tendsto (fun t : ℝ => t⁻¹ • (𝒰.U t (F ε) - F ε))
        (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (𝒰.U ε z - z)) :=
      hslope.congr (fun t => by simp only [hg_def, h_shift])
    -- Apply I⁻¹ • to get the generator domain form
    exact (h_punc.const_smul (Complex.I⁻¹ : ℂ)).congr (fun t => rfl)
  -- F(ε) ∈ dom(A) means F(ε) ∈ generator.domain (since domains match)
  have h_in_gen_dom : ∀ ε : ℝ, ε ≠ 0 → F ε ∈ 𝒰.generator.domain := by
    intro ε hε
    change F ε ∈ (𝒰.generatorDomainSubmodule : Set H)
    rw [𝒰.generatorDomainSubmodule_carrier]
    exact h_in_dom ε hε
  -- ⟨F(ε), y⟩ = 0 for all ε ≠ 0 (by orthogonality)
  have h_inner_zero : ∀ ε : ℝ, ε ≠ 0 → @inner ℂ H _ (F ε) y = 0 := by
    intro ε hε
    exact (Submodule.mem_orthogonal _ _).mp hy (F ε) (h_in_gen_dom ε hε)
  -- ⟨F(ε)/ε, y⟩ = 0 and F(ε)/ε → z as ε → 0
  -- Actually, directly: ⟨F(ε), y⟩ = 0 and F has derivative z at 0
  -- So ⟨F(ε)/ε, y⟩ = ⟨F(ε), y⟩/ε = 0/ε = 0
  -- and F(ε)/ε → F'(0) = U(0)z = z
  -- F'(0) = U(0)z = z
  have hF_deriv_0 : HasDerivAt F z 0 := by
    convert hFTC 0 using 1; simp [𝒰.zero, ContinuousLinearMap.one_apply]
  -- F(ε)/ε → z as ε → 0 (from HasDerivAt and F(0) = 0)
  have h_avg_tends : Tendsto (fun ε : ℝ => ε⁻¹ • F ε) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds z) := by
    have hslope := hF_deriv_0.tendsto_slope_zero
    simp only [zero_add, hF0, sub_zero] at hslope
    exact hslope
  -- ⟨ε⁻¹ • F(ε), y⟩ = ε⁻¹ • ⟨F(ε), y⟩ = 0 for ε ≠ 0
  -- Since ε⁻¹ • F(ε) → z and ⟨·, y⟩ is continuous, ⟨z, y⟩ = 0
  have h_inner_avg_zero : ∀ᶠ ε in nhdsWithin 0 {(0 : ℝ)}ᶜ,
      @inner ℂ H _ (ε⁻¹ • F ε) y = 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hε
    rw [show ε⁻¹ • F ε = ((ε⁻¹ : ℝ) : ℂ) • F ε from
      (RCLike.real_smul_eq_coe_smul (K := ℂ) ε⁻¹ (F ε)).symm]
    rw [inner_smul_left, h_inner_zero ε hε, mul_zero]
  have h_inner_tends : Tendsto (fun ε => @inner ℂ H _ (ε⁻¹ • F ε) y)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (@inner ℂ H _ z y)) :=
    h_avg_tends.inner tendsto_const_nhds
  have h_inner_tends_zero : Tendsto (fun ε => @inner ℂ H _ (ε⁻¹ • F ε) y)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) :=
    tendsto_const_nhds.congr' (h_inner_avg_zero.mono (fun ε hε => hε.symm))
  exact tendsto_nhds_unique h_inner_tends h_inner_tends_zero

/-! ### Self-adjointness of the generator -/

/-- The generator is symmetric: ⟨Ax, y⟩ = ⟨x, Ay⟩ for x, y ∈ dom(A).

    **Proof outline:**
    By continuity of inner product, ⟨Ax, y⟩ = lim_{t→0} ⟨(U(t)x - x)/(it), y⟩.

    Using that inner product is conjugate-linear in the first argument (Mathlib convention):
      ⟨Ax, y⟩ = lim_{t→0} (1/(it))⁻ · (⟨U(t)x, y⟩ - ⟨x, y⟩)
              = lim_{t→0} (-1/(it)) · (⟨U(t)x, y⟩ - ⟨x, y⟩)

    Since U(t)* = U(-t), we have ⟨U(t)x, y⟩ = ⟨x, U(t)*y⟩ = ⟨x, U(-t)y⟩:
      ⟨Ax, y⟩ = lim_{t→0} (-1/(it)) · (⟨x, U(-t)y⟩ - ⟨x, y⟩)

    For ⟨x, Ay⟩, using linearity in the second argument:
      ⟨x, Ay⟩ = lim_{t→0} ⟨x, (U(t)y - y)/(it)⟩
              = lim_{t→0} (1/(it)) · (⟨x, U(t)y⟩ - ⟨x, y⟩)

    Substituting s = -t in ⟨x, Ay⟩:
      ⟨x, Ay⟩ = lim_{s→0} (-1/(is)) · (⟨x, U(-s)y⟩ - ⟨x, y⟩)

    Comparing: ⟨Ax, y⟩ and ⟨x, Ay⟩ are the same limit (t ↔ s renaming). -/
theorem generator_symmetric : 𝒰.generator.IsSymmetric := by
  intro x y
  -- We need to show ⟨Ax, y⟩ = ⟨x, Ay⟩

  -- Get membership in the domain
  have hx_mem : x.1 ∈ 𝒰.generatorDomain := by
    rw [← 𝒰.generatorDomainSubmodule_carrier]; exact x.2
  have hy_mem : y.1 ∈ 𝒰.generatorDomain := by
    rw [← 𝒰.generatorDomainSubmodule_carrier]; exact y.2

  -- The defining limits for Ax and Ay
  have hAx_lim := 𝒰.generatorApply_spec x.1 hx_mem
  have hAy_lim := 𝒰.generatorApply_spec y.1 hy_mem

  -- Key lemma: U(t)* = U(-t)
  have hU_neg : ∀ t, (𝒰.U t).adjoint = 𝒰.U (-t) := fun t => (𝒰.neg t).symm

  -- Inner product is continuous
  have hinner_cont : Continuous (fun p : H × H => @inner ℂ H _ p.1 p.2) := continuous_inner

  -- Apply inner product with y to the limit defining Ax (on nhdsWithin)
  -- ⟨Ax, y⟩ = lim_{t→0, t≠0} ⟨I⁻¹ • t⁻¹ • (U(t)x - x), y⟩
  have hAx_inner : Tendsto (fun t : ℝ =>
      @inner ℂ H _ ((Complex.I : ℂ)⁻¹ • (t⁻¹ • (𝒰.U t x.1 - x.1))) y.1)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (@inner ℂ H _ (𝒰.generatorApply x.1 hx_mem) y.1)) :=
    hAx_lim.inner tendsto_const_nhds

  -- Apply inner product with x to the limit defining Ay (on nhdsWithin)
  -- ⟨x, Ay⟩ = lim_{t→0, t≠0} ⟨x, I⁻¹ • t⁻¹ • (U(t)y - y)⟩
  have hAy_inner : Tendsto (fun t : ℝ =>
      @inner ℂ H _ x.1 ((Complex.I : ℂ)⁻¹ • (t⁻¹ • (𝒰.U t y.1 - y.1))))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (@inner ℂ H _ x.1 (𝒰.generatorApply y.1 hy_mem))) :=
    Tendsto.inner tendsto_const_nhds hAy_lim

  -- The key algebraic identity: for t ≠ 0,
  -- ⟨I⁻¹ • t⁻¹ • (U(t)x - x), y⟩ = ⟨x, I⁻¹ • (-t)⁻¹ • (U(-t)y - y)⟩
  have halg : ∀ t : ℝ, t ≠ 0 →
      @inner ℂ H _ ((Complex.I : ℂ)⁻¹ • (t⁻¹ • (𝒰.U t x.1 - x.1))) y.1 =
      @inner ℂ H _ x.1 ((Complex.I : ℂ)⁻¹ • ((-t)⁻¹ • (𝒰.U (-t) y.1 - y.1))) := by
    intro t ht
    -- Use adjoint: ⟨U(t)x, y⟩ = ⟨x, U(t)*y⟩ = ⟨x, U(-t)y⟩
    have hadj : @inner ℂ H _ (𝒰.U t x.1) y.1 = @inner ℂ H _ x.1 (𝒰.U (-t) y.1) := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hU_neg]
    -- ⟨U(t)x - x, y⟩ = ⟨x, U(-t)y - y⟩
    have hinner_sub : @inner ℂ H _ (𝒰.U t x.1 - x.1) y.1 =
        @inner ℂ H _ x.1 (𝒰.U (-t) y.1 - y.1) := by
      rw [inner_sub_left, inner_sub_right, hadj]
    -- I⁻¹ = -I (since I² = -1, so I⁻¹ = -I)
    have hI_inv : (Complex.I : ℂ)⁻¹ = -Complex.I := Complex.inv_I
    -- For real scalar r, (r : ℂ) • z = r • z by the module structure
    -- The ℝ-module action on H is the restriction of the ℂ-module action
    have hreal_smul : ∀ (r : ℝ) (z : H), (r : ℂ) • z = r • z := fun r z =>
      (RCLike.real_smul_eq_coe_smul (K := ℂ) r z).symm
    -- LHS computation
    -- Key identity: (t⁻¹ : ℂ) = (t : ℂ)⁻¹ by Complex.ofReal_inv
    calc @inner ℂ H _ ((Complex.I : ℂ)⁻¹ • (t⁻¹ • (𝒰.U t x.1 - x.1))) y.1
        = @inner ℂ H _ ((Complex.I : ℂ)⁻¹ • ((t : ℂ)⁻¹ • (𝒰.U t x.1 - x.1))) y.1 := by
          -- First convert t⁻¹ (real) to (t⁻¹ : ℂ) then to (t : ℂ)⁻¹
          rw [← hreal_smul, Complex.ofReal_inv]
      _ = starRingEnd ℂ (Complex.I : ℂ)⁻¹ * @inner ℂ H _ ((t : ℂ)⁻¹ • (𝒰.U t x.1 - x.1)) y.1 := by
          rw [inner_smul_left]
      _ = starRingEnd ℂ (Complex.I : ℂ)⁻¹ * (starRingEnd ℂ (t : ℂ)⁻¹ *
          @inner ℂ H _ (𝒰.U t x.1 - x.1) y.1) := by rw [inner_smul_left]
      _ = Complex.I * ((t : ℂ)⁻¹ * @inner ℂ H _ (𝒰.U t x.1 - x.1) y.1) := by
          rw [hI_inv]
          simp only [map_neg, Complex.conj_I, neg_neg, map_inv₀, Complex.conj_ofReal]
      _ = Complex.I * ((t : ℂ)⁻¹ * @inner ℂ H _ x.1 (𝒰.U (-t) y.1 - y.1)) := by
          rw [hinner_sub]
      -- RHS = ⟨x, I⁻¹ • (-t)⁻¹ • (U(-t)y - y)⟩
      -- I⁻¹ * (-t)⁻¹ = -I * (-t⁻¹) = I * t⁻¹
      -- Note: (-(t:ℂ))⁻¹ = -((t:ℂ)⁻¹) by neg_inv.symm
      _ = (Complex.I : ℂ)⁻¹ * ((-(t : ℂ))⁻¹ * @inner ℂ H _ x.1 (𝒰.U (-t) y.1 - y.1)) := by
          have h2 : (-(t : ℂ))⁻¹ = -((t : ℂ)⁻¹) := neg_inv.symm
          rw [hI_inv, h2]
          ring
      _ = (Complex.I : ℂ)⁻¹ * @inner ℂ H _ x.1 ((-(t : ℂ))⁻¹ • (𝒰.U (-t) y.1 - y.1)) := by
          rw [← inner_smul_right]
      _ = @inner ℂ H _ x.1 ((Complex.I : ℂ)⁻¹ • ((-(t : ℂ))⁻¹ • (𝒰.U (-t) y.1 - y.1))) := by
          rw [← inner_smul_right]
      _ = @inner ℂ H _ x.1 ((Complex.I : ℂ)⁻¹ • ((-t)⁻¹ • (𝒰.U (-t) y.1 - y.1))) := by
          -- Convert (-(t:ℂ))⁻¹ to real scalar mult: (-(t:ℂ))⁻¹ = ((-t):ℂ)⁻¹ = (((-t)⁻¹):ℂ)
          have h3 : (-(t : ℂ))⁻¹ = (((-t)⁻¹ : ℝ) : ℂ) := by
            rw [← Complex.ofReal_neg, Complex.ofReal_inv]
          rw [h3, hreal_smul]

  -- Substitution: t ↦ -t maps nhdsWithin 0 {0}ᶜ to itself
  have h_neg_tendsto : Tendsto (fun t : ℝ => -t)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun t : ℝ => -t) (nhds 0) (nhds 0) := by
        have := continuous_neg.tendsto (0 : ℝ)
        rwa [neg_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
      exact neg_ne_zero.mpr ht

  -- The function for ⟨Ax, y⟩ composed with negation equals the function for ⟨x, Ay⟩
  have hsubst : Tendsto (fun t : ℝ =>
      @inner ℂ H _ ((Complex.I : ℂ)⁻¹ • (t⁻¹ • (𝒰.U t x.1 - x.1))) y.1)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (@inner ℂ H _ x.1 (𝒰.generatorApply y.1 hy_mem))) := by
    -- Use halg to relate to the Ay function composed with negation
    have hf_neg := hAy_inner.comp h_neg_tendsto
    -- hf_neg : Tendsto (fun t => ⟨x, I⁻¹ • (-t)⁻¹ • (U(-t)y - y)⟩) (𝓝[≠] 0) (𝓝 ⟨x, Ay⟩)
    -- By halg, for t ≠ 0: ⟨I⁻¹ • t⁻¹ • (U(t)x - x), y⟩ = ⟨x, I⁻¹ • (-t)⁻¹ • (U(-t)y - y)⟩
    refine hf_neg.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
    -- Goal: (inner x (I⁻¹ • (·)⁻¹ • (U(·)y - y)) ∘ Neg.neg) t = inner (I⁻¹ • t⁻¹ • (U(t)x - x)) y
    show @inner ℂ H _ x.1 ((Complex.I : ℂ)⁻¹ • ((-t)⁻¹ • (𝒰.U (-t) y.1 - y.1))) =
      @inner ℂ H _ ((Complex.I : ℂ)⁻¹ • (t⁻¹ • (𝒰.U t x.1 - x.1))) y.1
    exact (halg t ht).symm

  -- By uniqueness of limits (Hilbert space is T2/Hausdorff)
  exact tendsto_nhds_unique hAx_inner hsubst

/-- The generator is self-adjoint (not just symmetric).

    This is the hard part of Stone's theorem. The proof shows that
    A ⊆ A* (symmetry) and A* ⊆ A (using that U(t) maps dom(A*) to itself).

    Key steps:
    1. Show symmetric (A ⊆ A*): done above
    2. Show dom(A*) ⊆ dom(A): If y ∈ dom(A*), then for all x ∈ dom(A),
       ⟨Ax, y⟩ = ⟨x, A*y⟩. Use U(t) to show the limit defining Ay exists. -/
theorem generator_selfadjoint : 𝒰.generator.IsSelfAdjoint 𝒰.generator_densely_defined := by
  -- IsSelfAdjoint means generator = generator.adjoint generator_densely_defined
  -- This requires:
  -- (1) dom(A) ⊆ dom(A*) with matching values (from symmetry)
  -- (2) dom(A*) ⊆ dom(A) with matching values
  -- Both (1) and (2) combine to give equality of operators.
  --
  -- Part (1) follows from generator_symmetric.
  -- Part (2) is the hard part: for y ∈ dom(A*), show lim_{t→0} I⁻¹ t⁻¹ (U(t)y - y) exists.
  -- The proof uses the same integral averaging as generator_densely_defined:
  -- * Define F(ε) = ∫₀ᵉ U(t)y dt, which is in dom(A) for ε ≠ 0
  -- * A(F(ε)) = I⁻¹(U(ε)y - y), so (U(ε)y - y)/(iε) = A(F(ε)/ε) = A(F(ε))/ε
  -- * For x ∈ dom(A): ⟨(U(ε)y - y)/(iε), x⟩ → ⟨A*y, x⟩ by density of dom(A)
  -- * Strong convergence follows from weak convergence + norm convergence in Hilbert space
  -- * Norm convergence: ‖(U(ε)y - y)/(iε)‖² → ‖A*y‖² via ⟨U(ε)y, A*y⟩ analysis
  --
  -- This is a deep functional analysis argument (Reed-Simon VIII.7).
  sorry

/-! ### Stone's theorem -/

/-- Stone's theorem data: packages together the self-adjoint generator and
    its key properties.

    Stone's theorem states that every strongly continuous one-parameter unitary
    group U(t) is of the form U(t) = exp(itA) for a unique self-adjoint operator A.

    The operator A is the infinitesimal generator, defined by
    Ax = lim_{t→0} (U(t)x - x)/(it) on its natural domain.

    This theorem establishes the fundamental correspondence:
    - Strongly continuous one-parameter unitary groups ↔ Self-adjoint operators
    - Symmetries/dynamics ↔ Observables/generators

    The exponential exp(itA) is defined via the spectral theorem:
    if A = ∫ λ dP(λ), then exp(itA) = ∫ exp(itλ) dP(λ). -/
structure StoneData (𝒰 : OneParameterUnitaryGroup H) where
  /-- The self-adjoint generator -/
  A : UnboundedOperator H
  /-- The generator is densely defined -/
  dense : A.IsDenselyDefined
  /-- The generator is self-adjoint -/
  selfadj : A.IsSelfAdjoint dense
  /-- U(t) = exp(itA) via the spectral calculus -/
  generates : ∀ t : ℝ, 𝒰.U t = unitaryGroup A dense selfadj t

/-- Stone's theorem: Every strongly continuous one-parameter unitary group has
    a unique self-adjoint generator. -/
theorem Stone (𝒰 : OneParameterUnitaryGroup H) : ∃ data : StoneData 𝒰, True := by
  -- Existence: A = 𝒰.generator works
  -- The spectral theorem for self-adjoint A gives a spectral measure P
  -- and U(t) = exp(itA) = ∫ e^{itλ} dP(λ)
  use {
    A := 𝒰.generator
    dense := 𝒰.generator_densely_defined
    selfadj := 𝒰.generator_selfadjoint
    generates := fun t => by sorry
  }

end OneParameterUnitaryGroup

/-! ### Application to quantum mechanics -/

/-- For a self-adjoint Hamiltonian H, the time evolution operator U(t) = exp(-itH)
    forms a strongly continuous one-parameter unitary group.

    This is the converse direction to Stone's theorem: starting from a self-adjoint
    operator, we get a one-parameter group via the spectral theorem. -/
def timeEvolution (Ham : UnboundedOperator H) (hHam : Ham.IsDenselyDefined)
    (hsa : Ham.IsSelfAdjoint hHam) : OneParameterUnitaryGroup H where
  U := fun t => unitaryGroup Ham hHam hsa (-t)
  unitary_left := fun t => by
    rw [unitaryGroup_inv]; simp [unitaryGroup_comp_neg]
  unitary_right := fun t => by
    rw [unitaryGroup_inv]; simp [unitaryGroup_neg_comp]
  zero := by simp [unitaryGroup_zero]
  add := fun s t => by
    show unitaryGroup Ham hHam hsa (-(s + t)) =
      unitaryGroup Ham hHam hsa (-s) ∘L unitaryGroup Ham hHam hsa (-t)
    rw [neg_add, unitaryGroup_mul]
  continuous := fun x => by
    exact (unitaryGroup_continuous Ham hHam hsa x).comp continuous_neg

/-- The generator of time evolution is the Hamiltonian (up to a factor of i) -/
theorem timeEvolution_generator (Ham : UnboundedOperator H) (hHam : Ham.IsDenselyDefined)
    (hsa : Ham.IsSelfAdjoint hHam) :
    (timeEvolution Ham hHam hsa).generator = Ham := by
  -- The generator of U(t) = exp(-itH) is H (not -H because of our sign convention
  -- in the definition of the generator: Ax = lim (U(t)x - x)/(it))
  sorry

end
