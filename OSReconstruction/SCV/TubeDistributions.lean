/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.TubeDomainExtension
import OSReconstruction.SCV.IdentityTheorem
import Mathlib.Analysis.Distribution.SchwartzSpace

/-!
# Distribution Theory Axioms for Tube Domains

This file provides two axioms from the theory of distributions and holomorphic
functions on tube domains. These are deep results from several complex variables
that connect distributional boundary values to pointwise properties of holomorphic
functions.

## Axioms

* `continuous_boundary_tube` — holomorphic functions on tube domains with tempered
  distributional boundary values extend continuously to the real boundary.

* `polynomial_growth_tube` — holomorphic functions on tube domains with tempered
  distributional boundary values satisfy polynomial growth estimates.

## Mathematical Background

A tube domain T(C) = ℝᵐ + iC (where C ⊂ ℝᵐ is an open convex cone) carries a
natural notion of "distributional boundary value": a holomorphic function F on T(C)
has distributional boundary values if for each Schwartz function f and approach
direction η ∈ C, the integrals

    ∫ F(x + iεη) f(x) dx

converge as ε → 0⁺ to a tempered distribution.

**Theorem (Vladimirov):** If F is holomorphic on T(C) and has tempered distributional
boundary values, then:
1. F extends continuously to the closure of T(C) at every real point
   (`continuous_boundary_tube`)
2. F satisfies polynomial growth estimates on approach regions
   (`polynomial_growth_tube`)

These results are proved in:
- Vladimirov, V.S. "Methods of the Theory of Generalized Functions" (2002), §25-26
- Epstein, H. "Generalization of the Edge-of-the-Wedge Theorem" (1960)
- Streater & Wightman, "PCT, Spin and Statistics", Theorem 2-6 and 2-9

## Why Axioms?

The proofs of these results require:
- The Paley-Wiener-Schwartz theorem (characterizing Fourier transforms of
  compactly supported distributions)
- The theory of Laplace transforms of tempered distributions
- Estimates on holomorphic functions via their Fourier-Laplace representation

None of these are currently available in Mathlib.

## Application

These axioms are used in `WickRotation.lean` to:
1. Prove that the BHW hypotheses (Lorentz invariance, boundary continuity,
   local commutativity of W_analytic) follow from the Wightman axioms
2. Establish temperedness (E0) of the constructed Schwinger functions
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set

namespace SCV

/-! ### Axiom 1: Continuous Boundary Values -/

/-- **Continuous boundary values for tube-domain holomorphic functions.**

    If F is holomorphic on a tube domain T(C) and has distributional boundary
    values (the smeared integrals ∫ F(x+iεη)f(x)dx converge as ε→0⁺), then
    F extends continuously to the real boundary: for each real point x,
    `ContinuousWithinAt F (TubeDomain C) (realEmbed x)`.

    This is a fundamental result connecting the distributional and pointwise
    theories of boundary values of holomorphic functions on tube domains.

    The proof (not formalized here) proceeds by:
    1. The Fourier-Laplace representation: F(z) = ∫ e^{iz·ξ} dμ(ξ) where μ is
       a tempered distribution supported in the dual cone C*
    2. The Laplace integral converges absolutely for Im(z) ∈ C and extends
       continuously to Im(z) → 0 by dominated convergence
    3. The boundary value of this representation is the distributional boundary
       value of F

    Ref: Vladimirov, "Methods of the Theory of Generalized Functions" §26.2;
    Epstein, J. Math. Phys. 1 (1960) 524-531;
    Streater-Wightman, Theorem 2-9 -/
axiom continuous_boundary_tube {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (h_bv : ∃ (T : SchwartzMap (Fin m → ℝ) ℂ → ℂ),
      ∀ (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
        Filter.Tendsto (fun ε : ℝ =>
          ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (T f)))
    (x : Fin m → ℝ) :
    ContinuousWithinAt F (TubeDomain C) (realEmbed x)

/-- **Distributional uniqueness for tube-domain holomorphic functions.**

    If two holomorphic functions on a tube domain T(C) have the same distributional
    boundary values, they are equal on T(C).

    Proof from `continuous_boundary_tube`:
    1. G = F₁ - F₂ is holomorphic on T(C) with distributional BV = 0.
    2. `continuous_boundary_tube` gives ContinuousWithinAt G (TubeDomain C) (realEmbed x).
    3. The boundary value G(realEmbed x) = 0: the distributional BV is 0, the continuous
       extension recovers this value, and a continuous function integrating to 0 against
       all Schwartz functions must vanish.
    4. For any z₀ = x₀ + iy₀ ∈ T(C), restrict G to the complex line w ↦ x₀ + wy₀.
       This gives g holomorphic on {Im w > 0} (since C is a cone) with g(t) = 0 for
       t ∈ ℝ. By edge-of-the-wedge (glue with the zero function on {Im w < 0}) and
       the identity theorem, g ≡ 0. In particular G(z₀) = g(i) = 0.

    Ref: Vladimirov §26.3; Streater-Wightman, Corollary to Theorem 2-9 -/
theorem distributional_uniqueness_tube {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    {F₁ F₂ : (Fin m → ℂ) → ℂ}
    (hF₁ : DifferentiableOn ℂ F₁ (TubeDomain C))
    (hF₂ : DifferentiableOn ℂ F₂ (TubeDomain C))
    -- Same distributional boundary values: for all Schwartz test functions f
    -- and approach directions η ∈ C, the boundary integrals of (F₁-F₂)*f → 0.
    (h_agree : ∀ (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
      Filter.Tendsto (fun ε : ℝ =>
        ∫ x : Fin m → ℝ,
          (F₁ (fun i => ↑(x i) + ↑ε * ↑(η i) * I) -
           F₂ (fun i => ↑(x i) + ↑ε * ↑(η i) * I)) * f x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0)) :
    ∀ z ∈ TubeDomain C, F₁ z = F₂ z := by
  -- Step 1: G = F₁ - F₂ is holomorphic on T(C) with distributional BV = 0
  set G := fun z => F₁ z - F₂ z with hG_def
  have hG_diff : DifferentiableOn ℂ G (TubeDomain C) := hF₁.sub hF₂
  -- Package the distributional BV = 0 for continuous_boundary_tube
  have hG_bv : ∃ (T : SchwartzMap (Fin m → ℝ) ℂ → ℂ),
      ∀ (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
        Filter.Tendsto (fun ε : ℝ =>
          ∫ x : Fin m → ℝ, G (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (T f)) := by
    refine ⟨0, fun f η hη => ?_⟩
    simp only [Pi.zero_apply]
    -- The integrand G(x+iεη) * f(x) = (F₁ - F₂)(x+iεη) * f(x)
    exact h_agree f η hη
  -- Step 2: ContinuousWithinAt G (TubeDomain C) (realEmbed x) for all x
  have hG_cont : ∀ x : Fin m → ℝ,
      ContinuousWithinAt G (TubeDomain C) (realEmbed x) :=
    fun x => continuous_boundary_tube hC hconv hne hG_diff hG_bv x
  -- Step 3: G(realEmbed x) = 0 for all x ∈ ℝᵐ
  -- The continuous boundary value must equal the distributional BV (which is 0).
  -- This follows from: ContinuousWithinAt gives pointwise convergence G(x+iεη) → G(x),
  -- dominated convergence gives ∫ G(x+iεη)f(x)dx → ∫ G(x)f(x)dx = 0 for all Schwartz f,
  -- and a continuous function integrating to 0 against all Schwartz functions is 0.
  have hG_boundary : ∀ x : Fin m → ℝ, G (realEmbed x) = 0 := by
    sorry
  -- Step 4: G = 0 on T(C) by one-variable slicing + edge-of-the-wedge
  -- For z₀ = x₀ + iy₀ ∈ T(C) with y₀ ∈ C, the restriction g(w) = G(x₀ + wy₀) is
  -- holomorphic on {Im w > 0}, zero on ℝ (by hG_boundary), hence zero everywhere
  -- by edge_of_the_wedge_1d + identity_theorem_connected.
  intro z hz
  have hG_zero : G z = 0 := by
    sorry
  exact sub_eq_zero.mp hG_zero

/-! ### Axiom 2: Polynomial Growth Estimates -/

/-- **Polynomial growth of holomorphic functions on tube domains.**

    If F is holomorphic on a tube domain T(C) with tempered distributional boundary
    values, then F satisfies polynomial growth estimates: for any compact subset
    K ⊂ C of approach directions, there exist C > 0 and N ∈ ℕ such that

        |F(x + iy)| ≤ C · (1 + ‖x‖)^N

    for all x ∈ ℝᵐ and y ∈ K.

    This is the key estimate needed to show that Wick-rotated Wightman functions
    define tempered distributions (OS axiom E0). The polynomial growth follows
    from the Fourier-Laplace representation: the Laplace transform of a tempered
    distribution has at most polynomial growth in the real directions.

    Ref: Streater-Wightman, Theorem 2-6;
    Jost, "The General Theory of Quantized Fields" §III.1;
    Vladimirov §25.3 -/
axiom polynomial_growth_tube {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (h_bv : ∀ (η : Fin m → ℝ), η ∈ C →
      ∃ (T : (Fin m → ℝ) → ℂ), ContinuousOn T Set.univ ∧
        ∀ (f : (Fin m → ℝ) → ℂ), MeasureTheory.Integrable f →
          Filter.Tendsto (fun ε : ℝ =>
            ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * f x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (∫ x, T x * f x)))
    (K : Set (Fin m → ℝ)) (hK : IsCompact K) (hK_sub : K ⊆ C) :
    ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ (x : Fin m → ℝ) (y : Fin m → ℝ), y ∈ K →
        ‖F (fun i => ↑(x i) + ↑(y i) * I)‖ ≤ C_bd * (1 + ‖x‖) ^ N

/-! ### Axiom 3: Bochner Tube Theorem -/

/-- **Bochner's tube theorem (convex hull extension).**

    If F is holomorphic on a tube domain T(C) = ℝᵐ + iC, then F extends to a
    unique holomorphic function on T(conv C) = ℝᵐ + i(conv C), where conv C
    is the convex hull of C.

    This is a fundamental result in several complex variables: holomorphic functions
    on tube domains automatically extend to the convex hull of the base.

    In the OS reconstruction, this is used after the inductive analytic continuation
    (which produces holomorphicity on a tube over the positive orthant) to extend
    to the full forward tube (a tube over V₊, the forward light cone). The key:
    the union of SO(d+1)-rotations of the positive orthant covers V₊, and
    V₊ = conv(⋃_R R · (0,∞)^{d+1}) since V₊ is convex.

    Ref: Bochner, "A theorem on analytic continuation of functions in several
    variables" (1938); Vladimirov §20.2; Hörmander, "An Introduction to Complex
    Analysis in Several Variables", Theorem 2.5.10 -/
axiom bochner_tube_theorem {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C)) :
    ∃ (F_ext : (Fin m → ℂ) → ℂ),
      DifferentiableOn ℂ F_ext (TubeDomain (convexHull ℝ C)) ∧
      ∀ z ∈ TubeDomain C, F_ext z = F z

end SCV

end
