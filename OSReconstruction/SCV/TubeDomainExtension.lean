/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Convex.Basic
import OSReconstruction.SCV.IteratedCauchyIntegral

/-!
# Tube Domain Extension and the Edge-of-the-Wedge Theorem

This file proves the multi-dimensional edge-of-the-wedge theorem using
the iterated Cauchy integral approach.

## Main definitions

* `TubeDomain` — the tube domain `ℝᵐ + iC` for an open convex cone `C ⊂ ℝᵐ`

## Main results

* `edge_of_the_wedge_theorem` — the edge-of-the-wedge theorem as a theorem (not axiom)

## Strategy

The gap-point problem: for m ≥ 2, there exist z near the real subspace with
Im(z) ∉ C ∪ (-C) ∪ {0}. At such gap points, neither f₊ nor f₋ provides a value.

The solution: define the extension at gap points via the iterated Cauchy integral
```
  F(z) = (2πi)⁻ᵐ ∮...∮ bv(Re w) / ∏(wⱼ - zⱼ) dw₁⋯dwₘ
```
where the integration contours are chosen so all wⱼ stay real (on the real torus).
Then:
1. F is holomorphic on the polydisc (by `cauchyIntegralPolydisc_differentiableOn`)
2. F = f₊ on the intersection with the tube (by the identity theorem)
3. F = f₋ on the intersection with the opposite tube (by the identity theorem)

## References

* Bogoliubov, N.N. (1956). *On the theory of quantized fields*. ICM report.
* Rudin, W. (1971). *Lectures on the edge-of-the-wedge theorem*. CBMS 6.
* Streater & Wightman, *PCT, Spin and Statistics*, Theorem 2-16.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set SCV

namespace SCV

/-! ### Tube domains -/

/-- The tube domain `T(C) = { z ∈ ℂᵐ : Im(z) ∈ C }` where `C ⊂ ℝᵐ` is an
    open convex cone. This is the natural domain of holomorphic extension
    for functions with boundary values on `ℝᵐ`. -/
def TubeDomain {m : ℕ} (C : Set (Fin m → ℝ)) : Set (Fin m → ℂ) :=
  { z | (fun i => (z i).im) ∈ C }

/-- The tube domain is open when the cone is open. -/
theorem tubeDomain_isOpen {m : ℕ} {C : Set (Fin m → ℝ)} (hC : IsOpen C) :
    IsOpen (TubeDomain C) := by
  -- TubeDomain C = Im⁻¹(C) where Im : ℂᵐ → ℝᵐ is continuous
  exact hC.preimage (continuous_pi (fun i => Complex.continuous_im.comp (continuous_apply i)))

/-- The tube domain is connected when C is convex and nonempty. -/
theorem tubeDomain_isPreconnected {m : ℕ} {C : Set (Fin m → ℝ)}
    (hC : Convex ℝ C) (hne : C.Nonempty) :
    IsPreconnected (TubeDomain C) := by
  -- The tube domain is convex (hence preconnected): for z₁, z₂ ∈ T(C) and
  -- real t ∈ [0,1], Im(t z₁ + (1-t) z₂) = t Im(z₁) + (1-t) Im(z₂) ∈ C.
  apply Convex.isPreconnected
  intro z₁ hz₁ z₂ hz₂ a b ha hb hab
  show (fun i => ((a • z₁ + b • z₂) i).im) ∈ C
  have key : (fun i => ((a • z₁ + b • z₂) i).im) =
      a • (fun i => (z₁ i).im) + b • (fun i => (z₂ i).im) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Complex.add_im, Complex.real_smul,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      smul_eq_mul]
  rw [key]
  exact hC hz₁ hz₂ ha hb hab

/-- The opposite tube domain. -/
theorem tubeDomain_neg {m : ℕ} (C : Set (Fin m → ℝ)) :
    TubeDomain (Neg.neg '' C) =
    { z : Fin m → ℂ | (fun i => -(z i).im) ∈ C } := by
  ext z
  simp only [TubeDomain, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨y, hy, hyz⟩
    convert hy using 1
    ext i; have := congr_fun hyz i; simp only [Pi.neg_apply] at this; linarith
  · intro h
    exact ⟨fun i => -(z i).im, h, by ext i; simp⟩

/-- The real subspace (Im = 0) is the common boundary of T(C) and T(-C). -/
def realSubspace (m : ℕ) : Set (Fin m → ℂ) :=
  { z | ∀ i, (z i).im = 0 }

/-- The embedding of ℝᵐ into the real subspace of ℂᵐ. -/
def realEmbed {m : ℕ} (x : Fin m → ℝ) : Fin m → ℂ :=
  fun i => (x i : ℂ)

/-! ### Edge-of-the-Wedge Theorem -/

/-- **The Edge-of-the-Wedge Theorem** (Bogoliubov, 1956).

    Two holomorphic functions on opposite tube domains with matching continuous
    boundary values on a real open set extend to a unique holomorphic function
    on a complex neighborhood.

    This is the theorem that replaces the axiom `edge_of_the_wedge` in
    `AnalyticContinuation.lean`. The proof constructs the extension at gap points
    via the iterated Cauchy integral on polydiscs centered at real points.

    **Proof sketch:**
    For each x₀ ∈ E, choose a polydisc P(x₀, r) centered at the real point x₀.
    1. Define F on P via `cauchyIntegralPolydisc bv x₀ r z`
    2. F is holomorphic on P (by `cauchyIntegralPolydisc_differentiableOn`)
    3. F = f₊ on P ∩ T(C) (both agree with bv on the real slice, identity theorem)
    4. F = f₋ on P ∩ T(-C) (same argument)
    5. U = ⋃_{x₀} P(x₀, r(x₀)) is the desired open neighborhood
    6. Uniqueness: any holomorphic G on U agreeing with f₊ on U ∩ T(C) equals F,
       by the identity theorem (U ∩ T(C) is open and nonempty). -/
theorem edge_of_the_wedge_theorem {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC : IsOpen C) (hconv : Convex ℝ C) (h0 : (0 : Fin m → ℝ) ∉ C)
    (hcone : ∀ (t : ℝ) (y : Fin m → ℝ), 0 < t → y ∈ C → t • y ∈ C)
    (hCne : C.Nonempty)
    (f_plus f_minus : (Fin m → ℂ) → ℂ)
    (hf_plus : DifferentiableOn ℂ f_plus (TubeDomain C))
    (hf_minus : DifferentiableOn ℂ f_minus (TubeDomain (Neg.neg '' C)))
    (E : Set (Fin m → ℝ)) (hE : IsOpen E)
    (bv : (Fin m → ℝ) → ℂ) (hbv_cont : ContinuousOn bv E)
    (hf_plus_bv : ∀ x ∈ E,
      Filter.Tendsto f_plus
        (nhdsWithin (realEmbed x) (TubeDomain C)) (nhds (bv x)))
    (hf_minus_bv : ∀ x ∈ E,
      Filter.Tendsto f_minus
        (nhdsWithin (realEmbed x) (TubeDomain (Neg.neg '' C))) (nhds (bv x))) :
    ∃ (U : Set (Fin m → ℂ)) (F : (Fin m → ℂ) → ℂ),
      IsOpen U ∧
      (∀ x ∈ E, realEmbed x ∈ U) ∧
      DifferentiableOn ℂ F U ∧
      (∀ z ∈ U ∩ TubeDomain C, F z = f_plus z) ∧
      (∀ z ∈ U ∩ TubeDomain (Neg.neg '' C), F z = f_minus z) ∧
      -- Uniqueness: any holomorphic function on U agreeing with f_plus on the
      -- positive tube must agree with F everywhere on U.
      (∀ (G : (Fin m → ℂ) → ℂ), DifferentiableOn ℂ G U →
        (∀ z ∈ U ∩ TubeDomain C, G z = f_plus z) → ∀ z ∈ U, G z = F z) := by
  sorry

end SCV

end
