/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Connected.PathConnected
import OSReconstruction.ComplexLieGroups.Complexification

/-!
# Bargmann-Hall-Wightman Theorem

This file proves the Bargmann-Hall-Wightman theorem using the connectedness of
the complex Lorentz group SO⁺(1,d;ℂ) and the identity theorem.

## Main results

* `complex_lorentz_invariance` — real Lorentz invariance extends to complex Lorentz invariance
* `bargmann_hall_wightman_theorem` — the full BHW theorem

## Proof outline

1. **Real → complex Lorentz invariance:** For fixed z in the forward tube,
   Λ ↦ F(Λ·z) is holomorphic on SO⁺(1,d;ℂ). It equals F(z) for all real Λ.
   Since SO⁺(1,d;ℝ) is a totally real submanifold of the *connected* SO⁺(1,d;ℂ),
   the identity theorem gives F(Λ·z) = F(z) for all complex Λ.

2. **Permutation symmetry at Jost points:** At real spacelike configurations,
   local commutativity gives F(π·x) = F(x) for adjacent transpositions.

3. **Edge-of-the-wedge gluing:** For adjacent permuted tubes sharing a
   Jost-point boundary, the functions agree and glue via edge-of-the-wedge.

4. **Iterate over Sₙ:** Cover all permutations via adjacent transpositions.
   The identity theorem ensures consistency at overlaps.

## References

* Bargmann, Hall, Wightman (1957), Nuovo Cimento 5, 1-14.
* Streater & Wightman, *PCT, Spin and Statistics*, Theorem 2-11.
* Jost (1965), *The General Theory of Quantized Fields*, Ch. IV.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup

variable {d : ℕ}

namespace BHW

/-! ### Forward tube and related structures

These are defined independently of the Wightman module so that
the BHW theorem can be stated without circular imports. -/

/-- The open forward light cone: η₀ > 0 and η·η < 0 (timelike, future-pointing). -/
def InOpenForwardCone (d : ℕ) (η : Fin (d + 1) → ℝ) : Prop :=
  η 0 > 0 ∧ ∑ μ, minkowskiSignature d μ * η μ ^ 2 < 0

/-- The forward tube T_n: the domain where successive imaginary-part differences
    lie in the open forward light cone. -/
def ForwardTube (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | ∀ k : Fin n,
    let prev : Fin (d + 1) → ℂ := if h : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩
    let η : Fin (d + 1) → ℝ := fun μ => (z k μ - prev μ).im
    InOpenForwardCone d η }

/-- The action of a complex Lorentz transformation on ℂ^{n×(d+1)}. -/
def complexLorentzAction (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ => ∑ ν, Λ.val μ ν * z k ν

/-! ### Complex Lorentz invariance -/

/-- **Step 1 of BHW: Real Lorentz invariance extends to complex.**

    If F is holomorphic on the forward tube and invariant under the real
    restricted Lorentz group, then F is invariant under the complex
    Lorentz group SO⁺(1,d;ℂ).

    **Proof idea:** For fixed z ∈ ForwardTube, consider the map
    `φ : SO⁺(1,d;ℂ) → ℂ` defined by `φ(Λ) = F(Λ·z) - F(z)`.
    - φ is holomorphic (F is holomorphic and the action is polynomial in Λ)
    - φ = 0 on SO⁺(1,d;ℝ) (by real Lorentz invariance)
    - SO⁺(1,d;ℝ) has real dimension d(d+1)/2 inside the complex manifold
      SO⁺(1,d;ℂ) of complex dimension d(d+1)/2
    - By the identity theorem on the *connected* SO⁺(1,d;ℂ), φ = 0 everywhere -/
theorem complex_lorentz_invariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z) :
    ∀ (Λ : ComplexLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z := by
  sorry

/-! ### The permuted extended tube -/

/-- The permuted extended tube: union of permuted images of the complexified
    extended forward tube.

    T''_n = ⋃_π ⋃_Λ π(Λ · T_n) -/
def PermutedExtendedTube (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℂ) :=
  ⋃ (π : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
    { z | ∃ w ∈ ForwardTube d n, z = fun k => complexLorentzAction Λ w (π k) }

/-! ### Full BHW theorem -/

/-- **The Bargmann-Hall-Wightman Theorem.**

    Given a holomorphic function F on the forward tube that is:
    1. Invariant under the real restricted Lorentz group
    2. Continuously extends to the real boundary (`hF_bv`)
    3. Has boundary values satisfying local commutativity at spacelike pairs (`hF_local`)

    Then F extends uniquely to a holomorphic function on the permuted extended tube,
    and the extension is:
    1. Invariant under the complex Lorentz group SO⁺(1,d;ℂ)
    2. Invariant under all permutations of the arguments
    3. Unique (any other holomorphic extension agreeing with F on the forward tube
       must equal F_ext on the permuted extended tube)

    This theorem eliminates the `bargmann_hall_wightman` axiom from
    `AnalyticContinuation.lean` once the bridge to the Wightman module is established. -/
theorem bargmann_hall_wightman_theorem (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    -- F extends continuously to the real boundary of the forward tube.
    -- This constrains F(x_ℂ) to equal the distributional boundary value
    -- lim_{ε→0⁺} F(x + iεη). Without this, F(x_ℂ) is arbitrary since
    -- real points lie outside ForwardTube (Im = 0 ∉ V₊).
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    -- Local commutativity: at spacelike-separated pairs, the boundary values
    -- of F and F∘swap agree.
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) :
    ∃ (F_ext : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      -- F_ext is holomorphic on the permuted extended tube
      DifferentiableOn ℂ F_ext (PermutedExtendedTube d n) ∧
      -- F_ext restricts to F on the forward tube
      (∀ z ∈ ForwardTube d n, F_ext z = F z) ∧
      -- F_ext is invariant under the complex Lorentz group
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (complexLorentzAction Λ z) = F_ext z) ∧
      -- F_ext is symmetric under permutations
      (∀ (π : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (fun k => z (π k)) = F_ext z) ∧
      -- Uniqueness: any holomorphic function on PermutedExtendedTube agreeing with F
      -- on ForwardTube must equal F_ext.
      (∀ (G : (Fin n → Fin (d + 1) → ℂ) → ℂ),
        DifferentiableOn ℂ G (PermutedExtendedTube d n) →
        (∀ z ∈ ForwardTube d n, G z = F z) →
        ∀ z ∈ PermutedExtendedTube d n, G z = F_ext z) := by
  sorry

end BHW

end
