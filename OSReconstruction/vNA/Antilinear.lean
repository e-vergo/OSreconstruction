/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Antilinear and Antiunitary Operators

This file develops the theory of antilinear (conjugate-linear) and antiunitary
operators on Hilbert spaces, which are essential for Tomita-Takesaki modular theory.

## Main definitions

* `AntilinearMap` - a conjugate-linear map J(αx + y) = conj(α)J(x) + J(y)
* `AntilinearMap.IsAntiunitary` - ⟨Jx, Jy⟩ = ⟨y, x⟩
* `AntilinearMap.IsInvolution` - J² = id
* `AntiunitaryOp` - an antiunitary involution

## Main results

* `AntilinearMap.IsAntiunitary.isIsometric` - antiunitary maps preserve norms

## References

* Takesaki, "Theory of Operator Algebras I"
-/

noncomputable section

open scoped ComplexConjugate

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An antilinear (conjugate-linear) map on a Hilbert space.
    Satisfies J(αx + y) = conj(α)·J(x) + J(y). -/
structure AntilinearMap (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  toFun : H → H
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_smul' : ∀ (c : ℂ) x, toFun (c • x) = starRingEnd ℂ c • toFun x

namespace AntilinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

instance : CoeFun (AntilinearMap H) (fun _ => H → H) := ⟨AntilinearMap.toFun⟩

theorem map_add (J : AntilinearMap H) (x y : H) : J (x + y) = J x + J y := J.map_add' x y

theorem map_smul (J : AntilinearMap H) (c : ℂ) (x : H) : J (c • x) = starRingEnd ℂ c • J x :=
  J.map_smul' c x

theorem map_zero (J : AntilinearMap H) : J 0 = 0 := by
  have h := J.map_smul' 0 0
  simp only [zero_smul, starRingEnd_apply, star_zero] at h
  exact h

/-- An antilinear map is isometric if it preserves norms -/
def IsIsometric (J : AntilinearMap H) : Prop :=
  ∀ x : H, ‖J x‖ = ‖x‖

/-- An antilinear map is antiunitary if ⟨Jx, Jy⟩ = ⟨y, x⟩ for all x, y -/
def IsAntiunitary (J : AntilinearMap H) : Prop :=
  ∀ x y : H, @inner ℂ H _ (J x) (J y) = @inner ℂ H _ y x

/-- An antilinear map is an involution if J² = id -/
def IsInvolution (J : AntilinearMap H) : Prop :=
  ∀ x : H, J (J x) = x

/-- Antiunitary maps are isometric -/
theorem IsAntiunitary.isIsometric {J : AntilinearMap H} (hJ : J.IsAntiunitary) : J.IsIsometric := by
  intro x
  have h := hJ x x
  -- ⟨Jx, Jx⟩ = ⟨x, x⟩, and ‖y‖² = ⟨y, y⟩ (as a real via inner_self_eq_norm_sq)
  have h1 : ‖J x‖^2 = (@inner ℂ H _ (J x) (J x)).re := (inner_self_eq_norm_sq (𝕜 := ℂ) (J x)).symm
  have h2 : ‖x‖^2 = (@inner ℂ H _ x x).re := (inner_self_eq_norm_sq (𝕜 := ℂ) x).symm
  have h3 : (@inner ℂ H _ (J x) (J x)).re = (@inner ℂ H _ x x).re := by rw [h]
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  linarith [h1, h2, h3]

/-- An antiunitary involution preserves orthogonality -/
theorem IsAntiunitary.orthogonal_iff {J : AntilinearMap H} (hJ : J.IsAntiunitary)
    (x y : H) : @inner ℂ H _ (J x) (J y) = 0 ↔ @inner ℂ H _ x y = 0 := by
  rw [hJ x y]
  constructor
  · intro h
    have : @inner ℂ H _ x y = starRingEnd ℂ (@inner ℂ H _ y x) := by
      rw [inner_conj_symm]
    rw [this, h]
    simp
  · intro h
    have : @inner ℂ H _ y x = starRingEnd ℂ (@inner ℂ H _ x y) := by
      rw [inner_conj_symm]
    rw [this, h]
    simp

end AntilinearMap

/-- An antiunitary operator is an antilinear isometric involution.
    This is the type of operators like the modular conjugation J in Tomita-Takesaki theory. -/
structure AntiunitaryOp (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] extends
    AntilinearMap H where
  antiunitary' : toAntilinearMap.IsAntiunitary
  involution' : toAntilinearMap.IsInvolution

namespace AntiunitaryOp

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

instance : CoeFun (AntiunitaryOp H) (fun _ => H → H) := ⟨fun J => J.toAntilinearMap.toFun⟩

theorem antiunitary (J : AntiunitaryOp H) : J.toAntilinearMap.IsAntiunitary := J.antiunitary'
theorem involution (J : AntiunitaryOp H) : J.toAntilinearMap.IsInvolution := J.involution'
theorem isIsometric (J : AntiunitaryOp H) : J.toAntilinearMap.IsIsometric := J.antiunitary.isIsometric

/-- Antiunitary operators satisfy ⟨Jx, Jy⟩ = ⟨y, x⟩ -/
theorem inner_map_map (J : AntiunitaryOp H) (x y : H) :
    @inner ℂ H _ (J x) (J y) = @inner ℂ H _ y x := J.antiunitary x y

/-- Antiunitary operators are involutions: J(Jx) = x -/
theorem apply_apply (J : AntiunitaryOp H) (x : H) : J (J x) = x := J.involution x

/-- Antiunitary operators preserve norms -/
theorem norm_map (J : AntiunitaryOp H) (x : H) : ‖J x‖ = ‖x‖ := J.isIsometric x

end AntiunitaryOp

end
