/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Groups.Lorentz

/-!
# The Poincaré Group

This file defines the Poincaré group ISO(1,d) as the semidirect product of translations
and Lorentz transformations.

## Main Definitions

* `PoincareGroup d` - The Poincaré group ISO(1,d) = ℝ^{d+1} ⋊ O(1,d)
* `PoincareGroup.act` - The action on spacetime: x ↦ Λx + a
* `PoincareGroup.Restricted` - The restricted Poincaré group ISO⁺(1,d)

## Mathematical Background

The Poincaré group is the group of isometries of Minkowski spacetime. It consists of:
- Spacetime translations (ℝ^{d+1})
- Lorentz transformations (O(1,d))

The group multiplication is:
  (a₁, Λ₁) · (a₂, Λ₂) = (a₁ + Λ₁a₂, Λ₁Λ₂)

This is a semidirect product ℝ^{d+1} ⋊ O(1,d) where O(1,d) acts on ℝ^{d+1} by
matrix multiplication.

## References

* Weinberg, "The Quantum Theory of Fields", Vol. I, Chapter 2
* Streater-Wightman, "PCT, Spin and Statistics, and All That"
-/

noncomputable section

open Matrix BigOperators

set_option linter.unusedSectionVars false

variable (d : ℕ) [NeZero d]

/-! ### The Poincaré Group -/

/-- The Poincaré group ISO(1,d) as pairs (translation, Lorentz transformation).
    An element (a, Λ) acts on spacetime as x ↦ Λx + a.

    The group multiplication is defined as:
      (a₁, Λ₁) · (a₂, Λ₂) = (a₁ + Λ₁a₂, Λ₁Λ₂)

    This realizes the semidirect product structure ℝ^{d+1} ⋊ O(1,d). -/
structure PoincareGroup (d : ℕ) [NeZero d] where
  /-- The translation component a ∈ ℝ^{d+1} -/
  translation : MinkowskiSpace d
  /-- The Lorentz transformation component Λ ∈ O(1,d) -/
  lorentz : LorentzGroup d

namespace PoincareGroup

variable {d : ℕ} [NeZero d]

@[ext]
theorem ext {g₁ g₂ : PoincareGroup d}
    (h_trans : g₁.translation = g₂.translation)
    (h_lor : g₁.lorentz = g₂.lorentz) : g₁ = g₂ := by
  cases g₁; cases g₂
  simp only at h_trans h_lor
  simp [h_trans, h_lor]

/-- Multiplication in the Poincaré group: (a₁, Λ₁) · (a₂, Λ₂) = (a₁ + Λ₁a₂, Λ₁Λ₂) -/
instance : Mul (PoincareGroup d) where
  mul g₁ g₂ := {
    translation := g₁.translation + mulVec g₁.lorentz.val g₂.translation
    lorentz := g₁.lorentz * g₂.lorentz
  }

@[simp] theorem mul_translation (g₁ g₂ : PoincareGroup d) :
    (g₁ * g₂).translation = g₁.translation + mulVec g₁.lorentz.val g₂.translation := rfl

@[simp] theorem mul_lorentz (g₁ g₂ : PoincareGroup d) :
    (g₁ * g₂).lorentz = g₁.lorentz * g₂.lorentz := rfl

/-- The identity element: (0, I) -/
instance : One (PoincareGroup d) where
  one := { translation := 0, lorentz := 1 }

@[simp] theorem one_translation : (1 : PoincareGroup d).translation = 0 := rfl

@[simp] theorem one_lorentz : (1 : PoincareGroup d).lorentz = 1 := rfl

@[simp] theorem one_lorentz_val : (1 : LorentzGroup d).val = 1 := rfl

@[simp] theorem mul_lorentz_val (Λ₁ Λ₂ : LorentzGroup d) :
    (Λ₁ * Λ₂).val = Λ₁.val * Λ₂.val := rfl

/-- The inverse: (a, Λ)⁻¹ = (-Λ⁻¹a, Λ⁻¹) -/
instance : Inv (PoincareGroup d) where
  inv g := {
    translation := -mulVec g.lorentz⁻¹.val g.translation
    lorentz := g.lorentz⁻¹
  }

@[simp] theorem inv_translation (g : PoincareGroup d) :
    g⁻¹.translation = -mulVec g.lorentz⁻¹.val g.translation := rfl

@[simp] theorem inv_lorentz (g : PoincareGroup d) :
    g⁻¹.lorentz = g.lorentz⁻¹ := rfl

/-- The Poincaré group forms a group under the semidirect product multiplication.

    The group axioms follow from:
    - Associativity: (a₁ + Λ₁a₂) + Λ₁Λ₂a₃ = a₁ + Λ₁(a₂ + Λ₂a₃) using mulVec_add and mulVec_mulVec
    - Left identity: 0 + I·a = a using one_mulVec
    - Right identity: a + Λ·0 = a using mulVec_zero
    - Left inverse: -Λ⁻¹a + Λ⁻¹Λa = 0 using inv_mul_cancel for Lorentz -/
instance : Group (PoincareGroup d) where
  mul_assoc a b c := by
    apply ext
    · -- Translation: (a₁ + Λ₁a₂) + Λ₁Λ₂a₃ = a₁ + Λ₁(a₂ + Λ₂a₃)
      simp only [mul_translation, mul_lorentz, mul_lorentz_val]
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
      abel
    · exact mul_assoc _ _ _
  one_mul a := by
    apply ext
    · simp only [mul_translation, one_translation, one_lorentz, one_lorentz_val,
        Matrix.one_mulVec, zero_add]
    · exact one_mul _
  mul_one a := by
    apply ext
    · simp only [mul_translation, one_translation, Matrix.mulVec_zero, add_zero]
    · exact mul_one _
  inv_mul_cancel a := by
    apply ext
    · -- -Λ⁻¹a + Λ⁻¹a = 0 (note: the second term uses inv_lorentz to simplify)
      simp only [mul_translation, inv_translation, inv_lorentz, one_translation]
      -- Goal: -mulVec a.lorentz⁻¹.val a.translation + mulVec a.lorentz⁻¹.val a.translation = 0
      exact neg_add_cancel _
    · exact inv_mul_cancel _

/-- Action of the Poincaré group on spacetime: x ↦ Λx + a -/
def act (g : PoincareGroup d) (x : MinkowskiSpace d) : MinkowskiSpace d :=
  mulVec g.lorentz.val x + g.translation

theorem act_def (g : PoincareGroup d) (x : MinkowskiSpace d) :
    g.act x = mulVec g.lorentz.val x + g.translation := rfl

/-- The action is compatible with group multiplication -/
theorem act_mul (g₁ g₂ : PoincareGroup d) (x : MinkowskiSpace d) :
    (g₁ * g₂).act x = g₁.act (g₂.act x) := by
  simp only [act, mul_translation, mul_lorentz, mul_lorentz_val]
  -- LHS: mulVec (g₁.lorentz.val * g₂.lorentz.val) x + (g₁.translation + mulVec g₁.lorentz.val g₂.translation)
  -- RHS: mulVec g₁.lorentz.val (mulVec g₂.lorentz.val x + g₂.translation) + g₁.translation
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  -- Now both sides are equal up to associativity/commutativity of addition
  abel

/-- The identity acts trivially -/
@[simp]
theorem act_one (x : MinkowskiSpace d) : (1 : PoincareGroup d).act x = x := by
  simp only [act, one_translation, one_lorentz, one_lorentz_val, Matrix.one_mulVec, add_zero]

/-! ### Special Elements -/

/-- Pure translation: (a, 1) -/
def translation' (a : MinkowskiSpace d) : PoincareGroup d :=
  { translation := a, lorentz := 1 }

/-- Pure Lorentz transformation: (0, Λ) -/
def lorentz' (Λ : LorentzGroup d) : PoincareGroup d :=
  { translation := 0, lorentz := Λ }

@[simp]
theorem translation'_translation (a : MinkowskiSpace d) :
    (translation' a).translation = a := rfl

@[simp]
theorem translation'_lorentz (a : MinkowskiSpace d) :
    (translation' a).lorentz = 1 := rfl

@[simp]
theorem lorentz'_translation (Λ : LorentzGroup d) :
    (lorentz' Λ).translation = 0 := rfl

@[simp]
theorem lorentz'_lorentz (Λ : LorentzGroup d) :
    (lorentz' Λ).lorentz = Λ := rfl

@[simp]
theorem pureTranslation_act (a : MinkowskiSpace d) (x : MinkowskiSpace d) :
    (translation' a).act x = x + a := by
  simp only [act, translation'_translation, translation'_lorentz, one_lorentz_val,
    Matrix.one_mulVec]

@[simp]
theorem pureLorentz_act (Λ : LorentzGroup d) (x : MinkowskiSpace d) :
    (lorentz' Λ).act x = mulVec Λ.val x := by
  unfold act lorentz'
  simp only [add_zero]

/-! ### The Restricted Poincaré Group -/

/-- A Poincaré element is in the restricted group if its Lorentz part is
    proper orthochronous (det = 1, Λ₀₀ ≥ 1). -/
def IsRestricted (g : PoincareGroup d) : Prop :=
  g.lorentz.IsProper ∧ g.lorentz.IsOrthochronous

/-- The restricted Poincaré group ISO⁺(1,d): translations combined with
    restricted Lorentz transformations (proper orthochronous). -/
def Restricted : Subgroup (PoincareGroup d) where
  carrier := { g | IsRestricted g }
  mul_mem' {a b} ha hb := by
    simp only [IsRestricted, Set.mem_setOf_eq, mul_lorentz] at *
    exact ⟨LorentzGroup.IsProper.mul ha.1 hb.1, LorentzGroup.IsOrthochronous.mul ha.2 hb.2⟩
  one_mem' := by
    simp only [IsRestricted, Set.mem_setOf_eq, one_lorentz]
    exact ⟨LorentzGroup.IsProper.one, LorentzGroup.IsOrthochronous.one⟩
  inv_mem' {a} ha := by
    simp only [IsRestricted, Set.mem_setOf_eq, inv_lorentz] at *
    exact ⟨LorentzGroup.IsProper.inv ha.1, LorentzGroup.IsOrthochronous.inv ha.2⟩

end PoincareGroup

/-! ### Notation -/

/-- Standard notation for the 3+1 dimensional Poincaré group -/
abbrev Poincare4 := PoincareGroup 3

end
