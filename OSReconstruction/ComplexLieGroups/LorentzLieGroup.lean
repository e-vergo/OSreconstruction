/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Lorentz Group as a Topological Group

This file defines the Lorentz group independently and establishes its
topological group structure. The definitions here are self-contained —
they do not depend on the Wightman physics module.

## Main definitions

* `LorentzLieGroup.minkowskiSignature` — the metric signature (-1, +1, ..., +1)
* `LorentzLieGroup.minkowskiMatrix` — the Minkowski metric η = diag(-1, +1, ..., +1)
* `LorentzLieGroup.IsLorentzMatrix` — predicate: Λᵀ η Λ = η
* `LorentzLieGroup.LorentzGroup` — O(1,d) as a subtype of matrices
* `LorentzLieGroup.RestrictedLorentzGroup` — SO⁺(1,d) (proper orthochronous)

## Main results

* `LorentzGroup.instGroup` — group structure
* `LorentzGroup.instTopologicalSpace` — subspace topology
* `LorentzGroup.instIsTopologicalGroup` — topological group
* `RestrictedLorentzGroup.isPathConnected` — SO⁺(1,d) is path-connected (sorry)

## References

* Hall, B.C. (2015). *Lie Groups, Lie Algebras, and Representations*. Springer, Ch. 1.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Manifold
open Topology

namespace LorentzLieGroup

variable (d : ℕ)

/-! ### Minkowski metric -/

/-- The Minkowski metric signature: (-1, +1, +1, ..., +1). -/
def minkowskiSignature : Fin (d + 1) → ℝ :=
  fun i => if i = 0 then -1 else 1

/-- The Minkowski metric matrix η = diag(-1, +1, ..., +1). -/
def minkowskiMatrix : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.diagonal (minkowskiSignature d)

/-- η is symmetric: ηᵀ = η. -/
theorem minkowskiMatrix_transpose :
    (minkowskiMatrix d).transpose = minkowskiMatrix d := by
  simp [minkowskiMatrix, Matrix.diagonal_transpose]

/-- η is self-inverse: η² = 1. -/
theorem minkowskiMatrix_sq :
    minkowskiMatrix d * minkowskiMatrix d = 1 := by
  simp only [minkowskiMatrix, Matrix.diagonal_mul_diagonal, minkowskiSignature]
  ext i j
  simp [Matrix.diagonal, Matrix.one_apply]
  split_ifs <;> ring

/-! ### Lorentz group definition -/

/-- A matrix is Lorentz if it preserves the Minkowski metric: Λᵀ η Λ = η. -/
def IsLorentzMatrix (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) : Prop :=
  Λ.transpose * minkowskiMatrix d * Λ = minkowskiMatrix d

/-- The identity matrix is Lorentz. -/
theorem IsLorentzMatrix.one : IsLorentzMatrix d (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) := by
  simp [IsLorentzMatrix]

/-- The product of Lorentz matrices is Lorentz. -/
theorem IsLorentzMatrix.mul {Λ₁ Λ₂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h₁ : IsLorentzMatrix d Λ₁) (h₂ : IsLorentzMatrix d Λ₂) :
    IsLorentzMatrix d (Λ₁ * Λ₂) := by
  unfold IsLorentzMatrix at *
  -- (Λ₁Λ₂)ᵀ η (Λ₁Λ₂) = Λ₂ᵀ (Λ₁ᵀ η Λ₁) Λ₂ = Λ₂ᵀ η Λ₂ = η
  rw [Matrix.transpose_mul]
  have : Λ₂.transpose * Λ₁.transpose * minkowskiMatrix d * (Λ₁ * Λ₂)
      = Λ₂.transpose * (Λ₁.transpose * minkowskiMatrix d * Λ₁) * Λ₂ := by
    simp only [Matrix.mul_assoc]
  rw [this, h₁, h₂]

/-- The Lorentz group O(1,d) as a subtype of matrices. -/
def LorentzGroup := { Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ // IsLorentzMatrix d Λ }

instance : Coe (LorentzGroup d) (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) := ⟨Subtype.val⟩

/-- Lorentz matrices have det = ±1. -/
theorem IsLorentzMatrix.det_sq_eq_one {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h : IsLorentzMatrix d Λ) : Λ.det ^ 2 = 1 := by
  have hdet : Λ.det * (minkowskiMatrix d).det * Λ.det = (minkowskiMatrix d).det := by
    have := congr_arg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at this
    exact this
  have hη_ne : (minkowskiMatrix d).det ≠ 0 := by
    have := congr_arg Matrix.det (minkowskiMatrix_sq d)
    rw [Matrix.det_mul, Matrix.det_one] at this
    intro h0; rw [h0, mul_zero] at this; exact zero_ne_one this
  have key : Λ.det ^ 2 * (minkowskiMatrix d).det = (minkowskiMatrix d).det := by
    calc Λ.det ^ 2 * (minkowskiMatrix d).det
        = Λ.det * (minkowskiMatrix d).det * Λ.det := by ring
      _ = (minkowskiMatrix d).det := hdet
  exact mul_right_cancel₀ hη_ne (key.trans (one_mul _).symm)

/-- Lorentz matrices are invertible. -/
theorem IsLorentzMatrix.det_ne_zero {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h : IsLorentzMatrix d Λ) : Λ.det ≠ 0 := by
  intro hzero
  have := h.det_sq_eq_one
  rw [hzero, zero_pow (by norm_num : 2 ≠ 0)] at this
  exact zero_ne_one this

/-! ### Group structure -/

/-- The inverse of a Lorentz matrix via η Λᵀ η. -/
def lorentzInv (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  minkowskiMatrix d * Λ.transpose * minkowskiMatrix d

/-- η Λᵀ η is a left inverse of a Lorentz matrix Λ. -/
theorem lorentzInv_mul {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h : IsLorentzMatrix d Λ) : lorentzInv d Λ * Λ = 1 := by
  unfold lorentzInv
  calc minkowskiMatrix d * Λ.transpose * minkowskiMatrix d * Λ
      = minkowskiMatrix d * (Λ.transpose * minkowskiMatrix d * Λ) := by
        simp only [Matrix.mul_assoc]
    _ = minkowskiMatrix d * minkowskiMatrix d := by rw [h]
    _ = 1 := minkowskiMatrix_sq d

/-- η Λᵀ η is also a right inverse of a Lorentz matrix Λ. -/
theorem mul_lorentzInv {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h : IsLorentzMatrix d Λ) : Λ * lorentzInv d Λ = 1 :=
  mul_eq_one_comm.mpr (lorentzInv_mul d h)

theorem lorentzInv_isLorentz {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h : IsLorentzMatrix d Λ) : IsLorentzMatrix d (lorentzInv d Λ) := by
  have hη := minkowskiMatrix_sq d
  have hηt := minkowskiMatrix_transpose d
  -- From Λ * lorentzInv Λ = 1, derive Λ * η * Λᵀ = η
  have hΛηΛt : Λ * minkowskiMatrix d * Λ.transpose = minkowskiMatrix d := by
    have h1 : Λ * minkowskiMatrix d * Λ.transpose * minkowskiMatrix d = 1 := by
      have := mul_lorentzInv d h
      unfold lorentzInv at this
      calc Λ * minkowskiMatrix d * Λ.transpose * minkowskiMatrix d
          = Λ * (minkowskiMatrix d * Λ.transpose * minkowskiMatrix d) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := this
    calc Λ * minkowskiMatrix d * Λ.transpose
        = Λ * minkowskiMatrix d * Λ.transpose * 1 := by rw [Matrix.mul_one]
      _ = Λ * minkowskiMatrix d * Λ.transpose *
          (minkowskiMatrix d * minkowskiMatrix d) := by rw [hη]
      _ = (Λ * minkowskiMatrix d * Λ.transpose * minkowskiMatrix d) *
          minkowskiMatrix d := by simp only [Matrix.mul_assoc]
      _ = 1 * minkowskiMatrix d := by rw [h1]
      _ = minkowskiMatrix d := Matrix.one_mul _
  -- Now prove (lorentzInv Λ)ᵀ * η * (lorentzInv Λ) = η
  unfold IsLorentzMatrix lorentzInv
  -- (η * Λᵀ * η)ᵀ = η * Λ * η
  have htrans : (minkowskiMatrix d * Λ.transpose * minkowskiMatrix d).transpose =
      minkowskiMatrix d * Λ * minkowskiMatrix d := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hηt, Matrix.mul_assoc]
  rw [htrans]
  calc minkowskiMatrix d * Λ * minkowskiMatrix d * minkowskiMatrix d *
      (minkowskiMatrix d * Λ.transpose * minkowskiMatrix d)
      = minkowskiMatrix d * Λ * (minkowskiMatrix d * minkowskiMatrix d) *
        (minkowskiMatrix d * Λ.transpose * minkowskiMatrix d) := by
          simp only [Matrix.mul_assoc]
    _ = minkowskiMatrix d * Λ *
        (minkowskiMatrix d * Λ.transpose * minkowskiMatrix d) := by
          rw [hη, Matrix.mul_one]
    _ = minkowskiMatrix d * (Λ * minkowskiMatrix d * Λ.transpose) *
        minkowskiMatrix d := by simp only [Matrix.mul_assoc]
    _ = minkowskiMatrix d * minkowskiMatrix d * minkowskiMatrix d := by rw [hΛηΛt]
    _ = 1 * minkowskiMatrix d := by rw [hη]
    _ = minkowskiMatrix d := Matrix.one_mul _

instance : Group (LorentzGroup d) where
  mul Λ₁ Λ₂ := ⟨Λ₁.val * Λ₂.val, IsLorentzMatrix.mul d Λ₁.prop Λ₂.prop⟩
  one := ⟨1, IsLorentzMatrix.one d⟩
  inv Λ := ⟨lorentzInv d Λ.val, lorentzInv_isLorentz d Λ.prop⟩
  mul_assoc a b c := Subtype.ext (Matrix.mul_assoc _ _ _)
  one_mul a := Subtype.ext (Matrix.one_mul _)
  mul_one a := Subtype.ext (Matrix.mul_one _)
  inv_mul_cancel a := by
    apply Subtype.ext
    show lorentzInv d a.val * a.val = 1
    exact lorentzInv_mul d a.prop

/-! ### Proper and orthochronous conditions -/

/-- A Lorentz matrix is proper if det(Λ) = 1. -/
def IsProperLorentz (Λ : LorentzGroup d) : Prop :=
  (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).det = 1

/-- A Lorentz matrix is orthochronous if Λ₀₀ ≥ 1. -/
def IsOrthochronous (Λ : LorentzGroup d) : Prop :=
  (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) 0 0 ≥ 1

/-- The restricted Lorentz group SO⁺(1,d) = proper orthochronous. -/
def RestrictedLorentzGroup :=
  { Λ : LorentzGroup d // IsProperLorentz d Λ ∧ IsOrthochronous d Λ }

/-! ### Topology -/

instance instTopologicalSpace : TopologicalSpace (LorentzGroup d) :=
  instTopologicalSpaceSubtype

/-- The embedding into matrices is continuous. -/
theorem continuous_val :
    Continuous (Subtype.val : LorentzGroup d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :=
  continuous_subtype_val

/-- Multiplication is continuous. -/
theorem continuous_mul :
    Continuous (fun p : LorentzGroup d × LorentzGroup d => p.1 * p.2) := by
  apply continuous_induced_rng.mpr
  show Continuous (fun p : LorentzGroup d × LorentzGroup d => (p.1 * p.2).val)
  have : (fun p : LorentzGroup d × LorentzGroup d => (p.1 * p.2).val) =
      (fun p : LorentzGroup d × LorentzGroup d => p.1.val * p.2.val) := by
    ext p; rfl
  rw [this]
  exact (continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)

/-- Inversion is continuous. -/
theorem continuous_inv :
    Continuous (fun Λ : LorentzGroup d => Λ⁻¹) := by
  apply continuous_induced_rng.mpr
  show Continuous (fun Λ : LorentzGroup d => (Λ⁻¹).val)
  -- Λ⁻¹ = η Λᵀ η, which is continuous (transpose and const multiplication are continuous)
  have : (fun Λ : LorentzGroup d => (Λ⁻¹).val) =
      (fun Λ : LorentzGroup d => minkowskiMatrix d * Λ.val.transpose * minkowskiMatrix d) := by
    ext Λ; rfl
  rw [this]
  exact (continuous_const.matrix_mul
    (continuous_subtype_val.matrix_transpose)).matrix_mul continuous_const

instance instIsTopologicalGroup : IsTopologicalGroup (LorentzGroup d) where
  continuous_mul := continuous_mul d
  continuous_inv := continuous_inv d

instance RestrictedLorentzGroup.instTopologicalSpace :
    TopologicalSpace (RestrictedLorentzGroup d) :=
  instTopologicalSpaceSubtype

/-! ### Connectedness -/

/-- The Lorentz group is a closed subset of matrices. -/
theorem isClosed_lorentzGroup :
    IsClosed {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ | IsLorentzMatrix d Λ} := by
  have : {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ | IsLorentzMatrix d Λ} =
      (fun Λ => Λ.transpose * minkowskiMatrix d * Λ) ⁻¹' {minkowskiMatrix d} := by
    ext Λ; simp [IsLorentzMatrix, Set.mem_preimage]
  rw [this]
  exact IsClosed.preimage
    ((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id)
    isClosed_singleton

/-- SO⁺(1,d) is path-connected. -/
theorem RestrictedLorentzGroup.isPathConnected :
    IsPathConnected (Set.univ : Set (RestrictedLorentzGroup d)) := by
  sorry

/-! ### Embedding into GL -/

/-- Every Lorentz matrix is invertible, so we get an embedding into GL(d+1, ℝ). -/
def toGL (Λ : LorentzGroup d) : GL (Fin (d + 1)) ℝ where
  val := Λ.val
  inv := lorentzInv d Λ.val
  val_inv := mul_lorentzInv d Λ.prop
  inv_val := lorentzInv_mul d Λ.prop

end LorentzLieGroup
