/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Matrix.Reflection

/-!
# Minkowski Space and the Minkowski Metric

This file provides a rigorous mathematical foundation for Minkowski spacetime,
using the mostly positive signature convention (-,+,+,...,+).

## Main Definitions

* `MinkowskiSpace d` - (d+1)-dimensional spacetime ℝ^{1,d} as a vector space
* `minkowskiMetric d` - The Minkowski metric η = diag(-1, +1, +1, ..., +1)
* `minkowskiInner` - The indefinite inner product η(x, y)
* `minkowskiNormSq` - The Minkowski norm squared η(x, x)

## Signature Convention

We use the **mostly positive** convention (also called the "particle physics" convention):
  η = diag(-1, +1, +1, ..., +1)

This means:
- Timelike vectors have η(x,x) < 0
- Spacelike vectors have η(x,x) > 0
- The mass-shell condition is p² = -m² (with p² = η(p,p))

The index 0 corresponds to time, indices 1,...,d correspond to spatial dimensions.

## References

* Streater-Wightman, "PCT, Spin and Statistics, and All That"
* Weinberg, "The Quantum Theory of Fields", Vol. I
* Haag, "Local Quantum Physics"
-/

noncomputable section

open BigOperators Matrix

set_option linter.unusedSectionVars false

variable (d : ℕ) [NeZero d]

/-! ### Minkowski Space as a Vector Space -/

/-- Minkowski space ℝ^{1,d} as a (d+1)-dimensional real vector space.
    The parameter d is the number of spatial dimensions. -/
abbrev MinkowskiSpace := Fin (d + 1) → ℝ

namespace MinkowskiSpace

/-! ### The Minkowski Metric -/

/-- The Minkowski metric signature: η = diag(-1, +1, +1, ..., +1)
    This is the "mostly positive" or "particle physics" convention. -/
def metricSignature : Fin (d + 1) → ℝ :=
  fun i => if i = 0 then -1 else 1

/-- The metric signature at index 0 is -1 (timelike direction) -/
@[simp]
theorem metricSignature_zero : metricSignature d 0 = -1 := by
  simp [metricSignature]

/-- The metric signature at non-zero indices is +1 (spacelike directions) -/
theorem metricSignature_succ (i : Fin d) : metricSignature d (Fin.succ i) = 1 := by
  simp [metricSignature, Fin.succ_ne_zero]

/-- The metric signature squared is always 1 -/
@[simp]
theorem metricSignature_sq (i : Fin (d + 1)) : metricSignature d i ^ 2 = 1 := by
  simp only [metricSignature]
  split_ifs <;> ring

/-- The product of metric signatures at the same index gives 1 -/
@[simp]
theorem metricSignature_mul_self (i : Fin (d + 1)) :
    metricSignature d i * metricSignature d i = 1 := by
  rw [← sq]
  exact metricSignature_sq d i

/-! ### The Minkowski Inner Product -/

/-- The Minkowski inner product (not positive definite).
    η(x, y) = -x₀y₀ + x₁y₁ + x₂y₂ + ... + x_d y_d -/
def minkowskiInner (x y : MinkowskiSpace d) : ℝ :=
  ∑ i : Fin (d + 1), metricSignature d i * x i * y i

/-- The Minkowski quadratic form (norm squared): η(x, x) -/
def minkowskiNormSq (x : MinkowskiSpace d) : ℝ :=
  minkowskiInner d x x

/-! ### Basic Properties of the Minkowski Inner Product -/

/-- The Minkowski inner product is symmetric -/
theorem minkowskiInner_comm (x y : MinkowskiSpace d) :
    minkowskiInner d x y = minkowskiInner d y x := by
  unfold minkowskiInner
  congr 1
  ext i
  ring

/-- The Minkowski inner product is bilinear: left addition -/
theorem minkowskiInner_add_left (x y z : MinkowskiSpace d) :
    minkowskiInner d (x + y) z = minkowskiInner d x z + minkowskiInner d y z := by
  unfold minkowskiInner
  simp only [Pi.add_apply, ← Finset.sum_add_distrib]
  congr 1
  ext i
  ring

/-- The Minkowski inner product is bilinear: right addition -/
theorem minkowskiInner_add_right (x y z : MinkowskiSpace d) :
    minkowskiInner d x (y + z) = minkowskiInner d x y + minkowskiInner d x z := by
  rw [minkowskiInner_comm, minkowskiInner_add_left, minkowskiInner_comm, minkowskiInner_comm d x z]

/-- The Minkowski inner product is bilinear: left scalar multiplication -/
theorem minkowskiInner_smul_left (c : ℝ) (x y : MinkowskiSpace d) :
    minkowskiInner d (c • x) y = c * minkowskiInner d x y := by
  unfold minkowskiInner
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  ext i
  ring

/-- The Minkowski inner product is bilinear: right scalar multiplication -/
theorem minkowskiInner_smul_right (c : ℝ) (x y : MinkowskiSpace d) :
    minkowskiInner d x (c • y) = c * minkowskiInner d x y := by
  rw [minkowskiInner_comm, minkowskiInner_smul_left, minkowskiInner_comm]

/-- The Minkowski inner product with zero -/
@[simp]
theorem minkowskiInner_zero_left (y : MinkowskiSpace d) :
    minkowskiInner d 0 y = 0 := by
  unfold minkowskiInner
  simp

@[simp]
theorem minkowskiInner_zero_right (x : MinkowskiSpace d) :
    minkowskiInner d x 0 = 0 := by
  rw [minkowskiInner_comm, minkowskiInner_zero_left]

/-- Negation in the Minkowski inner product -/
theorem minkowskiInner_neg_left (x y : MinkowskiSpace d) :
    minkowskiInner d (-x) y = -minkowskiInner d x y := by
  have h : -x = (-1 : ℝ) • x := by ext i; simp
  rw [h, minkowskiInner_smul_left]
  ring

theorem minkowskiInner_neg_right (x y : MinkowskiSpace d) :
    minkowskiInner d x (-y) = -minkowskiInner d x y := by
  rw [minkowskiInner_comm, minkowskiInner_neg_left, minkowskiInner_comm]

/-! ### Components -/

/-- The time component x⁰ -/
def timeComponent (x : MinkowskiSpace d) : ℝ := x 0

/-- The spatial components (x¹, x², ..., xᵈ) -/
def spatialComponents (x : MinkowskiSpace d) : Fin d → ℝ := fun i => x (Fin.succ i)

/-- Construct a spacetime vector from time and space components -/
def ofTimeSpace (t : ℝ) (x : Fin d → ℝ) : MinkowskiSpace d :=
  fun i => if h : i = 0 then t else x (i.pred h)

@[simp]
theorem timeComponent_ofTimeSpace (t : ℝ) (x : Fin d → ℝ) :
    timeComponent d (ofTimeSpace d t x) = t := by
  simp [timeComponent, ofTimeSpace]

@[simp]
theorem spatialComponents_ofTimeSpace (t : ℝ) (x : Fin d → ℝ) :
    spatialComponents d (ofTimeSpace d t x) = x := by
  ext i
  simp [spatialComponents, ofTimeSpace, Fin.succ_ne_zero]

/-- The Minkowski norm squared in terms of time and space components:
    η(x,x) = -t² + |x|² -/
theorem minkowskiNormSq_eq (x : MinkowskiSpace d) :
    minkowskiNormSq d x = -(timeComponent d x)^2 + ∑ i : Fin d, (spatialComponents d x i)^2 := by
  unfold minkowskiNormSq minkowskiInner timeComponent spatialComponents metricSignature
  -- Split the sum at index 0
  rw [Fin.sum_univ_succ]
  simp only [↓reduceIte, Fin.succ_ne_zero, one_mul, sq]
  linarith [sq_nonneg (x 0)]

/-! ### Causal Structure -/

/-- A vector is timelike if η(x,x) < 0 (with mostly positive signature) -/
def IsTimelike (x : MinkowskiSpace d) : Prop :=
  minkowskiNormSq d x < 0

/-- A vector is spacelike if η(x,x) > 0 (with mostly positive signature) -/
def IsSpacelike (x : MinkowskiSpace d) : Prop :=
  minkowskiNormSq d x > 0

/-- A vector is lightlike (null) if η(x,x) = 0 -/
def IsLightlike (x : MinkowskiSpace d) : Prop :=
  minkowskiNormSq d x = 0

/-- A vector is causal (timelike or lightlike) -/
def IsCausal (x : MinkowskiSpace d) : Prop :=
  minkowskiNormSq d x ≤ 0

/-- Two points are spacelike separated if their difference is spacelike -/
def AreSpacelikeSeparated (x y : MinkowskiSpace d) : Prop :=
  IsSpacelike d (x - y)

/-- A vector is future-directed if x⁰ > 0 -/
def IsFutureDirected (x : MinkowskiSpace d) : Prop :=
  timeComponent d x > 0

/-- A vector is past-directed if x⁰ < 0 -/
def IsPastDirected (x : MinkowskiSpace d) : Prop :=
  timeComponent d x < 0

/-- The forward light cone: causal vectors with x⁰ ≥ 0 -/
def ForwardLightCone : Set (MinkowskiSpace d) :=
  { x | IsCausal d x ∧ timeComponent d x ≥ 0 }

/-- The open forward light cone: timelike future-directed vectors -/
def OpenForwardLightCone : Set (MinkowskiSpace d) :=
  { x | IsTimelike d x ∧ IsFutureDirected d x }

/-- The closed forward light cone (same as ForwardLightCone) -/
def ClosedForwardLightCone : Set (MinkowskiSpace d) :=
  ForwardLightCone d

/-- The backward light cone: causal vectors with x⁰ ≤ 0 -/
def BackwardLightCone : Set (MinkowskiSpace d) :=
  { x | IsCausal d x ∧ timeComponent d x ≤ 0 }

/-! ### Properties of Causal Structure -/

/-- Zero is lightlike -/
theorem zero_isLightlike : IsLightlike d (0 : MinkowskiSpace d) := by
  simp [IsLightlike, minkowskiNormSq, minkowskiInner]

/-- Timelike, spacelike, and lightlike are mutually exclusive -/
theorem trichotomy (x : MinkowskiSpace d) :
    (IsTimelike d x ∧ ¬IsSpacelike d x ∧ ¬IsLightlike d x) ∨
    (IsSpacelike d x ∧ ¬IsTimelike d x ∧ ¬IsLightlike d x) ∨
    (IsLightlike d x ∧ ¬IsTimelike d x ∧ ¬IsSpacelike d x) := by
  unfold IsTimelike IsSpacelike IsLightlike
  rcases lt_trichotomy (minkowskiNormSq d x) 0 with h | h | h
  · left; exact ⟨h, not_lt.mpr (le_of_lt h), ne_of_lt h⟩
  · right; right
    refine ⟨h, ?_, ?_⟩
    · intro h'; rw [h] at h'; exact (lt_irrefl 0 h')
    · intro h'; rw [h] at h'; exact (lt_irrefl 0 h')
  · right; left; exact ⟨h, not_lt.mpr (le_of_lt h), ne_of_gt h⟩

/-- The open forward light cone is contained in the closed forward light cone -/
theorem openForwardLightCone_subset_closed :
    OpenForwardLightCone d ⊆ ClosedForwardLightCone d := by
  intro x hx
  simp only [OpenForwardLightCone, ClosedForwardLightCone, ForwardLightCone,
    Set.mem_setOf_eq] at *
  exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩

end MinkowskiSpace

/-! ### The Minkowski Metric as a Matrix -/

/-- The Minkowski metric as a diagonal matrix η = diag(-1, +1, +1, ..., +1) -/
def minkowskiMatrix : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.diagonal (MinkowskiSpace.metricSignature d)

namespace MinkowskiMatrix

/-- The Minkowski matrix is symmetric -/
theorem transpose_eq : (minkowskiMatrix d)ᵀ = minkowskiMatrix d := by
  ext i j
  simp only [minkowskiMatrix, transpose_apply, diagonal_apply]
  by_cases h : i = j <;> simp [h, eq_comm]

/-- The Minkowski matrix is its own inverse: η² = I -/
theorem mul_self : minkowskiMatrix d * minkowskiMatrix d = 1 := by
  ext i j
  simp only [minkowskiMatrix, mul_apply, diagonal_apply, one_apply]
  by_cases hij : i = j
  · subst hij
    simp [MinkowskiSpace.metricSignature_mul_self]
  · simp only [ite_mul, zero_mul]
    rw [Finset.sum_eq_zero]
    · simp [hij]
    · intro k _
      split_ifs with hik hkj
      · subst hik; exact (hij hkj).elim
      · simp
      · rfl

/-- The Minkowski matrix is invertible -/
theorem isUnit : IsUnit (minkowskiMatrix d) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp only [minkowskiMatrix, det_diagonal]
  -- The product is (-1) * 1^d = -1, which is a unit
  have h : ∏ i : Fin (d + 1), MinkowskiSpace.metricSignature d i = -1 := by
    rw [Fin.prod_univ_succ]
    simp only [MinkowskiSpace.metricSignature_zero]
    have : ∏ i : Fin d, MinkowskiSpace.metricSignature d (Fin.succ i) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      exact MinkowskiSpace.metricSignature_succ d i
    simp [this]
  rw [h]
  exact isUnit_one.neg

/-- The determinant of the Minkowski matrix -/
theorem det_eq : (minkowskiMatrix d).det = -1 := by
  simp only [minkowskiMatrix, det_diagonal]
  rw [Fin.prod_univ_succ]
  simp only [MinkowskiSpace.metricSignature_zero]
  have : ∏ i : Fin d, MinkowskiSpace.metricSignature d (Fin.succ i) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    exact MinkowskiSpace.metricSignature_succ d i
  simp [this]

/-- The Minkowski matrix is nonsingular -/
instance : Invertible (minkowskiMatrix d) := by
  refine ⟨minkowskiMatrix d, ?_, ?_⟩
  · exact mul_self d
  · exact mul_self d

/-- The inverse of the Minkowski matrix is itself -/
theorem inv_eq : (minkowskiMatrix d)⁻¹ = minkowskiMatrix d :=
  Matrix.inv_eq_right_inv (mul_self d)

end MinkowskiMatrix

/-- The Minkowski inner product using matrix multiplication -/
theorem minkowskiInner_eq_matrix (x y : MinkowskiSpace d) :
    MinkowskiSpace.minkowskiInner d x y = dotProduct x ((minkowskiMatrix d).mulVec y) := by
  unfold MinkowskiSpace.minkowskiInner minkowskiMatrix dotProduct mulVec
  simp only [diagonal_dotProduct]
  congr 1
  ext i
  ring

end

