/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Nuclear Operators

This file defines nuclear operators between normed spaces and develops their basic theory.

## Main Definitions

* `IsNuclearOperator` - Predicate: a bounded linear map T : E →L[𝕜] F is nuclear if
  T(x) = Σₙ fₙ(x) · yₙ where fₙ ∈ E*, yₙ ∈ F, and Σₙ ‖fₙ‖ · ‖yₙ‖ < ∞.
* `NuclearRepresentation` - A concrete nuclear representation (sequences + convergence proof).
* `nuclearNorm` - The nuclear norm: inf over representations of Σₙ ‖fₙ‖ · ‖yₙ‖.

## Mathematical Background

A bounded operator T : E → F between Banach spaces is **nuclear** (or trace class) if it
admits a representation T = Σₙ fₙ ⊗ yₙ where fₙ ∈ E* and yₙ ∈ F with Σₙ ‖fₙ‖‖yₙ‖ < ∞.

Key properties:
- Nuclear operators form a two-sided ideal in the algebra of bounded operators
- Every nuclear operator is compact
- The nuclear norm ‖T‖₁ = inf{Σ ‖fₙ‖‖yₙ‖} is a complete norm
- For Hilbert spaces, nuclear = trace class

## References

* Grothendieck, "Produits tensoriels topologiques et espaces nucléaires" (1955)
* Pietsch, "Nuclear Locally Convex Spaces" (1972)
* Reed-Simon, "Methods of Modern Mathematical Physics I", Section VI.6
* Ryan, "Introduction to Tensor Products of Banach Spaces" (2002)
-/

noncomputable section

open scoped NNReal
open Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-! ### Nuclear Representations -/

/-- A nuclear representation of a bounded linear map T : E →L[𝕜] F consists of:
    - Sequences (fₙ) in E* and (yₙ) in F
    - A proof that Σₙ ‖fₙ‖ · ‖yₙ‖ < ∞
    - A proof that T(x) = Σₙ fₙ(x) · yₙ for all x

    The representation witnesses that T is a nuclear operator. -/
structure NuclearRepresentation (T : E →L[𝕜] F) where
  /-- The sequence of continuous linear functionals fₙ ∈ E* -/
  functionals : ℕ → (E →L[𝕜] 𝕜)
  /-- The sequence of vectors yₙ ∈ F -/
  vectors : ℕ → F
  /-- Absolute convergence: Σₙ ‖fₙ‖ · ‖yₙ‖ < ∞ -/
  summable_norms : Summable (fun n => ‖functionals n‖ * ‖vectors n‖)
  /-- Representation: T(x) = Σₙ fₙ(x) · yₙ for all x ∈ E -/
  hasSum : ∀ x : E, HasSum (fun n => (functionals n x) • (vectors n)) (T x)

/-- A bounded linear map is nuclear if it admits a nuclear representation. -/
def IsNuclearOperator (T : E →L[𝕜] F) : Prop :=
  Nonempty (NuclearRepresentation T)

/-! ### Equivalence for combining representations -/

/-- Even/odd interleaving bijection ℕ ⊕ ℕ ≃ ℕ.
    Maps `inl n ↦ 2n` and `inr n ↦ 2n + 1`. -/
private def nuclearSumEquiv : ℕ ⊕ ℕ ≃ ℕ where
  toFun | .inl n => 2 * n | .inr n => 2 * n + 1
  invFun n := if n % 2 = 0 then .inl (n / 2) else .inr (n / 2)
  left_inv x := by
    cases x with
    | inl n => simp
    | inr n =>
      have h : (2 * n + 1) % 2 = 1 := by omega
      simp [h]; omega
  right_inv n := by
    by_cases h : n % 2 = 0 <;> simp [h] <;> omega

/-! ### Basic Properties -/

namespace IsNuclearOperator

/-- The zero operator is nuclear (with zero representation). -/
theorem zero : IsNuclearOperator (0 : E →L[𝕜] F) := by
  refine ⟨⟨fun _ => 0, fun _ => 0, ?_, ?_⟩⟩
  · simp only [norm_zero, mul_zero]
    exact summable_zero
  · intro x
    simp only [ContinuousLinearMap.zero_apply, zero_smul]
    exact hasSum_zero

/-- A rank-one operator f(·) · y is nuclear. -/
theorem rankOne (f : E →L[𝕜] 𝕜) (y : F) :
    IsNuclearOperator (ContinuousLinearMap.smulRight f y) := by
  refine ⟨⟨fun n => if n = 0 then f else 0,
            fun n => if n = 0 then y else 0, ?_, ?_⟩⟩
  · apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [hn]
  · intro x
    rw [ContinuousLinearMap.smulRight_apply]
    have heq : (fun n => ((if n = 0 then f else 0 : E →L[𝕜] 𝕜) x) •
        (if n = 0 then y else 0 : F)) = fun n => if n = 0 then (f x) • y else 0 := by
      funext n
      split
      · simp
      · simp
    rw [heq]
    exact hasSum_ite_eq 0 _

/-- Scalar multiple of a nuclear operator is nuclear. -/
theorem smul {T : E →L[𝕜] F} (hT : IsNuclearOperator T) (c : 𝕜) :
    IsNuclearOperator (c • T) := by
  obtain ⟨rep⟩ := hT
  refine ⟨⟨fun n => c • rep.functionals n, rep.vectors, ?_, ?_⟩⟩
  · have : (fun n => ‖c • rep.functionals n‖ * ‖rep.vectors n‖) =
        fun n => ‖c‖ * (‖rep.functionals n‖ * ‖rep.vectors n‖) := by
      ext n; rw [norm_smul]; ring
    rw [this]
    exact rep.summable_norms.const_smul ‖c‖
  · intro x
    have hrep := rep.hasSum x
    show HasSum (fun n => (c • rep.functionals n) x • rep.vectors n) ((c • T) x)
    simp only [ContinuousLinearMap.smul_apply]
    have heq : (fun n => (c • (rep.functionals n) x) • rep.vectors n) =
        fun n => c • ((rep.functionals n x) • rep.vectors n) := by
      funext n
      simp only [smul_eq_mul, mul_smul]
    rw [heq]
    exact hrep.const_smul c

/-- Sum of nuclear operators is nuclear. -/
theorem add {S T : E →L[𝕜] F} (hS : IsNuclearOperator S) (hT : IsNuclearOperator T) :
    IsNuclearOperator (S + T) := by
  obtain ⟨repS⟩ := hS
  obtain ⟨repT⟩ := hT
  -- Combine representations via the ℕ ⊕ ℕ ≃ ℕ bijection
  let e := nuclearSumEquiv
  let fn := Sum.elim repS.functionals repT.functionals ∘ e.symm
  let vec := Sum.elim repS.vectors repT.vectors ∘ e.symm
  refine ⟨⟨fn, vec, ?_, ?_⟩⟩
  · -- Summability: transfer via equiv to ℕ ⊕ ℕ, then use Summable.sum
    show Summable ((fun i => ‖Sum.elim repS.functionals repT.functionals i‖ *
      ‖Sum.elim repS.vectors repT.vectors i‖) ∘ e.symm)
    rw [e.symm.summable_iff]
    exact Summable.sum _ repS.summable_norms repT.summable_norms
  · -- HasSum: transfer via equiv to ℕ ⊕ ℕ, then use HasSum.sum
    intro x
    show HasSum ((fun i => Sum.elim repS.functionals repT.functionals i x •
      Sum.elim repS.vectors repT.vectors i) ∘ e.symm) ((S + T) x)
    rw [e.symm.hasSum_iff, ContinuousLinearMap.add_apply]
    exact HasSum.sum (repS.hasSum x) (repT.hasSum x)

/-- Nuclear operators are continuous (bounded). This is immediate since
    `NuclearRepresentation` starts from a continuous linear map. -/
theorem continuous {T : E →L[𝕜] F} (_hT : IsNuclearOperator T) : Continuous T :=
  T.continuous

/-- Composition with a bounded operator on the right preserves nuclearity:
    If T is nuclear and S is bounded, then T ∘ S is nuclear. -/
theorem comp_right {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {T : E →L[𝕜] F} (hT : IsNuclearOperator T) (S : G →L[𝕜] E) :
    IsNuclearOperator (T.comp S) := by
  obtain ⟨rep⟩ := hT
  refine ⟨⟨fun n => (rep.functionals n).comp S, rep.vectors, ?_, ?_⟩⟩
  · apply Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    · intro n
      calc ‖(rep.functionals n).comp S‖ * ‖rep.vectors n‖
          ≤ ‖rep.functionals n‖ * ‖S‖ * ‖rep.vectors n‖ := by
            apply mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
        _ = ‖S‖ * (‖rep.functionals n‖ * ‖rep.vectors n‖) := by ring
    · exact rep.summable_norms.const_smul ‖S‖
  · intro x
    simp only [ContinuousLinearMap.comp_apply]
    exact rep.hasSum (S x)

/-- Composition with a bounded operator on the left preserves nuclearity:
    If T is nuclear and S is bounded, then S ∘ T is nuclear. -/
theorem comp_left {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {T : E →L[𝕜] F} (hT : IsNuclearOperator T) (S : F →L[𝕜] G) :
    IsNuclearOperator (S.comp T) := by
  obtain ⟨rep⟩ := hT
  refine ⟨⟨rep.functionals, fun n => S (rep.vectors n), ?_, ?_⟩⟩
  · apply Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    · intro n
      calc ‖rep.functionals n‖ * ‖S (rep.vectors n)‖
          ≤ ‖rep.functionals n‖ * (‖S‖ * ‖rep.vectors n‖) := by
            apply mul_le_mul_of_nonneg_left (S.le_opNorm _) (norm_nonneg _)
        _ = ‖S‖ * (‖rep.functionals n‖ * ‖rep.vectors n‖) := by ring
    · exact rep.summable_norms.const_smul ‖S‖
  · intro x
    simp only [ContinuousLinearMap.comp_apply]
    have hrep := (rep.hasSum x).mapL S
    simp only [ContinuousLinearMap.map_smul] at hrep
    exact hrep

/-- A rank-1 continuous linear map x ↦ f(x) • y is compact. -/
private theorem smulRight_isCompactOperator (f : E →L[𝕜] 𝕜) (y : F) :
    IsCompactOperator (ContinuousLinearMap.smulRight f y) := by
  -- The compact set: image of closedBall in 𝕜 under (c ↦ c • y)
  refine ⟨(fun c : 𝕜 => c • y) '' Metric.closedBall 0 ‖f‖, ?_, ?_⟩
  · -- Image of compact under continuous is compact
    exact (isCompact_closedBall 0 ‖f‖).image (continuous_id.smul continuous_const)
  · -- Preimage contains ball 0 1
    apply Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos)
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    simp only [Set.mem_preimage, ContinuousLinearMap.smulRight_apply]
    exact Set.mem_image_of_mem _ (Metric.mem_closedBall.mpr (by
      rw [dist_zero_right]
      exact (f.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg f) hx.le)))

/-- Nuclear operators are compact.

    Proof: A nuclear operator T = Σₙ fₙ ⊗ yₙ is the norm-limit of finite-rank operators
    Tₖ = Σₙ≤ₖ fₙ ⊗ yₙ. Since finite-rank operators are compact and compact operators
    form a closed set, T is compact. -/
theorem isCompactOperator [CompleteSpace F] {T : E →L[𝕜] F} (hT : IsNuclearOperator T) :
    IsCompactOperator T := by
  obtain ⟨rep⟩ := hT
  -- Define the rank-1 operators
  let T_n : ℕ → (E →L[𝕜] F) := fun n =>
    ContinuousLinearMap.smulRight (rep.functionals n) (rep.vectors n)
  -- Step 1: Show the norm series Σ ‖T_n‖ is summable
  have hnorm_sum : Summable (fun n => ‖T_n n‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    · intro n
      exact ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (fun x => by
          rw [ContinuousLinearMap.smulRight_apply, norm_smul]
          calc ‖rep.functionals n x‖ * ‖rep.vectors n‖
              ≤ (‖rep.functionals n‖ * ‖x‖) * ‖rep.vectors n‖ :=
                mul_le_mul_of_nonneg_right ((rep.functionals n).le_opNorm x) (norm_nonneg _)
            _ = ‖rep.functionals n‖ * ‖rep.vectors n‖ * ‖x‖ := by ring)
    · exact rep.summable_norms
  have hsum : Summable T_n := hnorm_sum.of_norm
  -- Step 2: Show ∑' T_n = T
  have heq : ∑' n, T_n n = T := by
    ext x
    have h1 : HasSum (fun n => (ContinuousLinearMap.apply 𝕜 F x) (T_n n))
        ((ContinuousLinearMap.apply 𝕜 F x) (∑' n, T_n n)) :=
      hsum.hasSum.mapL (ContinuousLinearMap.apply 𝕜 F x)
    simp only [ContinuousLinearMap.apply_apply] at h1
    have h2 : HasSum (fun n => T_n n x) (T x) := rep.hasSum x
    exact h1.unique h2
  -- Step 3: Apply isCompactOperator_of_tendsto (compact ops are closed)
  rw [← heq]
  apply isCompactOperator_of_tendsto hsum.hasSum.tendsto_sum_nat
  -- Step 4: Each partial sum is compact (finite sum of rank-1 compact operators)
  filter_upwards with k
  exact (Finset.range k).sum_induction T_n (fun f : E →L[𝕜] F => IsCompactOperator f)
    (fun _ _ ha hb => ha.add hb) isCompactOperator_zero
    (fun n _ => smulRight_isCompactOperator (rep.functionals n) (rep.vectors n))

end IsNuclearOperator

/-! ### The Nuclear Norm -/

/-- The cost of a nuclear representation: Σₙ ‖fₙ‖ · ‖yₙ‖ -/
def NuclearRepresentation.cost {T : E →L[𝕜] F} (rep : NuclearRepresentation T) : ℝ :=
  ∑' n, ‖rep.functionals n‖ * ‖rep.vectors n‖

/-- The cost of a nuclear representation is non-negative. -/
theorem NuclearRepresentation.cost_nonneg {T : E →L[𝕜] F} (rep : NuclearRepresentation T) :
    rep.cost ≥ 0 := by
  apply tsum_nonneg
  intro n
  exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- The nuclear norm of T is the infimum of costs over all nuclear representations.
    ‖T‖₁ = inf { Σₙ ‖fₙ‖ · ‖yₙ‖ : T = Σₙ fₙ ⊗ yₙ } -/
def nuclearNorm (T : E →L[𝕜] F) : ℝ :=
  iInf (fun (rep : NuclearRepresentation T) => rep.cost)

/-- The nuclear norm is non-negative for nuclear operators. -/
theorem nuclearNorm_nonneg {T : E →L[𝕜] F} (hT : IsNuclearOperator T) :
    nuclearNorm T ≥ 0 := by
  have : Nonempty (NuclearRepresentation T) := hT
  exact le_ciInf (fun rep => rep.cost_nonneg)

/-- The operator norm is bounded by the nuclear norm:
    ‖T‖ ≤ ‖T‖₁ for any nuclear operator T. -/
theorem opNorm_le_nuclearNorm {T : E →L[𝕜] F} (hT : IsNuclearOperator T) :
    ‖T‖ ≤ nuclearNorm T := by
  have hne : Nonempty (NuclearRepresentation T) := hT
  -- Strategy: show ‖T‖ ≤ rep.cost for EACH representation, then take iInf
  suffices h : ∀ rep : NuclearRepresentation T, ‖T‖ ≤ rep.cost by
    exact le_ciInf h
  intro rep
  apply ContinuousLinearMap.opNorm_le_bound _ rep.cost_nonneg
  intro x
  -- ‖T x‖ ≤ rep.cost * ‖x‖ via direct norm bound
  have hhs := rep.hasSum x
  rw [hhs.tsum_eq.symm]
  -- Use tsum_of_norm_bounded: ‖Σ fₙ(x) • yₙ‖ ≤ Σ (‖fₙ‖ * ‖yₙ‖ * ‖x‖) = rep.cost * ‖x‖
  exact tsum_of_norm_bounded (rep.summable_norms.hasSum.mul_right ‖x‖) (fun n => by
    rw [norm_smul]
    calc ‖rep.functionals n x‖ * ‖rep.vectors n‖
        ≤ ‖rep.functionals n‖ * ‖x‖ * ‖rep.vectors n‖ :=
          mul_le_mul_of_nonneg_right ((rep.functionals n).le_opNorm x) (norm_nonneg _)
      _ = ‖rep.functionals n‖ * ‖rep.vectors n‖ * ‖x‖ := by ring)

/-! ### Nuclear Operators on Hilbert Spaces -/

section HilbertSpace

variable {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

/-- For Hilbert spaces, a nuclear operator T has a representation
    T = Σₙ λₙ ⟨eₙ, ·⟩ fₙ where (eₙ) and (fₙ) are orthonormal sequences
    and Σₙ |λₙ| < ∞.

    This is the singular value decomposition for trace class operators. -/
structure HilbertNuclearRepresentation (T : H₁ →L[𝕜] H₂) where
  /-- The singular values (non-negative, summable) -/
  singularValues : ℕ → ℝ
  /-- Left singular vectors (orthonormal in H₁) -/
  leftVectors : ℕ → H₁
  /-- Right singular vectors (orthonormal in H₂) -/
  rightVectors : ℕ → H₂
  /-- Left singular vectors are orthonormal -/
  leftVectors_orthonormal : Orthonormal 𝕜 leftVectors
  /-- Right singular vectors are orthonormal -/
  rightVectors_orthonormal : Orthonormal 𝕜 rightVectors
  /-- Singular values are non-negative -/
  singularValues_nonneg : ∀ n, singularValues n ≥ 0
  /-- Summability: Σₙ |λₙ| < ∞ (trace class condition) -/
  summable_singularValues : Summable singularValues
  /-- Representation: T(x) = Σₙ λₙ ⟨eₙ, x⟩ fₙ -/
  hasSum : ∀ x : H₁, HasSum
    (fun n => (singularValues n : 𝕜) • (@inner 𝕜 _ _ (leftVectors n) x • rightVectors n)) (T x)

/-- A Hilbert nuclear representation gives a nuclear representation. -/
def HilbertNuclearRepresentation.toNuclearRepresentation
    {T : H₁ →L[𝕜] H₂} (rep : HilbertNuclearRepresentation T) :
    NuclearRepresentation T where
  functionals n := (rep.singularValues n : 𝕜) • (innerSL 𝕜 (rep.leftVectors n))
  vectors n := rep.rightVectors n
  summable_norms := by
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    · intro n
      calc ‖(rep.singularValues n : 𝕜) • innerSL 𝕜 (rep.leftVectors n)‖ * ‖rep.rightVectors n‖
          ≤ (|rep.singularValues n| * ‖rep.leftVectors n‖) * ‖rep.rightVectors n‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            calc ‖(rep.singularValues n : 𝕜) • innerSL 𝕜 (rep.leftVectors n)‖
                ≤ ‖(rep.singularValues n : 𝕜)‖ * ‖innerSL 𝕜 (rep.leftVectors n)‖ := by
                  exact ContinuousLinearMap.opNorm_smul_le _ _
              _ = |rep.singularValues n| * ‖rep.leftVectors n‖ := by
                  rw [RCLike.norm_ofReal, innerSL_apply_norm]
        _ ≤ rep.singularValues n * 1 * 1 := by
            have hln : ‖rep.leftVectors n‖ = 1 := rep.leftVectors_orthonormal.1 n
            have hrn : ‖rep.rightVectors n‖ = 1 := rep.rightVectors_orthonormal.1 n
            have hsn : |rep.singularValues n| = rep.singularValues n :=
              abs_of_nonneg (rep.singularValues_nonneg n)
            rw [hln, hrn, hsn]
        _ = rep.singularValues n := by ring
    · exact rep.summable_singularValues
  hasSum x := by
    convert rep.hasSum x using 1
    ext n
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply]
    simp [smul_smul]

/-- The trace of a nuclear operator on a Hilbert space:
    tr(T) = Σₙ λₙ ⟨eₙ, fₙ⟩ where T = Σₙ λₙ ⟨eₙ, ·⟩ fₙ.

    For self-adjoint nuclear operators with H₁ = H₂, this equals Σₙ ⟨eₙ, T eₙ⟩
    for any orthonormal basis (eₙ), and is independent of the choice of basis. -/
def hilbertTrace (T : H₁ →L[𝕜] H₁) (rep : HilbertNuclearRepresentation T) : 𝕜 :=
  ∑' n, (rep.singularValues n : 𝕜) * @inner 𝕜 _ _ (rep.leftVectors n) (rep.rightVectors n)

end HilbertSpace

end
