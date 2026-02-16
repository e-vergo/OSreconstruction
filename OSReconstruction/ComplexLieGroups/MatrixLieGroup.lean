/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Matrix Lie Groups

This file establishes that matrix groups over ℂ carry Lie group structure.

## Main results

* `GL(n, ℂ)` is a Lie group (automatic from Mathlib's units-of-normed-algebra construction)
* `Matrix.det` is smooth (as a polynomial map on matrices)
* `SL(n, ℂ)` is path-connected (stated, proof deferred)

## References

* Hall, B.C. (2015). *Lie Groups, Lie Algebras, and Representations*. Springer, Ch. 1-2.
-/

noncomputable section

open scoped Matrix MatrixGroups Matrix.Norms.Operator Manifold
open Complex Topology

namespace MatrixLieGroup

variable (n : ℕ)

/-! ### GL(n, ℂ) as a Lie group

`GL(n, ℂ) = (Matrix (Fin n) (Fin n) ℂ)ˣ` and `Matrix (Fin n) (Fin n) ℂ`
is a complete normed ℂ-algebra (via the L∞ operator norm from `Mathlib.Analysis.Matrix.Normed`).
The Lie group structure comes from `Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra`. -/

/-- `GL(n, ℂ)` is a Lie group. This is automatic from Mathlib's construction. -/
instance instLieGroupGL :
    LieGroup 𝓘(ℂ, Matrix (Fin n) (Fin n) ℂ) ⊤ (GL (Fin n) ℂ) := inferInstance

/-! ### Smoothness of the Determinant -/

/-- The determinant is smooth on `Matrix (Fin n) (Fin n) ℂ`.
    Since det is a finite sum of finite products of coordinate projections (which
    are continuous linear maps, hence smooth), the determinant is smooth. -/
theorem contDiff_det : ContDiff ℂ ⊤ (Matrix.det : Matrix (Fin n) (Fin n) ℂ → ℂ) := by
  -- det M = ∑ σ, ε(σ) * ∏ i, M (σ i) i
  -- Rewrite det as an explicit sum-of-products
  suffices h : ContDiff ℂ ⊤ (fun M : Matrix (Fin n) (Fin n) ℂ =>
      ∑ σ : Equiv.Perm (Fin n), (↑σ.sign : ℂ) * ∏ i : Fin n, M (σ i) i) by
    have heq : (Matrix.det : Matrix (Fin n) (Fin n) ℂ → ℂ) = fun M =>
        ∑ σ : Equiv.Perm (Fin n), (↑σ.sign : ℂ) * ∏ i, M (σ i) i := by
      ext M; exact M.det_apply'
    rwa [heq]
  -- Finite sum of smooth functions is smooth
  apply ContDiff.sum; intro σ _
  -- Constant ε(σ) times smooth function is smooth
  apply contDiff_const.mul
  apply contDiff_prod; intro idx _
  -- Each entry projection M ↦ M(σ idx, idx) is a bounded linear map, hence smooth
  apply IsBoundedLinearMap.contDiff
  refine ⟨⟨fun M N => rfl, fun c M => rfl⟩, 1, one_pos, fun M => ?_⟩
  rw [one_mul]
  -- ‖M(σ idx, idx)‖ ≤ ∑_j ‖M(σ idx, j)‖ ≤ sup_i ∑_j ‖M(i,j)‖ = ‖M‖
  have h1 : ‖M (σ idx) idx‖₊ ≤ ∑ j : Fin n, ‖M (σ idx) j‖₊ :=
    Finset.single_le_sum (f := fun j => ‖M (σ idx) j‖₊)
      (fun _ _ => zero_le') (Finset.mem_univ idx)
  have h2 : (∑ j : Fin n, ‖M (σ idx) j‖₊) ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i : Fin n => ∑ j : Fin n, ‖M i j‖₊)
      (Finset.mem_univ (σ idx))
  exact_mod_cast h1.trans h2

/-! ### SL(n, ℂ) -/

/-- `SL(n, ℂ)` embeds into `GL(n, ℂ)` as a group homomorphism. -/
def SL_toGL : SL(n, ℂ) →* GL (Fin n) ℂ :=
  Matrix.SpecialLinearGroup.toGL

/-- The embedding of `SL(n, ℂ)` into `M(n, ℂ)` is injective. -/
theorem SL_val_injective : Function.Injective
    (fun A : SL(n, ℂ) => (A : Matrix (Fin n) (Fin n) ℂ)) :=
  Subtype.val_injective

/-! ### Path-connectedness -/

/-- `GL(n, ℂ)` is path-connected.

    **Proof:** Given A, B ∈ GL(n,ℂ), consider the complex affine line
    M(t) = A + t(B − A) for t ∈ ℂ. The function det(M(t)) is a polynomial
    in t of degree ≤ n. It is nonzero (det(M(0)) = det(A) ≠ 0), so it has
    finitely many roots S ⊂ ℂ. Since ℂ has real dimension 2, the complement
    ℂ \ S is path-connected. A path from 0 to 1 in ℂ \ S lifts to a path
    from A to B in GL(n,ℂ). -/
theorem GL_isPathConnected : IsPathConnected (Set.univ : Set (GL (Fin n) ℂ)) := by
  rw [← pathConnectedSpace_iff_univ]
  refine ⟨⟨1⟩, fun A B => ?_⟩
  -- The affine map: M(t) = A + t(B - A)
  set D := (B : Matrix (Fin n) (Fin n) ℂ) - (A : Matrix (Fin n) (Fin n) ℂ) with hD_def
  -- Define polynomial p with eval t p = det(M(t))
  let entry (σ : Equiv.Perm (Fin n)) (i : Fin n) : Polynomial ℂ :=
    Polynomial.C ((A : Matrix (Fin n) (Fin n) ℂ) (σ i) i) +
    Polynomial.X * Polynomial.C (D (σ i) i)
  let p : Polynomial ℂ := ∑ σ : Equiv.Perm (Fin n),
    Polynomial.C (↑(Equiv.Perm.sign σ) : ℂ) * ∏ i : Fin n, entry σ i
  -- Key evaluation identity
  have hp_eval : ∀ t : ℂ, p.eval t =
      ((A : Matrix (Fin n) (Fin n) ℂ) + t • D).det := by
    intro t
    simp only [p, entry]
    rw [Polynomial.eval_finset_sum, Matrix.det_apply']
    apply Finset.sum_congr rfl; intro σ _
    rw [Polynomial.eval_mul, Polynomial.eval_C]; congr 1
    rw [Polynomial.eval_prod]
    apply Finset.prod_congr rfl; intro i _
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_C]
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  -- p ≠ 0 since det(A) ≠ 0
  have hdetA : (A : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 :=
    (Matrix.isUnits_det_units A).ne_zero
  have hp0 : p.eval 0 = (A : Matrix (Fin n) (Fin n) ℂ).det := by
    rw [hp_eval]; simp
  have hp_ne : p ≠ 0 := fun h => hdetA (by rw [← hp0, h, Polynomial.eval_zero])
  -- Root set is finite
  set S := {t : ℂ | p.eval t = 0}
  have hS_fin : S.Finite := by
    apply Set.Finite.subset (p.roots.toFinset.finite_toSet)
    intro t ht
    simp only [S, Set.mem_setOf_eq] at ht
    simp [Multiset.mem_toFinset, Polynomial.mem_roots hp_ne, Polynomial.IsRoot, ht]
  -- ℂ \ S is path-connected (rank ℝ ℂ = 2 > 1)
  have hpc : IsPathConnected Sᶜ :=
    hS_fin.countable.isPathConnected_compl_of_one_lt_rank
      (rank_real_complex ▸ Nat.one_lt_ofNat)
  -- 0 ∈ Sᶜ and 1 ∈ Sᶜ
  have h0 : (0 : ℂ) ∈ Sᶜ := by
    simp only [S, Set.mem_compl_iff, Set.mem_setOf_eq, hp0]; exact hdetA
  have h1 : (1 : ℂ) ∈ Sᶜ := by
    simp only [S, Set.mem_compl_iff, Set.mem_setOf_eq, hp_eval]
    simp only [one_smul, hD_def, add_sub_cancel]; exact (Matrix.isUnits_det_units B).ne_zero
  -- Get path γ from 0 to 1 in ℂ \ S
  obtain ⟨γ, hγ_mem⟩ := hpc.joinedIn _ h0 _ h1
  -- For each t, det(A + γ(t) • D) ≠ 0
  have hdet_ne : ∀ t : unitInterval,
      ((A : Matrix (Fin n) (Fin n) ℂ) + (γ t) • D).det ≠ 0 := by
    intro t
    have ht := hγ_mem t
    simp only [S, Set.mem_compl_iff, Set.mem_setOf_eq] at ht
    rwa [hp_eval] at ht
  -- Construct path in GL(n,ℂ)
  let Mt : unitInterval → Matrix (Fin n) (Fin n) ℂ :=
    fun t => (A : Matrix (Fin n) (Fin n) ℂ) + (γ t) • D
  have hdet_unit : ∀ t, IsUnit (Mt t).det :=
    fun t => isUnit_iff_ne_zero.mpr (hdet_ne t)
  let lift : unitInterval → GL (Fin n) ℂ := fun t =>
    Units.mk (Mt t) ((Mt t)⁻¹)
      ((Mt t).mul_nonsing_inv (hdet_unit t))
      ((Mt t).nonsing_inv_mul (hdet_unit t))
  refine ⟨Path.mk ⟨lift, ?_⟩ ?_ ?_⟩
  · -- Continuity: need val (= Mt) and inv (= nonsing_inv ∘ Mt) continuous
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · -- val component: t ↦ A + γ(t)•D is affine in γ, hence continuous
      show Continuous Mt
      exact continuous_const.add (γ.continuous.smul continuous_const)
    · -- inv component: Matrix inverse is continuous since det is continuous and nonzero.
      -- Uses: nonsing_inv = Ring.inverse(det) • adjugate, where adjugate is polynomial
      -- in entries (hence continuous) and Ring.inverse(det) is continuous at units.
      have hMt_cont : Continuous Mt :=
        continuous_const.add (γ.continuous.smul continuous_const)
      rw [continuous_iff_continuousAt]; intro t
      have hca_det : ContinuousAt Ring.inverse ((Mt t).det) := by
        have := NormedRing.inverse_continuousAt (hdet_unit t).unit
        rwa [(hdet_unit t).unit_spec] at this
      exact (continuousAt_matrix_inv (Mt t) hca_det).comp hMt_cont.continuousAt
  · -- Source: Mt(0) = A + 0•D = A
    show lift ⟨0, unitInterval.zero_mem⟩ = A
    apply Units.ext
    simp [lift, Mt]
  · -- Target: Mt(1) = A + D = B
    show lift ⟨1, unitInterval.one_mem⟩ = B
    apply Units.ext
    simp [lift, Mt, hD_def]

/-- `SL(n, ℂ)` is path-connected.

    **Proof:** For n = 0, SL(0,ℂ) is a singleton. For n ≥ 1, given A, B ∈ SL(n,ℂ),
    use GL(n,ℂ) path-connectedness to get a path γ from A to B in GL. Then
    multiply by diag(det(γ(t))⁻¹, 1, …, 1) to correct the determinant to 1.
    The corrected path is continuous and stays in SL. -/
theorem SL_isPathConnected : IsPathConnected (Set.univ : Set (SL(n, ℂ))) := by
  cases n with
  | zero =>
    refine ⟨1, Set.mem_univ _, fun A _ => ?_⟩
    have hA : A = 1 := Subtype.ext (Matrix.ext fun i _ => Fin.elim0 i)
    subst hA; exact JoinedIn.refl (Set.mem_univ _)
  | succ m =>
    rw [← pathConnectedSpace_iff_univ]
    haveI : PathConnectedSpace (GL (Fin (m + 1)) ℂ) :=
      pathConnectedSpace_iff_univ.mpr (GL_isPathConnected (m + 1))
    refine ⟨⟨1⟩, fun A B => ?_⟩
    obtain ⟨γ⟩ := PathConnectedSpace.joined
      (Matrix.SpecialLinearGroup.toGL A) (Matrix.SpecialLinearGroup.toGL B)
    -- Matrix-valued path from toGL A to toGL B
    let valγ : unitInterval → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := fun t => ↑(γ t)
    have hvalγ_cont : Continuous valγ := Units.continuous_val.comp γ.continuous
    have hdetγ_ne : ∀ t, (valγ t).det ≠ 0 :=
      fun t => (Matrix.isUnits_det_units (γ t)).ne_zero
    have hdetinv_cont : Continuous (fun t => (valγ t).det⁻¹) :=
      ((contDiff_det (m + 1)).continuous.comp hvalγ_cont).inv₀ hdetγ_ne
    -- Corrected path: multiply by diag(det⁻¹, 1, ..., 1) to force det = 1
    let corrMat : unitInterval → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
      fun t => Matrix.diagonal (Function.update 1 0 ((valγ t).det⁻¹)) * valγ t
    -- det(diag(a, 1, ..., 1)) = a
    have hdet_diag : ∀ a : ℂ,
        (Matrix.diagonal (Function.update (1 : Fin (m + 1) → ℂ) 0 a)).det = a := by
      intro a
      rw [Matrix.det_diagonal, Fin.prod_univ_succ, Function.update_self]
      suffices ∏ i : Fin m, Function.update (1 : Fin (m + 1) → ℂ) 0 a i.succ = 1 by
        rw [this, mul_one]
      exact Finset.prod_eq_one fun i _ =>
        (Function.update_of_ne (Fin.succ_ne_zero i) a 1).trans (Pi.one_apply _)
    -- Corrected path has det = 1
    have hdet_one : ∀ t, (corrMat t).det = 1 := by
      intro t
      show (Matrix.diagonal (Function.update 1 0 ((valγ t).det⁻¹)) * valγ t).det = 1
      rw [Matrix.det_mul, hdet_diag]
      exact inv_mul_cancel₀ (hdetγ_ne t)
    -- Continuity of the diagonal correction factor
    have hdiag_cont : Continuous (fun t =>
        Matrix.diagonal (Function.update (1 : Fin (m + 1) → ℂ) 0 ((valγ t).det⁻¹))) := by
      have h_upd : Continuous (fun a : ℂ => Function.update (1 : Fin (m + 1) → ℂ) 0 a) :=
        continuous_pi fun i => by
          by_cases h : i = 0
          · subst h; simp only [Function.update_self]; exact continuous_id
          · simp only [Function.update_apply, if_neg h]; exact continuous_const
      have h_diag : Continuous (Matrix.diagonal : (Fin (m + 1) → ℂ) →
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :=
        continuous_pi fun i => continuous_pi fun j => by
          by_cases hij : i = j
          · subst hij; simp only [Matrix.diagonal_apply_eq]; exact continuous_apply i
          · simp only [Matrix.diagonal_apply_ne _ hij]; exact continuous_const
      exact h_diag.comp (h_upd.comp hdetinv_cont)
    have hcorr_cont : Continuous corrMat := hdiag_cont.mul hvalγ_cont
    -- Endpoint values
    have hval_src : valγ (0 : unitInterval) = ↑A := by
      change ↑(γ (0 : unitInterval)) = (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
      rw [γ.source]; rfl
    have hval_tgt : valγ (1 : unitInterval) = ↑B := by
      change ↑(γ (1 : unitInterval)) = (B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
      rw [γ.target]; rfl
    -- Construct SL path
    let liftSL : unitInterval → SL(m + 1, ℂ) := fun t => ⟨corrMat t, hdet_one t⟩
    refine ⟨Path.mk ⟨liftSL, Continuous.subtype_mk hcorr_cont hdet_one⟩ ?_ ?_⟩
    · -- Source: liftSL 0 = A
      apply Subtype.ext
      show corrMat 0 = ↑A
      simp only [corrMat, hval_src, A.prop, inv_one]
      ext i j; simp
    · -- Target: liftSL 1 = B
      apply Subtype.ext
      show corrMat 1 = ↑B
      simp only [corrMat, hval_tgt, B.prop, inv_one]
      ext i j; simp

end MatrixLieGroup
