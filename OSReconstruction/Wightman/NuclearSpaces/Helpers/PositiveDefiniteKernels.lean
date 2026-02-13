/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef

/-!
# Positive-Definite Kernels

Infrastructure for proving that Gaussian characteristic functionals are positive-definite.

## Main Results

* `realPSDKernel_complex_form` - Real symmetric PSD kernel ⟹ complex form has im=0, re≥0
* `schur_product_psd` - Entrywise product of real PSD kernels is PSD (Schur product theorem)
* `exp_psd_kernel` - Entrywise exponential of a real PSD kernel is PSD
* `gaussian_kernel_posdef` - The Gaussian kernel exp(-½⟨xⱼ-xᵢ, A(xⱼ-xᵢ)⟩) is PSD
-/

noncomputable section

open Complex Finset
open scoped BigOperators

variable {n : ℕ}

/-! ### Real PSD Kernels -/

/-- A real-valued kernel on `Fin n` is positive semi-definite if symmetric and
    `∑ᵢⱼ aᵢ aⱼ K(i,j) ≥ 0` for all `a`. -/
def IsRealPSDKernel (K : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, K i j = K j i) ∧
  ∀ a : Fin n → ℝ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, a i * a j * K i j

/-! ### Complex Hermitian Forms from Real PSD Kernels -/

/-- For a real-valued symmetric kernel, `conj(S) = S`, so `S.im = 0`. -/
theorem realSymKernel_complex_im_zero {K : Fin n → Fin n → ℝ}
    (hK_sym : ∀ i j, K i j = K j i) (c : Fin n → ℂ) :
    (∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * ↑(K i j)).im = 0 := by
  set S := ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j * ↑(K i j)
  have hS_conj : starRingEnd ℂ S = S := by
    simp only [S, map_sum, map_mul, starRingEnd_self_apply, Complex.conj_ofReal]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun i _ => by rw [hK_sym i j]; ring))
  have : S.im = -S.im := by
    conv_lhs => rw [← hS_conj]
    simp [Complex.conj_im]
  linarith

/-- For a real PSD kernel, `re(S) ≥ 0` via decomposition `cᵢ = aᵢ + bᵢ√-1`. -/
theorem realPSDKernel_complex_re_nonneg {K : Fin n → Fin n → ℝ}
    (hK : IsRealPSDKernel K) (c : Fin n → ℂ) :
    0 ≤ (∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * ↑(K i j)).re := by
  set a := fun i => (c i).re
  set b := fun i => (c i).im
  rw [Complex.re_sum]; simp_rw [Complex.re_sum]
  have hterm : ∀ i j : Fin n,
      (starRingEnd ℂ (c i) * c j * ↑(K i j)).re =
      (a i * a j + b i * b j) * K i j := by
    intro i j
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, a, b]; ring
  simp_rw [hterm]
  have : ∑ i : Fin n, ∑ j : Fin n, (a i * a j + b i * b j) * K i j =
      (∑ i : Fin n, ∑ j : Fin n, a i * a j * K i j) +
      (∑ i : Fin n, ∑ j : Fin n, b i * b j * K i j) := by
    simp_rw [add_mul, ← Finset.sum_add_distrib]
  rw [this]; exact add_nonneg (hK.2 a) (hK.2 b)

/-- Combined: real PSD kernel gives im=0 and re≥0 for complex Hermitian form. -/
theorem realPSDKernel_complex_form {K : Fin n → Fin n → ℝ}
    (hK : IsRealPSDKernel K) (c : Fin n → ℂ) :
    let S := ∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * ↑(K i j)
    S.im = 0 ∧ 0 ≤ S.re :=
  ⟨realSymKernel_complex_im_zero hK.1 c, realPSDKernel_complex_re_nonneg hK c⟩

/-! ### Basic PSD Kernel Constructions -/

theorem ones_kernel_psd : IsRealPSDKernel (fun _ _ : Fin n => (1 : ℝ)) := by
  refine ⟨fun _ _ => rfl, fun a => ?_⟩
  have : ∑ i : Fin n, ∑ j : Fin n, a i * a j * 1 =
      (∑ i : Fin n, a i) ^ 2 := by
    simp only [mul_one]
    rw [sq, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by rw [← Finset.mul_sum])
  rw [this]; exact sq_nonneg _

theorem rank1_kernel_psd (f : Fin n → ℝ) :
    IsRealPSDKernel (fun i j => f i * f j) := by
  refine ⟨fun i j => by ring, fun a => ?_⟩
  have : ∑ i : Fin n, ∑ j : Fin n, a i * a j * (f i * f j) =
      (∑ i : Fin n, a i * f i) ^ 2 := by
    simp_rw [show ∀ i j : Fin n, a i * a j * (f i * f j) = (a i * f i) * (a j * f j)
      from fun i j => by ring, ← Finset.mul_sum, ← Finset.sum_mul, sq]
  rw [this]; exact sq_nonneg _

theorem smul_kernel_psd {K : Fin n → Fin n → ℝ} (hK : IsRealPSDKernel K)
    {c : ℝ} (hc : 0 ≤ c) :
    IsRealPSDKernel (fun i j => c * K i j) := by
  refine ⟨fun i j => by show c * K i j = c * K j i; rw [hK.1 i j], fun a => ?_⟩
  show 0 ≤ ∑ i : Fin n, ∑ j : Fin n, a i * a j * (c * K i j)
  simp_rw [show ∀ i j : Fin n, a i * a j * (c * K i j) = c * (a i * a j * K i j)
    from fun i j => by ring, ← Finset.mul_sum]
  exact mul_nonneg hc (hK.2 a)

theorem finsum_kernel_psd {m : ℕ} {K : Fin m → Fin n → Fin n → ℝ}
    (hK : ∀ l : Fin m, IsRealPSDKernel (K l)) :
    IsRealPSDKernel (fun i j => ∑ l : Fin m, K l i j) := by
  refine ⟨fun i j => by
    show ∑ l : Fin m, K l i j = ∑ l : Fin m, K l j i
    exact Finset.sum_congr rfl (fun l _ => (hK l).1 i j), fun a => ?_⟩
  show 0 ≤ ∑ i : Fin n, ∑ j : Fin n, a i * a j * (∑ l : Fin m, K l i j)
  simp_rw [Finset.mul_sum]
  have hrw : ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin m, a i * a j * K l i j =
      ∑ l : Fin m, ∑ i : Fin n, ∑ j : Fin n, a i * a j * K l i j := by
    calc ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin m, a i * a j * K l i j
        = ∑ i : Fin n, ∑ l : Fin m, ∑ j : Fin n, a i * a j * K l i j := by
          exact Finset.sum_congr rfl (fun (i : Fin n) _ =>
            Finset.sum_comm)
      _ = ∑ l : Fin m, ∑ i : Fin n, ∑ j : Fin n, a i * a j * K l i j :=
          Finset.sum_comm
  rw [hrw]; exact Finset.sum_nonneg (fun l _ => (hK l).2 a)

/-- PSD kernel × rank-1 kernel is PSD. -/
theorem schur_rank1_psd {K : Fin n → Fin n → ℝ} (hK : IsRealPSDKernel K)
    (f : Fin n → ℝ) :
    IsRealPSDKernel (fun i j => K i j * (f i * f j)) := by
  refine ⟨fun i j => by
    show K i j * (f i * f j) = K j i * (f j * f i); rw [hK.1 i j]; ring, fun a => ?_⟩
  show 0 ≤ ∑ i : Fin n, ∑ j : Fin n, a i * a j * (K i j * (f i * f j))
  have : ∑ i : Fin n, ∑ j : Fin n, a i * a j * (K i j * (f i * f j)) =
      ∑ i : Fin n, ∑ j : Fin n, (a i * f i) * (a j * f j) * K i j := by
    exact Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun j _ => by ring))
  rw [this]; exact hK.2 (fun i => a i * f i)

/-- PSD ⊙ (sum of nonneg * rank-1) is PSD. -/
theorem schur_psd_rank1_sum {K : Fin n → Fin n → ℝ} (hK : IsRealPSDKernel K)
    {m : ℕ} (f : Fin m → Fin n → ℝ) (c : Fin m → ℝ) (hc : ∀ l, 0 ≤ c l) :
    IsRealPSDKernel (fun i j => K i j * (∑ l : Fin m, c l * (f l i * f l j))) := by
  refine ⟨fun i j => by
    show K i j * ∑ l, c l * (f l i * f l j) = K j i * ∑ l, c l * (f l j * f l i)
    rw [hK.1 i j]; congr 1
    exact Finset.sum_congr rfl (fun l _ => by ring), fun a => ?_⟩
  show 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
    a i * a j * (K i j * (∑ l : Fin m, c l * (f l i * f l j)))
  have hstep1 : ∀ i j : Fin n,
      a i * a j * (K i j * (∑ l : Fin m, c l * (f l i * f l j))) =
      ∑ l : Fin m, c l * (a i * a j * (K i j * (f l i * f l j))) := by
    intro i j
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  simp_rw [hstep1]
  -- Reorder: ∑ᵢ ∑ⱼ ∑ₗ → ∑ₗ ∑ᵢ ∑ⱼ
  have hrw2 : ∑ i : Fin n, ∑ j : Fin n,
      ∑ l : Fin m, c l * (a i * a j * (K i j * (f l i * f l j))) =
      ∑ l : Fin m, ∑ i : Fin n, ∑ j : Fin n,
      c l * (a i * a j * (K i j * (f l i * f l j))) := by
    calc ∑ i : Fin n, ∑ j : Fin n,
          ∑ l : Fin m, c l * (a i * a j * (K i j * (f l i * f l j)))
        = ∑ i : Fin n, ∑ l : Fin m, ∑ j : Fin n,
          c l * (a i * a j * (K i j * (f l i * f l j))) := by
          exact Finset.sum_congr rfl (fun (i : Fin n) _ =>
            Finset.sum_comm)
      _ = ∑ l : Fin m, ∑ i : Fin n, ∑ j : Fin n,
          c l * (a i * a j * (K i j * (f l i * f l j))) := Finset.sum_comm
  rw [hrw2]
  simp_rw [← Finset.mul_sum]
  apply Finset.sum_nonneg; intro l _
  exact mul_nonneg (hc l) ((schur_rank1_psd hK (f l)).2 a)

/-! ### Inner Product Kernel -/

/-- The inner product kernel `⟨yᵢ, yⱼ⟩` is PSD. -/
theorem innerProduct_kernel_psd {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (y : Fin n → H) :
    IsRealPSDKernel (fun i j => @inner ℝ H _ (y i) (y j)) := by
  refine ⟨fun i j => real_inner_comm (y j) (y i), fun a => ?_⟩
  have : ∑ i : Fin n, ∑ j : Fin n, a i * a j * @inner ℝ H _ (y i) (y j) =
      @inner ℝ H _ (∑ i : Fin n, a i • y i) (∑ j : Fin n, a j • y j) := by
    simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    exact Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun j _ => by ring))
  rw [this]; exact real_inner_self_nonneg

/-! ### Bridge to Mathlib Matrix.PosSemidef -/

/-- An `IsRealPSDKernel` gives a `Matrix.PosSemidef` matrix. -/
theorem isRealPSDKernel_to_matrix_posSemidef {K : Fin n → Fin n → ℝ}
    (hK : IsRealPSDKernel K) :
    Matrix.PosSemidef (R := ℝ) (n := Fin n) K := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    exact hK.1 j i
  · intro x
    simp only [star_trivial]
    -- Unfold dotProduct and mulVec
    simp only [dotProduct, Matrix.mulVec]
    have : ∑ i : Fin n, x i * ∑ j : Fin n, K i j * x j =
        ∑ i : Fin n, ∑ j : Fin n, x i * x j * K i j := by
      exact Finset.sum_congr rfl (fun i _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring))
    rw [this]; exact hK.2 x

/-- Spectral representation: a real PSD kernel decomposes as
    `K(i,j) = ∑ k, eigval(k) * e(k,i) * e(k,j)` with `eigval(k) ≥ 0`. -/
theorem isRealPSDKernel_spectral_repr {K : Fin n → Fin n → ℝ}
    (hK : IsRealPSDKernel K) :
    ∃ (eigval : Fin n → ℝ) (e : Fin n → Fin n → ℝ),
      (∀ k, 0 ≤ eigval k) ∧
      (∀ i j, K i j = ∑ k : Fin n, eigval k * (e k i * e k j)) := by
  have hM_psd : Matrix.PosSemidef (R := ℝ) (n := Fin n) K :=
    isRealPSDKernel_to_matrix_posSemidef hK
  have hM_herm : Matrix.IsHermitian (α := ℝ) K := hM_psd.1
  set eigval := hM_herm.eigenvalues
  -- eigenvectorBasis gives an orthonormal basis of eigenvectors
  -- basis k : EuclideanSpace ℝ (Fin n), and (basis k) i : ℝ
  set e : Fin n → Fin n → ℝ := fun k i =>
    (hM_herm.eigenvectorBasis k : Fin n → ℝ) i
  refine ⟨eigval, e, fun k => Matrix.PosSemidef.eigenvalues_nonneg hM_psd k, ?_⟩
  intro i j
  -- From spectral theorem: K = U * diagonal(eigval) * Uᴴ
  have hspec := hM_herm.spectral_theorem (𝕜 := ℝ)
  -- Extract entry (i,j) from the matrix equation
  have h_ij := congr_fun (congr_fun hspec i) j
  -- h_ij : K i j = (conjStarAlgAut ... (diagonal ...)) i j
  -- Expand conjStarAlgAut to (U * D) * star U, then matrix multiply
  simp only [Unitary.conjStarAlgAut_apply] at h_ij
  rw [h_ij, Matrix.mul_apply]
  -- Use mul_diagonal to simplify (U * D) i k = U i k * d(k)
  -- and conjTranspose_apply + star_trivial for (star U) k j = U j k
  -- and eigenvectorUnitary_apply to connect U entries to e
  simp only [Matrix.mul_diagonal,
    Matrix.IsHermitian.eigenvectorUnitary_apply, Function.comp]
  exact Finset.sum_congr rfl (fun k _ => by
    -- star M for real matrices: (star M) k j = M j k
    have hstar : (star (↑(hM_herm.eigenvectorUnitary) : Matrix _ _ ℝ)) k j =
        (↑(hM_herm.eigenvectorUnitary) : Matrix _ _ ℝ) j k := by
      show @star ℝ _ ((↑(hM_herm.eigenvectorUnitary) : Matrix _ _ ℝ) j k) =
        (↑(hM_herm.eigenvectorUnitary) : Matrix _ _ ℝ) j k
      exact @star_trivial ℝ _ _ _
    rw [hstar, hM_herm.eigenvectorUnitary_apply j k]
    -- RCLike.ofReal for ℝ is id
    change e k i * (RCLike.ofReal (eigval k)) * e k j = eigval k * (e k i * e k j)
    simp only [RCLike.ofReal_real_eq_id, id]
    ring)

/-! ### Schur Product Theorem -/

/-- **Schur product theorem**: The entrywise product of two real PSD kernels is PSD. -/
theorem schur_product_psd {K L : Fin n → Fin n → ℝ}
    (hK : IsRealPSDKernel K) (hL : IsRealPSDKernel L) :
    IsRealPSDKernel (fun i j => K i j * L i j) := by
  obtain ⟨eigval, e, h_nonneg, hK_decomp⟩ := isRealPSDKernel_spectral_repr hK
  have hKL_eq : ∀ i j, K i j * L i j =
      L i j * (∑ k : Fin n, eigval k * (e k i * e k j)) := by
    intro i j; rw [hK_decomp i j]; ring
  constructor
  · intro i j; show K i j * L i j = K j i * L j i; rw [hK.1 i j, hL.1 i j]
  · intro a; simp_rw [hKL_eq]
    exact (schur_psd_rank1_sum hL e eigval h_nonneg).2 a

/-! ### Entrywise Powers and Exponential of PSD Kernels -/

/-- Entrywise power of a PSD kernel is PSD (by induction using Schur product). -/
theorem pow_psd_kernel {K : Fin n → Fin n → ℝ} (hK : IsRealPSDKernel K) :
    ∀ k : ℕ, IsRealPSDKernel (fun i j => K i j ^ k)
  | 0 => by simp only [pow_zero]; exact ones_kernel_psd
  | k + 1 => by
    simp only [pow_succ]
    exact schur_product_psd (pow_psd_kernel hK k) hK

/-- The entrywise exponential of a PSD kernel is PSD. -/
theorem exp_psd_kernel {K : Fin n → Fin n → ℝ} (hK : IsRealPSDKernel K) :
    IsRealPSDKernel (fun i j => Real.exp (K i j)) := by
  constructor
  · intro i j; show Real.exp (K i j) = Real.exp (K j i); rw [hK.1 i j]
  · intro a
    -- Strategy: exp(K i j) = ∑' k, K^k/k! (Taylor series)
    -- The double sum ∑_i ∑_j a_i a_j exp(K i j) is the limit of partial sums
    -- Each partial sum ≥ 0 (by pow_psd_kernel), so the limit ≥ 0

    -- Each exp(K i j) has a power series
    have hexp : ∀ i j : Fin n,
        HasSum (fun k => K i j ^ k / ↑(Nat.factorial k)) (Real.exp (K i j)) := by
      intro i j
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp (K i j)

    -- The weighted double sum of partial sums converges
    have h_lim : Filter.Tendsto
        (fun N => ∑ i : Fin n, ∑ j : Fin n, a i * a j *
          ((Finset.range N).sum fun k => K i j ^ k / ↑(Nat.factorial k)))
        Filter.atTop
        (nhds (∑ i : Fin n, ∑ j : Fin n, a i * a j * Real.exp (K i j))) := by
      apply tendsto_finset_sum _ fun i _ => ?_
      apply tendsto_finset_sum _ fun j _ => ?_
      exact Filter.Tendsto.const_mul (a i * a j)
        ((hexp i j).tendsto_sum_nat)

    -- Each partial sum is nonneg
    have h_nonneg : ∀ N, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, a i * a j *
        ((Finset.range N).sum fun k => K i j ^ k / ↑(Nat.factorial k)) := by
      intro N
      -- Distribute a_i * a_j into the k-sum
      simp_rw [Finset.mul_sum]
      -- Goal: 0 ≤ ∑_i ∑_j ∑_{k<N} a_i * a_j * (K^k / k!)
      -- Reorder sums: ∑_i ∑_j ∑_{k<N} → ∑_{k<N} ∑_i ∑_j
      have hrw_order : ∑ i : Fin n, ∑ j : Fin n,
          (Finset.range N).sum (fun k => a i * a j * (K i j ^ k / ↑(Nat.factorial k))) =
          (Finset.range N).sum fun k => ∑ i : Fin n, ∑ j : Fin n,
          a i * a j * (K i j ^ k / ↑(Nat.factorial k)) := by
        calc ∑ i : Fin n, ∑ j : Fin n,
              (Finset.range N).sum (fun k => a i * a j * (K i j ^ k / ↑(Nat.factorial k)))
            = ∑ i : Fin n, (Finset.range N).sum fun k => ∑ j : Fin n,
              a i * a j * (K i j ^ k / ↑(Nat.factorial k)) :=
              Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
          _ = (Finset.range N).sum fun k => ∑ i : Fin n, ∑ j : Fin n,
              a i * a j * (K i j ^ k / ↑(Nat.factorial k)) := Finset.sum_comm
      rw [hrw_order]
      -- Each term is nonneg: (k!)⁻¹ * K^k is PSD
      apply Finset.sum_nonneg; intro k _
      -- K^k/k! = (k!)⁻¹ * K^k, and (k!)⁻¹ * K^k is PSD by smul_kernel_psd
      have hpsd : IsRealPSDKernel (fun i j => (↑(Nat.factorial k) : ℝ)⁻¹ * K i j ^ k) :=
        smul_kernel_psd (pow_psd_kernel hK k) (by positivity)
      have hcongr : ∀ i j : Fin n,
          a i * a j * (K i j ^ k / ↑(Nat.factorial k)) =
          a i * a j * ((↑(Nat.factorial k) : ℝ)⁻¹ * K i j ^ k) := by
        intro i j; congr 1; rw [div_eq_mul_inv, mul_comm]
      simp_rw [hcongr]
      exact hpsd.2 a

    -- Conclude: limit of nonneg terms is nonneg
    exact ge_of_tendsto' h_lim h_nonneg

/-! ### The Gaussian Kernel -/

/-- The quadratic form `⟨f, Af⟩` is even: `⟨-f, A(-f)⟩ = ⟨f, Af⟩`. -/
theorem quadratic_form_even {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →L[ℝ] H) (f : H) :
    @inner ℝ H _ (-f) (A (-f)) = @inner ℝ H _ f (A f) := by
  simp [inner_neg_left, inner_neg_right, map_neg]

/-- The symmetrized bilinear form is PSD. -/
theorem symmetrized_kernel_psd {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →L[ℝ] H) (hA_pos : ∀ x, 0 ≤ @inner ℝ H _ x (A x))
    (x : Fin n → H) :
    IsRealPSDKernel (fun i j =>
      (1/2 : ℝ) * (@inner ℝ H _ (x i) (A (x j)) + @inner ℝ H _ (x j) (A (x i)))) := by
  constructor
  · intro i j; ring
  · intro a
    -- Rewrite each term: a_i * a_j * (½ * (⟨xᵢ,Axⱼ⟩ + ⟨xⱼ,Axᵢ⟩)) = ½ * (...)
    simp_rw [show ∀ i j : Fin n,
        a i * a j * ((1/2 : ℝ) * (@inner ℝ H _ (x i) (A (x j)) +
        @inner ℝ H _ (x j) (A (x i)))) =
        (1/2 : ℝ) * (a i * a j * @inner ℝ H _ (x i) (A (x j)) +
        a i * a j * @inner ℝ H _ (x j) (A (x i)))
      from fun i j => by ring, ← Finset.mul_sum,
      Finset.sum_add_distrib]
    apply mul_nonneg (by positivity)
    have hswap : ∑ i : Fin n, ∑ j : Fin n,
        a i * a j * @inner ℝ H _ (x j) (A (x i)) =
        ∑ i : Fin n, ∑ j : Fin n,
        a i * a j * @inner ℝ H _ (x i) (A (x j)) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j _ =>
        Finset.sum_congr rfl (fun i _ => by ring))
    rw [hswap, ← two_mul]; apply mul_nonneg (by positivity)
    have hinner : ∑ i : Fin n, ∑ j : Fin n,
        a i * a j * @inner ℝ H _ (x i) (A (x j)) =
        @inner ℝ H _ (∑ i : Fin n, a i • x i) (A (∑ j : Fin n, a j • x j)) := by
      rw [map_sum]; simp_rw [map_smul]
      simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
      exact Finset.sum_congr rfl (fun i _ =>
        Finset.sum_congr rfl (fun j _ => by ring))
    rw [hinner]; exact hA_pos _

/-- **Main theorem**: The Gaussian kernel `exp(-½⟨xⱼ-xᵢ, A(xⱼ-xᵢ)⟩)` is PSD. -/
theorem gaussian_kernel_posdef {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →L[ℝ] H) (hA_pos : ∀ x, 0 ≤ @inner ℝ H _ x (A x))
    (x : Fin n → H) (c : Fin n → ℂ) :
    let S := ∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j *
      ↑(Real.exp (-(1/2 : ℝ) * @inner ℝ H _ (x j - x i) (A (x j - x i))))
    S.im = 0 ∧ 0 ≤ S.re := by
  set K : Fin n → Fin n → ℝ :=
    fun i j => Real.exp (-(1/2 : ℝ) * @inner ℝ H _ (x j - x i) (A (x j - x i)))
  have hK_sym : ∀ i j, K i j = K j i := by
    intro i j
    show Real.exp (-(1/2) * @inner ℝ H _ (x j - x i) (A (x j - x i))) =
      Real.exp (-(1/2) * @inner ℝ H _ (x i - x j) (A (x i - x j)))
    congr 1; congr 1
    rw [show x i - x j = -(x j - x i) from by abel]
    exact (quadratic_form_even A (x j - x i)).symm
  have hK_psd : IsRealPSDKernel K := by
    constructor
    · exact hK_sym
    · intro a
      set Q := fun i => @inner ℝ H _ (x i) (A (x i))
      set Bs := fun i j =>
        (1/2 : ℝ) * (@inner ℝ H _ (x i) (A (x j)) + @inner ℝ H _ (x j) (A (x i)))
      have hfactor : ∀ i j : Fin n,
          K i j = Real.exp (-(1/2) * Q i) * Real.exp (-(1/2) * Q j) *
          Real.exp (Bs i j) := by
        intro i j; simp only [K, Q, Bs]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1; simp only [map_sub, inner_sub_left, inner_sub_right]; ring
      have hrw : ∀ i j,
          a i * a j * K i j =
          (a i * Real.exp (-(1/2) * Q i)) *
          (a j * Real.exp (-(1/2) * Q j)) *
          Real.exp (Bs i j) := by
        intro i j; rw [hfactor i j]; ring
      simp_rw [hrw]
      exact (exp_psd_kernel (symmetrized_kernel_psd A hA_pos x)).2
        (fun i => a i * Real.exp (-(1/2) * Q i))
  exact realPSDKernel_complex_form hK_psd c

/-! ### General Quadratic Form PSD Theorem -/

/-- The bilinear form associated to a quadratic form Q:
    `B(f,g) = (Q(f+g) - Q(f) - Q(g)) / 2`. -/
def quadraticBilinearForm {E : Type*} [AddCommGroup E] (Q : E → ℝ) (f g : E) : ℝ :=
  (Q (f + g) - Q f - Q g) / 2

/-- For a quadratic form satisfying the parallelogram law, `exp(-½ Q(fⱼ - fᵢ))` is PSD
    provided the associated bilinear form is PSD. -/
theorem quadratic_exp_kernel_posdef {E : Type*} [AddCommGroup E]
    (Q : E → ℝ)
    (hQ_par : ∀ f g : E, Q (f - g) + Q (f + g) = 2 * Q f + 2 * Q g)
    (x : Fin n → E) (c : Fin n → ℂ)
    (hB_psd : IsRealPSDKernel (fun i j => quadraticBilinearForm Q (x i) (x j))) :
    let S := ∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j *
      ↑(Real.exp (-(1/2 : ℝ) * Q (x j - x i)))
    S.im = 0 ∧ 0 ≤ S.re := by
  -- Set K(i,j) = exp(-½ Q(x_j - x_i))
  set K : Fin n → Fin n → ℝ :=
    fun i j => Real.exp (-(1/2 : ℝ) * Q (x j - x i))
  -- Symmetry: Q(f-g) = Q(g-f) from parallelogram law
  have hQ_even : ∀ f : E, Q (-f) = Q f := by
    intro f
    have h1 := hQ_par f f
    rw [sub_self] at h1
    -- h1 : Q 0 + Q (f + f) = 2 * Q f + 2 * Q f
    have h2 := hQ_par f (-f)
    rw [show f - (-f) = f + f from by abel, show f + (-f) = (0 : E) from by abel] at h2
    -- h2 : Q (f + f) + Q 0 = 2 * Q f + 2 * Q (-f)
    linarith
  have hK_sym : ∀ i j, K i j = K j i := by
    intro i j
    show Real.exp (-(1/2) * Q (x j - x i)) = Real.exp (-(1/2) * Q (x i - x j))
    congr 1; congr 1
    rw [show x i - x j = -(x j - x i) from by abel, hQ_even]
  -- The bilinear form B(f,g) = (Q(f+g) - Q(f) - Q(g))/2
  set Bs := fun i j => quadraticBilinearForm Q (x i) (x j)
  -- Key factorization: -½ Q(f-g) = -½ Q(f) + -½ Q(g) + B(f,g)
  have hfactor : ∀ i j : Fin n,
      -(1/2 : ℝ) * Q (x j - x i) =
      -(1/2) * Q (x i) + -(1/2) * Q (x j) + Bs i j := by
    intro i j
    simp only [quadraticBilinearForm, Bs]
    have hpar := hQ_par (x i) (x j)
    have h_sym : Q (x i - x j) = Q (x j - x i) := by
      rw [show x i - x j = -(x j - x i) from by abel, hQ_even]
    linarith
  have hK_psd : IsRealPSDKernel K := by
    constructor
    · exact hK_sym
    · intro a
      have hfactor' : ∀ i j : Fin n,
          K i j = Real.exp (-(1/2) * Q (x i)) * Real.exp (-(1/2) * Q (x j)) *
          Real.exp (Bs i j) := by
        intro i j; simp only [K]
        rw [← Real.exp_add, ← Real.exp_add, hfactor i j]
      have hrw : ∀ i j,
          a i * a j * K i j =
          (a i * Real.exp (-(1/2) * Q (x i))) *
          (a j * Real.exp (-(1/2) * Q (x j))) *
          Real.exp (Bs i j) := by
        intro i j; rw [hfactor' i j]; ring
      simp_rw [hrw]
      exact (exp_psd_kernel hB_psd).2
        (fun i => a i * Real.exp (-(1/2) * Q (x i)))
  exact realPSDKernel_complex_form hK_psd c

end
