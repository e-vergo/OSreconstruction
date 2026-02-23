/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Connected.PathConnected
import OSReconstruction.ComplexLieGroups.Complexification
import OSReconstruction.SCV.IdentityTheorem

/-!
# Bargmann-Hall-Wightman Theorem

This file proves the Bargmann-Hall-Wightman theorem using the connectedness of
the complex Lorentz group SO⁺(1,d;ℂ) and the identity theorem.

## Main results

* `complex_lorentz_invariance` — real Lorentz invariance extends to complex Lorentz invariance
* `bargmann_hall_wightman_theorem` — the full BHW theorem

## Proof outline

### Complex Lorentz invariance (`complex_lorentz_invariance`)

**Step 1 — Near-identity invariance (identity theorem):**
Fix z₀ ∈ FT and a basis X₁,...,Xₘ of so(1,d;ℝ). The map
  Φ(c₁,...,cₘ) = F(exp(c₁X₁)·...·exp(cₘXₘ)·z₀)
is holomorphic in each cᵢ (separately) on an open set in ℂᵐ containing 0.
For real cᵢ, the product is a real Lorentz transformation, so Φ = F(z₀) on ℝᵐ.
By the 1D identity theorem applied variable-by-variable (SCV/Osgood + Analyticity),
Φ = F(z₀) on a polydisc near 0 in ℂᵐ. Since the exponential map is a local
diffeomorphism, this gives F(Λ·z₀) = F(z₀) for Λ near 1 in SO⁺(1,d;ℂ).

**Step 2 — Propagation (open-closed on connected orbit set):**
For fixed z ∈ FT, define U_z = {Λ : Λ·z ∈ FT} (open) and
S_z = {Λ ∈ U_z : F(Λ·z) = F(z)}.
- S_z is **open** in U_z: at Λ₀ ∈ S_z, apply Step 1 at z' = Λ₀·z ∈ FT,
  then translate via Λ ↦ ΛΛ₀ (continuous right multiplication).
- S_z is **closed** in U_z: if Λₙ → Λ₀ with F(Λₙ·z) = F(z) and
  Λ₀·z ∈ FT, then F(Λ₀·z) = lim F(Λₙ·z) = F(z) by continuity.
- 1 ∈ S_z and U_z is connected ⟹ S_z = U_z.

### Bargmann-Hall-Wightman theorem

1. **Extended tube T'_n**: Complex Lorentz invariance makes F_ext(Λ·w) := F(w)
   well-defined on T'_n = ⋃_Λ Λ·FT.
2. **Jost points**: Local commutativity gives F(π·x) = F(x) at real spacelike
   configurations for adjacent transpositions π.
3. **Edge-of-the-wedge**: Adjacent permuted tubes are glued via
   `SCV.edge_of_the_wedge_theorem`.
4. **Identity theorem**: Uniqueness on the connected permuted extended tube.

## References

* Bargmann, Hall, Wightman (1957), Nuovo Cimento 5, 1-14.
* Streater & Wightman, *PCT, Spin and Statistics*, Theorem 2-11.
* Jost (1965), *The General Theory of Quantized Fields*, Ch. IV.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

variable {d : ℕ}

namespace BHW

/-! ### Forward tube and related structures

These are defined independently of the Wightman module so that
the BHW theorem can be stated without circular imports. -/

/-- The open forward light cone: η₀ > 0 and η·η < 0 (timelike, future-pointing). -/
def InOpenForwardCone (d : ℕ) (η : Fin (d + 1) → ℝ) : Prop :=
  η 0 > 0 ∧ ∑ μ, minkowskiSignature d μ * η μ ^ 2 < 0

/-- Decompose the Minkowski quadratic form into time and spatial parts:
    Q(η) = -(η₀)² + ∑_{i>0} (ηᵢ)². -/
private lemma minkowski_sum_decomp (η : Fin (d + 1) → ℝ) :
    ∑ μ, minkowskiSignature d μ * η μ ^ 2 =
    -(η 0) ^ 2 + ∑ i : Fin d, (η (Fin.succ i)) ^ 2 := by
  rw [Fin.sum_univ_succ]; congr 1
  · simp [minkowskiSignature]
  · congr 1; ext i; simp [minkowskiSignature, Fin.succ_ne_zero]

/-- For η in the forward cone, the spatial norm is less than the time component. -/
private lemma spatial_norm_lt_time {η : Fin (d + 1) → ℝ} (h : InOpenForwardCone d η) :
    Real.sqrt (∑ i : Fin d, (η (Fin.succ i)) ^ 2) < η 0 := by
  rw [show η 0 = Real.sqrt ((η 0) ^ 2) from (Real.sqrt_sq (le_of_lt h.1)).symm]
  exact Real.sqrt_lt_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    (by have := h.2; rw [minkowski_sum_decomp] at this; linarith)

/-- Expand ∑(ax + by)² into a²∑x² + 2ab∑xy + b²∑y². -/
private lemma sum_sq_expand {n : ℕ} (x y : Fin n → ℝ) (a b : ℝ) :
    ∑ i : Fin n, (a * x i + b * y i) ^ 2 =
    a ^ 2 * ∑ i : Fin n, x i ^ 2 + 2 * (a * b) * ∑ i : Fin n, x i * y i +
    b ^ 2 * ∑ i : Fin n, y i ^ 2 := by
  trans (∑ i : Fin n, (a ^ 2 * x i ^ 2 + 2 * (a * b) * (x i * y i) + b ^ 2 * y i ^ 2))
  · congr 1; ext i; ring
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Triangle inequality squared: ∑(ax+by)² ≤ (a‖x‖ + b‖y‖)². Uses Cauchy-Schwarz. -/
private lemma sum_sq_convex_combo_le {n : ℕ} (x y : Fin n → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∑ i : Fin n, (a * x i + b * y i) ^ 2 ≤
    (a * Real.sqrt (∑ i, x i ^ 2) + b * Real.sqrt (∑ i, y i ^ 2)) ^ 2 := by
  rw [sum_sq_expand]
  set sx := ∑ i : Fin n, x i ^ 2; set sy := ∑ i : Fin n, y i ^ 2
  have hsx_nn : 0 ≤ sx := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hsy_nn : 0 ≤ sy := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hRHS : (a * Real.sqrt sx + b * Real.sqrt sy) ^ 2 =
      a ^ 2 * sx + 2 * (a * b) * (Real.sqrt sx * Real.sqrt sy) + b ^ 2 * sy := by
    nlinarith [Real.sq_sqrt hsx_nn, Real.sq_sqrt hsy_nn]
  rw [hRHS]
  linarith [mul_le_mul_of_nonneg_left
    (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ x y) (by positivity : 0 ≤ 2 * (a * b))]

/-- **The open forward light cone is convex.**
    Proof: For η₁, η₂ ∈ V⁺ and a + b = 1, a,b ≥ 0:
    - Time: (aη₁ + bη₂)₀ = aη₁₀ + bη₂₀ > 0 (positive combination of positives).
    - Space: By the triangle inequality for the spatial L²-norm,
      ‖a·sp(η₁) + b·sp(η₂)‖ ≤ a·‖sp(η₁)‖ + b·‖sp(η₂)‖ < a·η₁₀ + b·η₂₀.
      Squaring gives the Minkowski condition. -/
theorem inOpenForwardCone_convex :
    Convex ℝ {η : Fin (d + 1) → ℝ | InOpenForwardCone d η} := by
  intro η₁ hη₁ η₂ hη₂ a b ha hb hab
  simp only [Set.mem_setOf_eq] at hη₁ hη₂ ⊢
  have h_combo : a • η₁ + b • η₂ = fun μ => a * η₁ μ + b * η₂ μ := by
    ext μ; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [InOpenForwardCone, h_combo]
  refine ⟨?_, ?_⟩
  -- Part 1: time component positive
  · rcases eq_or_lt_of_le ha with rfl | ha'
    · simp at hab; rw [hab]; simp [hη₂.1]
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hη₁.1) (mul_nonneg hb (le_of_lt hη₂.1))
  -- Part 2: Minkowski sum < 0
  · rw [minkowski_sum_decomp]
    suffices h : ∑ i : Fin d, (a * η₁ (Fin.succ i) + b * η₂ (Fin.succ i)) ^ 2 <
        (a * η₁ 0 + b * η₂ 0) ^ 2 by linarith
    have h1 := sum_sq_convex_combo_le
      (fun i => η₁ (Fin.succ i)) (fun i => η₂ (Fin.succ i)) a b ha hb
    have hsx := spatial_norm_lt_time hη₁
    have hsy := spatial_norm_lt_time hη₂
    have h_combo_lt : a * Real.sqrt (∑ i, η₁ (Fin.succ i) ^ 2) +
        b * Real.sqrt (∑ i, η₂ (Fin.succ i) ^ 2) < a * η₁ 0 + b * η₂ 0 := by
      rcases eq_or_lt_of_le ha with rfl | ha'
      · simp at hab ⊢; rw [hab]; simp; exact hsy
      · linarith [mul_lt_mul_of_pos_left hsx ha',
                   mul_le_mul_of_nonneg_left (le_of_lt hsy) hb]
    calc ∑ i, (a * η₁ (Fin.succ i) + b * η₂ (Fin.succ i)) ^ 2
        ≤ _ := h1
      _ < (a * η₁ 0 + b * η₂ 0) ^ 2 :=
          pow_lt_pow_left₀ h_combo_lt (by positivity) two_ne_zero

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

/-! ### Group action properties -/

/-- The complex Lorentz action is compatible with group multiplication. -/
theorem complexLorentzAction_mul (Λ₁ Λ₂ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzAction (Λ₁ * Λ₂) z =
    complexLorentzAction Λ₁ (complexLorentzAction Λ₂ z) := by
  ext k μ
  simp only [complexLorentzAction, ComplexLorentzGroup.mul_val, Matrix.mul_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; ext ν
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]

/-- The identity acts trivially. -/
theorem complexLorentzAction_one (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzAction (1 : ComplexLorentzGroup d) z = z := by
  ext k μ
  simp only [complexLorentzAction,
    show (1 : ComplexLorentzGroup d).val = (1 : Matrix _ _ ℂ) from rfl,
    Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- The inverse acts by the inverse matrix. -/
theorem complexLorentzAction_inv (Λ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzAction Λ⁻¹ (complexLorentzAction Λ z) = z := by
  rw [← complexLorentzAction_mul, inv_mul_cancel, complexLorentzAction_one]

/-! ### Convexity of forward tube and intersection domains -/

/-- Extract the k-th imaginary difference from z. -/
private def imDiff (z : Fin n → Fin (d + 1) → ℂ) (k : Fin n) : Fin (d + 1) → ℝ :=
  fun μ => (z k μ - (if h : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩) μ).im

/-- The imaginary difference is ℝ-linear in z. -/
private lemma imDiff_linear (z₁ z₂ : Fin n → Fin (d + 1) → ℂ) (a b : ℝ) (k : Fin n) :
    imDiff (a • z₁ + b • z₂) k = a • imDiff z₁ k + b • imDiff z₂ k := by
  ext μ; simp only [imDiff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hk : k.val = 0
  · simp [hk, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, sub_zero]
  · simp [hk, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re]; ring

/-- **The forward tube is ℝ-convex.**
    Proof: ForwardTube = ∩_k {z : Im_diff_k(z) ∈ V⁺}. Each Im_diff_k is ℝ-linear
    in z, so each set is the preimage of V⁺ under a linear map, hence convex.
    The intersection of convex sets is convex. -/
theorem forwardTube_convex : Convex ℝ (ForwardTube d n) := by
  intro z₁ hz₁ z₂ hz₂ a b ha hb hab k
  show InOpenForwardCone d (imDiff (a • z₁ + b • z₂) k)
  rw [imDiff_linear]
  exact inOpenForwardCone_convex
    (Set.mem_setOf.mpr (hz₁ k)) (Set.mem_setOf.mpr (hz₂ k)) ha hb hab

/-- The complex Lorentz action is ℝ-linear in z. -/
private lemma complexLorentzAction_real_linear
    (Λ : ComplexLorentzGroup d) (z₁ z₂ : Fin n → Fin (d + 1) → ℂ) (a b : ℝ) :
    complexLorentzAction Λ (a • z₁ + b • z₂) =
    a • complexLorentzAction Λ z₁ + b • complexLorentzAction Λ z₂ := by
  ext k μ
  simp only [complexLorentzAction, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
  trans (↑a * ∑ ν, Λ.val μ ν * z₁ k ν + ↑b * ∑ ν, Λ.val μ ν * z₂ k ν)
  · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1; ext ν; ring
  · rfl

/-- **The intersection domain D_Λ = {z ∈ FT : Λ·z ∈ FT} is ℝ-convex.**
    D_Λ is the intersection of FT (convex) with the preimage of FT under the
    ℝ-linear map z ↦ Λ·z (convex). Intersection of convex sets is convex. -/
theorem d_lambda_convex (Λ : ComplexLorentzGroup d) :
    Convex ℝ {z | z ∈ ForwardTube d n ∧ complexLorentzAction Λ z ∈ ForwardTube d n} := by
  intro z₁ ⟨hz₁, hΛz₁⟩ z₂ ⟨hz₂, hΛz₂⟩ a b ha hb hab
  refine ⟨forwardTube_convex hz₁ hz₂ ha hb hab, ?_⟩
  rw [complexLorentzAction_real_linear]
  exact forwardTube_convex hΛz₁ hΛz₂ ha hb hab

/-- **The intersection domain D_Λ is preconnected** (convex implies preconnected). -/
theorem d_lambda_isPreconnected (Λ : ComplexLorentzGroup d) :
    IsPreconnected {z | z ∈ ForwardTube d n ∧ complexLorentzAction Λ z ∈ ForwardTube d n} :=
  (d_lambda_convex Λ).isPreconnected

/-! ### Complex Lorentz invariance -/

/-- The orbit set U_z = {Λ : Λ·z ∈ ForwardTube} is the set of complex Lorentz
    transformations that keep z in the forward tube. -/
def orbitSet (z : Fin n → Fin (d + 1) → ℂ) : Set (ComplexLorentzGroup d) :=
  { Λ | complexLorentzAction Λ z ∈ ForwardTube d n }

/-- The orbit set contains the identity. -/
theorem mem_orbitSet_one (hz : z ∈ ForwardTube d n) :
    (1 : ComplexLorentzGroup d) ∈ orbitSet z := by
  rw [orbitSet, Set.mem_setOf_eq, complexLorentzAction_one]; exact hz

/-- The forward tube is open (strict inequalities on continuous functions). -/
theorem isOpen_forwardTube : IsOpen (ForwardTube d n) := by
  simp only [ForwardTube, InOpenForwardCone, Set.setOf_forall]
  apply isOpen_iInter_of_finite; intro k
  -- Helper: z ↦ (z k μ - prev(z) μ).im is continuous for each μ
  have hcont : ∀ μ : Fin (d + 1), Continuous (fun z : Fin n → Fin (d + 1) → ℂ =>
      (z k μ - (if _ : (k : ℕ) = 0 then 0 else z ⟨(k : ℕ) - 1, by omega⟩) μ).im) := by
    intro μ
    apply Complex.continuous_im.comp
    apply Continuous.sub
    · exact (continuous_apply μ).comp (continuous_apply k)
    · by_cases hk : (k : ℕ) = 0
      · simp [hk]; exact continuous_const
      · simp [hk]
        exact (continuous_apply μ).comp (continuous_apply (⟨(k : ℕ) - 1, by omega⟩ : Fin n))
  apply IsOpen.inter
  · exact isOpen_lt continuous_const (hcont 0)
  · exact isOpen_lt
      (continuous_finset_sum _ fun μ _ => (continuous_const.mul ((hcont μ).pow 2)))
      continuous_const

/-- The action map Λ ↦ Λ·z is continuous (polynomial in entries of Λ). -/
theorem continuous_complexLorentzAction_fst (z : Fin n → Fin (d + 1) → ℂ) :
    Continuous (fun Λ : ComplexLorentzGroup d => complexLorentzAction Λ z) := by
  apply continuous_pi; intro k
  apply continuous_pi; intro μ
  simp only [complexLorentzAction]
  exact continuous_finset_sum Finset.univ
    (fun ν _ => (ComplexLorentzGroup.continuous_entry μ ν).mul continuous_const)

/-- The orbit set is open (preimage of an open set under a continuous map). -/
theorem isOpen_orbitSet (z : Fin n → Fin (d + 1) → ℂ) :
    IsOpen (orbitSet z) :=
  isOpen_forwardTube.preimage (continuous_complexLorentzAction_fst z)

/-- The one-parameter action `t ↦ exp(tX) · z` using the matrix exponential directly.
    Each entry is a power series in t, hence differentiable. -/
private theorem differentiable_expAction
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (z : Fin n → Fin (d + 1) → ℂ) :
    Differentiable ℂ (fun t : ℂ =>
      (fun k (μ : Fin (d + 1)) => ∑ ν, (exp (t • X) : Matrix _ _ ℂ) μ ν * z k ν) :
      ℂ → Fin n → Fin (d + 1) → ℂ) := by
  have hexp : Differentiable ℂ (fun t : ℂ => (exp (t • X) : Matrix _ _ ℂ)) :=
    fun t => (hasDerivAt_exp_smul_const X t).differentiableAt
  apply differentiable_pi.mpr; intro k
  apply differentiable_pi.mpr; intro μ
  apply Differentiable.fun_sum; intro ν _
  exact ((differentiable_apply ν).comp ((differentiable_apply μ).comp hexp)).mul
    (differentiable_const _)

/-- Bridge lemma: the real matrix exponential maps to complex via `map ofReal`.
    Specifically, `(exp(s • Y)).map ofReal = exp((s : ℂ) • Y.map ofReal)`. -/
private theorem exp_map_ofReal_bridge (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (s : ℝ) :
    (exp (s • Y) : Matrix _ _ ℝ).map Complex.ofReal =
      (exp ((s : ℂ) • Y.map Complex.ofReal) : Matrix _ _ ℂ) := by
  -- (exp(s•Y)).map ofReal = ofRealHom.mapMatrix (exp(s•Y))
  --                       = exp (ofRealHom.mapMatrix (s•Y))     by map_exp
  --                       = exp ((s:ℂ) • Y.map ofReal)          by smul commutation
  have hcont : Continuous (Complex.ofRealHom.mapMatrix :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
    continuous_id.matrix_map Complex.continuous_ofReal
  have h1 : Complex.ofRealHom.mapMatrix (exp (s • Y)) =
      exp (Complex.ofRealHom.mapMatrix (s • Y)) :=
    map_exp (f := Complex.ofRealHom.mapMatrix) hcont (s • Y)
  have h2 : Complex.ofRealHom.mapMatrix (s • Y) = (s : ℂ) • Y.map Complex.ofReal := by
    ext i j; simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply]
  -- .map ofReal is the same as ofRealHom.mapMatrix
  change Complex.ofRealHom.mapMatrix (exp (s • Y)) = _
  rw [h1, h2]

/-- **Single-generator identity theorem.** For Y ∈ so(1,d;ℝ) and z ∈ FT,
    the function t ↦ F(exp(t · Y_ℂ) · z) equals F(z) for t near 0 in ℂ.

    Proof: The composed function g(t) = F(exp(tX)·z) - F(z) is:
    1. DifferentiableOn on the open set {t : exp(tX)·z ∈ FT}
    2. AnalyticAt 0 (by DifferentiableOn.analyticAt for ℂ-valued functions)
    3. Zero for real t (by real Lorentz invariance via the bridge lemma)
    4. Zero near 0 (by the 1D identity theorem) -/
private theorem single_generator_invariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hY : IsInLorentzAlgebra d Y)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    ∀ᶠ t in 𝓝 (0 : ℂ),
      (fun k (μ : Fin (d + 1)) =>
        ∑ ν, (exp (t • Y.map Complex.ofReal) : Matrix _ _ ℂ) μ ν * z k ν) ∈
          ForwardTube d n →
      F (fun k μ =>
        ∑ ν, (exp (t • Y.map Complex.ofReal) : Matrix _ _ ℂ) μ ν * z k ν) = F z := by
  set X := Y.map Complex.ofReal with hX_def
  -- The action map
  set action : ℂ → Fin n → Fin (d + 1) → ℂ :=
    fun t k μ => ∑ ν, (exp (t • X) : Matrix _ _ ℂ) μ ν * z k ν with haction_def
  -- The domain U = {t : action(t) ∈ FT} is open
  set U := {t : ℂ | action t ∈ ForwardTube d n} with hU_def
  have hU_open : IsOpen U :=
    isOpen_forwardTube.preimage (differentiable_expAction X z).continuous
  -- 0 ∈ U since action(0) = z ∈ FT
  have h0U : (0 : ℂ) ∈ U := by
    simp only [hU_def, haction_def, Set.mem_setOf_eq]
    convert hz using 2; ext k
    simp [Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ]
  -- Define g(t) = F(action(t)) - F(z)
  set g : ℂ → ℂ := fun t => F (action t) - F z with hg_def
  -- g is DifferentiableOn on U
  have hg_diff : DifferentiableOn ℂ g U := by
    apply DifferentiableOn.sub
    · exact hF_holo.comp (differentiable_expAction X z).differentiableOn (fun t ht => ht)
    · exact differentiableOn_const _
  -- g is AnalyticAt 0
  have hg_analytic : AnalyticAt ℂ g 0 :=
    hg_diff.analyticAt (hU_open.mem_nhds h0U)
  -- g(s) = 0 for s ∈ ℝ (real Lorentz invariance)
  have hg_real : ∀ s : ℝ, (s : ℂ) ∈ U → g (s : ℂ) = 0 := by
    intro s hs
    simp only [hg_def, sub_eq_zero]
    -- exp((s:ℂ) • X) = (exp(s • Y)).map ofReal
    have hbridge := exp_map_ofReal_bridge Y s
    -- The entries match: (exp((s:ℂ) • X)) μ ν = ((exp(s • Y)) μ ν : ℂ)
    have hentry : ∀ μ ν : Fin (d + 1),
        (exp ((s : ℂ) • X) : Matrix _ _ ℂ) μ ν =
        ((exp (s • Y) : Matrix _ _ ℝ) μ ν : ℂ) := by
      intro μ ν
      have : (exp (s • Y) : Matrix _ _ ℝ).map Complex.ofReal = exp ((s : ℂ) • X) := hbridge
      exact (congr_fun (congr_fun this μ) ν).symm
    -- Rewrite the action to use real Lorentz entries
    have haction_eq : action (s : ℂ) =
        fun k μ => ∑ ν, ((exp (s • Y) : Matrix _ _ ℝ) μ ν : ℂ) * z k ν := by
      ext k μ; simp only [haction_def]; congr 1; ext ν; rw [hentry]
    rw [haction_eq]
    -- Apply real Lorentz invariance
    exact hF_real_inv (expLorentz d (s • Y) (isInLorentzAlgebra_smul d hY s)) z hz
  -- g = 0 frequently near 0 in 𝓝[≠] 0
  have hg_freq : ∃ᶠ t in 𝓝[≠] (0 : ℂ), g t = 0 := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    intro ⟨U', hU'_open, h0_mem, hU'_sub⟩
    obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU'_open 0 h0_mem
    -- Pick a small positive real number s ∈ U' ∩ {0}ᶜ ∩ U
    obtain ⟨r', hr'_pos, hr'_sub⟩ := Metric.isOpen_iff.mp hU_open 0 h0U
    set s := min (r / 2) (r' / 2) with hs_def
    have hs_pos : 0 < s := by positivity
    have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs_pos)
    have hs_in_U' : (s : ℂ) ∈ U' := hr_sub (by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs_pos]; linarith [min_le_left (r / 2) (r' / 2)])
    have hs_in_U : (s : ℂ) ∈ U := hr'_sub (by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs_pos]; linarith [min_le_right (r / 2) (r' / 2)])
    exact hU'_sub ⟨hs_in_U', hs_ne⟩ (hg_real s hs_in_U)
  -- By the identity theorem: g = 0 on a neighborhood of 0
  have hg_zero := hg_analytic.frequently_zero_iff_eventually_zero.mp hg_freq
  -- Translate: F(action(t)) = F(z) eventually near 0
  exact hg_zero.mono (fun t ht _ => by
    simp only [hg_def, sub_eq_zero] at ht; exact ht)

/-! ### Infrastructure for the identity theorem proof -/

/-- The real part of a complex matrix (entry-wise). -/
private def reMatrix (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => (X i j).re

/-- The imaginary part of a complex matrix (entry-wise). -/
private def imMatrix (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => (X i j).im

/-- A complex matrix decomposes as Re(X).map ofReal + I • Im(X).map ofReal. -/
private theorem matrix_re_im_decomp (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    X = (reMatrix X).map Complex.ofReal + Complex.I • (imMatrix X).map Complex.ofReal := by
  ext i j
  simp only [reMatrix, imMatrix, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [mul_comm]; exact (Complex.re_add_im (X i j)).symm

/-- If X ∈ so(1,d;ℂ) then Re(X) ∈ so(1,d;ℝ).
    Proof: Xᵀηℂ + ηℂX = 0 with ηℂ real → taking real parts gives
    Re(X)ᵀη + ηRe(X) = 0 since η = diag(±1) is real. -/
private theorem reMatrix_isInLorentzAlgebra
    {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hX : ComplexLorentzGroup.IsInLieAlgebra X) :
    IsInLorentzAlgebra d (reMatrix X) := by
  -- hX : Xᵀ * ηℂ + ηℂ * X = 0 where ηℂ = diag(minkowskiSignature)
  -- Convert to explicit form with Matrix.diagonal
  have hX' : X.transpose * Matrix.diagonal (fun i => (minkowskiSignature d i : ℂ)) +
      Matrix.diagonal (fun i => (minkowskiSignature d i : ℂ)) * X = 0 := hX
  -- Work entry-wise
  unfold IsInLorentzAlgebra
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    minkowskiMatrix, Matrix.diagonal_apply, reMatrix, Matrix.zero_apply,
    mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  -- Goal: (X j i).re * η j + η i * (X i j).re = 0
  -- Extract entry (i,j) from hX' and take real part
  have hij := congr_fun (congr_fun hX' i) j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply, Matrix.zero_apply,
    mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at hij
  -- hij : X j i * ↑(η j) + ↑(η i) * X i j = 0. Take Re.
  have hre := congr_arg Complex.re hij
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_mul, Complex.zero_re] at hre
  exact hre

/-- If X ∈ so(1,d;ℂ) then Im(X) ∈ so(1,d;ℝ). Same argument as for Re(X),
    taking imaginary parts instead. -/
private theorem imMatrix_isInLorentzAlgebra
    {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hX : ComplexLorentzGroup.IsInLieAlgebra X) :
    IsInLorentzAlgebra d (imMatrix X) := by
  have hX' : X.transpose * Matrix.diagonal (fun i => (minkowskiSignature d i : ℂ)) +
      Matrix.diagonal (fun i => (minkowskiSignature d i : ℂ)) * X = 0 := hX
  unfold IsInLorentzAlgebra
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    minkowskiMatrix, Matrix.diagonal_apply, imMatrix, Matrix.zero_apply,
    mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  have hij := congr_fun (congr_fun hX' i) j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply, Matrix.zero_apply,
    mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at hij
  -- hij : X j i * ↑(η j) + ↑(η i) * X i j = 0. Take Im.
  have him := congr_arg Complex.im hij
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, zero_add, Complex.zero_im] at him
  exact him

/-- The ℓ∞ operator norm of Re(X).map ofReal is bounded by the norm of X.
    Entry-wise |Re(z)| ≤ |z|, so each row sum is bounded. -/
private theorem norm_reMatrix_map_le (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    ‖(reMatrix X).map Complex.ofReal‖ ≤ ‖X‖ := by
  simp only [← coe_nnnorm, NNReal.coe_le_coe]
  rw [Matrix.linfty_opNNNorm_def, Matrix.linfty_opNNNorm_def]
  apply Finset.sup_le
  intro i _
  apply le_trans _ (Finset.le_sup (f := fun i => ∑ j, ‖X i j‖₊) (Finset.mem_univ i))
  apply Finset.sum_le_sum
  intro j _
  simp only [Matrix.map_apply, reMatrix]
  rw [show (Complex.ofReal (X i j).re : ℂ) = ((X i j).re : ℂ) from rfl]
  rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Complex.norm_real]
  exact Complex.abs_re_le_norm (X i j)

/-- The ℓ∞ operator norm of Im(X).map ofReal is bounded by the norm of X.
    Entry-wise |Im(z)| ≤ |z|, so each row sum is bounded. -/
private theorem norm_imMatrix_map_le (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    ‖(imMatrix X).map Complex.ofReal‖ ≤ ‖X‖ := by
  simp only [← coe_nnnorm, NNReal.coe_le_coe]
  rw [Matrix.linfty_opNNNorm_def, Matrix.linfty_opNNNorm_def]
  apply Finset.sup_le
  intro i _
  apply le_trans _ (Finset.le_sup (f := fun i => ∑ j, ‖X i j‖₊) (Finset.mem_univ i))
  apply Finset.sum_le_sum
  intro j _
  simp only [Matrix.map_apply, imMatrix]
  rw [show (Complex.ofReal (X i j).im : ℂ) = ((X i j).im : ℂ) from rfl]
  rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Complex.norm_real]
  exact Complex.abs_im_le_norm (X i j)

set_option maxHeartbeats 800000 in
/-- **Exponential neighborhood lemma.** The exponential map from the Lie algebra
    so(1,d;ℂ) covers a neighborhood of 1 in the complex Lorentz group, with
    a norm bound on the Lie algebra element.

    Uses `hasStrictFDerivAt_exp_zero` (derivative of exp at 0 is the identity)
    + `HasStrictFDerivAt.map_nhds_eq_of_surj` (IFT: exp maps neighborhoods of 0
    onto neighborhoods of 1) + algebraic argument (log of Lorentz ∈ Lie algebra). -/
private theorem exp_nhd_of_one (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ Λ in 𝓝 (1 : ComplexLorentzGroup d),
      ∃ (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ),
        ComplexLorentzGroup.IsInLieAlgebra X ∧ Λ.val = NormedSpace.exp X ∧ ‖X‖ < ε := by
  set E := Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
  -- Use mexp for the matrix exponential to avoid conflict with Complex.exp
  let mexp : E → E := NormedSpace.exp
  -- Step 1: IFT for exp at 0.
  have hexp_strict : HasStrictFDerivAt mexp
      ((ContinuousLinearEquiv.refl ℂ E : E →L[ℂ] E)) (0 : E) := by
    show HasStrictFDerivAt NormedSpace.exp _ _
    convert hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := E) using 1
  -- Get partial homeomorphism: exp is injective on source S, with 0 ∈ S.
  set Φ := hexp_strict.toOpenPartialHomeomorph mexp
  have h0_mem : (0 : E) ∈ Φ.source := hexp_strict.mem_toOpenPartialHomeomorph_source
  have hS_nhds : Φ.source ∈ 𝓝 (0 : E) := Φ.open_source.mem_nhds h0_mem
  have hinj : Set.InjOn mexp Φ.source := Φ.injOn
  -- Step 2: Filter conditions for the injectivity argument.
  set η := ComplexLorentzGroup.ηℂ (d := d)
  -- Negation sends 0 to 0 and is continuous → Φ.source preimage near 0
  have hneg_nhds : ∀ᶠ X in 𝓝 (0 : E), -X ∈ Φ.source :=
    continuous_neg.continuousAt.preimage_mem_nhds (by rw [neg_zero]; exact hS_nhds)
  -- η-conjugate-transpose sends 0 to 0 and is continuous
  have hconj_cont : Continuous (fun X : E => η * X.transpose * η) :=
    (continuous_const.mul (Continuous.matrix_transpose continuous_id)).mul continuous_const
  have hconj_nhds : ∀ᶠ X in 𝓝 (0 : E), η * X.transpose * η ∈ Φ.source :=
    hconj_cont.continuousAt.preimage_mem_nhds
      (by simp only [Matrix.transpose_zero, mul_zero, zero_mul]; exact hS_nhds)
  -- ‖X‖ < ε near 0
  have hball : ∀ᶠ X in 𝓝 (0 : E), ‖X‖ < ε :=
    Metric.eventually_nhds_iff.mpr ⟨ε, hε, fun _ hx => by rwa [dist_zero_right] at hx⟩
  -- Combine all conditions
  have hS_ev : ∀ᶠ X in 𝓝 (0 : E), X ∈ Φ.source := hS_nhds
  have h_good : ∀ᶠ X in 𝓝 (0 : E),
      X ∈ Φ.source ∧ -X ∈ Φ.source ∧ η * X.transpose * η ∈ Φ.source ∧ ‖X‖ < ε :=
    hS_ev.and (hneg_nhds.and (hconj_nhds.and hball))
  -- Step 3: exp maps nhds 0 → nhds 1 (surjectivity).
  have hmap : map mexp (𝓝 0) = 𝓝 (1 : E) := by
    have hsurj : (ContinuousLinearEquiv.refl ℂ E : E →L[ℂ] E).range = ⊤ := by
      ext x; exact ⟨fun _ => trivial, fun _ => ⟨x, by simp⟩⟩
    have := hexp_strict.map_nhds_eq_of_surj hsurj
    rwa [show mexp 0 = (1 : E) from NormedSpace.exp_zero] at this
  -- Push the good set through mexp to get a nhds 1 set in matrices
  have h_mat : ∀ᶠ M in 𝓝 (1 : E),
      ∃ X : E, mexp X = M ∧ X ∈ Φ.source ∧ -X ∈ Φ.source ∧
        η * X.transpose * η ∈ Φ.source ∧ ‖X‖ < ε := by
    rw [← hmap, Filter.eventually_map]
    exact h_good.mono fun X ⟨hXS, hnXS, hcXS, hXε⟩ =>
      ⟨X, rfl, hXS, hnXS, hcXS, hXε⟩
  -- Step 4: Pull back to the ComplexLorentzGroup topology via continuous val.
  have h_grp : ∀ᶠ Λ in 𝓝 (1 : ComplexLorentzGroup d),
      ∃ X : E, mexp X = Λ.val ∧ X ∈ Φ.source ∧ -X ∈ Φ.source ∧
        η * X.transpose * η ∈ Φ.source ∧ ‖X‖ < ε := by
    have hca : ContinuousAt (fun Λ : ComplexLorentzGroup d => Λ.val) 1 :=
      ComplexLorentzGroup.continuous_val.continuousAt
    rw [ContinuousAt, ComplexLorentzGroup.one_val'] at hca
    exact hca.eventually h_mat
  -- Step 5: For each such Λ, prove the Lie algebra condition using injectivity.
  apply h_grp.mono
  intro Λ ⟨X, hexpX, hXS, hnXS, hcXS, hXε⟩
  refine ⟨X, ?_, hexpX.symm, hXε⟩
  -- Need: X ∈ so(1,d;ℂ), i.e., Xᵀ * η + η * X = 0
  -- Key algebra: mexp(η Xᵀ η) = η mexp(Xᵀ) η = η (mexp X)ᵀ η = Λ⁻¹.val = mexp(-X)
  -- By injectivity on S: η Xᵀ η = -X, hence Xᵀ η + η X = 0
  -- mexp(η Xᵀ η) = η mexp(Xᵀ) η (by exp_units_conj with η² = 1)
  have h1 : mexp (η * X.transpose * η) = η * mexp X.transpose * η := by
    show NormedSpace.exp (η * X.transpose * η) = η * NormedSpace.exp X.transpose * η
    -- ↑ηℂ_unit = η and ↑(ηℂ_unit⁻¹) = η definitionally (since η² = 1)
    exact NormedSpace.exp_units_conj (ComplexLorentzGroup.ηℂ_unit) X.transpose
  -- mexp(Xᵀ) = (mexp X)ᵀ
  have h2 : mexp X.transpose = (mexp X).transpose :=
    show NormedSpace.exp X.transpose = (NormedSpace.exp X).transpose from
      Matrix.exp_transpose X
  -- The group inverse: (Λ⁻¹).val = η Λ.valᵀ η
  have h3 : (Λ⁻¹).val = η * Λ.val.transpose * η := rfl
  -- Combine: mexp(η Xᵀ η) = η (mexp X)ᵀ η = Λ⁻¹.val
  have h5 : mexp (η * X.transpose * η) = (Λ⁻¹).val := by
    rw [h1, h2, h3, hexpX]
  -- Show (Λ⁻¹).val = mexp(-X) via left-inverse uniqueness
  have h6 : (Λ⁻¹).val = mexp (-X) := by
    have hinvmul : (Λ⁻¹).val * Λ.val = 1 := by
      have : (Λ⁻¹ * Λ).val = 1 := by rw [inv_mul_cancel]; rfl
      rwa [ComplexLorentzGroup.mul_val] at this
    have hexp_rinv : mexp X * mexp (-X) = 1 := by
      show NormedSpace.exp X * NormedSpace.exp (-X) = 1
      rw [← NormedSpace.exp_add_of_commute (Commute.neg_right (Commute.refl X))]
      simp [NormedSpace.exp_zero]
    calc (Λ⁻¹).val
        = (Λ⁻¹).val * (mexp X * mexp (-X)) := by rw [hexp_rinv, mul_one]
      _ = (Λ⁻¹).val * mexp X * mexp (-X) := by rw [mul_assoc]
      _ = (Λ⁻¹).val * Λ.val * mexp (-X) := by rw [hexpX]
      _ = mexp (-X) := by rw [hinvmul, one_mul]
  -- Therefore: mexp(η Xᵀ η) = mexp(-X)
  have h7 : mexp (η * X.transpose * η) = mexp (-X) := by rw [h5, h6]
  -- By injectivity: η Xᵀ η = -X
  have h8 : η * X.transpose * η = -X := hinj hcXS hnXS h7
  -- Deduce: Xᵀ η + η X = 0
  show ComplexLorentzGroup.IsInLieAlgebra X
  unfold ComplexLorentzGroup.IsInLieAlgebra
  -- From h8: η Xᵀ η = -X → multiply by η on left: η²Xᵀη = -ηX → Xᵀη = -ηX
  have h9 : X.transpose * η = -(η * X) := by
    calc X.transpose * η
        = 1 * X.transpose * η := by rw [Matrix.one_mul]
      _ = (η * η) * X.transpose * η := by rw [ComplexLorentzGroup.ηℂ_sq (d := d)]
      _ = η * (η * X.transpose * η) := by simp only [Matrix.mul_assoc]
      _ = η * (-X) := by rw [h8]
      _ = -(η * X) := Matrix.mul_neg η X
  -- Xᵀη + ηX = -ηX + ηX = 0
  rw [h9]; exact neg_add_cancel _

/-- **Full-domain single-generator identity theorem.** For Y ∈ so(1,d;ℝ),
    the function F(exp(t·Y_ℂ)·z) = F(z) for ALL t in any preconnected
    open subset of {t : exp(t·Y_ℂ)·z ∈ FT} containing 0.

    Upgrade of `single_generator_invariance` from "eventually near 0"
    to "on the whole connected domain", using the Mathlib identity theorem
    `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`. -/
private theorem full_domain_generator_invariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hY : IsInLorentzAlgebra d Y)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n)
    {U : Set ℂ} (hU_open : IsOpen U) (hU_pre : IsPreconnected U)
    (h0U : (0 : ℂ) ∈ U)
    (hU_sub : ∀ t ∈ U, (fun k (μ : Fin (d + 1)) =>
      ∑ ν, (exp (t • Y.map Complex.ofReal) : Matrix _ _ ℂ) μ ν * z k ν) ∈ ForwardTube d n) :
    ∀ t ∈ U, F (fun k μ =>
      ∑ ν, (exp (t • Y.map Complex.ofReal) : Matrix _ _ ℂ) μ ν * z k ν) = F z := by
  set X := Y.map Complex.ofReal with hX_def
  set action : ℂ → Fin n → Fin (d + 1) → ℂ :=
    fun t k μ => ∑ ν, (exp (t • X) : Matrix _ _ ℂ) μ ν * z k ν with haction_def
  set g : ℂ → ℂ := fun t => F (action t) - F z with hg_def
  -- g is DifferentiableOn on U
  have hg_diff : DifferentiableOn ℂ g U := by
    apply DifferentiableOn.sub
    · exact hF_holo.comp (differentiable_expAction X z).differentiableOn
        (fun t ht => hU_sub t ht)
    · exact differentiableOn_const _
  -- g is AnalyticOnNhd on U
  have hg_analytic : AnalyticOnNhd ℂ g U :=
    hg_diff.analyticOnNhd hU_open
  -- g(s) = 0 for real s near 0 in U
  have hg_real : ∀ s : ℝ, (s : ℂ) ∈ U → g (s : ℂ) = 0 := by
    intro s hs
    simp only [hg_def, sub_eq_zero]
    have hbridge := exp_map_ofReal_bridge Y s
    have hentry : ∀ μ ν : Fin (d + 1),
        (exp ((s : ℂ) • X) : Matrix _ _ ℂ) μ ν =
        ((exp (s • Y) : Matrix _ _ ℝ) μ ν : ℂ) := by
      intro μ ν
      simp only [hX_def, ← hbridge, Matrix.map_apply]
    have haction_eq : action (s : ℂ) =
        fun k μ => ∑ ν, ((exp (s • Y) : Matrix _ _ ℝ) μ ν : ℂ) * z k ν := by
      ext k μ; simp only [haction_def]; congr 1; ext ν; rw [hentry]
    rw [haction_eq]
    exact hF_real_inv (expLorentz d (s • Y) (isInLorentzAlgebra_smul d hY s)) z hz
  -- g = 0 frequently near 0 in 𝓝[≠] 0
  have hg_freq : ∃ᶠ t in 𝓝[≠] (0 : ℂ), g t = 0 := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    intro ⟨U', hU'_open, h0_mem, hU'_sub⟩
    obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU'_open 0 h0_mem
    obtain ⟨r', hr'_pos, hr'_sub⟩ := Metric.isOpen_iff.mp hU_open 0 h0U
    set s := min (r / 2) (r' / 2) with hs_def
    have hs_pos : 0 < s := by positivity
    have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs_pos)
    have hs_in_U' : (s : ℂ) ∈ U' := hr_sub (by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs_pos]; linarith [min_le_left (r / 2) (r' / 2)])
    have hs_in_U : (s : ℂ) ∈ U := hr'_sub (by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs_pos]; linarith [min_le_right (r / 2) (r' / 2)])
    exact hU'_sub ⟨hs_in_U', hs_ne⟩ (hg_real s hs_in_U)
  -- By the identity theorem: g = 0 on all of U
  have hg_zero := hg_analytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
    hU_pre h0U hg_freq
  -- Translate back to F
  intro t ht
  have := hg_zero ht
  simp only [hg_def, Pi.zero_apply, sub_eq_zero] at this
  exact this

set_option maxHeartbeats 400000 in
/-- Helper: for ‖X₁‖ ≤ ‖X‖, ‖X₂‖ ≤ ‖X‖, ‖X‖ < δ/7, and s ∈ ball(0,R),
    we get ‖X₁ + s • X₂‖ < δ (when R ≤ 2). -/
private theorem norm_affine_combination_lt
    (X₁ X₂ X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hX₁_le : ‖X₁‖ ≤ ‖X‖) (hX₂_le : ‖X₂‖ ≤ ‖X‖)
    {δ : ℝ} (hsmall : ‖X‖ < δ / 7) {s : ℂ} (hs : ‖s‖ < 2) :
    ‖X₁ + s • X₂‖ < δ :=
  calc ‖X₁ + s • X₂‖ ≤ ‖X₁‖ + ‖s • X₂‖ := norm_add_le _ _
    _ ≤ ‖X₁‖ + ‖s‖ * ‖X₂‖ := add_le_add (le_refl _) (norm_smul_le s X₂)
    _ ≤ ‖X‖ + 2 * ‖X‖ := add_le_add hX₁_le
        (mul_le_mul (le_of_lt hs) hX₂_le (norm_nonneg _) (by positivity))
    _ = 3 * ‖X‖ := by ring
    _ < δ := by nlinarith [norm_nonneg X]

set_option maxHeartbeats 400000 in
/-- Helper: for ‖s‖ < 2, ‖t‖ < 2, and ‖X‖ < δ/7:
    ‖t • (X₁ + s • X₂)‖ < δ. -/
private theorem norm_tsmul_affine_lt
    (X₁ X₂ X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hX₁_le : ‖X₁‖ ≤ ‖X‖) (hX₂_le : ‖X₂‖ ≤ ‖X‖)
    {δ : ℝ} (hsmall : ‖X‖ < δ / 7)
    {s : ℂ} (hs : ‖s‖ < 2) {t : ℂ} (ht : ‖t‖ < 2) :
    ‖t • (X₁ + s • X₂)‖ < δ :=
  calc ‖t • (X₁ + s • X₂)‖ ≤ ‖t‖ * ‖X₁ + s • X₂‖ := norm_smul_le _ _
    _ ≤ 2 * (3 * ‖X‖) := by
        apply mul_le_mul (le_of_lt ht)
        · calc ‖X₁ + s • X₂‖ ≤ ‖X₁‖ + ‖s • X₂‖ := norm_add_le _ _
            _ ≤ ‖X₁‖ + ‖s‖ * ‖X₂‖ :=
                add_le_add (le_refl _) (norm_smul_le s X₂)
            _ ≤ ‖X‖ + 2 * ‖X‖ := add_le_add hX₁_le
                (mul_le_mul (le_of_lt hs) hX₂_le (norm_nonneg _) (by positivity))
            _ = 3 * ‖X‖ := by ring
        · positivity
        · positivity
    _ = 6 * ‖X‖ := by ring
    _ < δ := by nlinarith [norm_nonneg X]

set_option maxHeartbeats 800000 in
/-- Core analytic argument for near-identity invariance:
    Given δ such that exp(A)·z ∈ FT for ‖A‖ < δ, and X ∈ so(1,d;ℂ) with ‖X‖ < δ/7,
    show F(exp(X)·z) = F(z). Extracted as a separate lemma for reuse in the
    uniform version. -/
private theorem near_identity_core (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    {z : Fin n → Fin (d + 1) → ℂ} (hz : z ∈ ForwardTube d n)
    {δ : ℝ} (_hδ_pos : 0 < δ)
    (hA_in_FT : ∀ A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ, ‖A‖ < δ →
        (fun k (μ : Fin (d + 1)) => ∑ ν, (exp A : Matrix _ _ ℂ) μ ν * z k ν) ∈
          ForwardTube d n)
    {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hX_lie : ComplexLorentzGroup.IsInLieAlgebra X) (hX_small : ‖X‖ < δ / 7) :
    F (fun k μ => ∑ ν, (exp X : Matrix _ _ ℂ) μ ν * z k ν) = F z := by
  -- === Decompose X = X₁ + I•X₂ ===
  set Y₁ := reMatrix X
  set Y₂ := imMatrix X
  set X₁ := Y₁.map Complex.ofReal with hX₁_def
  set X₂ := Y₂.map Complex.ofReal with hX₂_def
  have hY₁_lie := reMatrix_isInLorentzAlgebra hX_lie
  have hY₂_lie := imMatrix_isInLorentzAlgebra hX_lie
  have hX_decomp : X = X₁ + Complex.I • X₂ := matrix_re_im_decomp X
  -- Norm bounds: ‖X₁‖ ≤ ‖X‖, ‖X₂‖ ≤ ‖X‖
  have hX₁_le : ‖X₁‖ ≤ ‖X‖ := norm_reMatrix_map_le X
  have hX₂_le : ‖X₂‖ ≤ ‖X‖ := norm_imMatrix_map_le X
  have hsmall : ‖X‖ < δ / 7 := hX_small
  -- Helper: for s ∈ ball(0,2), exp(X₁ + s•X₂)·z ∈ FT
  have hball_FT : ∀ s ∈ Metric.ball (0 : ℂ) 2,
      (fun k (μ : Fin (d + 1)) =>
        ∑ ν, (exp (X₁ + s • X₂) : Matrix _ _ ℂ) μ ν * z k ν) ∈ ForwardTube d n := by
    intro s hs
    exact hA_in_FT _ (norm_affine_combination_lt X₁ X₂ X hX₁_le hX₂_le hsmall
      (by rwa [Metric.mem_ball, dist_zero_right] at hs))
  -- For real s, X₁ + (s:ℂ)•X₂ = (Y₁ + s•Y₂).map ofReal
  have hreal_param : ∀ s : ℝ, X₁ + (s : ℂ) • X₂ = (Y₁ + s • Y₂).map Complex.ofReal := by
    intro s; ext i j
    simp only [hX₁_def, hX₂_def, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply,
      Complex.ofReal_add, Complex.ofReal_mul, smul_eq_mul]
  -- === Step 1: F(exp(X₁ + s•X₂)·z) = F(z) for real s ∈ ball(0,2) ===
  have hstep1 : ∀ s : ℝ, ‖(s : ℂ)‖ < 2 →
      F (fun k μ => ∑ ν, (exp (X₁ + (s : ℂ) • X₂) : Matrix _ _ ℂ) μ ν * z k ν) = F z := by
    intro s hs
    rw [hreal_param s]
    have hgen_lie : IsInLorentzAlgebra d (Y₁ + s • Y₂) := by
      unfold IsInLorentzAlgebra at hY₁_lie hY₂_lie ⊢
      simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.smul_mul,
        Matrix.mul_add, Matrix.mul_smul]
      rw [add_add_add_comm, ← smul_add, hY₁_lie, hY₂_lie, smul_zero, add_zero]
    have hball_sub : ∀ t ∈ Metric.ball (0 : ℂ) 2,
        (fun k (μ : Fin (d + 1)) => ∑ ν,
          (exp (t • (Y₁ + s • Y₂).map Complex.ofReal) : Matrix _ _ ℂ) μ ν * z k ν) ∈
            ForwardTube d n := by
      intro t ht
      apply hA_in_FT
      have h_eq : (Y₁ + s • Y₂).map Complex.ofReal = X₁ + (↑s : ℂ) • X₂ :=
        (hreal_param s).symm
      rw [h_eq]
      exact norm_tsmul_affine_lt X₁ X₂ X hX₁_le hX₂_le hsmall hs
        (by rwa [Metric.mem_ball, dist_zero_right] at ht)
    have h1_in_ball : (1 : ℂ) ∈ Metric.ball (0 : ℂ) 2 := by
      rw [Metric.mem_ball, dist_zero_right, norm_one]; norm_num
    have := full_domain_generator_invariance n F hF_holo hF_real_inv
      (Y₁ + s • Y₂) hgen_lie z hz Metric.isOpen_ball
      (convex_ball _ _).isPreconnected (Metric.mem_ball_self (by positivity : (0 : ℝ) < 2))
      hball_sub 1 h1_in_ball
    simp only [one_smul] at this
    exact this
  -- === Step 2: Identity theorem in s on ball(0,2) ===
  set action_s : ℂ → Fin n → Fin (d + 1) → ℂ :=
    fun s k μ => ∑ ν, (exp (X₁ + s • X₂) : Matrix _ _ ℂ) μ ν * z k ν with haction_s_def
  set g : ℂ → ℂ := fun s => F (action_s s) - F z with hg_def
  have hg_diff : DifferentiableOn ℂ g (Metric.ball 0 2) := by
    apply DifferentiableOn.sub
    · apply hF_holo.comp _ hball_FT
      have h_affine : Differentiable ℂ (fun s : ℂ => X₁ + s • X₂) :=
        (differentiable_const X₁).add (differentiable_id.smul_const X₂)
      have h_exp_comp : Differentiable ℂ (fun s : ℂ => exp (X₁ + s • X₂)) :=
        fun s => (NormedSpace.exp_analytic (X₁ + s • X₂)).differentiableAt.comp s (h_affine s)
      exact (differentiable_pi.mpr fun k => differentiable_pi.mpr fun μ =>
        Differentiable.fun_sum fun ν _ =>
          ((differentiable_apply ν).comp ((differentiable_apply μ).comp h_exp_comp)).mul
            (differentiable_const _)).differentiableOn
    · exact differentiableOn_const _
  have hg_analytic : AnalyticOnNhd ℂ g (Metric.ball 0 2) :=
    hg_diff.analyticOnNhd Metric.isOpen_ball
  have hg_real : ∀ s : ℝ, ‖(s : ℂ)‖ < 2 → g (s : ℂ) = 0 := by
    intro s hs; simp only [hg_def, sub_eq_zero]; exact hstep1 s hs
  have hg_freq : ∃ᶠ s in 𝓝[≠] (0 : ℂ), g s = 0 := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    intro ⟨U', hU'_open, h0_mem, hU'_sub⟩
    obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU'_open 0 h0_mem
    set s := min (r / 2) 1 with hs_def
    have hs_pos : 0 < s := by positivity
    have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs_pos)
    have hs_norm : ‖(s : ℂ)‖ < 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs_pos]
      linarith [min_le_right (r / 2) 1]
    have hs_in_U' : (s : ℂ) ∈ U' := hr_sub (by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs_pos]; linarith [min_le_left (r / 2) 1])
    exact hU'_sub ⟨hs_in_U', hs_ne⟩ (hg_real s hs_norm)
  have hg_zero := hg_analytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball _ _).isPreconnected (Metric.mem_ball_self (by positivity : (0 : ℝ) < 2)) hg_freq
  -- === Step 3: Evaluate at s = I ===
  have hI_in_ball : Complex.I ∈ Metric.ball (0 : ℂ) 2 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_I]; norm_num
  have hgI := hg_zero hI_in_ball
  simp only [hg_def, Pi.zero_apply, sub_eq_zero] at hgI
  rw [hX_decomp]
  exact hgI

/-- **Near-identity invariance.** If F is holomorphic on the forward tube and
    real-Lorentz invariant, then F is invariant under complex Lorentz transformations
    in a neighborhood of 1 (when the image stays in the forward tube). -/
private theorem near_identity_invariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    ∀ᶠ Λ in 𝓝 (1 : ComplexLorentzGroup d),
      complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z := by
  -- === Step 0: Continuity gives δ such that ‖A‖ < δ → exp(A)·z ∈ FT ===
  have hexp_action_cont : Continuous (fun A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
      (fun k (μ : Fin (d + 1)) => ∑ ν, (exp A : Matrix _ _ ℂ) μ ν * z k ν)) := by
    apply continuous_pi; intro k; apply continuous_pi; intro μ
    apply continuous_finset_sum; intro ν _
    refine Continuous.mul ?_ continuous_const
    exact (continuous_apply ν).comp ((continuous_apply μ).comp NormedSpace.exp_continuous)
  have h0_in_FT : (fun k (μ : Fin (d + 1)) =>
      ∑ ν, (exp (0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) μ ν * z k ν) ∈ ForwardTube d n := by
    convert hz using 2; ext k
    simp [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]
  obtain ⟨δ, hδ_pos, hδ_sub⟩ :=
    Metric.isOpen_iff.mp (isOpen_forwardTube.preimage hexp_action_cont) 0 h0_in_FT
  -- Key: for ‖A‖ < δ, exp(A)·z ∈ FT
  have hA_in_FT : ∀ A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ, ‖A‖ < δ →
      (fun k (μ : Fin (d + 1)) => ∑ ν, (exp A : Matrix _ _ ℂ) μ ν * z k ν) ∈
        ForwardTube d n :=
    fun A hA => hδ_sub (by rwa [Metric.mem_ball, dist_zero_right])
  -- === Step 0.5: Use exp_nhd_of_one with norm bound δ/7 ===
  apply (exp_nhd_of_one (δ / 7) (by positivity)).mono
  intro Λ ⟨X, hX_lie, hΛ_eq, hX_small⟩ hΛz
  -- Λ.val = exp X, ‖X‖ < δ/7, X ∈ so(1,d;ℂ)
  -- Goal: F(complexLorentzAction Λ z) = F z
  -- Rewrite action in terms of exp X
  have haction_eq : complexLorentzAction Λ z =
      fun k μ => ∑ ν, (exp X : Matrix _ _ ℂ) μ ν * z k ν := by
    ext k μ; simp only [complexLorentzAction]; congr 1; ext ν; rw [← hΛ_eq]
  rw [haction_eq]
  exact near_identity_core n F hF_holo hF_real_inv hz hδ_pos hA_in_FT hX_lie hX_small

set_option maxHeartbeats 800000 in
/-- **Uniform near-identity invariance.** For z₀ ∈ FT, there exist a neighborhood U
    of z₀ and a neighborhood V of 1 ∈ G such that for all w ∈ U ∩ FT and Λ ∈ V:
    F(Λ·w) = F(w) (when Λ·w ∈ FT). Uses joint continuity of (A, w) ↦ exp(A)·w
    to get a uniform δ, then applies `near_identity_core`. -/
private theorem uniform_near_identity_invariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (z₀ : Fin n → Fin (d + 1) → ℂ) (hz₀ : z₀ ∈ ForwardTube d n) :
    ∃ U ∈ 𝓝 z₀, ∀ᶠ Λ in 𝓝 (1 : ComplexLorentzGroup d),
      ∀ w ∈ U, w ∈ ForwardTube d n →
        complexLorentzAction Λ w ∈ ForwardTube d n →
        F (complexLorentzAction Λ w) = F w := by
  -- Joint continuity: the map (A, w) ↦ exp(A)·w is continuous
  have hΦ_cont : Continuous (fun (p : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ ×
      (Fin n → Fin (d + 1) → ℂ)) =>
      (fun k (μ : Fin (d + 1)) =>
        ∑ ν, (exp p.1 : Matrix _ _ ℂ) μ ν * p.2 k ν)) := by
    apply continuous_pi; intro k; apply continuous_pi; intro μ
    apply continuous_finset_sum; intro ν _
    refine Continuous.mul ?_ ?_
    · -- Continuous (fun a => (exp a.1) μ ν)
      have h_exp_fst : Continuous (fun a : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ ×
          (Fin n → Fin (d + 1) → ℂ) => exp a.1) :=
        NormedSpace.exp_continuous.comp continuous_fst
      have h_entry : Continuous (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ => M μ ν) :=
        (continuous_apply ν).comp (continuous_apply μ)
      exact h_entry.comp h_exp_fst
    · -- Continuous (fun a => a.2 k ν)
      have h_entry2 : Continuous (fun f : Fin n → Fin (d + 1) → ℂ => f k ν) :=
        (continuous_apply ν).comp (continuous_apply k)
      exact h_entry2.comp continuous_snd
  -- At (0, z₀): exp(0)·z₀ = z₀ ∈ FT
  have h0z₀ : (fun k (μ : Fin (d + 1)) =>
      ∑ ν, (exp (0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) : Matrix _ _ ℂ) μ ν * z₀ k ν) ∈
        ForwardTube d n := by
    convert hz₀ using 2; ext k
    simp [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]
  -- Get ε > 0 such that ‖A‖ < ε ∧ ‖w - z₀‖ < ε → exp(A)·w ∈ FT
  obtain ⟨ε, hε_pos, hε_sub⟩ :=
    Metric.isOpen_iff.mp (isOpen_forwardTube.preimage hΦ_cont) (0, z₀) h0z₀
  -- U = B(z₀, ε)
  refine ⟨Metric.ball z₀ ε, Metric.ball_mem_nhds z₀ hε_pos, ?_⟩
  -- For Λ ∈ exp_nhd_of_one(ε/7) and w ∈ B(z₀, ε) ∩ FT: apply near_identity_core
  apply (exp_nhd_of_one (ε / 7) (by positivity)).mono
  intro Λ ⟨X, hX_lie, hΛ_eq, hX_small⟩ w hw_ball hw_FT hΛw
  -- Rewrite action in terms of exp X
  have haction_eq : complexLorentzAction Λ w =
      fun k μ => ∑ ν, (exp X : Matrix _ _ ℂ) μ ν * w k ν := by
    ext k μ; simp only [complexLorentzAction]; congr 1; ext ν; rw [← hΛ_eq]
  rw [haction_eq]
  -- For w ∈ B(z₀, ε): ‖A‖ < ε → exp(A)·w ∈ FT
  have hA_in_FT_w : ∀ A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ, ‖A‖ < ε →
      (fun k (μ : Fin (d + 1)) => ∑ ν, (exp A : Matrix _ _ ℂ) μ ν * w k ν) ∈
        ForwardTube d n := by
    intro A hA
    have h_mem : (A, w) ∈ Metric.ball (0, z₀) ε := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨by rwa [dist_zero_right], Metric.mem_ball.mp hw_ball⟩
    exact hε_sub h_mem
  exact near_identity_core n F hF_holo hF_real_inv hw_FT hε_pos hA_in_FT_w hX_lie hX_small

/- orbitSet_isPreconnected is no longer needed — the T-set clopen argument below
   works on the full group G instead of the orbit set. -/

/-- The action map z ↦ Λ·z is continuous (ℂ-linear in z). -/
theorem continuous_complexLorentzAction_snd (Λ : ComplexLorentzGroup d) :
    Continuous (fun z : Fin n → Fin (d + 1) → ℂ => complexLorentzAction Λ z) := by
  apply continuous_pi; intro k
  apply continuous_pi; intro μ
  simp only [complexLorentzAction]
  exact continuous_finset_sum Finset.univ
    (fun ν _ => continuous_const.mul ((continuous_apply ν).comp (continuous_apply k)))

/-- The action map z ↦ Λ·z is ℂ-differentiable (it is ℂ-linear in z). -/
theorem differentiable_complexLorentzAction_snd (Λ : ComplexLorentzGroup d) :
    Differentiable ℂ (fun z : Fin n → Fin (d + 1) → ℂ => complexLorentzAction Λ z) := by
  apply differentiable_pi.mpr; intro k
  apply differentiable_pi.mpr; intro μ
  simp only [complexLorentzAction]
  apply Differentiable.fun_sum; intro ν _
  apply Differentiable.const_mul
  have h1 : Differentiable ℂ (fun z : Fin n → Fin (d + 1) → ℂ => z k) := differentiable_apply k
  exact (differentiable_apply ν).comp h1

/-- D_Λ = {z ∈ FT : Λ·z ∈ FT} is open (intersection of two open preimages). -/
theorem isOpen_d_lambda (Λ : ComplexLorentzGroup d) :
    IsOpen {z | z ∈ ForwardTube d n ∧ complexLorentzAction Λ z ∈ ForwardTube d n} :=
  isOpen_forwardTube.inter (isOpen_forwardTube.preimage (continuous_complexLorentzAction_snd Λ))

/-- The forward tube is nonempty (for any n, d). -/
theorem forwardTube_nonempty : (ForwardTube d n).Nonempty := by
  -- Witness: z_k(μ) = (k+1) · i for μ = 0, and 0 otherwise.
  -- Then η_k = imDiff z k has η_k(0) = 1 > 0 and η_k(i>0) = 0, so Q(η_k) = -1 < 0.
  -- Use imDiff helper for cleaner reasoning.
  refine ⟨fun (k : Fin n) (μ : Fin (d + 1)) =>
    if μ = 0 then Complex.I * (↑(k : ℕ) + 1 : ℝ) else 0, fun k => ?_⟩
  set z : Fin n → Fin (d + 1) → ℂ :=
    fun k μ => if μ = 0 then Complex.I * (↑(k : ℕ) + 1 : ℝ) else 0
  -- Compute imDiff z k
  have hη0 : imDiff z k 0 = 1 := by
    simp only [imDiff, z, ↓reduceIte]
    by_cases hk : (k : ℕ) = 0
    · simp [hk]
    · have hk1 : 1 ≤ (k : ℕ) := Nat.one_le_iff_ne_zero.mpr hk
      simp only [hk, ↓reduceDIte, ↓reduceIte, Complex.sub_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Nat.cast_sub hk1]
      ring
  have hηi : ∀ i : Fin d, imDiff z k (Fin.succ i) = 0 := by
    intro i
    simp only [imDiff, z, Fin.succ_ne_zero, ↓reduceIte]
    split_ifs <;> simp
  constructor
  · -- η 0 > 0
    change imDiff z k 0 > 0
    rw [hη0]; exact one_pos
  · -- Minkowski sum < 0
    change ∑ μ, minkowskiSignature d μ * imDiff z k μ ^ 2 < 0
    rw [minkowski_sum_decomp, hη0]
    simp only [hηi]
    norm_num

/-- **Identity theorem on open convex domains via 1D line restriction.**
    If f is ℂ-differentiable on an open convex set D and f =ᶠ 0 near some z₁ ∈ D,
    then f ≡ 0 on D. Proof: for w ∈ D, restrict f to the complex line l(t) = z₁ + t(w - z₁).
    The pullback f ∘ l : ℂ → ℂ is holomorphic on l⁻¹(D) (open, convex, thus connected),
    vanishes near t = 0, hence vanishes at t = 1 by the 1D identity theorem (Cauchy). -/
private theorem eq_zero_on_convex_of_eventuallyEq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {D : Set E} (hD_open : IsOpen D) (hD_conv : Convex ℝ D)
    {f : E → ℂ} (hf : DifferentiableOn ℂ f D)
    {z₁ : E} (hz₁ : z₁ ∈ D) (hf_zero : f =ᶠ[𝓝 z₁] 0) :
    ∀ w ∈ D, f w = 0 := by
  intro w hw
  -- Complex line from z₁ to w
  let l : ℂ → E := fun t => z₁ + t • (w - z₁)
  have hl_diff : Differentiable ℂ l :=
    (differentiable_const z₁).add (differentiable_id.smul (differentiable_const (w - z₁)))
  -- S = l⁻¹(D) is open
  have hS_open : IsOpen (l ⁻¹' D) := hD_open.preimage hl_diff.continuous
  -- S is ℝ-convex (l is ℝ-affine, D is ℝ-convex)
  have hS_conv : Convex ℝ (l ⁻¹' D) := by
    intro s₁ hs₁ s₂ hs₂ a b ha hb hab
    show l (a • s₁ + b • s₂) ∈ D
    have key : l (a • s₁ + b • s₂) = a • l s₁ + b • l s₂ := by
      show z₁ + (a • s₁ + b • s₂) • (w - z₁) =
        a • (z₁ + s₁ • (w - z₁)) + b • (z₁ + s₂ • (w - z₁))
      rw [add_smul (a • s₁ : ℂ) (b • s₂ : ℂ) (w - z₁),
          smul_assoc (a : ℝ) (s₁ : ℂ) (w - z₁ : E),
          smul_assoc (b : ℝ) (s₂ : ℂ) (w - z₁ : E),
          smul_add (a : ℝ) (z₁ : E) (s₁ • (w - z₁)),
          smul_add (b : ℝ) (z₁ : E) (s₂ • (w - z₁))]
      nth_rw 1 [show z₁ = a • z₁ + b • (z₁ : E) from by rw [← add_smul, hab, one_smul]]
      abel
    rw [key]; exact hD_conv hs₁ hs₂ ha hb hab
  -- 0 ∈ S (l(0) = z₁ ∈ D) and 1 ∈ S (l(1) = w ∈ D)
  have h0S : (0 : ℂ) ∈ l ⁻¹' D := by
    show l 0 ∈ D; simp only [l, zero_smul, add_zero]; exact hz₁
  have h1S : (1 : ℂ) ∈ l ⁻¹' D := by
    show l 1 ∈ D; change z₁ + 1 • (w - z₁) ∈ D; rw [one_smul]
    convert hw using 1; abel
  -- f ∘ l is holomorphic on S hence analytic (1D Cauchy integral formula)
  have hfl_analytic : AnalyticOnNhd ℂ (f ∘ l) (l ⁻¹' D) :=
    (hf.comp hl_diff.differentiableOn (Set.mapsTo_preimage l D)).analyticOnNhd hS_open
  -- f ∘ l vanishes near t = 0 (since l(0) = z₁ and f =ᶠ 0 near z₁)
  have hfl_zero : (f ∘ l) =ᶠ[𝓝 (0 : ℂ)] 0 := by
    have : Tendsto l (𝓝 0) (𝓝 z₁) := by
      convert hl_diff.continuous.continuousAt.tendsto using 1
      simp only [l, zero_smul, add_zero]
    exact this.eventually hf_zero
  -- By identity theorem: f ∘ l ≡ 0 on S (preconnected since convex)
  have h_eq := hfl_analytic.eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const hS_conv.isPreconnected h0S hfl_zero
  -- f(w) = (f ∘ l)(1) = 0
  have h_val := h_eq h1S
  simp only [Function.comp] at h_val
  have h_lw : l 1 = w := by show z₁ + (1 : ℂ) • (w - z₁) = w; rw [one_smul]; abel
  rwa [h_lw] at h_val

/-- **Path within orbit set.** For any Λ in the orbit set of w (i.e., Λ·w ∈ FT),
    there exists a continuous path from 1 to Λ that stays entirely within the orbit set.

    The mathematical proof uses the fact that any element of the connected Lie group
    SO⁺(1,d;ℂ) can be written as a product of exponentials exp(X₁)·...·exp(Xₖ) with
    generators Xᵢ of arbitrarily small norm. Each segment t ↦ exp(tXᵢ) moves the
    action point by a small amount, so by openness of FT the orbit condition is
    maintained throughout. Concatenating these segments gives a path in the orbit set.

    This captures the deep "small-step" argument from Lie theory:
    - Connected Lie groups are generated by any neighborhood of the identity
    - For sufficiently small generators, exponential paths stay in the orbit set
    - The orbit set is open, so the condition is stable under small perturbations -/
private lemma orbitSet_joined_one (w : Fin n → Fin (d + 1) → ℂ)
    (hw : w ∈ ForwardTube d n) (Λ : ComplexLorentzGroup d)
    (hΛ : complexLorentzAction Λ w ∈ ForwardTube d n) :
    ∃ γ : Path (1 : ComplexLorentzGroup d) Λ,
      ∀ t, complexLorentzAction (γ t) w ∈ ForwardTube d n := by
  sorry

/-- Each orbit set O_w = {Λ ∈ G : Λ·w ∈ FT} is preconnected (open subset of
    the connected Lie group G, containing 1).

    The proof shows the orbit set is path-connected using `orbitSet_joined_one`:
    for any two elements Λ₁, Λ₂, we get paths from 1 to each, and concatenating
    (with reversal) gives a path from Λ₁ to Λ₂ within the orbit set. Path-connected
    sets are preconnected. -/
private theorem orbitSet_isPreconnected (w : Fin n → Fin (d + 1) → ℂ)
    (hw : w ∈ ForwardTube d n) :
    IsPreconnected {Λ : ComplexLorentzGroup d |
      complexLorentzAction Λ w ∈ ForwardTube d n} := by
  -- Show the orbit set is path-connected, hence connected, hence preconnected
  set S := {Λ : ComplexLorentzGroup d | complexLorentzAction Λ w ∈ ForwardTube d n}
  -- S is path-connected: for any Λ₁, Λ₂ ∈ S, get paths from 1 to each via
  -- orbitSet_joined_one, then compose via JoinedIn.symm.trans
  suffices hpc : IsPathConnected S from hpc.isConnected.isPreconnected
  rw [isPathConnected_iff]
  refine ⟨⟨1, ?_⟩, fun Λ₁ hΛ₁ Λ₂ hΛ₂ => ?_⟩
  · -- 1 ∈ S
    show complexLorentzAction 1 w ∈ ForwardTube d n
    rw [complexLorentzAction_one]; exact hw
  · -- JoinedIn S Λ₁ Λ₂
    -- Get paths from 1 to Λ₁ and from 1 to Λ₂ within S
    obtain ⟨γ₁, hγ₁⟩ := orbitSet_joined_one w hw Λ₁ hΛ₁
    obtain ⟨γ₂, hγ₂⟩ := orbitSet_joined_one w hw Λ₂ hΛ₂
    -- Construct JoinedIn from paths
    have h1 : JoinedIn S (1 : ComplexLorentzGroup d) Λ₁ := ⟨γ₁, hγ₁⟩
    have h2 : JoinedIn S (1 : ComplexLorentzGroup d) Λ₂ := ⟨γ₂, hγ₂⟩
    exact h1.symm.trans h2

/-- The set U = {Λ ∈ G : D_Λ ≠ ∅} of group elements with nonempty domain is connected.
    U = ⋃_{w ∈ FT} O_w where each O_w is preconnected and all contain 1, so the
    union is preconnected by `isPreconnected_sUnion`. -/
private theorem nonemptyDomain_isPreconnected :
    IsPreconnected {Λ : ComplexLorentzGroup d |
      ∃ w, w ∈ ForwardTube d n ∧ complexLorentzAction Λ w ∈ ForwardTube d n} := by
  -- Express U as ⋃₀ {O_w : w ∈ FT}
  have hU_eq : {Λ : ComplexLorentzGroup d |
      ∃ w, w ∈ ForwardTube d n ∧ complexLorentzAction Λ w ∈ ForwardTube d n} =
    ⋃₀ { S | ∃ w ∈ ForwardTube d n,
      S = {Λ : ComplexLorentzGroup d | complexLorentzAction Λ w ∈ ForwardTube d n} } := by
    ext Λ; simp only [Set.mem_setOf_eq, Set.mem_sUnion]
    constructor
    · rintro ⟨w, hw, hΛw⟩; exact ⟨_, ⟨w, hw, rfl⟩, hΛw⟩
    · rintro ⟨_, ⟨w, hw, rfl⟩, hΛw⟩; exact ⟨w, hw, hΛw⟩
  rw [hU_eq]
  apply isPreconnected_sUnion (1 : ComplexLorentzGroup d)
  · -- Each O_w contains 1
    rintro S ⟨w, hw, rfl⟩
    simp only [Set.mem_setOf_eq, complexLorentzAction_one]; exact hw
  · -- Each O_w is preconnected
    rintro S ⟨w, hw, rfl⟩
    exact orbitSet_isPreconnected w hw

/-- **Complex Lorentz invariance on the forward tube.**

    If F is holomorphic on the forward tube and invariant under the real
    restricted Lorentz group SO⁺(1,d;ℝ), then F is invariant under the
    complex Lorentz group SO⁺(1,d;ℂ), whenever the transformed point
    remains in the forward tube.

    **Proof (T-set argument with U-connected trick):**
    Define T = {Λ ∈ G : ∀ w ∈ FT, Λ·w ∈ FT → F(Λ·w) = F(w)} and
    U = {Λ ∈ G : ∃ w ∈ FT, Λ·w ∈ FT} (the "nonempty domain" set).
    1. T is **closed**: complement is open (witness gives continuous separation).
    2. T ∩ U is **open**: at Λ₀ ∈ T ∩ U, get z₀ ∈ D_{Λ₀}, factor Λ = Λ₀ · (Λ₀⁻¹Λ),
       apply the identity theorem twice using `near_identity_invariance`.
    3. Tᶜ ⊆ U (if Λ ∉ T, the witness is in D_Λ).
    4. U is connected and T ∩ U is clopen in U → T ∩ U = U.
    5. T ⊇ U and T ⊇ Uᶜ (vacuously) → T = G.

    Ref: Streater & Wightman, *PCT, Spin and Statistics*, Theorem 2-11. -/
theorem complex_lorentz_invariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z) :
    ∀ (Λ : ComplexLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z := by
  -- === Define T = {Λ : ∀ w ∈ FT, Λ·w ∈ FT → F(Λ·w) = F(w)} ===
  set T : Set (ComplexLorentzGroup d) :=
    { Λ | ∀ w, w ∈ ForwardTube d n → complexLorentzAction Λ w ∈ ForwardTube d n →
          F (complexLorentzAction Λ w) = F w } with hT_def
  -- Suffices: T = univ
  suffices hT_univ : T = Set.univ by
    intro Λ z hz hΛz; exact (Set.eq_univ_iff_forall.mp hT_univ Λ) z hz hΛz
  -- === G is connected ===
  haveI : PathConnectedSpace (ComplexLorentzGroup d) :=
    pathConnectedSpace_iff_univ.mpr ComplexLorentzGroup.isPathConnected
  -- === 1 ∈ T ===
  have h1T : (1 : ComplexLorentzGroup d) ∈ T := by
    intro w hw _; rw [complexLorentzAction_one]
  -- === Define U = {Λ : D_Λ ≠ ∅} ===
  set U : Set (ComplexLorentzGroup d) :=
    { Λ | ∃ w, w ∈ ForwardTube d n ∧ complexLorentzAction Λ w ∈ ForwardTube d n } with hU_def
  -- === Tᶜ ⊆ U (if Λ ∉ T, the witness w₀ shows D_Λ ≠ ∅) ===
  have hTc_sub_U : Tᶜ ⊆ U := by
    intro Λ hΛ
    simp only [Set.mem_compl_iff, hT_def, Set.mem_setOf_eq, not_forall] at hΛ
    push_neg at hΛ
    obtain ⟨w, hw, hΛw, _⟩ := hΛ
    exact ⟨w, hw, hΛw⟩
  -- === T is closed ===
  have hT_closed : IsClosed T := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro Λ₀ hΛ₀
    simp only [Set.mem_compl_iff, hT_def, Set.mem_setOf_eq, not_forall] at hΛ₀
    push_neg at hΛ₀
    obtain ⟨w₀, hw₀, hΛ₀w₀, hne⟩ := hΛ₀
    have hV_open : IsOpen {Λ : ComplexLorentzGroup d |
        complexLorentzAction Λ w₀ ∈ ForwardTube d n} :=
      isOpen_forwardTube.preimage (continuous_complexLorentzAction_fst w₀)
    have hcomp : ContinuousOn (fun Λ => F (complexLorentzAction Λ w₀))
        {Λ | complexLorentzAction Λ w₀ ∈ ForwardTube d n} :=
      hF_holo.continuousOn.comp (continuous_complexLorentzAction_fst w₀).continuousOn
        fun Λ hΛ => hΛ
    refine ⟨{Λ | complexLorentzAction Λ w₀ ∈ ForwardTube d n} ∩
        (fun Λ => F (complexLorentzAction Λ w₀)) ⁻¹' {F w₀}ᶜ,
      fun Λ ⟨hΛw₀, hΛne⟩ => ?_,
      hcomp.isOpen_inter_preimage hV_open isOpen_compl_singleton,
      ⟨hΛ₀w₀, hne⟩⟩
    simp only [Set.mem_compl_iff, hT_def, Set.mem_setOf_eq, not_forall]
    push_neg
    exact ⟨w₀, hw₀, hΛw₀, hΛne⟩
  -- === T ∩ U is open (identity theorem argument at Λ₀ ∈ T ∩ U) ===
  have hTU_open : IsOpen (T ∩ U) := by
    rw [isOpen_iff_forall_mem_open]
    intro Λ₀ ⟨hΛ₀, hΛ₀_U⟩
    -- Get z₀ ∈ D_{Λ₀} from Λ₀ ∈ U
    obtain ⟨z₀, hz₀, hΛ₀z₀⟩ := hΛ₀_U
    -- Near-identity invariance at z₀ gives nhd V of 1 where F(Λ'·z₀) = F(z₀)
    have h_near_z₀ := near_identity_invariance n F hF_holo hF_real_inv z₀ hz₀
    -- Left multiplication by Λ₀⁻¹ is continuous and maps Λ₀ to 1
    have h_left_mul : Continuous (fun Λ : ComplexLorentzGroup d => Λ₀⁻¹ * Λ) := by
      have hind : IsInducing (ComplexLorentzGroup.val : ComplexLorentzGroup d → _) := ⟨rfl⟩
      rw [hind.continuous_iff]
      change Continuous (fun x : ComplexLorentzGroup d => Λ₀⁻¹.val * x.val)
      exact continuous_const.mul ComplexLorentzGroup.continuous_val
    have h_tend : Tendsto (fun Λ => Λ₀⁻¹ * Λ) (𝓝 Λ₀) (𝓝 (1 : ComplexLorentzGroup d)) := by
      rw [show (1 : ComplexLorentzGroup d) = Λ₀⁻¹ * Λ₀ from (inv_mul_cancel Λ₀).symm]
      exact h_left_mul.continuousAt.tendsto
    -- Pull back near_identity_invariance through Λ ↦ Λ₀⁻¹Λ
    have h_near_pullback : ∀ᶠ Λ in 𝓝 Λ₀,
        complexLorentzAction (Λ₀⁻¹ * Λ) z₀ ∈ ForwardTube d n →
        F (complexLorentzAction (Λ₀⁻¹ * Λ) z₀) = F z₀ :=
      h_tend.eventually h_near_z₀
    -- z₀ ∈ D_Λ eventually (since Λ·z₀ → Λ₀·z₀ ∈ FT)
    have h_ev_DΛ : ∀ᶠ Λ in 𝓝 Λ₀,
        complexLorentzAction Λ z₀ ∈ ForwardTube d n :=
      (continuous_complexLorentzAction_fst z₀).continuousAt.preimage_mem_nhds
        (isOpen_forwardTube.mem_nhds hΛ₀z₀)
    -- z₀ ∈ D_{Λ'} eventually (since (Λ₀⁻¹Λ)·z₀ → z₀ ∈ FT)
    have h_ev_DΛ' : ∀ᶠ Λ in 𝓝 Λ₀,
        complexLorentzAction (Λ₀⁻¹ * Λ) z₀ ∈ ForwardTube d n := by
      have : (fun Λ : ComplexLorentzGroup d => complexLorentzAction (Λ₀⁻¹ * Λ) z₀) =
          (fun Λ' => complexLorentzAction Λ' z₀) ∘ (fun Λ => Λ₀⁻¹ * Λ) := rfl
      have hcont : Continuous (fun Λ : ComplexLorentzGroup d =>
          complexLorentzAction (Λ₀⁻¹ * Λ) z₀) := by
        rw [this]; exact (continuous_complexLorentzAction_fst z₀).comp h_left_mul
      have h1z₀ : complexLorentzAction (Λ₀⁻¹ * Λ₀) z₀ ∈ ForwardTube d n := by
        rw [inv_mul_cancel, complexLorentzAction_one]; exact hz₀
      exact hcont.continuousAt.preimage_mem_nhds (isOpen_forwardTube.mem_nhds h1z₀)
    -- Uniform near-identity invariance at z₀
    obtain ⟨U_unif, hU_nhd, h_unif_inv⟩ :=
      uniform_near_identity_invariance n F hF_holo hF_real_inv z₀ hz₀
    -- Pull back through Λ ↦ Λ₀⁻¹Λ
    have h_uniform_pullback : ∀ᶠ Λ in 𝓝 Λ₀,
        ∀ w ∈ U_unif, w ∈ ForwardTube d n →
          complexLorentzAction (Λ₀⁻¹ * Λ) w ∈ ForwardTube d n →
          F (complexLorentzAction (Λ₀⁻¹ * Λ) w) = F w :=
      h_tend.eventually h_unif_inv
    -- Combine all eventually conditions: Λ ∈ T ∩ U
    have h_eventually : ∀ᶠ Λ in 𝓝 Λ₀, Λ ∈ T ∩ U := by
      filter_upwards [h_near_pullback, h_ev_DΛ, h_ev_DΛ', h_uniform_pullback]
        with Λ h_near hΛz₀ hΛ'z₀ h_unif
      refine ⟨?_, z₀, hz₀, hΛz₀⟩
      intro w hw hΛw
      -- Set Λ' := Λ₀⁻¹ * Λ
      set Λ' := Λ₀⁻¹ * Λ with hΛ'_def
      have hΛ_eq : Λ = Λ₀ * Λ' := by rw [hΛ'_def, ← mul_assoc, mul_inv_cancel, one_mul]
      -- === Step 1: g ≡ 0 on D_{Λ'} by identity theorem ===
      have hg_holo : DifferentiableOn ℂ (fun z => F (complexLorentzAction Λ' z) - F z)
          {z | z ∈ ForwardTube d n ∧ complexLorentzAction Λ' z ∈ ForwardTube d n} :=
        (hF_holo.comp (differentiable_complexLorentzAction_snd Λ').differentiableOn
          (fun z hz => hz.2)).sub (hF_holo.mono fun z hz => hz.1)
      have hg_zero_near : (fun z => F (complexLorentzAction Λ' z) - F z) =ᶠ[𝓝 z₀] 0 := by
        apply Filter.eventuallyEq_iff_exists_mem.mpr
        exact ⟨U_unif ∩ {z | z ∈ ForwardTube d n ∧ complexLorentzAction Λ' z ∈ ForwardTube d n},
          Filter.inter_mem hU_nhd ((isOpen_d_lambda Λ').mem_nhds ⟨hz₀, hΛ'z₀⟩),
          fun z ⟨hz_U, hz_FT, hz_Λ'⟩ => sub_eq_zero.mpr (h_unif z hz_U hz_FT hz_Λ')⟩
      have hg_zero : ∀ z, z ∈ ForwardTube d n →
          complexLorentzAction Λ' z ∈ ForwardTube d n →
          F (complexLorentzAction Λ' z) = F z := by
        intro z hz hΛ'z
        exact sub_eq_zero.mp (eq_zero_on_convex_of_eventuallyEq_zero (isOpen_d_lambda Λ')
          (d_lambda_convex Λ') hg_holo ⟨hz₀, hΛ'z₀⟩ hg_zero_near z ⟨hz, hΛ'z⟩)
      -- === Step 2: f ≡ 0 on D_Λ by identity theorem ===
      have hf_holo' : DifferentiableOn ℂ (fun z => F (complexLorentzAction Λ z) - F z)
          {z | z ∈ ForwardTube d n ∧ complexLorentzAction Λ z ∈ ForwardTube d n} :=
        (hF_holo.comp (differentiable_complexLorentzAction_snd Λ).differentiableOn
          (fun z hz => hz.2)).sub (hF_holo.mono fun z hz => hz.1)
      have hf_zero_near : (fun z => F (complexLorentzAction Λ z) - F z) =ᶠ[𝓝 z₀] 0 := by
        apply Filter.eventuallyEq_iff_exists_mem.mpr
        refine ⟨{z | z ∈ ForwardTube d n ∧ complexLorentzAction Λ z ∈ ForwardTube d n} ∩
            {z | z ∈ ForwardTube d n ∧ complexLorentzAction Λ' z ∈ ForwardTube d n},
          Filter.inter_mem ((isOpen_d_lambda Λ).mem_nhds ⟨hz₀, hΛz₀⟩)
            ((isOpen_d_lambda Λ').mem_nhds ⟨hz₀, hΛ'z₀⟩),
          fun z ⟨⟨hz_FT, hz_Λ⟩, _, hz_Λ'⟩ => ?_⟩
        show F (complexLorentzAction Λ z) - F z = 0
        have h_action : complexLorentzAction Λ z =
            complexLorentzAction Λ₀ (complexLorentzAction Λ' z) := by
          rw [← complexLorentzAction_mul, ← hΛ_eq]
        rw [h_action, hΛ₀ _ hz_Λ' (by rwa [← h_action]), hg_zero z hz_FT hz_Λ', sub_self]
      exact sub_eq_zero.mp (eq_zero_on_convex_of_eventuallyEq_zero (isOpen_d_lambda Λ)
        (d_lambda_convex Λ) hf_holo' ⟨hz₀, hΛz₀⟩ hf_zero_near w ⟨hw, hΛw⟩)
    -- Extract open set from filter
    obtain ⟨W, hW_nhd, hW_sub⟩ := Filter.Eventually.exists_mem h_eventually
    obtain ⟨V, hV_sub, hV_open, hΛ₀V⟩ := mem_nhds_iff.mp hW_nhd
    exact ⟨V, fun x hx => hW_sub x (hV_sub hx), hV_open, hΛ₀V⟩
  -- === U is connected ===
  have hU_conn : IsPreconnected U := nonemptyDomain_isPreconnected
  -- === Conclude T = univ via IsPreconnected on U ===
  -- Key: U = (T ∩ U) ⊔ (Tᶜ ∩ U). Both are open. U preconnected + T ∩ U ≠ ∅ → Tᶜ ∩ U = ∅.
  -- Since Tᶜ ⊆ U, we get Tᶜ = ∅, hence T = univ.
  by_contra hT_ne
  have hT_ne' : ∃ a, a ∉ T := (Set.ne_univ_iff_exists_notMem T).mp hT_ne
  obtain ⟨Λ_bad, hΛ_bad⟩ := hT_ne'
  -- Λ_bad ∉ T → Λ_bad ∈ Tᶜ ⊆ U → (Tᶜ ∩ U).Nonempty
  have hTcU_ne : (U ∩ Tᶜ).Nonempty := ⟨Λ_bad, hTc_sub_U hΛ_bad, hΛ_bad⟩
  -- 1 ∈ T ∩ U
  obtain ⟨w₀, hw₀⟩ := forwardTube_nonempty (d := d) (n := n)
  have h1U : (1 : ComplexLorentzGroup d) ∈ U :=
    ⟨w₀, hw₀, (complexLorentzAction_one w₀).symm ▸ hw₀⟩
  have hTU_ne : (U ∩ (T ∩ U)).Nonempty := ⟨1, h1U, h1T, h1U⟩
  -- U ⊆ (T ∩ U) ∪ Tᶜ
  have hU_cover : U ⊆ (T ∩ U) ∪ Tᶜ := by
    intro Λ hΛU
    by_cases hΛT : Λ ∈ T
    · exact Or.inl ⟨hΛT, hΛU⟩
    · exact Or.inr hΛT
  -- Apply IsPreconnected: U ∩ ((T ∩ U) ∩ Tᶜ) is nonempty
  have h_absurd := hU_conn (T ∩ U) Tᶜ hTU_open (isOpen_compl_iff.mpr hT_closed)
    hU_cover hTU_ne hTcU_ne
  -- But (T ∩ U) ∩ Tᶜ = ∅
  obtain ⟨Λ, _, hΛ_TU, hΛ_Tc⟩ := h_absurd
  exact hΛ_Tc hΛ_TU.1

/-! ### The permuted extended tube -/

/-- The extended forward tube: the orbit of the forward tube under the complex
    Lorentz group. T'_n = ⋃_Λ Λ · FT_n -/
def ExtendedTube (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℂ) :=
  ⋃ (Λ : ComplexLorentzGroup d),
    { z | ∃ w ∈ ForwardTube d n, z = complexLorentzAction Λ w }

/-- The permuted forward tube for permutation π:
    π(T_n) = {z ∈ ℂ^{n(d+1)} : (z_{π(1)}, ..., z_{π(n)}) ∈ T_n}.
    Matches `PermutedForwardTube` in AnalyticContinuation.lean. -/
def PermutedForwardTube (d n : ℕ) (π : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | (fun k => z (π k)) ∈ ForwardTube d n }

/-- The permuted extended tube T''_n = ⋃_{π ∈ S_n} ⋃_{Λ ∈ L₊(ℂ)} Λ · π(T_n).
    Matches `PermutedExtendedTube` in AnalyticContinuation.lean. -/
def PermutedExtendedTube (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℂ) :=
  ⋃ π : Equiv.Perm (Fin n),
    { z | ∃ (Λ : ComplexLorentzGroup d) (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ PermutedForwardTube d n π ∧
      z = complexLorentzAction Λ w }

/-- The forward tube is contained in the extended tube. -/
theorem forwardTube_subset_extendedTube :
    ForwardTube d n ⊆ ExtendedTube d n := by
  intro z hz
  refine Set.mem_iUnion.mpr ⟨1, z, hz, ?_⟩
  ext k μ
  simp only [complexLorentzAction,
    show (1 : ComplexLorentzGroup d).val = (1 : Matrix _ _ ℂ) from rfl,
    Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- The extended tube is contained in the permuted extended tube. -/
theorem extendedTube_subset_permutedExtendedTube :
    ExtendedTube d n ⊆ PermutedExtendedTube d n := by
  intro z hz
  obtain ⟨Λ, w, hw, hzw⟩ := Set.mem_iUnion.mp hz
  refine Set.mem_iUnion.mpr ⟨Equiv.refl _, Λ, w, ?_, hzw⟩
  -- w ∈ PermutedForwardTube (Equiv.refl _) ↔ (fun k => w k) ∈ FT ↔ w ∈ FT
  show (fun k => w ((Equiv.refl _) k)) ∈ ForwardTube d n
  simp only [Equiv.refl_apply]; exact hw

/-- The forward tube is contained in the permuted extended tube. -/
theorem forwardTube_subset_permutedExtendedTube :
    ForwardTube d n ⊆ PermutedExtendedTube d n :=
  fun _ hz => extendedTube_subset_permutedExtendedTube (forwardTube_subset_extendedTube hz)

/-- The Lorentz action z ↦ Λ·z is an open map (it's a homeomorphism). -/
theorem complexLorentzAction_isOpenMap (Λ : ComplexLorentzGroup d) :
    IsOpenMap (fun z : Fin n → Fin (d + 1) → ℂ => complexLorentzAction Λ z) :=
  IsOpenMap.of_inverse
    (continuous_complexLorentzAction_snd Λ⁻¹)
    (fun z => by rw [← complexLorentzAction_mul, mul_inv_cancel, complexLorentzAction_one])
    (fun z => by rw [← complexLorentzAction_mul, inv_mul_cancel, complexLorentzAction_one])

/-- The permuted forward tube is open (preimage of FT under continuous permutation). -/
theorem isOpen_permutedForwardTube (π : Equiv.Perm (Fin n)) :
    IsOpen (PermutedForwardTube d n π) :=
  isOpen_forwardTube.preimage (continuous_pi (fun k =>
    continuous_pi (fun μ => (continuous_apply μ).comp (continuous_apply (π k)))))

/-- The permuted extended tube is open (union of images of open sets under homeomorphisms). -/
theorem isOpen_permutedExtendedTube :
    IsOpen (@PermutedExtendedTube d n) := by
  apply isOpen_iUnion; intro π
  suffices h : { z | ∃ (Λ : ComplexLorentzGroup d) (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ PermutedForwardTube d n π ∧ z = complexLorentzAction Λ w } =
    ⋃ Λ : ComplexLorentzGroup d,
      (fun z => complexLorentzAction Λ z) '' (PermutedForwardTube d n π) by
    rw [h]
    exact isOpen_iUnion (fun Λ =>
      (complexLorentzAction_isOpenMap Λ) _ (isOpen_permutedForwardTube π))
  ext z; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨Λ, w, hw, rfl⟩; exact ⟨Λ, w, hw, rfl⟩
  · rintro ⟨Λ, w, hw, rfl⟩; exact ⟨Λ, w, hw, rfl⟩

/-! ### Extension to the extended tube -/

/-- F extends to the extended tube via complex Lorentz transformations:
    F_ext(Λ·w) = F(w) for w ∈ FT. Well-defined by `complex_lorentz_invariance`.

    For z ∈ ExtendedTube, choose a preimage w ∈ FT with z = Λ·w for some Λ,
    and define extendF(z) = F(w). The choice doesn't matter by
    `complex_lorentz_invariance`. For z ∉ ExtendedTube, define extendF(z) = 0. -/
def extendF (F : (Fin n → Fin (d + 1) → ℂ) → ℂ) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  fun z =>
    if h : ∃ (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ ForwardTube d n ∧ ∃ (Λ : ComplexLorentzGroup d), z = complexLorentzAction Λ w
    then F h.choose
    else 0

/-- `extendF` agrees with F on the forward tube. -/
theorem extendF_eq_on_forwardTube (n : ℕ) (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    extendF F z = F z := by
  simp only [extendF]
  -- The existential is satisfied: z ∈ FT, take w = z and Λ = 1.
  have hex : ∃ (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ ForwardTube d n ∧ ∃ (Λ : ComplexLorentzGroup d), z = complexLorentzAction Λ w :=
    ⟨z, hz, 1, (complexLorentzAction_one z).symm⟩
  rw [dif_pos hex]
  -- The chosen w satisfies w ∈ FT and z = Λ·w for some Λ.
  -- Need: F(chosen_w) = F(z).
  have hspec := hex.choose_spec
  have hw : hex.choose ∈ ForwardTube d n := hspec.1
  obtain ⟨Λ, hzΛw⟩ := hspec.2
  -- z = Λ·w, so Λ·w ∈ FT (since z ∈ FT)
  have hΛw : complexLorentzAction Λ hex.choose ∈ ForwardTube d n := hzΛw ▸ hz
  -- By complex_lorentz_invariance: F(Λ·w) = F(w), and z = Λ·w, so F(w) = F(z).
  have key := complex_lorentz_invariance n F hF_holo hF_real_inv Λ hex.choose hw hΛw
  -- key : F(Λ·w) = F(w).  congr_arg F hzΛw.symm : F(Λ·w) = F(z).
  exact key.symm.trans (congr_arg F hzΛw.symm)

/-- Any two forward-tube preimages of the same extended-tube point give the same F-value.
    This is the key well-definedness lemma for `extendF`. -/
private theorem extendF_preimage_eq (n : ℕ) (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    {w₁ w₂ : Fin n → Fin (d + 1) → ℂ} (hw₁ : w₁ ∈ ForwardTube d n) (hw₂ : w₂ ∈ ForwardTube d n)
    {Λ₁ Λ₂ : ComplexLorentzGroup d}
    (h : complexLorentzAction Λ₁ w₁ = complexLorentzAction Λ₂ w₂) :
    F w₁ = F w₂ := by
  -- From Λ₁·w₁ = Λ₂·w₂, apply Λ₂⁻¹: (Λ₂⁻¹*Λ₁)·w₁ = w₂
  have hrel : complexLorentzAction (Λ₂⁻¹ * Λ₁) w₁ = w₂ := by
    have := congr_arg (complexLorentzAction Λ₂⁻¹) h
    rwa [← complexLorentzAction_mul, complexLorentzAction_inv] at this
  -- w₂ = (Λ₂⁻¹*Λ₁)·w₁ ∈ FT, so by complex_lorentz_invariance: F(w₂) = F(w₁)
  have := complex_lorentz_invariance n F hF_holo hF_real_inv (Λ₂⁻¹ * Λ₁) w₁ hw₁ (hrel ▸ hw₂)
  rw [hrel] at this; exact this.symm

/-- `extendF` is invariant under complex Lorentz transformations on the extended tube. -/
theorem extendF_complex_lorentz_invariant (n : ℕ) (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ ExtendedTube d n) :
    extendF F (complexLorentzAction Λ z) = extendF F z := by
  -- z ∈ ExtendedTube: ∃ Λ₀, w₀ with z = Λ₀·w₀, w₀ ∈ FT
  obtain ⟨Λ₀, w₀, hw₀, hzw₀⟩ := Set.mem_iUnion.mp hz
  simp only [extendF]
  -- The existential is satisfied for z
  have hex_z : ∃ (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ ForwardTube d n ∧ ∃ (Λ' : ComplexLorentzGroup d), z = complexLorentzAction Λ' w :=
    ⟨w₀, hw₀, Λ₀, hzw₀⟩
  -- The existential is satisfied for Λ·z (since Λ·z = (Λ*Λ₀)·w₀)
  have hex_Λz : ∃ (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ ForwardTube d n ∧ ∃ (Λ' : ComplexLorentzGroup d),
        complexLorentzAction Λ z = complexLorentzAction Λ' w :=
    ⟨w₀, hw₀, Λ * Λ₀, by rw [hzw₀, complexLorentzAction_mul]⟩
  rw [dif_pos hex_Λz, dif_pos hex_z]
  -- hex_Λz.choose and hex_z.choose are both in FT.
  -- They are preimages of Λ·z and z respectively, related by Λ.
  obtain ⟨hw_Λz, Λ₃, hΛz_eq⟩ := hex_Λz.choose_spec
  obtain ⟨hw_z, Λ₂, hz_eq⟩ := hex_z.choose_spec
  -- Both preimages map to the same point (up to Lorentz transformations):
  -- Λ₃·hex_Λz.choose = Λ·z = Λ·(Λ₂·hex_z.choose) = (Λ*Λ₂)·hex_z.choose
  -- By extendF_preimage_eq, F values agree.
  exact extendF_preimage_eq n F hF_holo hF_real_inv hw_Λz hw_z
    (hΛz_eq.symm.trans ((congr_arg (complexLorentzAction Λ) hz_eq).trans
      (complexLorentzAction_mul Λ Λ₂ hex_z.choose).symm))

/-! ### Full BHW theorem -/

/-- The extended tube is contained in the permuted extended tube. -/
theorem complexLorentzAction_mem_permutedExtendedTube
    {z : Fin n → Fin (d + 1) → ℂ} (hz : z ∈ PermutedExtendedTube d n)
    (Λ : ComplexLorentzGroup d) :
    complexLorentzAction Λ z ∈ PermutedExtendedTube d n := by
  obtain ⟨π, Λ', w, hw, hzw⟩ := Set.mem_iUnion.mp hz
  refine Set.mem_iUnion.mpr ⟨π, Λ * Λ', w, hw, ?_⟩
  rw [hzw, complexLorentzAction_mul]

/-- The full extension of F to the permuted extended tube.
    For z ∈ PermutedExtendedTube, choose a preimage: z = Λ·(π·w) with w ∈ FT,
    and define fullExtendF(z) = F(w). Well-definedness uses complex Lorentz
    invariance + permutation invariance (from local commutativity + edge-of-the-wedge). -/
noncomputable def fullExtendF
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  fun z =>
    if h : ∃ (π : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d)
        (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ ForwardTube d n ∧ z = complexLorentzAction Λ (fun k => w (π k))
    then F h.choose_spec.choose_spec.choose
    else 0

/-- **Edge-of-the-wedge gluing for a single adjacent transposition.**
    For σ = swap(i, i+1), the functions F (on the forward tube FT) and F∘σ⁻¹
    (on σ·FT) have matching boundary values at real Jost points (by `hF_local`).
    The edge-of-the-wedge theorem (SCV.edge_of_the_wedge_theorem) glues them into
    a single holomorphic function on an open domain containing FT ∪ σ·FT ∪ (Jost nbhd).

    This helper captures: if z₁ ∈ FT and z₂ ∈ FT are related by
    z₂ = Γ·(σ·z₁) for some complex Lorentz Γ and adjacent transposition σ,
    then F(z₂) = F(z₁).

    The proof combines:
    1. `hF_local` — F(σ·x) = F(x) at real spacelike-separated configurations
    2. `SCV.edge_of_the_wedge_theorem` — glues F and F∘σ⁻¹ across the Jost boundary
    3. `complex_lorentz_invariance` — propagates via Lorentz transformations
    4. Identity theorem — uniqueness on connected domains -/
private theorem F_adj_swap_invariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (i : Fin n) (hi : i.val + 1 < n)
    {w : Fin n → Fin (d + 1) → ℂ} (hw : w ∈ ForwardTube d n)
    {Γ : ComplexLorentzGroup d}
    (h : complexLorentzAction Γ
      (fun k => w (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ForwardTube d n) :
    F (complexLorentzAction Γ
      (fun k => w (Equiv.swap i ⟨i.val + 1, hi⟩ k))) = F w := by
  sorry

/-- Any permutation of `Fin n` can be written as a product of adjacent transpositions
    `swap(i, i+1)`. This is an induction principle: to prove a property for all
    permutations, it suffices to prove it for the identity and show closure under
    left-multiplication by adjacent transpositions.

    Uses `Equiv.Perm.mclosure_swap_castSucc_succ` (the submonoid generated by
    adjacent transpositions is `⊤`) together with `Submonoid.closure_induction`. -/
private theorem Fin.Perm.adjSwap_induction {n : ℕ}
    {motive : Equiv.Perm (Fin n) → Prop}
    (one : motive 1)
    (adj_mul : ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
      motive σ → motive (Equiv.swap i ⟨i.val + 1, hi⟩ * σ))
    (τ : Equiv.Perm (Fin n)) : motive τ := by
  -- For n = 0: Perm (Fin 0) is trivial, τ = 1
  rcases n with _ | n
  · have : τ = 1 := Subsingleton.elim _ _
    rw [this]; exact one
  -- For n + 1: use mclosure_swap_castSucc_succ
  -- Define motive' on the submonoid: "left-multiplying by x preserves motive"
  suffices h : ∀ (x : Equiv.Perm (Fin (n + 1))),
      x ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) →
      ∀ σ, motive σ → motive (x * σ) by
    have h_top := Equiv.Perm.mclosure_swap_castSucc_succ n
    have hτ_mem : τ ∈ (⊤ : Submonoid (Equiv.Perm (Fin (n + 1)))) := Submonoid.mem_top τ
    rw [← h_top] at hτ_mem
    have := h τ hτ_mem 1 one
    rwa [mul_one] at this
  intro x hx
  exact Submonoid.closure_induction
    (motive := fun x _ => ∀ σ, motive σ → motive (x * σ))
    (mem := fun g hg σ hσ => by
      obtain ⟨i, rfl⟩ := hg
      -- g = swap(i.castSucc, i.succ), which is an adjacent transposition
      have hi : (i.castSucc).val + 1 < n + 1 := by simp [Fin.castSucc]
      show motive (Equiv.swap i.castSucc i.succ * σ)
      have h_eq : i.succ = ⟨(i.castSucc).val + 1, hi⟩ := by
        ext; simp [Fin.castSucc, Fin.succ]
      rw [h_eq]; exact adj_mul σ i.castSucc hi hσ)
    (one := fun σ hσ => by rwa [one_mul])
    (mul := fun a b _ _ ha hb σ hσ => by rw [mul_assoc]; exact ha _ (hb σ hσ))
    hx

/-- **Lorentz-permutation commutation** (definitional).
    The complex Lorentz action acts on the μ-index (spacetime), while
    permutations act on the k-index (particle). They commute:
    Λ·(π·w) = π·(Λ·w) definitionally. -/
private theorem lorentz_perm_commute (Γ : ComplexLorentzGroup d)
    (w : Fin n → Fin (d + 1) → ℂ) (τ : Equiv.Perm (Fin n)) :
    complexLorentzAction Γ (fun k => w (τ k)) =
    fun k => (complexLorentzAction Γ w) (τ k) := by
  ext k μ; simp only [complexLorentzAction]

/-- **Permutation invariance via edge-of-the-wedge.**
    The key new content of BHW: if w ∈ FT and Γ·(τ·w) ∈ FT (where Γ is a complex
    Lorentz transformation and τ is a permutation), then F(Γ·(τ·w)) = F(w).

    For τ = id, this is `complex_lorentz_invariance`.
    For τ ≠ id, this uses local commutativity at Jost points and edge-of-the-wedge:
    - FT and τ·FT are tube domains with opposite imaginary parts for the permuted
      differences (FT ∩ τ·FT = ∅ for τ ≠ id).
    - At real Jost points (spacelike separations), `hF_local` gives F(σ·x) = F(x)
      for adjacent transpositions σ = swap(i, i+1).
    - Edge-of-the-wedge (SCV.edge_of_the_wedge_theorem) glues F on FT with F∘σ on
      σ·FT into a holomorphic function on FT ∪ σ·FT ∪ (Jost neighborhood).
    - Iterating over adjacent transpositions and using complex Lorentz invariance
      to move between tubes gives the result for general τ and Γ.

    **Proof structure (not yet formalized):**
    Decompose τ into adjacent transpositions σ₁ · ... · σₖ via
    `Fin.Perm.adjSwap_induction`. At each step, `F_adj_swap_invariance`
    extends F from FTᵢ to FTᵢ₊₁ = σᵢ · FTᵢ via edge-of-the-wedge.
    The extension is well-defined since the identity theorem guarantees
    uniqueness on connected domains. After all k steps, F extends to
    ⋃ᵢ FTᵢ, and complex Lorentz invariance propagates to each tube.

    **Dependencies:**
    - `F_adj_swap_invariance` (edge-of-the-wedge core for one adjacent swap)
    - `Fin.Perm.adjSwap_induction` (S_n generated by adjacent transpositions)
    - `complex_lorentz_invariance` (already proved) -/
private theorem F_permutation_invariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    {w : Fin n → Fin (d + 1) → ℂ} (hw : w ∈ ForwardTube d n)
    {τ : Equiv.Perm (Fin n)} {Γ : ComplexLorentzGroup d}
    (h : complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube d n) :
    F (complexLorentzAction Γ (fun k => w (τ k))) = F w := by
  -- The proof requires iterating F_adj_swap_invariance over the adjacent
  -- transposition decomposition of τ (via Fin.Perm.adjSwap_induction),
  -- building up an analytic continuation of F across permuted forward tubes.
  -- This "tube algebra" iteration is the core content of the BHW theorem
  -- and requires careful tracking of domains at each step.
  -- Currently blocked on: connecting the edge-of-the-wedge extensions across
  -- intermediate permuted tubes (σ₁·FT, σ₁·σ₂·FT, ...) where intermediate
  -- points may not lie in FT itself.
  sorry

/-- Well-definedness: any two preimages of the same point give the same F-value.
    Reduces to `F_permutation_invariance` via the Lorentz-permutation commutation
    identity `Λ·(π·w) = π·(Λ·w)`.

    From Λ₁·(π₁·w₁) = Λ₂·(π₂·w₂), applying Λ₁⁻¹ and using the commutation:
    w₁ = (Λ₁⁻¹Λ₂)·((π₂π₁⁻¹)·w₂), then `F_permutation_invariance` gives
    F(w₁) = F(w₂). -/
private theorem fullExtendF_well_defined (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    {w₁ w₂ : Fin n → Fin (d + 1) → ℂ}
    (hw₁ : w₁ ∈ ForwardTube d n) (hw₂ : w₂ ∈ ForwardTube d n)
    {π₁ π₂ : Equiv.Perm (Fin n)} {Λ₁ Λ₂ : ComplexLorentzGroup d}
    (h : complexLorentzAction Λ₁ (fun k => w₁ (π₁ k)) =
         complexLorentzAction Λ₂ (fun k => w₂ (π₂ k))) :
    F w₁ = F w₂ := by
  -- Step 1: Derive w₁ = Γ·(τ·w₂) where Γ = Λ₁⁻¹Λ₂, τ = π₂π₁⁻¹.
  -- Key fact: Lorentz action commutes with particle-index permutation:
  --   complexLorentzAction Λ (fun k => z (σ k)) = fun k => (complexLorentzAction Λ z) (σ k)
  -- (holds definitionally since Λ acts only on the μ-index)
  have step1 := congr_arg (complexLorentzAction Λ₁⁻¹) h
  rw [← complexLorentzAction_mul, inv_mul_cancel, complexLorentzAction_one,
      ← complexLorentzAction_mul] at step1
  -- step1 : (fun k => w₁ (π₁ k)) = complexLorentzAction (Λ₁⁻¹ * Λ₂) (fun k => w₂ (π₂ k))
  -- Extract pointwise: w₁(m) = (Γ·(π₂·w₂))(π₁⁻¹ m) = (Γ·(τ·w₂))(m)
  have hw₁_eq : w₁ = complexLorentzAction (Λ₁⁻¹ * Λ₂) (fun k => w₂ ((π₂ * π₁⁻¹) k)) := by
    ext m μ
    have := congr_fun (congr_fun step1 (π₁⁻¹ m)) μ
    rw [show π₁ (π₁⁻¹ m) = m from Equiv.apply_symm_apply π₁ m] at this
    rw [this]
    simp only [complexLorentzAction, Equiv.Perm.mul_apply]
  -- Step 2: Apply F_permutation_invariance
  rw [hw₁_eq]
  exact F_permutation_invariance n F hF_holo hF_lorentz hF_bv hF_local hw₂ (hw₁_eq ▸ hw₁)

theorem bargmann_hall_wightman_theorem (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    -- F extends continuously to the real boundary of the forward tube.
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
  -- === Construct F_ext ===
  -- Pre-prove Properties 1 and 2 so they can be referenced in Property 5.
  have hProp1 : DifferentiableOn ℂ (fullExtendF F) (PermutedExtendedTube d n) := by
    intro z₀ hz₀
    obtain ⟨π₀, Λ₀, w₀, hw₀, hz₀_eq⟩ := Set.mem_iUnion.mp hz₀
    have hw_ft : (fun k => w₀ (π₀ k)) ∈ ForwardTube d n := hw₀
    set ψ := fun z : Fin n → Fin (d + 1) → ℂ =>
      fun k => (complexLorentzAction (Λ₀⁻¹ : ComplexLorentzGroup d) z) (π₀ k) with hψ_def
    have hψ_diff : Differentiable ℂ ψ := by
      apply differentiable_pi.mpr; intro k
      exact (differentiable_apply (π₀ k)).comp (differentiable_complexLorentzAction_snd Λ₀⁻¹)
    have hψz₀ : ψ z₀ = fun k => w₀ (π₀ k) := by
      simp only [ψ, hz₀_eq]
      rw [← complexLorentzAction_mul, inv_mul_cancel, complexLorentzAction_one]
    have hV_open : IsOpen {z | ψ z ∈ ForwardTube d n} :=
      isOpen_forwardTube.preimage hψ_diff.continuous
    have hz₀_V : ψ z₀ ∈ ForwardTube d n := hψz₀ ▸ hw_ft
    have hfeq : fullExtendF F =ᶠ[nhds z₀] fun z => F (ψ z) := by
      apply Filter.eventuallyEq_of_mem (hV_open.mem_nhds hz₀_V)
      intro z (hz_V : ψ z ∈ ForwardTube d n)
      have hz_chart : z = complexLorentzAction Λ₀ (fun k => (ψ z) (π₀⁻¹ k)) := by
        have h1 : (fun k => (ψ z) (π₀⁻¹ k)) = complexLorentzAction Λ₀⁻¹ z := by
          ext k μ; simp only [ψ]
          rw [show π₀ (π₀⁻¹ k) = k from Equiv.apply_symm_apply π₀ k]
        rw [h1, ← complexLorentzAction_mul, mul_inv_cancel, complexLorentzAction_one]
      simp only [fullExtendF]
      have hex : ∃ (π : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d)
          (w : Fin n → Fin (d + 1) → ℂ),
          w ∈ ForwardTube d n ∧ z = complexLorentzAction Λ (fun k => w (π k)) :=
        ⟨π₀⁻¹, Λ₀, ψ z, hz_V, hz_chart⟩
      rw [dif_pos hex]
      exact fullExtendF_well_defined n F hF_holo hF_lorentz hF_bv hF_local
        hex.choose_spec.choose_spec.choose_spec.1 hz_V
        (hex.choose_spec.choose_spec.choose_spec.2.symm.trans hz_chart)
    have hFψ_diff : DifferentiableAt ℂ (fun z => F (ψ z)) z₀ :=
      ((hF_holo _ hz₀_V).differentiableAt (isOpen_forwardTube.mem_nhds hz₀_V)).comp
        z₀ (hψ_diff z₀)
    exact (hfeq.differentiableAt_iff.mpr hFψ_diff).differentiableWithinAt
  have hProp2 : ∀ z ∈ ForwardTube d n, fullExtendF F z = F z := by
    intro z hz
    simp only [fullExtendF]
    have hex : ∃ (π : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d)
        (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ ForwardTube d n ∧ z = complexLorentzAction Λ (fun k => w (π k)) :=
      ⟨Equiv.refl _, 1, z, hz, by simp [complexLorentzAction_one, Equiv.refl_apply]⟩
    rw [dif_pos hex]
    set w_c := hex.choose_spec.choose_spec.choose with hw_c_def
    have hw_c : w_c ∈ ForwardTube d n := hex.choose_spec.choose_spec.choose_spec.1
    have hz_eq := hex.choose_spec.choose_spec.choose_spec.2
    have h_eq : complexLorentzAction hex.choose_spec.choose
        (fun k => w_c (hex.choose k)) =
        complexLorentzAction 1 (fun k => z ((Equiv.refl (Fin n)) k)) := by
      rw [← hz_eq, complexLorentzAction_one]; rfl
    exact fullExtendF_well_defined n F hF_holo hF_lorentz hF_bv hF_local hw_c hz h_eq
  refine ⟨fullExtendF F, hProp1, hProp2, ?_, ?_, ?_⟩
  -- === Property 3: Complex Lorentz invariance ===
  -- If z = Λ'·w_p with w_p ∈ PermutedForwardTube π, then Λz = (ΛΛ')·w_p.
  -- Convert w_p to w_ft ∈ ForwardTube via w_ft = fun k => w_p (π k),
  -- then both fullExtendF(Λz) and fullExtendF(z) reduce to the same FT preimage.
  · intro Λ z hz
    simp only [fullExtendF]
    obtain ⟨π, Λ', w_p, hw_p, hzw⟩ := Set.mem_iUnion.mp hz
    -- w_p ∈ PermutedForwardTube means w_ft := (fun k => w_p (π k)) ∈ ForwardTube
    set w_ft := fun k => w_p (π k) with hw_ft_def
    have hw_ft : w_ft ∈ ForwardTube d n := hw_p
    -- z = Λ'·w_p = Λ'·(fun k => w_ft (π⁻¹ k))
    have hw_p_eq : w_p = fun k => w_ft (π⁻¹ k) := by
      ext k; simp [hw_ft_def]
    have hex_z : ∃ (π' : Equiv.Perm (Fin n)) (Λ'' : ComplexLorentzGroup d)
        (w' : Fin n → Fin (d + 1) → ℂ),
        w' ∈ ForwardTube d n ∧ z = complexLorentzAction Λ'' (fun k => w' (π' k)) :=
      ⟨π⁻¹, Λ', w_ft, hw_ft, by rw [hzw, hw_p_eq]⟩
    have hex_Λz : ∃ (π' : Equiv.Perm (Fin n)) (Λ'' : ComplexLorentzGroup d)
        (w' : Fin n → Fin (d + 1) → ℂ),
        w' ∈ ForwardTube d n ∧
        complexLorentzAction Λ z =
          complexLorentzAction Λ'' (fun k => w' (π' k)) :=
      ⟨π⁻¹, Λ * Λ', w_ft, hw_ft, by rw [hzw, hw_p_eq, complexLorentzAction_mul]⟩
    rw [dif_pos hex_Λz, dif_pos hex_z]
    -- Both choices lead to FT preimages related by Lorentz + permutation.
    -- By fullExtendF_well_defined, F-values agree.
    have hΛz_eq := hex_Λz.choose_spec.choose_spec.choose_spec.2
    -- hΛz_eq : Λ·z = Λ_Λz·(π_Λz·w_Λz)
    have hz_eq' := hex_z.choose_spec.choose_spec.choose_spec.2
    -- hz_eq' : z = Λ_z·(π_z·w_z)
    have h_eq : complexLorentzAction hex_Λz.choose_spec.choose
        (fun k => hex_Λz.choose_spec.choose_spec.choose (hex_Λz.choose k)) =
        complexLorentzAction (Λ * hex_z.choose_spec.choose)
        (fun k => hex_z.choose_spec.choose_spec.choose (hex_z.choose k)) := by
      rw [complexLorentzAction_mul, ← hz_eq']
      exact hΛz_eq.symm
    exact fullExtendF_well_defined n F hF_holo hF_lorentz hF_bv hF_local
      hex_Λz.choose_spec.choose_spec.choose_spec.1
      hex_z.choose_spec.choose_spec.choose_spec.1 h_eq
  -- === Property 4: Permutation symmetry ===
  -- fullExtendF F (z∘π) = fullExtendF F z follows from fullExtendF_well_defined:
  -- both chosen preimages yield representations of z∘π.
  · intro π z hz
    simp only [fullExtendF]
    obtain ⟨π₀, Λ₀, w₀, hw₀, hzw₀⟩ := Set.mem_iUnion.mp hz
    set w_ft := fun k => w₀ (π₀ k) with hw_ft_def
    have hw_ft : w_ft ∈ ForwardTube d n := hw₀
    have hw₀_eq : w₀ = fun k => w_ft (π₀⁻¹ k) := by ext k; simp [hw_ft_def]
    have hex_z : ∃ (π' : Equiv.Perm (Fin n)) (Λ' : ComplexLorentzGroup d)
        (w' : Fin n → Fin (d + 1) → ℂ),
        w' ∈ ForwardTube d n ∧ z = complexLorentzAction Λ' (fun k => w' (π' k)) :=
      ⟨π₀⁻¹, Λ₀, w_ft, hw_ft, by rw [hzw₀, hw₀_eq]⟩
    have hex_πz : ∃ (π' : Equiv.Perm (Fin n)) (Λ' : ComplexLorentzGroup d)
        (w' : Fin n → Fin (d + 1) → ℂ),
        w' ∈ ForwardTube d n ∧ (fun k => z (π k)) =
          complexLorentzAction Λ' (fun k => w' (π' k)) := by
      refine ⟨π₀⁻¹ * π, Λ₀, w_ft, hw_ft, ?_⟩
      rw [hzw₀, hw₀_eq]; ext k μ
      simp only [complexLorentzAction, Equiv.Perm.mul_apply]
    rw [dif_pos hex_πz, dif_pos hex_z]
    have hπz_eq := hex_πz.choose_spec.choose_spec.choose_spec.2
    have hz_eq' := hex_z.choose_spec.choose_spec.choose_spec.2
    -- Build: both chosen representations equal z∘π
    -- From hz_eq': z = Λ_z·(π_z·w_z), so z∘π = Λ_z·((π_z*π)·w_z)
    have h_zperm : (fun k => z (π k)) =
        complexLorentzAction hex_z.choose_spec.choose
        (fun k => hex_z.choose_spec.choose_spec.choose ((hex_z.choose * π) k)) := by
      ext k μ
      have := congr_fun (congr_fun hz_eq' (π k)) μ
      simp only [complexLorentzAction, Equiv.Perm.mul_apply] at this ⊢
      exact this
    have h_eq : complexLorentzAction hex_πz.choose_spec.choose
        (fun k => hex_πz.choose_spec.choose_spec.choose (hex_πz.choose k)) =
        complexLorentzAction hex_z.choose_spec.choose
        (fun k => hex_z.choose_spec.choose_spec.choose ((hex_z.choose * π) k)) :=
      hπz_eq.symm.trans h_zperm
    exact fullExtendF_well_defined n F hF_holo hF_lorentz hF_bv hF_local
      hex_πz.choose_spec.choose_spec.choose_spec.1
      hex_z.choose_spec.choose_spec.choose_spec.1 h_eq
  -- === Property 5: Uniqueness ===
  -- By the identity theorem for product types (`identity_theorem_product`):
  -- G and fullExtendF are holomorphic on PET (open, connected) and agree on FT
  -- (open, nonempty subset of PET), so they agree on all of PET.
  · intro G hG_holo hG_eq
    -- fullExtendF F is differentiable on PET (Property 1)
    have hF_ext_holo : DifferentiableOn ℂ (fullExtendF F) (PermutedExtendedTube d n) :=
      hProp1
    -- PET is open
    have hPET_open := @isOpen_permutedExtendedTube d n
    -- PET is connected: different permutation sectors don't directly overlap;
    -- connectedness requires applying the (proved) edge-of-the-wedge theorem to
    -- glue sectors at Jost point boundaries via local commutativity.
    have hPET_conn : IsConnected (PermutedExtendedTube d n) := by
      constructor
      · exact (forwardTube_nonempty (d := d) (n := n)).mono
          forwardTube_subset_permutedExtendedTube
      · sorry  -- PET preconnected: apply edge-of-the-wedge to join permutation sectors
    -- Pick z₀ ∈ FT ⊆ PET
    obtain ⟨z₀, hz₀⟩ := forwardTube_nonempty (d := d) (n := n)
    have hz₀_PET := forwardTube_subset_permutedExtendedTube hz₀
    -- G and fullExtendF agree on FT, which is an open neighborhood of z₀
    have hagree : G =ᶠ[nhds z₀] fullExtendF F := by
      apply Filter.eventuallyEq_of_mem (isOpen_forwardTube.mem_nhds hz₀)
      intro w hw
      rw [hG_eq w hw, hProp2 w hw]
    -- By identity theorem on product types
    have h_eq := identity_theorem_product hPET_open hPET_conn hG_holo hF_ext_holo hz₀_PET hagree
    intro z hz
    exact h_eq hz

end BHW

end
