/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Tensor Products of Schwartz Functions

This file provides the external tensor product of Schwartz functions, which is
essential for the OS reconstruction theorem and the Wightman inner product.

## Main Definitions

* `SchwartzMap.tensorProduct` - The external tensor product f ⊗ g of Schwartz functions
* `SchwartzMap.conj` - Complex conjugation of a Schwartz function
* `SchwartzMap.conjTensorProduct` - The conjugated tensor product f̄ ⊗ g

## Mathematical Background

Given f ∈ S(ℝ^{m·d}, ℂ) and g ∈ S(ℝ^{k·d}, ℂ), the **external tensor product** is:
  (f ⊗ g)(x₁,...,x_{m+k}) = f(x₁,...,xₘ) · g(x_{m+1},...,x_{m+k})

This is a Schwartz function in S(ℝ^{(m+k)·d}, ℂ) because:
1. **Smoothness**: f and g are smooth, projections are smooth (linear), and multiplication
   of complex numbers is smooth (bilinear), so the composition is smooth.
2. **Rapid decay**: By the Leibniz rule for derivatives of products, each derivative of f⊗g
   is a sum of terms involving derivatives of f and g separately. The rapid decay of f and g
   on their respective variables gives rapid decay of f⊗g on all variables.

## References

* Osterwalder-Schrader, "Axioms for Euclidean Green's Functions" (1973), §2-3
* Reed-Simon, "Methods of Modern Mathematical Physics I", §V.3
-/

noncomputable section

open scoped SchwartzMap
open Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ### Complex Conjugation of Schwartz Functions -/

/-- Complex conjugation of a ℂ-valued Schwartz function.
    If f ∈ S(E, ℂ), then f̄ ∈ S(E, ℂ) where f̄(x) = conj(f(x)).

    This is well-defined because:
    1. conj : ℂ → ℂ is smooth (it's ℝ-linear)
    2. conj preserves norms: ‖conj(z)‖ = ‖z‖
    So f̄ has the same decay bounds as f. -/
def SchwartzMap.conj (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) where
  toFun := fun x => starRingEnd ℂ (f x)
  smooth' := by
    -- conj = Complex.conjCLE is a ContinuousLinearEquiv over ℝ, hence smooth
    exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp f.smooth'
  decay' := by
    intro k n
    -- Complex conjugation is a linear isometry, so ‖iteratedFDeriv ℝ n (conj ∘ f) x‖ = ‖iteratedFDeriv ℝ n f x‖
    obtain ⟨C, hC⟩ := f.decay' k n
    exact ⟨C, fun x => by
      have := Complex.conjLIE.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) f x n
      simp only [Function.comp_def] at this
      -- starRingEnd ℂ and conjLIE are definitionally equal
      have heq : (fun x => (starRingEnd ℂ) (f x)) = (fun x => Complex.conjLIE (f x)) := rfl
      rw [heq, this]; exact hC x⟩

/-- Conjugation preserves the pointwise values. -/
@[simp]
theorem SchwartzMap.conj_apply (f : 𝓢(E, ℂ)) (x : E) :
    f.conj x = starRingEnd ℂ (f x) := rfl

/-- Conjugation is an involution. -/
theorem SchwartzMap.conj_conj (f : 𝓢(E, ℂ)) :
    f.conj.conj = f := by
  ext x
  simp [SchwartzMap.conj_apply]

/-! ### Argument Reversal for n-Point Functions -/

/-- Reversal of argument order for Schwartz functions on Fin n → E.
    Given f ∈ S(Fin n → E, ℂ), define f_rev(x₁,...,xₙ) = f(xₙ,...,x₁).

    This is well-defined because:
    1. (· ∘ Fin.rev) is a linear isomorphism on (Fin n → E)
    2. Composing a Schwartz function with a linear isomorphism is Schwartz -/
def SchwartzMap.reverse {n : ℕ} (f : 𝓢(Fin n → E, ℂ)) : 𝓢(Fin n → E, ℂ) where
  toFun := fun x => f (fun i => x (Fin.rev i))
  smooth' := by
    -- (· ∘ Fin.rev) is a continuous linear map (each component is a projection)
    exact f.smooth'.comp
      (contDiff_pi.mpr fun i =>
        (ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ => E)
          (Fin.rev i)).contDiff)
  decay' := by
    -- (· ∘ Fin.rev) preserves norms and iteratedFDeriv norms
    intro k l
    obtain ⟨C, hC⟩ := f.decay' k l
    refine ⟨C, fun x => ?_⟩
    -- Build the LinearIsometryEquiv for (· ∘ Fin.rev) directly
    let revEquiv : Fin n ≃ Fin n := ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩
    let revLE : (Fin n → E) ≃ₗ[ℝ] (Fin n → E) :=
      { toFun := fun y i => y (Fin.rev i)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun y i => y (Fin.rev i)
        left_inv := fun y => funext fun i => by simp [Fin.rev_rev]
        right_inv := fun y => funext fun i => by simp [Fin.rev_rev] }
    let revLIE : (Fin n → E) ≃ₗᵢ[ℝ] (Fin n → E) :=
      { revLE with
        norm_map' := fun y => by
          simp only [Pi.norm_def]
          congr 1
          change Finset.univ.sup ((fun b => ‖y b‖₊) ∘ revEquiv.toEmbedding) = _
          simp only [← Finset.sup_map, Finset.univ_map_equiv_to_embedding] }
    have hcomp : (fun x => f (fun i => x (Fin.rev i))) = f ∘ revLIE := rfl
    rw [hcomp, revLIE.norm_iteratedFDeriv_comp_right (𝕜 := ℝ) f x l,
      show ‖x‖ = ‖revLIE x‖ from (revLIE.norm_map x).symm]
    exact hC _

/-- Reversal preserves pointwise values. -/
@[simp]
theorem SchwartzMap.reverse_apply {n : ℕ} (f : 𝓢(Fin n → E, ℂ)) (x : Fin n → E) :
    f.reverse x = f (fun i => x (Fin.rev i)) := rfl

/-- Reversal is an involution. -/
theorem SchwartzMap.reverse_reverse {n : ℕ} (f : 𝓢(Fin n → E, ℂ)) :
    f.reverse.reverse = f := by
  ext x; simp [SchwartzMap.reverse_apply, Fin.rev_rev]

/-- Reversal of zero is zero. -/
@[simp]
theorem SchwartzMap.reverse_zero {n : ℕ} :
    (0 : 𝓢(Fin n → E, ℂ)).reverse = 0 := by
  ext x; simp [SchwartzMap.reverse_apply]

/-- Reversal distributes over addition. -/
@[simp]
theorem SchwartzMap.reverse_add {n : ℕ} (f g : 𝓢(Fin n → E, ℂ)) :
    (f + g).reverse = f.reverse + g.reverse := by
  ext x; simp [SchwartzMap.reverse_apply]

/-- Reversal distributes over negation. -/
@[simp]
theorem SchwartzMap.reverse_neg {n : ℕ} (f : 𝓢(Fin n → E, ℂ)) :
    (-f).reverse = -(f.reverse) := by
  ext x; simp [SchwartzMap.reverse_apply]

/-- Reversal commutes with scalar multiplication. -/
theorem SchwartzMap.reverse_smul {n : ℕ} (c : ℂ) (f : 𝓢(Fin n → E, ℂ)) :
    (c • f).reverse = c • f.reverse := by
  ext x; simp [SchwartzMap.reverse_apply]

/-! ### Borchers Conjugation (Involution) -/

/-- The Borchers conjugation (involution): reverse arguments and conjugate.
    f*(x₁,...,xₙ) = conj(f(xₙ,...,x₁))

    This is the adjoint operation in the Borchers algebra used to define the
    Wightman inner product: ⟨F, G⟩ = W(F⁺ × G) where F⁺ = (f₀*, f₁*, ...).

    Reference: Streater-Wightman, "PCT, Spin and Statistics", §3.4 -/
def SchwartzMap.borchersConj {n : ℕ} (f : 𝓢(Fin n → E, ℂ)) : 𝓢(Fin n → E, ℂ) :=
  f.reverse.conj

/-- Borchers conjugation preserves pointwise values. -/
@[simp]
theorem SchwartzMap.borchersConj_apply {n : ℕ} (f : 𝓢(Fin n → E, ℂ)) (x : Fin n → E) :
    f.borchersConj x = starRingEnd ℂ (f (fun i => x (Fin.rev i))) := rfl

/-- Borchers conjugation is an involution. -/
theorem SchwartzMap.borchersConj_borchersConj {n : ℕ} (f : 𝓢(Fin n → E, ℂ)) :
    f.borchersConj.borchersConj = f := by
  ext x; simp [SchwartzMap.borchersConj_apply, Fin.rev_rev]

/-- Borchers conjugation of zero is zero. -/
@[simp]
theorem SchwartzMap.borchersConj_zero {n : ℕ} :
    (0 : 𝓢(Fin n → E, ℂ)).borchersConj = 0 := by
  ext x; simp [SchwartzMap.borchersConj_apply]

/-- Borchers conjugation distributes over addition. -/
@[simp]
theorem SchwartzMap.borchersConj_add {n : ℕ} (f g : 𝓢(Fin n → E, ℂ)) :
    (f + g).borchersConj = f.borchersConj + g.borchersConj := by
  ext x; simp [SchwartzMap.borchersConj_apply, map_add]

/-- Borchers conjugation distributes over negation. -/
@[simp]
theorem SchwartzMap.borchersConj_neg {n : ℕ} (f : 𝓢(Fin n → E, ℂ)) :
    (-f).borchersConj = -(f.borchersConj) := by
  ext x; simp [SchwartzMap.borchersConj_apply, map_neg]

/-- Borchers conjugation is conjugate-linear in the scalar. -/
theorem SchwartzMap.borchersConj_smul {n : ℕ} (c : ℂ) (f : 𝓢(Fin n → E, ℂ)) :
    (c • f).borchersConj = starRingEnd ℂ c • f.borchersConj := by
  ext x; simp [SchwartzMap.borchersConj_apply, map_mul]

/-! ### External Tensor Product of Schwartz Functions -/

/-- The splitting map: given x : Fin (m+k) → E, extract the first m components.
    This sends x to (x₁, ..., xₘ). -/
def splitFirst (m k : ℕ) (x : Fin (m + k) → E) : Fin m → E :=
  fun i => x (Fin.castAdd k i)

/-- The splitting map: given x : Fin (m+k) → E, extract the last k components.
    This sends x to (x_{m+1}, ..., x_{m+k}). -/
def splitLast (m k : ℕ) (x : Fin (m + k) → E) : Fin k → E :=
  fun j => x (Fin.natAdd m j)

/-- splitFirst is a continuous linear map (projection). -/
theorem splitFirst_continuousLinear (m k : ℕ) :
    Continuous (splitFirst m k : (Fin (m + k) → E) → (Fin m → E)) :=
  continuous_pi fun i => continuous_apply _

/-- splitLast is a continuous linear map (projection). -/
theorem splitLast_continuousLinear (m k : ℕ) :
    Continuous (splitLast m k : (Fin (m + k) → E) → (Fin k → E)) :=
  continuous_pi fun j => continuous_apply _

/-- splitFirst as a ContinuousLinearMap (projection to first m components). -/
noncomputable def splitFirstCLM (m k : ℕ) :
    (Fin (m + k) → E) →L[ℝ] (Fin m → E) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (R := ℝ) (ι := Fin (m + k)) (φ := fun _ => E) (Fin.castAdd k i)

/-- splitLast as a ContinuousLinearMap (projection to last k components). -/
noncomputable def splitLastCLM (m k : ℕ) :
    (Fin (m + k) → E) →L[ℝ] (Fin k → E) :=
  ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (R := ℝ) (ι := Fin (m + k)) (φ := fun _ => E) (Fin.natAdd m j)

@[simp]
theorem splitFirstCLM_apply (m k : ℕ) (x : Fin (m + k) → E) :
    splitFirstCLM m k x = splitFirst m k x := rfl

@[simp]
theorem splitLastCLM_apply (m k : ℕ) (x : Fin (m + k) → E) :
    splitLastCLM m k x = splitLast m k x := rfl

/-- The norm of splitFirst x is at most the norm of x. -/
theorem splitFirst_norm_le (m k : ℕ) (x : Fin (m + k) → E) :
    ‖splitFirst m k x‖ ≤ ‖x‖ := by
  simp only [splitFirst, Pi.norm_def]
  exact_mod_cast Finset.sup_le fun b _ =>
    Finset.le_sup (f := fun j => ‖x j‖₊) (Finset.mem_univ (Fin.castAdd k b))

/-- The norm of splitLast x is at most the norm of x. -/
theorem splitLast_norm_le (m k : ℕ) (x : Fin (m + k) → E) :
    ‖splitLast m k x‖ ≤ ‖x‖ := by
  simp only [splitLast, Pi.norm_def]
  exact_mod_cast Finset.sup_le fun b _ =>
    Finset.le_sup (f := fun j => ‖x j‖₊) (Finset.mem_univ (Fin.natAdd m b))

/-- The operator norm of splitFirstCLM is at most 1. -/
theorem splitFirstCLM_opNorm_le (m k : ℕ) :
    ‖splitFirstCLM m k (E := E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [splitFirstCLM_apply, one_mul]; exact splitFirst_norm_le m k x

/-- The operator norm of splitLastCLM is at most 1. -/
theorem splitLastCLM_opNorm_le (m k : ℕ) :
    ‖splitLastCLM m k (E := E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [splitLastCLM_apply, one_mul]; exact splitLast_norm_le m k x

/-- The norm of x is at most ‖splitFirst x‖ + ‖splitLast x‖.
    This follows from ‖x‖ = max(‖splitFirst x‖, ‖splitLast x‖) ≤ sum. -/
theorem norm_le_splitFirst_add_splitLast (m k : ℕ) (x : Fin (m + k) → E) :
    ‖x‖ ≤ ‖splitFirst m k x‖ + ‖splitLast m k x‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro j
  by_cases hj : j.val < m
  · -- j is in first m components: ‖x j‖ ≤ ‖splitFirst x‖ ≤ sum
    have heq : x j = splitFirst m k x ⟨j.val, hj⟩ := rfl
    rw [heq]
    exact (norm_le_pi_norm _ _).trans (le_add_of_nonneg_right (norm_nonneg _))
  · -- j is in last k components: ‖x j‖ ≤ ‖splitLast x‖ ≤ sum
    push_neg at hj
    have hjk : j.val - m < k := by omega
    have heq : x j = splitLast m k x ⟨j.val - m, hjk⟩ := by
      show x j = x (Fin.natAdd m ⟨j.val - m, hjk⟩)
      congr 1; exact Fin.ext (by simp [Fin.natAdd]; omega)
    rw [heq]
    exact (norm_le_pi_norm _ _).trans (le_add_of_nonneg_left (norm_nonneg _))

/-- The external tensor product of two Schwartz functions.

    Given f ∈ S(Fin m → E, ℂ) and g ∈ S(Fin k → E, ℂ), define:
      (f ⊗ g)(x₁,...,x_{m+k}) = f(x₁,...,xₘ) · g(x_{m+1},...,x_{m+k})

    This is Schwartz because projections are smooth (linear), f and g are smooth,
    multiplication is smooth (bilinear), and the decay bounds combine. -/
def SchwartzMap.tensorProduct {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    𝓢(Fin (m + k) → E, ℂ) where
  toFun := fun x => f (splitFirst m k x) * g (splitLast m k x)
  smooth' := by
    -- f ∘ splitFirst and g ∘ splitLast are smooth (smooth ∘ linear projection)
    -- Their product is smooth (ContDiff.mul)
    apply ContDiff.mul
    · exact f.smooth'.comp (contDiff_pi.mpr fun i =>
        (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (m + k)) (φ := fun _ => E)
          (Fin.castAdd k i)).contDiff)
    · exact g.smooth'.comp (contDiff_pi.mpr fun j =>
        (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (m + k)) (φ := fun _ => E)
          (Fin.natAdd m j)).contDiff)
  decay' := by
    intro p l
    -- Smooth factors (for Leibniz rule)
    -- Note: f.smooth' has order ∞ : ℕ∞, which coerces to ↑∞ : WithTop ℕ∞
    have hfs := f.smooth'.comp (splitFirstCLM m k (E := E)).contDiff
    have hgs := g.smooth'.comp (splitLastCLM m k (E := E)).contDiff
    -- Composition norm bounds: ‖D^j(f ∘ π₁) x‖ ≤ ‖D^j f (π₁ x)‖ (since ‖π₁‖ ≤ 1)
    have hcf : ∀ j (x : Fin (m + k) → E),
        ‖iteratedFDeriv ℝ j (f.toFun ∘ splitFirst m k) x‖ ≤
        ‖iteratedFDeriv ℝ j f.toFun (splitFirst m k x)‖ := by
      intro j x
      rw [show f.toFun ∘ splitFirst m k = f.toFun ∘ ↑(splitFirstCLM m k (E := E)) from rfl,
        (splitFirstCLM m k).iteratedFDeriv_comp_right f.smooth' x
          (by exact_mod_cast le_top)]
      exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _)
          (Finset.prod_le_one (fun _ _ => norm_nonneg _)
            (fun _ _ => splitFirstCLM_opNorm_le m k)))
    have hcg : ∀ j (x : Fin (m + k) → E),
        ‖iteratedFDeriv ℝ j (g.toFun ∘ splitLast m k) x‖ ≤
        ‖iteratedFDeriv ℝ j g.toFun (splitLast m k x)‖ := by
      intro j x
      rw [show g.toFun ∘ splitLast m k = g.toFun ∘ ↑(splitLastCLM m k (E := E)) from rfl,
        (splitLastCLM m k).iteratedFDeriv_comp_right g.smooth' x
          (by exact_mod_cast le_top)]
      exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _)
          (Finset.prod_le_one (fun _ _ => norm_nonneg _)
            (fun _ _ => splitLastCLM_opNorm_le m k)))
    -- Schwartz decay constants (via Choice)
    choose Cf hCf using fun p j => f.decay' p j
    choose Cg hCg using fun p j => g.decay' p j
    -- The total bound constant
    refine ⟨2 ^ p * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
      (Cf p i * Cg 0 (l - i) + Cf 0 i * Cg p (l - i)), fun x => ?_⟩
    -- Step 1: Leibniz rule gives bound on ‖D^l(f⊗g)‖
    have hLeib := norm_iteratedFDeriv_mul_le (n := l) hfs hgs x
      (WithTop.coe_le_coe.mpr (le_top (a := (l : ℕ∞))))
    -- Step 2: Bound ‖x‖^p using norm splitting
    have hnorm_split := norm_le_splitFirst_add_splitLast m k x
    -- Step 3: (a+b)^p ≤ 2^p (a^p + b^p) for a, b ≥ 0
    have add_pow_le : (‖splitFirst m k x‖ + ‖splitLast m k x‖) ^ p ≤
        2 ^ p * (‖splitFirst m k x‖ ^ p + ‖splitLast m k x‖ ^ p) := by
      have hmax : (max ‖splitFirst m k x‖ ‖splitLast m k x‖) ^ p ≤
          ‖splitFirst m k x‖ ^ p + ‖splitLast m k x‖ ^ p := by
        rcases max_cases ‖splitFirst m k x‖ ‖splitLast m k x‖ with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]; exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
        · rw [h]; exact le_add_of_nonneg_left (pow_nonneg (norm_nonneg _) _)
      have h_add_le_2max : ‖splitFirst m k x‖ + ‖splitLast m k x‖ ≤
          2 * max ‖splitFirst m k x‖ ‖splitLast m k x‖ := by
        linarith [le_max_left ‖splitFirst m k x‖ ‖splitLast m k x‖,
                  le_max_right ‖splitFirst m k x‖ ‖splitLast m k x‖]
      calc _ ≤ (2 * max ‖splitFirst m k x‖ ‖splitLast m k x‖) ^ p :=
            pow_le_pow_left₀ (add_nonneg (norm_nonneg _) (norm_nonneg _)) h_add_le_2max _
        _ = (2 : ℝ) ^ p * (max ‖splitFirst m k x‖ ‖splitLast m k x‖) ^ p :=
            mul_pow (2 : ℝ) _ p
        _ ≤ 2 ^ p * (‖splitFirst m k x‖ ^ p + ‖splitLast m k x‖ ^ p) :=
            mul_le_mul_of_nonneg_left hmax (pow_nonneg (by norm_num) _)
    -- Step 4: Main calculation
    have h_pow : ‖x‖ ^ p ≤ 2 ^ p * (‖splitFirst m k x‖ ^ p + ‖splitLast m k x‖ ^ p) :=
      (pow_le_pow_left₀ (norm_nonneg _) hnorm_split _).trans add_pow_le
    -- For each summand, bound using Schwartz decay of f and g
    have h_term : ∀ i ∈ Finset.range (l + 1),
        ‖x‖ ^ p * (↑(l.choose i) * ‖iteratedFDeriv ℝ i f.toFun (splitFirst m k x)‖ *
        ‖iteratedFDeriv ℝ (l - i) g.toFun (splitLast m k x)‖) ≤
        2 ^ p * (↑(l.choose i) * (Cf p i * Cg 0 (l - i) + Cf 0 i * Cg p (l - i))) := by
      intro i _
      -- Name the key quantities for readability
      set a := ‖splitFirst m k x‖ with ha_def
      set b := ‖splitLast m k x‖ with hb_def
      set F := ‖iteratedFDeriv ℝ i f.toFun (splitFirst m k x)‖ with hF_def
      set G := ‖iteratedFDeriv ℝ (l - i) g.toFun (splitLast m k x)‖ with hG_def
      have ha_nn : 0 ≤ a := norm_nonneg _
      have hb_nn : 0 ≤ b := norm_nonneg _
      have hF_nn : 0 ≤ F := norm_nonneg _
      have hG_nn : 0 ≤ G := norm_nonneg _
      -- a^p * F ≤ Cf p i and G ≤ Cg 0 (l-i)
      have hf1 : a ^ p * F ≤ Cf p i := hCf p i (splitFirst m k x)
      have hg1 : G ≤ Cg 0 (l - i) := by
        have := hCg 0 (l - i) (splitLast m k x); simp at this; linarith
      -- F ≤ Cf 0 i and b^p * G ≤ Cg p (l-i)
      have hf2 : F ≤ Cf 0 i := by
        have := hCf 0 i (splitFirst m k x); simp at this; linarith
      have hg2 : b ^ p * G ≤ Cg p (l - i) := hCg p (l - i) (splitLast m k x)
      -- Key: a^p * F * G ≤ Cf(p,i) * Cg(0,l-i)
      have hprod1 : a ^ p * F * G ≤ Cf p i * Cg 0 (l - i) :=
        mul_le_mul hf1 hg1 hG_nn (le_trans (mul_nonneg (pow_nonneg ha_nn _) hF_nn) hf1)
      -- Key: b^p * F * G = F * (b^p * G) ≤ Cf(0,i) * Cg(p,l-i)
      have hprod2 : b ^ p * F * G ≤ Cf 0 i * Cg p (l - i) := by
        calc b ^ p * F * G = F * (b ^ p * G) := by ring
          _ ≤ Cf 0 i * Cg p (l - i) :=
            mul_le_mul hf2 hg2 (mul_nonneg (pow_nonneg hb_nn _) hG_nn)
              (le_trans hF_nn hf2)
      -- Assemble
      have hchoose_nn : (0 : ℝ) ≤ ↑(l.choose i) := Nat.cast_nonneg _
      calc ‖x‖ ^ p * (↑(l.choose i) * F * G)
          ≤ (2 ^ p * (a ^ p + b ^ p)) * (↑(l.choose i) * F * G) :=
            mul_le_mul_of_nonneg_right h_pow
              (mul_nonneg (mul_nonneg hchoose_nn hF_nn) hG_nn)
        _ = 2 ^ p * (↑(l.choose i) * (a ^ p * F * G + b ^ p * F * G)) := by ring
        _ ≤ 2 ^ p * (↑(l.choose i) * (Cf p i * Cg 0 (l - i) + Cf 0 i * Cg p (l - i))) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
            exact mul_le_mul_of_nonneg_left (add_le_add hprod1 hprod2) hchoose_nn
    -- Assemble the final bound
    calc ‖x‖ ^ p * ‖iteratedFDeriv ℝ l
          (fun y => f (splitFirst m k y) * g (splitLast m k y)) x‖
        ≤ ‖x‖ ^ p * ∑ i ∈ Finset.range (l + 1),
          ↑(l.choose i) * ‖iteratedFDeriv ℝ i (f.toFun ∘ splitFirst m k) x‖ *
          ‖iteratedFDeriv ℝ (l - i) (g.toFun ∘ splitLast m k) x‖ := by
          gcongr; exact hLeib
      _ ≤ ‖x‖ ^ p * ∑ i ∈ Finset.range (l + 1),
          ↑(l.choose i) * ‖iteratedFDeriv ℝ i f.toFun (splitFirst m k x)‖ *
          ‖iteratedFDeriv ℝ (l - i) g.toFun (splitLast m k x)‖ := by
          gcongr with i hi
          · exact (hcf i x).trans le_rfl
          · exact (hcg (l - i) x).trans le_rfl
      _ = ∑ i ∈ Finset.range (l + 1),
          ‖x‖ ^ p * (↑(l.choose i) * ‖iteratedFDeriv ℝ i f.toFun (splitFirst m k x)‖ *
          ‖iteratedFDeriv ℝ (l - i) g.toFun (splitLast m k x)‖) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range (l + 1),
          2 ^ p * (↑(l.choose i) * (Cf p i * Cg 0 (l - i) + Cf 0 i * Cg p (l - i))) := by
          exact Finset.sum_le_sum h_term
      _ = _ := by rw [← Finset.mul_sum]

/-- The tensor product function at a point. -/
@[simp]
theorem SchwartzMap.tensorProduct_apply {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ))
    (x : Fin (m + k) → E) :
    f.tensorProduct g x = f (splitFirst m k x) * g (splitLast m k x) := rfl

/-- The Borchers conjugated tensor product: f* ⊗ g where f* is the Borchers involution.
    This is the pairing used in the Wightman inner product:
    ⟨F, G⟩ = Σ W_{n+m}(f*_n ⊗ g_m)
    where f*_n(x₁,...,xₙ) = conj(f_n(xₙ,...,x₁)).

    This is the CORRECT definition including argument reversal. The reversal is essential
    for the Hermiticity of the inner product: ⟨F, G⟩ = conj(⟨G, F⟩).

    Reference: Streater-Wightman, "PCT, Spin and Statistics", §3.4 -/
def SchwartzMap.conjTensorProduct {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    𝓢(Fin (m + k) → E, ℂ) :=
  f.borchersConj.tensorProduct g

@[simp]
theorem SchwartzMap.conjTensorProduct_apply {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ))
    (x : Fin (m + k) → E) :
    f.conjTensorProduct g x =
      starRingEnd ℂ (f (fun i => splitFirst m k x (Fin.rev i))) * g (splitLast m k x) := rfl

/-! ### Properties of the Tensor Product -/

/-- The tensor product is bilinear in the second argument. -/
theorem SchwartzMap.tensorProduct_add_right {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g₁ g₂ : 𝓢(Fin k → E, ℂ)) :
    f.tensorProduct (g₁ + g₂) = f.tensorProduct g₁ + f.tensorProduct g₂ := by
  ext x
  simp [mul_add]

/-- The tensor product is bilinear in the first argument. -/
theorem SchwartzMap.tensorProduct_add_left {m k : ℕ}
    (f₁ f₂ : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    (f₁ + f₂).tensorProduct g = f₁.tensorProduct g + f₂.tensorProduct g := by
  ext x
  simp [add_mul]

/-- The tensor product with zero on the left is zero. -/
@[simp]
theorem SchwartzMap.tensorProduct_zero_left {m k : ℕ}
    (g : 𝓢(Fin k → E, ℂ)) :
    (0 : 𝓢(Fin m → E, ℂ)).tensorProduct g = 0 := by
  ext x; simp

/-- The tensor product with zero on the right is zero. -/
@[simp]
theorem SchwartzMap.tensorProduct_zero_right {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) :
    f.tensorProduct (0 : 𝓢(Fin k → E, ℂ)) = 0 := by
  ext x; simp

/-- Scalar multiplication distributes over tensor product. -/
theorem SchwartzMap.tensorProduct_smul_left {m k : ℕ}
    (c : ℂ) (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    (c • f).tensorProduct g = c • (f.tensorProduct g) := by
  ext x
  simp [mul_assoc]

/-! ### Tensor Product Continuity Infrastructure -/

/-- Algebraic decomposition of the tensor product difference.
    f ⊗ g - f₀ ⊗ g₀ = (f - f₀) ⊗ g₀ + f₀ ⊗ (g - g₀) + (f - f₀) ⊗ (g - g₀) -/
private theorem tensorProduct_decompose {m k : ℕ}
    (f f₀ : 𝓢(Fin m → E, ℂ)) (g g₀ : 𝓢(Fin k → E, ℂ)) :
    f.tensorProduct g - f₀.tensorProduct g₀ =
    (f - f₀).tensorProduct g₀ + f₀.tensorProduct (g - g₀) +
    (f - f₀).tensorProduct (g - g₀) := by
  ext x; simp [SchwartzMap.tensorProduct_apply]; ring

/-- Seminorm bound for the tensor product: each seminorm of f ⊗ g is bounded
    by a finite sum of products of seminorms of f and g.
    This is the key estimate for joint continuity. -/
private theorem seminorm_tensorProduct_le {m k : ℕ} (p l : ℕ)
    (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    SchwartzMap.seminorm ℂ p l (f.tensorProduct g) ≤
    2 ^ p * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
      (SchwartzMap.seminorm ℂ p i f * SchwartzMap.seminorm ℂ 0 (l - i) g +
       SchwartzMap.seminorm ℂ 0 i f * SchwartzMap.seminorm ℂ p (l - i) g) := by
  apply SchwartzMap.seminorm_le_bound ℂ p l _ (by positivity)
  intro x
  -- Smooth factors for Leibniz rule
  have hfs := f.smooth'.comp (splitFirstCLM m k (E := E)).contDiff
  have hgs := g.smooth'.comp (splitLastCLM m k (E := E)).contDiff
  -- Composition norm bounds: ‖D^j(f ∘ π₁) x‖ ≤ ‖D^j f (π₁ x)‖
  have hcf : ∀ j (x : Fin (m + k) → E),
      ‖iteratedFDeriv ℝ j (f.toFun ∘ splitFirst m k) x‖ ≤
      ‖iteratedFDeriv ℝ j f.toFun (splitFirst m k x)‖ := by
    intro j x
    rw [show f.toFun ∘ splitFirst m k = f.toFun ∘ ↑(splitFirstCLM m k (E := E)) from rfl,
      (splitFirstCLM m k).iteratedFDeriv_comp_right f.smooth' x
        (by exact_mod_cast le_top)]
    exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _)
        (Finset.prod_le_one (fun _ _ => norm_nonneg _)
          (fun _ _ => splitFirstCLM_opNorm_le m k)))
  have hcg : ∀ j (x : Fin (m + k) → E),
      ‖iteratedFDeriv ℝ j (g.toFun ∘ splitLast m k) x‖ ≤
      ‖iteratedFDeriv ℝ j g.toFun (splitLast m k x)‖ := by
    intro j x
    rw [show g.toFun ∘ splitLast m k = g.toFun ∘ ↑(splitLastCLM m k (E := E)) from rfl,
      (splitLastCLM m k).iteratedFDeriv_comp_right g.smooth' x
        (by exact_mod_cast le_top)]
    exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _)
        (Finset.prod_le_one (fun _ _ => norm_nonneg _)
          (fun _ _ => splitLastCLM_opNorm_le m k)))
  -- Leibniz rule
  have hLeib := norm_iteratedFDeriv_mul_le (n := l) hfs hgs x
    (WithTop.coe_le_coe.mpr (le_top (a := (l : ℕ∞))))
  -- Norm splitting: ‖x‖^p ≤ 2^p * (‖π₁ x‖^p + ‖π₂ x‖^p)
  have hnorm_split := norm_le_splitFirst_add_splitLast m k x
  have add_pow_le : (‖splitFirst m k x‖ + ‖splitLast m k x‖) ^ p ≤
      2 ^ p * (‖splitFirst m k x‖ ^ p + ‖splitLast m k x‖ ^ p) := by
    have hmax : (max ‖splitFirst m k x‖ ‖splitLast m k x‖) ^ p ≤
        ‖splitFirst m k x‖ ^ p + ‖splitLast m k x‖ ^ p := by
      rcases max_cases ‖splitFirst m k x‖ ‖splitLast m k x‖ with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]; exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
      · rw [h]; exact le_add_of_nonneg_left (pow_nonneg (norm_nonneg _) _)
    calc _ ≤ (2 * max ‖splitFirst m k x‖ ‖splitLast m k x‖) ^ p :=
          pow_le_pow_left₀ (add_nonneg (norm_nonneg _) (norm_nonneg _))
            (by linarith [le_max_left ‖splitFirst m k x‖ ‖splitLast m k x‖,
                          le_max_right ‖splitFirst m k x‖ ‖splitLast m k x‖]) _
      _ = (2 : ℝ) ^ p * (max ‖splitFirst m k x‖ ‖splitLast m k x‖) ^ p := mul_pow _ _ _
      _ ≤ 2 ^ p * (‖splitFirst m k x‖ ^ p + ‖splitLast m k x‖ ^ p) :=
          mul_le_mul_of_nonneg_left hmax (pow_nonneg (by norm_num) _)
  have h_pow : ‖x‖ ^ p ≤ 2 ^ p * (‖splitFirst m k x‖ ^ p + ‖splitLast m k x‖ ^ p) :=
    (pow_le_pow_left₀ (norm_nonneg _) hnorm_split _).trans add_pow_le
  -- Per-term bound using le_seminorm
  have h_term : ∀ i ∈ Finset.range (l + 1),
      ‖x‖ ^ p * (↑(l.choose i) * ‖iteratedFDeriv ℝ i f.toFun (splitFirst m k x)‖ *
      ‖iteratedFDeriv ℝ (l - i) g.toFun (splitLast m k x)‖) ≤
      2 ^ p * (↑(l.choose i) *
        (SchwartzMap.seminorm ℂ p i f * SchwartzMap.seminorm ℂ 0 (l - i) g +
         SchwartzMap.seminorm ℂ 0 i f * SchwartzMap.seminorm ℂ p (l - i) g)) := by
    intro i _
    set a := ‖splitFirst m k x‖
    set b := ‖splitLast m k x‖
    set F := ‖iteratedFDeriv ℝ i f.toFun (splitFirst m k x)‖
    set G := ‖iteratedFDeriv ℝ (l - i) g.toFun (splitLast m k x)‖
    have ha_nn : 0 ≤ a := norm_nonneg _
    have hb_nn : 0 ≤ b := norm_nonneg _
    have hF_nn : 0 ≤ F := norm_nonneg _
    have hG_nn : 0 ≤ G := norm_nonneg _
    -- Seminorm bounds (replacing the chosen constants from decay')
    have hf1 : a ^ p * F ≤ SchwartzMap.seminorm ℂ p i f :=
      SchwartzMap.le_seminorm ℂ p i f (splitFirst m k x)
    have hg1 : G ≤ SchwartzMap.seminorm ℂ 0 (l - i) g := by
      have h := SchwartzMap.le_seminorm ℂ 0 (l - i) g (splitLast m k x)
      simp only [pow_zero, one_mul] at h; exact h
    have hf2 : F ≤ SchwartzMap.seminorm ℂ 0 i f := by
      have h := SchwartzMap.le_seminorm ℂ 0 i f (splitFirst m k x)
      simp only [pow_zero, one_mul] at h; exact h
    have hg2 : b ^ p * G ≤ SchwartzMap.seminorm ℂ p (l - i) g :=
      SchwartzMap.le_seminorm ℂ p (l - i) g (splitLast m k x)
    -- Cross products
    have hprod1 : a ^ p * F * G ≤
        SchwartzMap.seminorm ℂ p i f * SchwartzMap.seminorm ℂ 0 (l - i) g :=
      mul_le_mul hf1 hg1 hG_nn (le_trans (mul_nonneg (pow_nonneg ha_nn _) hF_nn) hf1)
    have hprod2 : b ^ p * F * G ≤
        SchwartzMap.seminorm ℂ 0 i f * SchwartzMap.seminorm ℂ p (l - i) g := by
      calc b ^ p * F * G = F * (b ^ p * G) := by ring
        _ ≤ SchwartzMap.seminorm ℂ 0 i f * SchwartzMap.seminorm ℂ p (l - i) g :=
          mul_le_mul hf2 hg2 (mul_nonneg (pow_nonneg hb_nn _) hG_nn)
            (le_trans hF_nn hf2)
    have hchoose_nn : (0 : ℝ) ≤ ↑(l.choose i) := Nat.cast_nonneg _
    calc ‖x‖ ^ p * (↑(l.choose i) * F * G)
        ≤ (2 ^ p * (a ^ p + b ^ p)) * (↑(l.choose i) * F * G) :=
          mul_le_mul_of_nonneg_right h_pow
            (mul_nonneg (mul_nonneg hchoose_nn hF_nn) hG_nn)
      _ = 2 ^ p * (↑(l.choose i) * (a ^ p * F * G + b ^ p * F * G)) := by ring
      _ ≤ 2 ^ p * (↑(l.choose i) *
          (SchwartzMap.seminorm ℂ p i f * SchwartzMap.seminorm ℂ 0 (l - i) g +
           SchwartzMap.seminorm ℂ 0 i f * SchwartzMap.seminorm ℂ p (l - i) g)) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
          exact mul_le_mul_of_nonneg_left (add_le_add hprod1 hprod2) hchoose_nn
  -- Assemble
  calc ‖x‖ ^ p * ‖iteratedFDeriv ℝ l
        (fun y => f (splitFirst m k y) * g (splitLast m k y)) x‖
      ≤ ‖x‖ ^ p * ∑ i ∈ Finset.range (l + 1),
        ↑(l.choose i) * ‖iteratedFDeriv ℝ i (f.toFun ∘ splitFirst m k) x‖ *
        ‖iteratedFDeriv ℝ (l - i) (g.toFun ∘ splitLast m k) x‖ := by
        gcongr; exact hLeib
    _ ≤ ‖x‖ ^ p * ∑ i ∈ Finset.range (l + 1),
        ↑(l.choose i) * ‖iteratedFDeriv ℝ i f.toFun (splitFirst m k x)‖ *
        ‖iteratedFDeriv ℝ (l - i) g.toFun (splitLast m k x)‖ := by
        gcongr with i hi
        · exact (hcf i x).trans le_rfl
        · exact (hcg (l - i) x).trans le_rfl
    _ = ∑ i ∈ Finset.range (l + 1),
        ‖x‖ ^ p * (↑(l.choose i) * ‖iteratedFDeriv ℝ i f.toFun (splitFirst m k x)‖ *
        ‖iteratedFDeriv ℝ (l - i) g.toFun (splitLast m k x)‖) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (l + 1),
        2 ^ p * (↑(l.choose i) *
          (SchwartzMap.seminorm ℂ p i f * SchwartzMap.seminorm ℂ 0 (l - i) g +
           SchwartzMap.seminorm ℂ 0 i f * SchwartzMap.seminorm ℂ p (l - i) g)) :=
        Finset.sum_le_sum h_term
    _ = _ := by rw [← Finset.mul_sum]

/-- The tensor product is jointly continuous as a bilinear map on Schwartz spaces.
    Uses sequential continuity (Schwartz space is first countable, hence sequential)
    with the bilinear seminorm bound. -/
theorem SchwartzMap.tensorProduct_continuous {m k : ℕ} :
    Continuous (fun p : 𝓢(Fin m → E, ℂ) × 𝓢(Fin k → E, ℂ) =>
      p.1.tensorProduct p.2) := by
  rw [continuous_iff_seqContinuous]
  intro u a hu
  -- Extract component convergences
  have hf : Filter.Tendsto (fun n => (u n).1) Filter.atTop (nhds a.1) :=
    (continuous_fst.tendsto a).comp hu
  have hg : Filter.Tendsto (fun n => (u n).2) Filter.atTop (nhds a.2) :=
    (continuous_snd.tendsto a).comp hu
  -- Use WithSeminorms characterization for the target
  show Filter.Tendsto (fun n => (u n).1.tensorProduct (u n).2)
    Filter.atTop (nhds (a.1.tensorProduct a.2))
  rw [(schwartz_withSeminorms ℂ (Fin (m + k) → E) ℂ).tendsto_nhds_atTop
    (fun n => (u n).1.tensorProduct (u n).2) (a.1.tensorProduct a.2)]
  intro ⟨p, l⟩ ε hε
  -- Get convergence of source seminorms
  rw [(schwartz_withSeminorms ℂ (Fin m → E) ℂ).tendsto_nhds_atTop _ _] at hf
  rw [(schwartz_withSeminorms ℂ (Fin k → E) ℂ).tendsto_nhds_atTop _ _] at hg
  -- The difference decomposes: T(f,g) - T(f₀,g₀) = T(f-f₀,g₀) + T(f₀,g-g₀) + T(f-f₀,g-g₀)
  -- Bound by seminorm triangle inequality + bilinear bound
  -- Abbreviation for the bound function
  set B := fun (f' : 𝓢(Fin m → E, ℂ)) (g' : 𝓢(Fin k → E, ℂ)) =>
    2 ^ p * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
      (SchwartzMap.seminorm ℂ p i f' * SchwartzMap.seminorm ℂ 0 (l - i) g' +
       SchwartzMap.seminorm ℂ 0 i f' * SchwartzMap.seminorm ℂ p (l - i) g') with hB_def
  -- B is nonneg
  have hB_nn : ∀ f' g', 0 ≤ B f' g' := by
    intro f' g'; apply mul_nonneg (pow_nonneg (by norm_num) _)
    exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
        (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))
  -- B(f',g') → 0 when seminorms of f' → 0 (with g' having bounded seminorms)
  -- We use: sem(f⊗g - f₀⊗g₀) ≤ sem(T1) + sem(T2) + sem(T3)
  -- ≤ B(f-f₀, g₀) + B(f₀, g-g₀) + B(f-f₀, g-g₀)
  -- Choose δ so that each term < ε/3
  -- For term 1: B(h, g₀) ≤ C₁ * max_sem(h) where C₁ depends on g₀
  -- For term 2: B(f₀, k) ≤ C₂ * max_sem(k) where C₂ depends on f₀
  -- For term 3: B(h, k) ≤ C₃ * max_sem(h) * max_sem(k)
  -- So we need max_sem(h) < δ₁ and max_sem(k) < δ₂ with appropriate δ's.
  -- Define the relevant finite set of seminorm indices
  set S_f := Finset.image (fun i => ((p, i) : ℕ × ℕ))
      (Finset.range (l + 1)) ∪
    Finset.image (fun i => ((0, i) : ℕ × ℕ))
      (Finset.range (l + 1)) with hS_f_def
  set S_g := Finset.image (fun i => ((0, l - i) : ℕ × ℕ))
      (Finset.range (l + 1)) ∪
    Finset.image (fun i => ((p, l - i) : ℕ × ℕ))
      (Finset.range (l + 1)) with hS_g_def
  -- B(h, k) ≤ C * (max_{i ∈ S_f} sem_i h) * (max_{j ∈ S_g} sem_j k) for some C
  -- More precisely, note each seminorm in B is ≤ the sup over the finite set
  -- We bound B(h, k) ≤ 2^(p+1) * 2^l * Sh * Sk where Sh = max sem_i(h)
  -- Actually, for the ε-δ argument, it's easier to directly use the
  -- convergence of each individual seminorm and the finite sum structure.
  -- Each seminorm term in B involves sem(a,b)(f') * sem(c,d)(g')
  -- We collect all needed indices and show they all become small.
  -- Simple approach: find N such that all individual seminorms < δ, then bound B
  -- For each (a, b) in S_f, eventually sem(a,b)(f_n - f₀) < δ
  -- For each (c, d) in S_g, eventually sem(c,d)(g_n - g₀) < δ
  -- Choose δ small enough that the resulting bound on B < ε/3 for each term
  -- Let C_g = max of B(0, g₀) + 1 as a bound on g₀ seminorms (just need finiteness)
  -- Actually, let's just find N for each of the 3 terms separately
  -- TERM 1: B(f_n - a.1, a.2) → 0
  -- Each summand has form sem(a,b)(f_n - a.1) * sem(c,d)(a.2)
  -- = (→ 0) * (constant), so → 0
  -- TERM 2: B(a.1, g_n - a.2) → 0, similarly
  -- TERM 3: B(f_n - a.1, g_n - a.2) → 0
  -- Each summand: sem(a,b)(f_n - a.1) * sem(c,d)(g_n - a.2) → 0 * 0 = 0
  -- For each i in range(l+1), we get convergence of each product.
  -- Then the finite sum converges to 0.
  -- First, get the triangle inequality
  have htri : ∀ n, schwartzSeminormFamily ℂ (Fin (m + k) → E) ℂ (p, l)
      ((u n).1.tensorProduct (u n).2 - a.1.tensorProduct a.2) ≤
      SchwartzMap.seminorm ℂ p l (((u n).1 - a.1).tensorProduct a.2) +
      SchwartzMap.seminorm ℂ p l (a.1.tensorProduct ((u n).2 - a.2)) +
      SchwartzMap.seminorm ℂ p l (((u n).1 - a.1).tensorProduct ((u n).2 - a.2)) := by
    intro n
    simp only [schwartzSeminormFamily_apply]
    calc SchwartzMap.seminorm ℂ p l ((u n).1.tensorProduct (u n).2 - a.1.tensorProduct a.2)
        = SchwartzMap.seminorm ℂ p l
            (((u n).1 - a.1).tensorProduct a.2 + a.1.tensorProduct ((u n).2 - a.2) +
             ((u n).1 - a.1).tensorProduct ((u n).2 - a.2)) := by
          congr 1; exact tensorProduct_decompose (u n).1 a.1 (u n).2 a.2
      _ ≤ SchwartzMap.seminorm ℂ p l
              (((u n).1 - a.1).tensorProduct a.2 + a.1.tensorProduct ((u n).2 - a.2)) +
          SchwartzMap.seminorm ℂ p l (((u n).1 - a.1).tensorProduct ((u n).2 - a.2)) :=
          map_add_le_add _ _ _
      _ ≤ _ := by
          have := map_add_le_add (SchwartzMap.seminorm ℂ p l)
            (((u n).1 - a.1).tensorProduct a.2) (a.1.tensorProduct ((u n).2 - a.2))
          linarith
  -- Each of the 3 terms is bounded by B applied to appropriate arguments
  have hb1 : ∀ n, SchwartzMap.seminorm ℂ p l (((u n).1 - a.1).tensorProduct a.2) ≤
      B ((u n).1 - a.1) a.2 := fun n => seminorm_tensorProduct_le p l _ _
  have hb2 : ∀ n, SchwartzMap.seminorm ℂ p l (a.1.tensorProduct ((u n).2 - a.2)) ≤
      B a.1 ((u n).2 - a.2) := fun n => seminorm_tensorProduct_le p l _ _
  have hb3 : ∀ n, SchwartzMap.seminorm ℂ p l
      (((u n).1 - a.1).tensorProduct ((u n).2 - a.2)) ≤
      B ((u n).1 - a.1) ((u n).2 - a.2) := fun n => seminorm_tensorProduct_le p l _ _
  -- B(h, k) → 0 when seminorms of h and k → 0
  -- Strategy: find N such that all 3 terms < ε/3
  -- For term 1: B(f_n - a.1, a.2) is a finite sum of products (sem_f * sem_g₀)
  -- Each sem_f → 0 while sem_g₀ is constant
  -- Similarly for terms 2 and 3
  -- Use: for each (i, j) pair, eventually |sem_i(f_n - a.1) * sem_j(a.2)| < δ
  -- Since the sum is finite, there's a uniform N
  suffices h_all_small : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n, N ≤ n →
      B ((u n).1 - a.1) a.2 < δ ∧
      B a.1 ((u n).2 - a.2) < δ ∧
      B ((u n).1 - a.1) ((u n).2 - a.2) < δ by
    obtain ⟨N, hN⟩ := h_all_small (ε / 3) (by linarith)
    exact ⟨N, fun n hn => by
      have ⟨h1, h2, h3⟩ := hN n hn
      calc schwartzSeminormFamily ℂ (Fin (m + k) → E) ℂ (p, l)
            ((u n).1.tensorProduct (u n).2 - a.1.tensorProduct a.2)
          ≤ _ := htri n
        _ ≤ B ((u n).1 - a.1) a.2 + B a.1 ((u n).2 - a.2) +
            B ((u n).1 - a.1) ((u n).2 - a.2) :=
            add_le_add (add_le_add (hb1 n) (hb2 n)) (hb3 n)
        _ < ε / 3 + ε / 3 + ε / 3 := by linarith
        _ = ε := by ring⟩
  -- Now prove the key: B terms become small
  intro δ hδ
  -- B(h, k) = 2^p * Σ_i C(l,i) * (sem(p,i)(h)*sem(0,l-i)(k) + sem(0,i)(h)*sem(p,l-i)(k))
  -- Each individual product sem(a,b)(h) * sem(c,d)(k) tends to 0 when the appropriate
  -- factor tends to 0. We find N for each factor in the finite sum.
  -- Collect all needed seminorm convergence:
  -- For f-convergence: need sem(p,i)(f_n - a.1) < δ_f and sem(0,i)(f_n - a.1) < δ_f
  -- For g-convergence: need sem(0,l-i)(g_n - a.2) < δ_g and sem(p,l-i)(g_n - a.2) < δ_g
  -- Choose δ_f and δ_g appropriately
  -- Compute the "constant" factors
  -- For term 1: the g₀ factors are fixed. We need Σ_i C(l,i) * (sem(p,i)(h)*Cg + Cf_h*sem(p,l-i)(g₀))
  -- where h = f_n - a.1. Each sem of h → 0.
  -- Let Mg = max of all sem(c,d)(a.2) for relevant indices, similarly Mf for a.1
  -- Upper bounds on fixed seminorms
  set Mg := (Finset.range (l + 1)).sup'
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ l)⟩
    (fun i => max (SchwartzMap.seminorm ℂ 0 (l - i) a.2)
                  (SchwartzMap.seminorm ℂ p (l - i) a.2) + 1) with hMg_def
  set Mf := (Finset.range (l + 1)).sup'
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ l)⟩
    (fun i => max (SchwartzMap.seminorm ℂ p i a.1)
                  (SchwartzMap.seminorm ℂ 0 i a.1) + 1) with hMf_def
  have hMg_pos : 0 < Mg := by
    have h1 := Finset.le_sup' (fun i => max (SchwartzMap.seminorm ℂ 0 (l - i) a.2)
      (SchwartzMap.seminorm ℂ p (l - i) a.2) + 1)
      (Finset.mem_range.mpr (Nat.zero_lt_succ l) : (0 : ℕ) ∈ Finset.range (l + 1))
    simp only [Nat.sub_zero] at h1
    linarith [apply_nonneg (SchwartzMap.seminorm ℂ 0 l) a.2,
              le_max_left (SchwartzMap.seminorm ℂ 0 l a.2) (SchwartzMap.seminorm ℂ p l a.2)]
  have hMf_pos : 0 < Mf := by
    have h1 := Finset.le_sup' (fun i => max (SchwartzMap.seminorm ℂ p i a.1)
      (SchwartzMap.seminorm ℂ 0 i a.1) + 1)
      (Finset.mem_range.mpr (Nat.zero_lt_succ l) : (0 : ℕ) ∈ Finset.range (l + 1))
    linarith [apply_nonneg (SchwartzMap.seminorm ℂ p 0) a.1,
              le_max_left (SchwartzMap.seminorm ℂ p 0 a.1) (SchwartzMap.seminorm ℂ 0 0 a.1)]
  -- The constant in B
  set K := 2 ^ p * ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ)
  have hK_pos : 0 < K := by
    apply mul_pos (pow_pos (by norm_num : (0:ℝ) < 2) _)
    apply Finset.sum_pos
    · intro i hi
      exact Nat.cast_pos.mpr (Nat.choose_pos
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    · exact ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ l)⟩
  -- Choose δ values
  set δ_f := min 1 (δ / (4 * K * Mg)) with hδ_f_def
  set δ_g := min 1 (δ / (4 * K * Mf)) with hδ_g_def
  have hδ_f_pos : 0 < δ_f := lt_min one_pos (div_pos hδ (by positivity))
  have hδ_g_pos : 0 < δ_g := lt_min one_pos (div_pos hδ (by positivity))
  -- Bounds on fixed seminorms by Mg/Mf
  have hMg_bound : ∀ i ∈ Finset.range (l + 1),
      SchwartzMap.seminorm ℂ 0 (l - i) a.2 ≤ Mg ∧
      SchwartzMap.seminorm ℂ p (l - i) a.2 ≤ Mg := by
    intro i hi
    have hsup := Finset.le_sup' (fun i => max (SchwartzMap.seminorm ℂ 0 (l - i) a.2)
      (SchwartzMap.seminorm ℂ p (l - i) a.2) + 1) hi
    constructor
    · have := le_max_left (SchwartzMap.seminorm ℂ 0 (l - i) a.2)
        (SchwartzMap.seminorm ℂ p (l - i) a.2)
      linarith
    · have := le_max_right (SchwartzMap.seminorm ℂ 0 (l - i) a.2)
        (SchwartzMap.seminorm ℂ p (l - i) a.2)
      linarith
  have hMf_bound : ∀ i ∈ Finset.range (l + 1),
      SchwartzMap.seminorm ℂ p i a.1 ≤ Mf ∧
      SchwartzMap.seminorm ℂ 0 i a.1 ≤ Mf := by
    intro i hi
    have hsup := Finset.le_sup' (fun i => max (SchwartzMap.seminorm ℂ p i a.1)
      (SchwartzMap.seminorm ℂ 0 i a.1) + 1) hi
    constructor
    · have := le_max_left (SchwartzMap.seminorm ℂ p i a.1)
        (SchwartzMap.seminorm ℂ 0 i a.1)
      linarith
    · have := le_max_right (SchwartzMap.seminorm ℂ p i a.1)
        (SchwartzMap.seminorm ℂ 0 i a.1)
      linarith
  -- Get N for f-seminorms (non-dependent choose by including membership in conclusion)
  have hf_conv : ∀ i : ℕ, ∃ N, i ∈ Finset.range (l + 1) → ∀ n, N ≤ n →
      SchwartzMap.seminorm ℂ p i ((u n).1 - a.1) < δ_f ∧
      SchwartzMap.seminorm ℂ 0 i ((u n).1 - a.1) < δ_f := by
    intro i
    by_cases hi : i ∈ Finset.range (l + 1)
    · obtain ⟨N₁, hN₁⟩ := hf (p, i) δ_f hδ_f_pos
      obtain ⟨N₂, hN₂⟩ := hf (0, i) δ_f hδ_f_pos
      exact ⟨max N₁ N₂, fun _ n hn => ⟨hN₁ n (le_of_max_le_left hn),
        hN₂ n (le_of_max_le_right hn)⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  have hg_conv : ∀ i : ℕ, ∃ N, i ∈ Finset.range (l + 1) → ∀ n, N ≤ n →
      SchwartzMap.seminorm ℂ 0 (l - i) ((u n).2 - a.2) < δ_g ∧
      SchwartzMap.seminorm ℂ p (l - i) ((u n).2 - a.2) < δ_g := by
    intro i
    by_cases hi : i ∈ Finset.range (l + 1)
    · obtain ⟨N₁, hN₁⟩ := hg (0, l - i) δ_g hδ_g_pos
      obtain ⟨N₂, hN₂⟩ := hg (p, l - i) δ_g hδ_g_pos
      exact ⟨max N₁ N₂, fun _ n hn => ⟨hN₁ n (le_of_max_le_left hn),
        hN₂ n (le_of_max_le_right hn)⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  -- Extract uniform N (now choose gives non-dependent functions)
  choose Nf hNf using hf_conv
  choose Ng hNg using hg_conv
  set N := (Finset.range (l + 1)).sup Nf ⊔ (Finset.range (l + 1)).sup Ng
  refine ⟨N, fun n hn => ?_⟩
  have hn_f : ∀ i ∈ Finset.range (l + 1),
      SchwartzMap.seminorm ℂ p i ((u n).1 - a.1) < δ_f ∧
      SchwartzMap.seminorm ℂ 0 i ((u n).1 - a.1) < δ_f := by
    intro i hi
    exact hNf i hi n (le_trans (Finset.le_sup hi) (le_sup_left.trans hn))
  have hn_g : ∀ i ∈ Finset.range (l + 1),
      SchwartzMap.seminorm ℂ 0 (l - i) ((u n).2 - a.2) < δ_g ∧
      SchwartzMap.seminorm ℂ p (l - i) ((u n).2 - a.2) < δ_g := by
    intro i hi
    exact hNg i hi n (le_trans (Finset.le_sup hi) (le_sup_right.trans hn))
  -- Bound each term
  -- TERM 1: B((u n).1 - a.1, a.2) < δ
  constructor
  · -- Each summand: C(l,i) * (sem_p_i(h) * sem_0_li(a.2) + sem_0_i(h) * sem_p_li(a.2))
    -- ≤ C(l,i) * (δ_f * Mg + δ_f * Mg) = C(l,i) * 2 * δ_f * Mg
    calc B ((u n).1 - a.1) a.2
        = 2 ^ p * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
          (SchwartzMap.seminorm ℂ p i ((u n).1 - a.1) *
           SchwartzMap.seminorm ℂ 0 (l - i) a.2 +
           SchwartzMap.seminorm ℂ 0 i ((u n).1 - a.1) *
           SchwartzMap.seminorm ℂ p (l - i) a.2) := rfl
      _ ≤ 2 ^ p * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) * (δ_f * Mg + δ_f * Mg) := by
          gcongr with i hi
          · exact le_of_lt (hn_f i hi).1
          · exact (hMg_bound i hi).1
          · exact le_of_lt (hn_f i hi).2
          · exact (hMg_bound i hi).2
      _ = K * (2 * δ_f * Mg) := by
          have hsub : ∀ i ∈ Finset.range (l + 1),
              (l.choose i : ℝ) * (δ_f * Mg + δ_f * Mg) =
              (l.choose i : ℝ) * (2 * δ_f * Mg) := fun i _ => by ring
          rw [Finset.sum_congr rfl hsub, ← Finset.sum_mul, ← mul_assoc]
      _ < δ := by
          have hδ_f_le : δ_f ≤ δ / (4 * K * Mg) := min_le_right _ _
          calc K * (2 * δ_f * Mg) ≤ K * (2 * (δ / (4 * K * Mg)) * Mg) :=
                by gcongr
            _ = δ / 2 := by field_simp; ring
            _ < δ := by linarith
  constructor
  · -- TERM 2: B(a.1, (u n).2 - a.2) < δ (symmetric to term 1)
    calc B a.1 ((u n).2 - a.2)
        = 2 ^ p * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
          (SchwartzMap.seminorm ℂ p i a.1 *
           SchwartzMap.seminorm ℂ 0 (l - i) ((u n).2 - a.2) +
           SchwartzMap.seminorm ℂ 0 i a.1 *
           SchwartzMap.seminorm ℂ p (l - i) ((u n).2 - a.2)) := rfl
      _ ≤ 2 ^ p * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) * (Mf * δ_g + Mf * δ_g) := by
          gcongr with i hi
          · exact (hMf_bound i hi).1
          · exact le_of_lt (hn_g i hi).1
          · exact (hMf_bound i hi).2
          · exact le_of_lt (hn_g i hi).2
      _ = K * (2 * Mf * δ_g) := by
          have hsub : ∀ i ∈ Finset.range (l + 1),
              (l.choose i : ℝ) * (Mf * δ_g + Mf * δ_g) =
              (l.choose i : ℝ) * (2 * Mf * δ_g) := fun i _ => by ring
          rw [Finset.sum_congr rfl hsub, ← Finset.sum_mul, ← mul_assoc]
      _ < δ := by
          have hδ_g_le : δ_g ≤ δ / (4 * K * Mf) := min_le_right _ _
          calc K * (2 * Mf * δ_g) ≤ K * (2 * Mf * (δ / (4 * K * Mf))) :=
                by gcongr
            _ = δ / 2 := by field_simp; ring
            _ < δ := by linarith
  · -- TERM 3: B((u n).1 - a.1, (u n).2 - a.2) < δ
    -- Both factors are < min(1, ...), so product is small
    calc B ((u n).1 - a.1) ((u n).2 - a.2)
        = 2 ^ p * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
          (SchwartzMap.seminorm ℂ p i ((u n).1 - a.1) *
           SchwartzMap.seminorm ℂ 0 (l - i) ((u n).2 - a.2) +
           SchwartzMap.seminorm ℂ 0 i ((u n).1 - a.1) *
           SchwartzMap.seminorm ℂ p (l - i) ((u n).2 - a.2)) := rfl
      _ ≤ 2 ^ p * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
          (δ_f * δ_g + δ_f * δ_g) := by
          gcongr with i hi
          · exact le_of_lt (hn_f i hi).1
          · exact le_of_lt (hn_g i hi).1
          · exact le_of_lt (hn_f i hi).2
          · exact le_of_lt (hn_g i hi).2
      _ = K * (2 * δ_f * δ_g) := by
          have hsub : ∀ i ∈ Finset.range (l + 1),
              (l.choose i : ℝ) * (δ_f * δ_g + δ_f * δ_g) =
              (l.choose i : ℝ) * (2 * δ_f * δ_g) := fun i _ => by ring
          rw [Finset.sum_congr rfl hsub, ← Finset.sum_mul, ← mul_assoc]
      _ ≤ K * (2 * 1 * (δ / (4 * K * Mf))) := by
          gcongr
          · exact min_le_left _ _
          · exact min_le_right _ _
      _ = δ / (2 * Mf) := by field_simp; ring
      _ < δ := by
          apply div_lt_self hδ
          have hMf_ge : 1 ≤ Mf := by
            have h1 := Finset.le_sup' (fun i => max (SchwartzMap.seminorm ℂ p i a.1)
              (SchwartzMap.seminorm ℂ 0 i a.1) + 1)
              (Finset.mem_range.mpr (Nat.zero_lt_succ l) : (0 : ℕ) ∈ Finset.range (l + 1))
            linarith [apply_nonneg (SchwartzMap.seminorm ℂ p 0) a.1,
                      le_max_left (SchwartzMap.seminorm ℂ p 0 a.1)
                        (SchwartzMap.seminorm ℂ 0 0 a.1)]
          linarith

/-- Scalar multiplication distributes over tensor product (right). -/
theorem SchwartzMap.tensorProduct_smul_right {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (c : ℂ) (g : 𝓢(Fin k → E, ℂ)) :
    f.tensorProduct (c • g) = c • (f.tensorProduct g) := by
  ext x
  simp [mul_left_comm]

/-- Negation distributes over tensor product (left). -/
@[simp]
theorem SchwartzMap.tensorProduct_neg_left {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    (-f).tensorProduct g = -(f.tensorProduct g) := by
  ext x; simp [neg_mul]

/-- Negation distributes over tensor product (right). -/
@[simp]
theorem SchwartzMap.tensorProduct_neg_right {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    f.tensorProduct (-g) = -(f.tensorProduct g) := by
  ext x; simp [mul_neg]

/-! ### Conjugation Algebra -/

/-- Conjugation of zero is zero. -/
@[simp]
theorem SchwartzMap.conj_zero : (0 : 𝓢(E, ℂ)).conj = 0 := by
  ext x; simp [SchwartzMap.conj_apply]

/-- Conjugation distributes over addition. -/
@[simp]
theorem SchwartzMap.conj_add (f g : 𝓢(E, ℂ)) : (f + g).conj = f.conj + g.conj := by
  ext x; simp [SchwartzMap.conj_apply, map_add]

/-- Conjugation distributes over negation. -/
@[simp]
theorem SchwartzMap.conj_neg (f : 𝓢(E, ℂ)) : (-f).conj = -(f.conj) := by
  ext x; simp [SchwartzMap.conj_apply, map_neg]

/-- Conjugation interacts with scalar multiplication via conjugation of the scalar. -/
theorem SchwartzMap.conj_smul (c : ℂ) (f : 𝓢(E, ℂ)) :
    (c • f).conj = starRingEnd ℂ c • f.conj := by
  ext x; simp [SchwartzMap.conj_apply, map_mul]

/-! ### Conjugated Tensor Product Algebra -/

/-- Conjugated tensor product with zero on the left is zero. -/
@[simp]
theorem SchwartzMap.conjTensorProduct_zero_left {m k : ℕ}
    (g : 𝓢(Fin k → E, ℂ)) :
    (0 : 𝓢(Fin m → E, ℂ)).conjTensorProduct g = 0 := by
  simp [SchwartzMap.conjTensorProduct]

/-- Conjugated tensor product with zero on the right is zero. -/
@[simp]
theorem SchwartzMap.conjTensorProduct_zero_right {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) :
    f.conjTensorProduct (0 : 𝓢(Fin k → E, ℂ)) = 0 := by
  simp [SchwartzMap.conjTensorProduct]

/-- Conjugated tensor product is additive in the second argument. -/
theorem SchwartzMap.conjTensorProduct_add_right {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g₁ g₂ : 𝓢(Fin k → E, ℂ)) :
    f.conjTensorProduct (g₁ + g₂) = f.conjTensorProduct g₁ + f.conjTensorProduct g₂ := by
  simp [SchwartzMap.conjTensorProduct, SchwartzMap.tensorProduct_add_right]

/-- Conjugated tensor product is additive in the first argument. -/
theorem SchwartzMap.conjTensorProduct_add_left {m k : ℕ}
    (f₁ f₂ : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    (f₁ + f₂).conjTensorProduct g = f₁.conjTensorProduct g + f₂.conjTensorProduct g := by
  simp [SchwartzMap.conjTensorProduct, SchwartzMap.tensorProduct_add_left]

/-- Conjugated tensor product: negation in the first argument. -/
@[simp]
theorem SchwartzMap.conjTensorProduct_neg_left {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    (-f).conjTensorProduct g = -(f.conjTensorProduct g) := by
  simp [SchwartzMap.conjTensorProduct]

/-- Conjugated tensor product: negation in the second argument. -/
@[simp]
theorem SchwartzMap.conjTensorProduct_neg_right {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    f.conjTensorProduct (-g) = -(f.conjTensorProduct g) := by
  simp [SchwartzMap.conjTensorProduct]

/-- Conjugated tensor product: scalar multiplication in the second argument. -/
theorem SchwartzMap.conjTensorProduct_smul_right {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (c : ℂ) (g : 𝓢(Fin k → E, ℂ)) :
    f.conjTensorProduct (c • g) = c • (f.conjTensorProduct g) := by
  simp [SchwartzMap.conjTensorProduct, SchwartzMap.tensorProduct_smul_right]

/-- Conjugated tensor product: scalar multiplication in the first argument.
    Uses conjugation: conj(c·f) ⊗ g = c̄ · (conj(f) ⊗ g) -/
theorem SchwartzMap.conjTensorProduct_smul_left {m k : ℕ}
    (c : ℂ) (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    (c • f).conjTensorProduct g = starRingEnd ℂ c • (f.conjTensorProduct g) := by
  simp [SchwartzMap.conjTensorProduct, SchwartzMap.borchersConj_smul,
    SchwartzMap.tensorProduct_smul_left]

/-! ### Prepend Operation -/

/-- The tail projection as a ContinuousLinearMap: x ↦ (x₁,...,xₙ) from Fin (n+1) → E. -/
noncomputable def tailCLM (n : ℕ) :
    (Fin (n + 1) → E) →L[ℝ] (Fin n → E) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => E) i.succ

@[simp]
theorem tailCLM_apply (n : ℕ) (x : Fin (n + 1) → E) :
    tailCLM n x = fun i => x i.succ := rfl

/-- The tail projection has operator norm ≤ 1. -/
theorem tailCLM_opNorm_le (n : ℕ) :
    ‖tailCLM n (E := E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [tailCLM_apply, one_mul]; exact tail_norm_le n x
  where
  tail_norm_le (n : ℕ) (x : Fin (n + 1) → E) :
      ‖fun i : Fin n => x i.succ‖ ≤ ‖x‖ := by
    simp only [Pi.norm_def]
    exact_mod_cast Finset.sup_le fun b _ =>
      Finset.le_sup (f := fun j => ‖x j‖₊) (Finset.mem_univ (Fin.succ b))

/-- The pi norm of x : Fin (n+1) → E is bounded by ‖x 0‖ + ‖tail x‖. -/
theorem norm_le_head_add_tail (n : ℕ) (x : Fin (n + 1) → E) :
    ‖x‖ ≤ ‖x 0‖ + ‖fun i : Fin n => x i.succ‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  refine Fin.cases ?_ (fun i => ?_)
  · -- j = 0: ‖x 0‖ ≤ ‖x 0‖ + ‖tail‖
    exact le_add_of_nonneg_right (norm_nonneg _)
  · -- j = i.succ: ‖x i.succ‖ ≤ ‖x 0‖ + ‖tail‖
    exact (norm_le_pi_norm (fun i : Fin n => x i.succ) i).trans
      (le_add_of_nonneg_left (norm_nonneg _))

/-- Prepend a single-variable Schwartz function to an n-point Schwartz function.
    (prepend f g)(x₀, x₁,...,xₙ) = f(x₀) · g(x₁,...,xₙ)

    This returns `𝓢(Fin (n + 1) → E, ℂ)` directly, avoiding the `Fin (1 + n)` vs
    `Fin (n + 1)` definitional equality issue that arises with `tensorProduct`. -/
def SchwartzMap.prependField {n : ℕ}
    (f : 𝓢(E, ℂ)) (g : 𝓢(Fin n → E, ℂ)) : 𝓢(Fin (n + 1) → E, ℂ) where
  toFun := fun x => f (x 0) * g (fun i => x i.succ)
  smooth' := by
    apply ContDiff.mul
    · exact f.smooth'.comp
        (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => E) 0).contDiff
    · exact g.smooth'.comp (tailCLM n (E := E)).contDiff
  decay' := by
    intro p l
    -- Smooth factors via CLM composition
    let headCLM := ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => E) 0
    have hfs := f.smooth'.comp headCLM.contDiff
    have hgs := g.smooth'.comp (tailCLM n (E := E)).contDiff
    -- The projection CLM has norm ≤ 1
    have headCLM_norm_le : ‖headCLM‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        (fun x => by rw [one_mul]; exact norm_le_pi_norm x 0)
    -- Composition norm bounds
    have hcf : ∀ j (x : Fin (n + 1) → E),
        ‖iteratedFDeriv ℝ j (f.toFun ∘ fun x => x 0) x‖ ≤
        ‖iteratedFDeriv ℝ j f.toFun (x 0)‖ := by
      intro j x
      rw [show (f.toFun ∘ fun x => x 0) = f.toFun ∘ ⇑headCLM from rfl,
        headCLM.iteratedFDeriv_comp_right f.smooth' x (by exact_mod_cast le_top)]
      exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _)
          (Finset.prod_le_one (fun _ _ => norm_nonneg _)
            (fun _ _ => headCLM_norm_le)))
    have hcg : ∀ j (x : Fin (n + 1) → E),
        ‖iteratedFDeriv ℝ j (g.toFun ∘ fun x => fun i => x i.succ) x‖ ≤
        ‖iteratedFDeriv ℝ j g.toFun (fun i => x i.succ)‖ := by
      intro j x
      rw [show (g.toFun ∘ fun x => fun i => x i.succ) =
            g.toFun ∘ ⇑(tailCLM n (E := E)) from rfl,
        (tailCLM n).iteratedFDeriv_comp_right g.smooth' x (by exact_mod_cast le_top)]
      exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _)
          (Finset.prod_le_one (fun _ _ => norm_nonneg _)
            (fun _ _ => tailCLM_opNorm_le n)))
    -- Schwartz decay constants
    choose Cf hCf using fun p j => f.decay' p j
    choose Cg hCg using fun p j => g.decay' p j
    -- Total bound constant
    refine ⟨2 ^ p * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
      (Cf p i * Cg 0 (l - i) + Cf 0 i * Cg p (l - i)), fun x => ?_⟩
    -- Step 1: Leibniz rule
    have hLeib := norm_iteratedFDeriv_mul_le (n := l) hfs hgs x
      (WithTop.coe_le_coe.mpr (le_top (a := (l : ℕ∞))))
    -- Step 2: Norm splitting + polynomial weight bound
    have hnorm_split := norm_le_head_add_tail n x
    have h_add_le_2max : ‖x 0‖ + ‖fun i : Fin n => x i.succ‖ ≤
        2 * max ‖x 0‖ ‖fun i : Fin n => x i.succ‖ := by
      linarith [le_max_left ‖x 0‖ ‖fun i : Fin n => x i.succ‖,
                le_max_right ‖x 0‖ ‖fun i : Fin n => x i.succ‖]
    have add_pow_le : (‖x 0‖ + ‖fun i : Fin n => x i.succ‖) ^ p ≤
        2 ^ p * (‖x 0‖ ^ p + ‖fun i : Fin n => x i.succ‖ ^ p) := by
      have hmax : (max ‖x 0‖ ‖fun i : Fin n => x i.succ‖) ^ p ≤
          ‖x 0‖ ^ p + ‖fun i : Fin n => x i.succ‖ ^ p := by
        rcases max_cases ‖x 0‖ ‖fun i : Fin n => x i.succ‖ with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]; exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
        · rw [h]; exact le_add_of_nonneg_left (pow_nonneg (norm_nonneg _) _)
      calc _ ≤ (2 * max ‖x 0‖ ‖fun i : Fin n => x i.succ‖) ^ p :=
            pow_le_pow_left₀ (add_nonneg (norm_nonneg _) (norm_nonneg _)) h_add_le_2max _
        _ = (2 : ℝ) ^ p * (max ‖x 0‖ ‖fun i : Fin n => x i.succ‖) ^ p :=
            mul_pow (2 : ℝ) _ p
        _ ≤ 2 ^ p * (‖x 0‖ ^ p + ‖fun i : Fin n => x i.succ‖ ^ p) :=
            mul_le_mul_of_nonneg_left hmax (pow_nonneg (by norm_num) _)
    have h_pow : ‖x‖ ^ p ≤ 2 ^ p * (‖x 0‖ ^ p + ‖fun i : Fin n => x i.succ‖ ^ p) :=
      (pow_le_pow_left₀ (norm_nonneg _) hnorm_split _).trans add_pow_le
    -- Step 3: Bound each Leibniz summand
    have h_term : ∀ i ∈ Finset.range (l + 1),
        ‖x‖ ^ p * (↑(l.choose i) * ‖iteratedFDeriv ℝ i f.toFun (x 0)‖ *
        ‖iteratedFDeriv ℝ (l - i) g.toFun (fun j => x j.succ)‖) ≤
        2 ^ p * (↑(l.choose i) * (Cf p i * Cg 0 (l - i) + Cf 0 i * Cg p (l - i))) := by
      intro i _
      set a := ‖x 0‖ with ha_def
      set b := ‖fun j : Fin n => x j.succ‖ with hb_def
      set F := ‖iteratedFDeriv ℝ i f.toFun (x 0)‖ with hF_def
      set G := ‖iteratedFDeriv ℝ (l - i) g.toFun (fun j => x j.succ)‖ with hG_def
      have ha_nn : 0 ≤ a := norm_nonneg _
      have hb_nn : 0 ≤ b := norm_nonneg _
      have hF_nn : 0 ≤ F := norm_nonneg _
      have hG_nn : 0 ≤ G := norm_nonneg _
      have hf1 : a ^ p * F ≤ Cf p i := hCf p i (x 0)
      have hg1 : G ≤ Cg 0 (l - i) := by
        have := hCg 0 (l - i) (fun j => x j.succ); simp at this; linarith
      have hf2 : F ≤ Cf 0 i := by
        have := hCf 0 i (x 0); simp at this; linarith
      have hg2 : b ^ p * G ≤ Cg p (l - i) := hCg p (l - i) (fun j => x j.succ)
      have hprod1 : a ^ p * F * G ≤ Cf p i * Cg 0 (l - i) :=
        mul_le_mul hf1 hg1 hG_nn (le_trans (mul_nonneg (pow_nonneg ha_nn _) hF_nn) hf1)
      have hprod2 : b ^ p * F * G ≤ Cf 0 i * Cg p (l - i) := by
        calc b ^ p * F * G = F * (b ^ p * G) := by ring
          _ ≤ Cf 0 i * Cg p (l - i) :=
            mul_le_mul hf2 hg2 (mul_nonneg (pow_nonneg hb_nn _) hG_nn)
              (le_trans hF_nn hf2)
      have hchoose_nn : (0 : ℝ) ≤ ↑(l.choose i) := Nat.cast_nonneg _
      calc ‖x‖ ^ p * (↑(l.choose i) * F * G)
          ≤ (2 ^ p * (a ^ p + b ^ p)) * (↑(l.choose i) * F * G) :=
            mul_le_mul_of_nonneg_right h_pow
              (mul_nonneg (mul_nonneg hchoose_nn hF_nn) hG_nn)
        _ = 2 ^ p * (↑(l.choose i) * (a ^ p * F * G + b ^ p * F * G)) := by ring
        _ ≤ 2 ^ p * (↑(l.choose i) * (Cf p i * Cg 0 (l - i) + Cf 0 i * Cg p (l - i))) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
            exact mul_le_mul_of_nonneg_left (add_le_add hprod1 hprod2) hchoose_nn
    -- Step 4: Assemble final bound
    calc ‖x‖ ^ p * ‖iteratedFDeriv ℝ l
          (fun y => f (y 0) * g (fun i => y i.succ)) x‖
        ≤ ‖x‖ ^ p * ∑ i ∈ Finset.range (l + 1),
          ↑(l.choose i) * ‖iteratedFDeriv ℝ i (f.toFun ∘ fun y => y 0) x‖ *
          ‖iteratedFDeriv ℝ (l - i) (g.toFun ∘ fun y => fun j => y j.succ) x‖ := by
          gcongr; exact hLeib
      _ ≤ ‖x‖ ^ p * ∑ i ∈ Finset.range (l + 1),
          ↑(l.choose i) * ‖iteratedFDeriv ℝ i f.toFun (x 0)‖ *
          ‖iteratedFDeriv ℝ (l - i) g.toFun (fun j => x j.succ)‖ := by
          gcongr with i hi
          · exact (hcf i x).trans le_rfl
          · exact (hcg (l - i) x).trans le_rfl
      _ = ∑ i ∈ Finset.range (l + 1),
          ‖x‖ ^ p * (↑(l.choose i) * ‖iteratedFDeriv ℝ i f.toFun (x 0)‖ *
          ‖iteratedFDeriv ℝ (l - i) g.toFun (fun j => x j.succ)‖) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range (l + 1),
          2 ^ p * (↑(l.choose i) * (Cf p i * Cg 0 (l - i) + Cf 0 i * Cg p (l - i))) := by
          exact Finset.sum_le_sum h_term
      _ = _ := by rw [← Finset.mul_sum]

@[simp]
theorem SchwartzMap.prependField_apply {n : ℕ}
    (f : 𝓢(E, ℂ)) (g : 𝓢(Fin n → E, ℂ)) (x : Fin (n + 1) → E) :
    f.prependField g x = f (x 0) * g (fun i => x i.succ) := rfl

@[simp]
theorem SchwartzMap.prependField_zero_right {n : ℕ}
    (f : 𝓢(E, ℂ)) :
    f.prependField (0 : 𝓢(Fin n → E, ℂ)) = 0 := by
  ext x; simp

@[simp]
theorem SchwartzMap.prependField_zero_left {n : ℕ}
    (g : 𝓢(Fin n → E, ℂ)) :
    (0 : 𝓢(E, ℂ)).prependField g = 0 := by
  ext x; simp

theorem SchwartzMap.prependField_add_right {n : ℕ}
    (f : 𝓢(E, ℂ)) (g₁ g₂ : 𝓢(Fin n → E, ℂ)) :
    f.prependField (g₁ + g₂) = f.prependField g₁ + f.prependField g₂ := by
  ext x; simp [mul_add]

@[simp]
theorem SchwartzMap.prependField_neg_right {n : ℕ}
    (f : 𝓢(E, ℂ)) (g : 𝓢(Fin n → E, ℂ)) :
    f.prependField (-g) = -(f.prependField g) := by
  ext x; simp [mul_neg]

theorem SchwartzMap.prependField_sub_right {n : ℕ}
    (f : 𝓢(E, ℂ)) (g₁ g₂ : 𝓢(Fin n → E, ℂ)) :
    f.prependField (g₁ - g₂) = f.prependField g₁ - f.prependField g₂ := by
  ext x; simp [mul_sub]

theorem SchwartzMap.prependField_smul_right {n : ℕ}
    (f : 𝓢(E, ℂ)) (c : ℂ) (g : 𝓢(Fin n → E, ℂ)) :
    f.prependField (c • g) = c • (f.prependField g) := by
  ext x; simp [mul_left_comm]

/-! ### Splitting and Appending -/

/-- splitFirst ∘ Fin.append extracts the first component. -/
@[simp]
theorem splitFirst_append {α : Type*} {m k : ℕ}
    (f : Fin m → α) (g : Fin k → α) :
    splitFirst m k (Fin.append f g) = f := by
  ext i
  simp [splitFirst, Fin.append_left]

/-- splitLast ∘ Fin.append extracts the second component. -/
@[simp]
theorem splitLast_append {α : Type*} {m k : ℕ}
    (f : Fin m → α) (g : Fin k → α) :
    splitLast m k (Fin.append f g) = g := by
  ext j
  simp [splitLast, Fin.append_right]

/-! ### Product Tensor Product

The product tensor product of n individual test functions f₁,...,fₙ ∈ S(E, ℂ) is
the n-point test function (f₁ ⊗ ... ⊗ fₙ)(x₁,...,xₙ) = f₁(x₁) · ... · fₙ(xₙ).

This is built iteratively using `prependField`. -/

/-- The product tensor product of n individual test functions.
    (productTensor fs)(x₁,...,xₙ) = f₁(x₁) · f₂(x₂) · ... · fₙ(xₙ) -/
def SchwartzMap.productTensor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    : {n : ℕ} → (Fin n → 𝓢(E, ℂ)) → 𝓢(Fin n → E, ℂ)
  | 0, _ => {
      toFun := fun _ => 1
      smooth' := contDiff_const
      decay' := by
        intro k n
        use 1
        intro x
        -- Domain Fin 0 → E is a singleton, so x = 0 and ‖x‖ = 0
        rw [show x = 0 from Subsingleton.elim x 0, norm_zero]
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp only [pow_zero, one_mul]
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · rw [norm_iteratedFDeriv_zero]; simp
          · simp [iteratedFDeriv_const_of_ne (𝕜 := ℝ)
              (Nat.pos_iff_ne_zero.mp hn) (1 : ℂ)]
        · simp [zero_pow (Nat.pos_iff_ne_zero.mp hk)]
    }
  | n + 1, fs => (fs 0).prependField (SchwartzMap.productTensor (fun i => fs i.succ))

@[simp]
theorem SchwartzMap.productTensor_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (fs : Fin 0 → 𝓢(E, ℂ)) (x : Fin 0 → E) :
    SchwartzMap.productTensor fs x = 1 := rfl

@[simp]
theorem SchwartzMap.productTensor_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (fs : Fin (n + 1) → 𝓢(E, ℂ)) (x : Fin (n + 1) → E) :
    SchwartzMap.productTensor fs x =
      fs 0 (x 0) * SchwartzMap.productTensor (fun i => fs i.succ) (fun i => x i.succ) := rfl

end
