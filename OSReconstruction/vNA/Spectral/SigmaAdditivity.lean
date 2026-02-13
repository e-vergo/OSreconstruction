/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.vNA.Spectral.SpectralViaCayleyRMK
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# σ-Additivity Transfer for Spectral Measures

This file proves that the spectral projection-valued measure (PVM) constructed via the
RMK approach is σ-additive in the strong operator topology.

The key result `spectralProjection_sigma_additive` establishes:
for disjoint measurable sets Eᵢ ⊆ ℝ,
  P(⋃ Eᵢ)x = Σ P(Eᵢ)x   (strong convergence in H)

## Proof Strategy

The proof uses the norm identity:
  ‖P(⋃ Eᵢ)x - Σⁿ P(Eᵢ)x‖² = ‖P(⋃ Eᵢ)x‖² - Σⁿ ‖P(Eᵢ)x‖²

Combined with the scalar σ-additivity (from the Mathlib Measure):
  ‖P(⋃ Eᵢ)x‖² = Σ∞ ‖P(Eᵢ)x‖²

The difference ‖P(⋃ Eᵢ)x - Σⁿ P(Eᵢ)x‖² is the tail of a convergent series → 0.

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I", Theorem VII.7
-/

noncomputable section

open scoped InnerProduct ComplexConjugate Classical
open Filter Topology MeasureTheory

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Helper: norm squared equals diagonal measure -/

/-- The norm squared ‖P(E)x‖² equals the diagonal spectral measure evaluated on E.
    Specifically: ‖spectralMeasureFromRMK T hT hsa C E hE x‖² =
    (spectralMeasureDiagonal C.U hU x (cayleyToCircle '' E)).toReal -/
theorem norm_sq_spectralMeasureFromRMK_eq_diag
    (T : UnboundedOperator H) (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT)
    (C : CayleyTransform T hT hsa) (E : Set ℝ) (hE : MeasurableSet E) (x : H) :
    ‖spectralMeasureFromRMK T hT hsa C E hE x‖ ^ 2 =
    (spectralMeasureDiagonal C.U (cayley_mem_unitary T hT hsa C) x
      (cayleyToCircle '' E)).toReal := by
  set hU := cayley_mem_unitary T hT hsa C
  set E_circle := cayleyToCircle '' E
  set hE_circle := cayleyToCircle_measurableSet_image E hE
  set P := spectralMeasureFromRMK T hT hsa C E hE
  -- P is self-adjoint and idempotent
  have hsa_P := spectralMeasureFromRMK_selfAdjoint T hT hsa C E hE
  have hidem_P := spectralMeasureFromRMK_idempotent T hT hsa C E hE
  -- Step: ⟨P x, P x⟩ = ⟨x, P x⟩ (using self-adjoint + idempotent)
  have key : @inner ℂ H _ (P x) (P x) = @inner ℂ H _ x (P x) := by
    have step1 : @inner ℂ H _ (P x) (P x) = @inner ℂ H _ x (P.adjoint (P x)) :=
      (ContinuousLinearMap.adjoint_inner_right P x (P x)).symm
    rw [step1, hsa_P, show P (P x) = (P ∘L P) x from rfl, hidem_P]
  -- ‖P x‖² = re⟨P x, P x⟩ = re⟨x, P x⟩
  have h_norm_sq : ‖P x‖ ^ 2 = (@inner ℂ H _ x (P x)).re := by
    have h_iss := @inner_self_eq_norm_sq ℂ H _ _ _ (P x)
    -- h_iss : RCLike.re ⟨P x, P x⟩ = ‖P x‖² (RCLike.re = Complex.re for ℂ)
    have h_key_re := congr_arg Complex.re key
    -- h_key_re : Complex.re ⟨P x, P x⟩ = Complex.re ⟨x, P x⟩
    -- Bridge RCLike.re to Complex.re (definitionally equal for ℂ)
    have h_iss' : (@inner ℂ H _ (P x) (P x)).re = ‖P x‖ ^ 2 := h_iss
    linarith
  -- ⟨x, P(E) x⟩ = spectralMeasurePolarized x x E_circle
  have h_inner_eq : @inner ℂ H _ x (P x) =
      spectralMeasurePolarized C.U hU x x E_circle hE_circle := by
    show @inner ℂ H _ x (spectralMeasureFromRMK T hT hsa C E hE x) = _
    unfold spectralMeasureFromRMK spectralProjectionOfUnitary
    rw [← sesquilinearToOperator_inner]
  -- spectralMeasurePolarized x x E_circle = μ_x(E_circle).toReal
  have h_diag := spectralMeasurePolarized_diag C.U hU x E_circle hE_circle
  -- Combine
  rw [h_norm_sq, h_inner_eq, h_diag, Complex.ofReal_re]

/-- cayleyToCircle maps disjoint sets to disjoint sets (by injectivity). -/
theorem cayleyToCircle_image_disjoint {E F : Set ℝ} (h : Disjoint E F) :
    Disjoint (cayleyToCircle '' E) (cayleyToCircle '' F) :=
  Set.disjoint_image_of_injective cayleyToCircle_injective h

/-- The key σ-additivity result: for disjoint measurable sets Eᵢ ⊆ ℝ,
    P(⋃ Eᵢ)x = Σ P(Eᵢ)x in norm.

    This uses:
    1. ‖P(⋃ Eᵢ)x - Σⁿ P(Eᵢ)x‖² = ‖P(⋃ Eᵢ)x‖² - Σⁿ ‖P(Eᵢ)x‖²
    2. ‖P(⋃ Eᵢ)x‖² = Σ∞ ‖P(Eᵢ)x‖² (from σ-additivity of spectralMeasureDiagonal) -/
theorem spectralProjection_sigma_additive
    (T : UnboundedOperator H) (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT)
    (C : CayleyTransform T hT hsa) (E : ℕ → Set ℝ)
    (hE_meas : ∀ i, MeasurableSet (E i))
    (hE_disj : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (x : H) :
    Tendsto (fun n => ∑ i ∈ Finset.range n,
      spectralMeasureFromRMK T hT hsa C (E i) (hE_meas i) x)
      atTop (nhds (spectralMeasureFromRMK T hT hsa C (⋃ i, E i)
        (MeasurableSet.iUnion hE_meas) x)) := by
  set hU := cayley_mem_unitary T hT hsa C
  set P := fun i => spectralMeasureFromRMK T hT hsa C (E i) (hE_meas i) with hP_def
  set Q := spectralMeasureFromRMK T hT hsa C (⋃ i, E i) (MeasurableSet.iUnion hE_meas)
    with hQ_def
  -- Abbreviations for Circle images
  set E_c := fun i => cayleyToCircle '' (E i) with hE_c_def
  set hE_c_meas := fun i => cayleyToCircle_measurableSet_image (E i) (hE_meas i)
  -- The diagonal measure
  set μ := spectralMeasureDiagonal C.U hU x with hμ_def
  -- Finite measure instance (from SpectralFunctionalViaRMK)
  haveI hμ_fin : IsFiniteMeasure μ := spectralMeasureDiagonal_isFiniteMeasure C.U hU x
  -- Disjointness of Circle images
  have hE_c_disj : ∀ i j, i ≠ j → Disjoint (E_c i) (E_c j) := by
    intro i j hij
    exact cayleyToCircle_image_disjoint (hE_disj i j hij)
  -- Multiplicativity: Q ∘L P(Eᵢ) = P(Eᵢ) (since Eᵢ ⊆ ⋃ Eₖ)
  have hQP : ∀ i, Q ∘L P i = P i := by
    intro i
    have hsub : E i ⊆ ⋃ j, E j := Set.subset_iUnion E i
    have hmult := spectralMeasureFromRMK_multiplicative T hT hsa C
      (⋃ j, E j) (E i) (MeasurableSet.iUnion hE_meas) (hE_meas i)
    have hcongr : spectralMeasureFromRMK T hT hsa C ((⋃ j, E j) ∩ E i)
        ((MeasurableSet.iUnion hE_meas).inter (hE_meas i)) =
        spectralMeasureFromRMK T hT hsa C (E i) (hE_meas i) := by
      congr 1
      exact Set.inter_eq_right.mpr hsub
    exact hmult.symm.trans hcongr
  -- Self-adjointness of Q
  have hQsa : Q.adjoint = Q :=
    spectralMeasureFromRMK_selfAdjoint T hT hsa C (⋃ j, E j) (MeasurableSet.iUnion hE_meas)
  -- Orthogonality: ⟨P(Eᵢ)x, P(Eⱼ)x⟩ = 0 for i ≠ j
  have horth : ∀ i j, i ≠ j → @inner ℂ H _ (P i x) (P j x) = 0 := by
    intro i j hij
    have h_disj : E i ∩ E j = ∅ := Set.disjoint_iff_inter_eq_empty.mp (hE_disj i j hij)
    have hmult := spectralMeasureFromRMK_multiplicative T hT hsa C
      (E i) (E j) (hE_meas i) (hE_meas j)
    have hsa_Pi := spectralMeasureFromRMK_selfAdjoint T hT hsa C (E i) (hE_meas i)
    have hcongr : spectralMeasureFromRMK T hT hsa C (E i ∩ E j)
        ((hE_meas i).inter (hE_meas j)) =
        spectralMeasureFromRMK T hT hsa C ∅ MeasurableSet.empty := by
      congr 1
    have h_empty : spectralMeasureFromRMK T hT hsa C (E i ∩ E j)
        ((hE_meas i).inter (hE_meas j)) = 0 :=
      hcongr.trans (spectralMeasureFromRMK_empty T hT hsa C)
    have hPiPj : P i ∘L P j = 0 := hmult.symm.trans h_empty
    calc @inner ℂ H _ (P i x) (P j x)
        = @inner ℂ H _ x ((P i).adjoint (P j x)) :=
          (ContinuousLinearMap.adjoint_inner_right (P i) x _).symm
      _ = @inner ℂ H _ x (P i (P j x)) := by rw [hsa_Pi]
      _ = @inner ℂ H _ x ((P i ∘L P j) x) := rfl
      _ = @inner ℂ H _ x ((0 : H →L[ℂ] H) x) := by rw [hPiPj]
      _ = 0 := by simp
  -- Now the main proof via norm convergence
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Norm squared of P(Eᵢ)x equals μ(E_c i).toReal
  have hnorm_sq : ∀ i, ‖P i x‖ ^ 2 = (μ (E_c i)).toReal := by
    intro i
    exact norm_sq_spectralMeasureFromRMK_eq_diag T hT hsa C (E i) (hE_meas i) x
  -- And for Q
  have hnorm_sq_Q : ‖Q x‖ ^ 2 = (μ (cayleyToCircle '' (⋃ i, E i))).toReal := by
    exact norm_sq_spectralMeasureFromRMK_eq_diag T hT hsa C _ _ x
  -- cayleyToCircle '' (⋃ i, E i) = ⋃ i, cayleyToCircle '' E i
  have himg_union : cayleyToCircle '' (⋃ i, E i) = ⋃ i, E_c i := Set.image_iUnion
  -- Each E_c i has finite measure
  have hμ_ne_top : ∀ i, μ (E_c i) ≠ ⊤ := fun i => measure_ne_top μ (E_c i)
  -- σ-additivity of the measure: μ(⋃ E_c i) = Σ μ(E_c i)
  have hμ_sigma : μ (⋃ i, E_c i) = ∑' i, μ (E_c i) :=
    measure_iUnion (fun i j hij => hE_c_disj i j hij) (fun i => hE_c_meas i)
  -- Summable: Σ μ(E_c i).toReal converges (from finiteness of tsum)
  have hsummable : Summable (fun i => (μ (E_c i)).toReal) := by
    apply ENNReal.summable_toReal
    rw [← hμ_sigma]
    exact measure_ne_top μ _
  -- The tsum in ENNReal converts to tsum in ℝ
  have htsum_eq : (∑' i, μ (E_c i)).toReal = ∑' i, (μ (E_c i)).toReal :=
    ENNReal.tsum_toReal_eq hμ_ne_top
  -- Summable in terms of norms
  have hsummable_norm : Summable (fun i => ‖P i x‖ ^ 2) := by
    convert hsummable using 1; ext i; exact hnorm_sq i
  -- Key: ‖Qx‖² = Σ∞ ‖P(Eᵢ)x‖²
  have hQ_eq_sum : ‖Q x‖ ^ 2 = ∑' i, ‖P i x‖ ^ 2 := by
    rw [hnorm_sq_Q, himg_union, hμ_sigma, htsum_eq]
    congr 1; ext i; exact (hnorm_sq i).symm
  -- The partial sums of ‖P(Eᵢ)x‖² converge to ‖Qx‖²
  have hpartial_tendsto : Tendsto (fun n => ∑ i ∈ Finset.range n, ‖P i x‖ ^ 2)
      atTop (nhds (‖Q x‖ ^ 2)) := by
    rw [hQ_eq_sum]
    exact hsummable_norm.hasSum.tendsto_sum_nat
  -- Pythagorean theorem for the partial sums
  have hpythag : ∀ m, ‖∑ i ∈ Finset.range m, P i x‖ ^ 2 =
      ∑ i ∈ Finset.range m, ‖P i x‖ ^ 2 := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have horth_last : @inner ℂ H _ (∑ i ∈ Finset.range k, P i x) (P k x) = 0 := by
        rw [sum_inner]
        apply Finset.sum_eq_zero
        intro i hi
        exact horth i k (Nat.ne_of_lt (Finset.mem_range.mp hi))
      have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth_last
      have hsq1 : ‖∑ i ∈ Finset.range k, P i x + P k x‖ ^ 2 =
          ‖∑ i ∈ Finset.range k, P i x + P k x‖ *
          ‖∑ i ∈ Finset.range k, P i x + P k x‖ := sq _
      have hsq2 : ‖∑ i ∈ Finset.range k, P i x‖ ^ 2 =
          ‖∑ i ∈ Finset.range k, P i x‖ * ‖∑ i ∈ Finset.range k, P i x‖ := sq _
      have hsq3 : ‖P k x‖ ^ 2 = ‖P k x‖ * ‖P k x‖ := sq _
      linarith
  -- Inner product of Q with partial sums: re⟨Qx, Σⁿ P(Eᵢ)x⟩ = Σⁿ ‖P(Eᵢ)x‖²
  have hinner_sum : ∀ m, (@inner ℂ H _ (Q x) (∑ i ∈ Finset.range m, P i x)).re =
      ∑ i ∈ Finset.range m, ‖P i x‖ ^ 2 := by
    intro m
    rw [inner_sum, Complex.re_sum]
    congr 1; ext i
    calc (@inner ℂ H _ (Q x) (P i x)).re
        = (@inner ℂ H _ x (Q.adjoint (P i x))).re := by
          rw [ContinuousLinearMap.adjoint_inner_right]
      _ = (@inner ℂ H _ x (Q (P i x))).re := by rw [hQsa]
      _ = (@inner ℂ H _ x ((Q ∘L P i) x)).re := rfl
      _ = (@inner ℂ H _ x (P i x)).re := by rw [hQP i]
      _ = ‖P i x‖ ^ 2 := by
          rw [hnorm_sq i]
          have h_inner2 : @inner ℂ H _ x (P i x) =
              spectralMeasurePolarized C.U hU x x (E_c i) (hE_c_meas i) := by
            show @inner ℂ H _ x (spectralMeasureFromRMK T hT hsa C (E i) (hE_meas i) x) = _
            unfold spectralMeasureFromRMK spectralProjectionOfUnitary
            rw [← sesquilinearToOperator_inner]
          have h_diag := spectralMeasurePolarized_diag C.U hU x (E_c i) (hE_c_meas i)
          rw [h_inner2, h_diag, Complex.ofReal_re]
  -- Norm identity: ‖Qx - Sₙx‖² = ‖Qx‖² - Σⁿ ‖P(Eᵢ)x‖²
  have hnorm_diff : ∀ n, ‖Q x - ∑ i ∈ Finset.range n, P i x‖ ^ 2 =
      ‖Q x‖ ^ 2 - ∑ i ∈ Finset.range n, ‖P i x‖ ^ 2 := by
    intro n
    have hexp := @norm_sub_sq ℂ H _ _ _ (Q x) (∑ i ∈ Finset.range n, P i x)
    -- hexp uses RCLike.re; bridge to .re via change
    have hinner_bridge : RCLike.re (@inner ℂ H _ (Q x) (∑ i ∈ Finset.range n, P i x)) =
        ∑ i ∈ Finset.range n, ‖P i x‖ ^ 2 := by
      change (@inner ℂ H _ (Q x) (∑ i ∈ Finset.range n, P i x)).re = _
      exact hinner_sum n
    rw [hexp, hinner_bridge, hpythag n]
    ring
  -- Get N₀ such that for n ≥ N₀, ‖Qx‖² - Σⁿ ‖P(Eᵢ)x‖² < ε²
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  rw [Metric.tendsto_atTop] at hpartial_tendsto
  obtain ⟨N₀, hN₀⟩ := hpartial_tendsto (ε ^ 2) hε2
  use N₀
  intro n hn
  rw [dist_comm, dist_eq_norm]
  -- Goal: ‖Qx - Sₙx‖ < ε
  by_cases hzero : ‖Q x - ∑ i ∈ Finset.range n, P i x‖ = 0
  · rw [hzero]; exact hε
  · have hdist := hN₀ n hn
    rw [dist_comm, Real.dist_eq] at hdist
    have hge_zero : ‖Q x‖ ^ 2 - ∑ i ∈ Finset.range n, ‖P i x‖ ^ 2 ≥ 0 := by
      have : ‖Q x - ∑ i ∈ Finset.range n, P i x‖ ^ 2 ≥ 0 := sq_nonneg _
      rw [hnorm_diff] at this
      linarith
    rw [abs_of_nonneg hge_zero] at hdist
    have h_sq_lt : ‖Q x - ∑ i ∈ Finset.range n, P i x‖ ^ 2 < ε ^ 2 := by
      rw [hnorm_diff]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h_sq_lt

end
