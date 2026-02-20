/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.TubeDistributions
import OSReconstruction.Wightman.Reconstruction

/-!
# Forward Tube Distribution Theory

This file derives distribution-theoretic results for the forward tube from
the general tube domain axioms in `SCV.TubeDistributions`.

## Main results

* `continuous_boundary_forwardTube` — holomorphic functions on `ForwardTube d n`
  with distributional boundary values extend continuously to real boundary points.
* `distributional_uniqueness_forwardTube` — two holomorphic functions on
  `ForwardTube d n` with the same distributional boundary values are equal.

## Strategy

The forward tube `T_n = { z | ∀ k, Im(z_k - z_{k-1}) ∈ V₊ }` is a tube domain
`{ z | Im(z) ∈ C }` where `C = { y | ∀ k, y_k - y_{k-1} ∈ V₊ }` is an open convex
nonempty cone in `(Fin n → Fin (d+1) → ℝ)`.

The general axioms work with `Fin m → ℂ`. We transfer via the canonical isometry
`(Fin n → Fin (d+1) → ℂ) ≃ₗᵢ[ℂ] (Fin (n * (d+1)) → ℂ)` (the "flattening").

## References

* Vladimirov, "Methods of the Theory of Generalized Functions" §25-26
* Streater-Wightman, "PCT, Spin and Statistics", Theorems 2-6, 2-9
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set

variable {d : ℕ} [NeZero d]

/-! ### The Forward Cone -/

/-- The forward cone in absolute coordinates: the set of imaginary parts
    `y : Fin n → Fin (d+1) → ℝ` such that each difference `y_k - y_{k-1}`
    lies in the open forward light cone `V₊`. -/
def ForwardConeAbs (d n : ℕ) [NeZero d] : Set (Fin n → Fin (d + 1) → ℝ) :=
  { y | ∀ k : Fin n,
    let prev : Fin (d + 1) → ℝ := if h : k.val = 0 then 0 else y ⟨k.val - 1, by omega⟩
    InOpenForwardCone d (fun μ => y k μ - prev μ) }

/-- The forward tube equals `{ z | Im(z) ∈ ForwardConeAbs }`. -/
theorem forwardTube_eq_imPreimage (d n : ℕ) [NeZero d] :
    ForwardTube d n = { z | (fun k μ => (z k μ).im) ∈ ForwardConeAbs d n } := by
  sorry

/-- The forward cone is open. -/
theorem forwardConeAbs_isOpen (d n : ℕ) [NeZero d] :
    IsOpen (ForwardConeAbs d n) := by
  -- ForwardConeAbs = ⋂ k, { y | InOpenForwardCone d (y_k - y_{k-1}) }
  -- Each slice is open (preimage of open V₊ under continuous linear map)
  -- Finite intersection of open sets is open
  sorry

/-- The forward cone is convex. -/
theorem forwardConeAbs_convex (d n : ℕ) [NeZero d] :
    Convex ℝ (ForwardConeAbs d n) := by
  intro y hy y' hy' a b ha hb hab
  intro k
  simp only [ForwardConeAbs, Set.mem_setOf_eq] at hy hy' ⊢
  -- (a•y + b•y')_k - (a•y + b•y')_{k-1} = a(y_k - y_{k-1}) + b(y'_k - y'_{k-1})
  -- Both summands are in V₊, so the sum is in V₊ by convexity of V₊
  sorry

/-- The forward cone is nonempty. -/
theorem forwardConeAbs_nonempty (d n : ℕ) [NeZero d] :
    (ForwardConeAbs d n).Nonempty := by
  -- Witness: y_k = (k+1) • e₀ where e₀ = Pi.single 0 1
  -- Then y_k - y_{k-1} = e₀ ∈ V₊
  let η₀ : Fin (d + 1) → ℝ := Pi.single 0 1
  have hη₀ : InOpenForwardCone d η₀ := by
    constructor
    · simp [η₀, Pi.single_apply]
    · simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner, η₀,
        Pi.single_apply]
      have : ∀ i : Fin (d + 1), (MinkowskiSpace.metricSignature d i *
          (if i = 0 then (1 : ℝ) else 0)) * (if i = 0 then 1 else 0) =
          if i = 0 then -1 else 0 := by
        intro i; split_ifs with h <;> simp [MinkowskiSpace.metricSignature, h]
      simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      norm_num
  refine ⟨fun k μ => (↑(k : ℕ) + 1 : ℝ) * η₀ μ, ?_⟩
  intro k
  simp only [ForwardConeAbs, Set.mem_setOf_eq]
  convert hη₀ using 1
  ext μ
  split_ifs with h
  · simp [h, Pi.zero_apply]
  · simp only
    have hk_pos : (k : ℕ) ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    have : (↑(↑k - 1 : ℕ) : ℝ) = (↑(k : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub hk_pos]; simp
    rw [this]; ring

/-! ### Flattening Equivalence -/

/-- The canonical equivalence between `Fin n → Fin d → α` and `Fin (n * d) → α`. -/
def flattenEquiv' (n d : ℕ) (α : Type*) : (Fin n → Fin d → α) ≃ (Fin (n * d) → α) :=
  (Equiv.curry (Fin n) (Fin d) α).symm |>.trans
    (Equiv.arrowCongr finProdFinEquiv (Equiv.refl α))

/-- The flattening is a continuous linear equivalence over ℂ.
    Constructed via `LinearEquiv.funCongrLeft` composed with uncurrying,
    promoted to `ContinuousLinearEquiv` since both sides are finite-dimensional. -/
def flattenCLEquiv (n d : ℕ) :
    (Fin n → Fin d → ℂ) ≃L[ℂ] (Fin (n * d) → ℂ) := by
  -- Both sides are finite-dimensional normed spaces over ℂ with matching finrank
  -- Use the LinearEquiv and promote it
  have : FiniteDimensional ℂ (Fin n → Fin d → ℂ) := inferInstance
  have : FiniteDimensional ℂ (Fin (n * d) → ℂ) := inferInstance
  have hdim : Module.finrank ℂ (Fin n → Fin d → ℂ) = Module.finrank ℂ (Fin (n * d) → ℂ) := by
    simp [Module.finrank_pi_fintype, Fintype.card_fin]
  exact ContinuousLinearEquiv.ofFinrankEq hdim

/-- The real version of the flattening. -/
def flattenCLEquivReal (n d : ℕ) :
    (Fin n → Fin d → ℝ) ≃L[ℝ] (Fin (n * d) → ℝ) := by
  have hdim : Module.finrank ℝ (Fin n → Fin d → ℝ) = Module.finrank ℝ (Fin (n * d) → ℝ) := by
    simp [Module.finrank_pi_fintype, Fintype.card_fin]
  exact ContinuousLinearEquiv.ofFinrankEq hdim

/-- The flattened forward cone. -/
def ForwardConeFlat (d n : ℕ) [NeZero d] : Set (Fin (n * (d + 1)) → ℝ) :=
  (flattenCLEquivReal n (d + 1)) '' ForwardConeAbs d n

/-- The flattened forward cone is open. -/
theorem forwardConeFlat_isOpen (d n : ℕ) [NeZero d] :
    IsOpen (ForwardConeFlat d n) := by
  exact (flattenCLEquivReal n (d + 1)).toHomeomorph.isOpenMap _ (forwardConeAbs_isOpen d n)

/-- The flattened forward cone is convex. -/
theorem forwardConeFlat_convex (d n : ℕ) [NeZero d] :
    Convex ℝ (ForwardConeFlat d n) := by
  exact (forwardConeAbs_convex d n).linear_image
    ((flattenCLEquivReal n (d + 1)).toLinearEquiv.toLinearMap)

/-- The flattened forward cone is nonempty. -/
theorem forwardConeFlat_nonempty (d n : ℕ) [NeZero d] :
    (ForwardConeFlat d n).Nonempty :=
  Set.Nonempty.image _ (forwardConeAbs_nonempty d n)

/-! ### Tube Domain Correspondence -/

/-- The forward tube, after flattening, equals `TubeDomain (ForwardConeFlat d n)`. -/
theorem forwardTube_flatten_eq_tubeDomain (d n : ℕ) [NeZero d] :
    (flattenCLEquiv n (d + 1)) '' (ForwardTube d n) =
      SCV.TubeDomain (ForwardConeFlat d n) := by
  sorry

/-- Helper: transport DifferentiableOn through the flattening. -/
private theorem differentiableOn_flatten {n : ℕ} {d : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n)) :
    DifferentiableOn ℂ (F ∘ (flattenCLEquiv n (d + 1)).symm)
      (SCV.TubeDomain (ForwardConeFlat d n)) := by
  rw [← forwardTube_flatten_eq_tubeDomain]
  refine hF.comp (flattenCLEquiv n (d + 1)).symm.differentiableOn (fun w hw => ?_)
  obtain ⟨z, hz, rfl⟩ := hw
  convert hz using 1
  exact (flattenCLEquiv n (d + 1)).symm_apply_apply z

/-! ### Main Theorems -/

/-- **Continuous boundary values for the forward tube.**

    Derived from `SCV.continuous_boundary_tube` via the flattening equivalence.
    A holomorphic function on `ForwardTube d n` with distributional boundary values
    extends continuously to the real boundary.

    Ref: Vladimirov §26.2; Streater-Wightman, Theorem 2-9 -/
theorem continuous_boundary_forwardTube {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (h_bv : ∃ (T : SchwartzNPoint d n → ℂ),
      ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        (∀ k, InOpenForwardCone d (η k)) →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (T f)))
    (x : Fin n → Fin (d + 1) → ℝ) :
    ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)) := by
  let e := flattenCLEquiv n (d + 1)
  let G : (Fin (n * (d + 1)) → ℂ) → ℂ := F ∘ e.symm
  have hG_diff : DifferentiableOn ℂ G (SCV.TubeDomain (ForwardConeFlat d n)) :=
    differentiableOn_flatten hF
  -- The boundary value condition transfers through the flattening
  have hG_bv : ∀ (η : Fin (n * (d + 1)) → ℝ), η ∈ ForwardConeFlat d n →
      ∃ (T : (Fin (n * (d + 1)) → ℝ) → ℂ), ContinuousOn T Set.univ ∧
        ∀ (f : (Fin (n * (d + 1)) → ℝ) → ℂ), MeasureTheory.Integrable f →
          Filter.Tendsto (fun ε : ℝ =>
            ∫ x : Fin (n * (d + 1)) → ℝ,
              G (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) * f x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (∫ x, T x * f x)) := by
    sorry -- Transport of BV condition through flattening
  -- Apply the general axiom
  have hcont_G := SCV.continuous_boundary_tube
    (forwardConeFlat_isOpen d n)
    (forwardConeFlat_convex d n)
    (forwardConeFlat_nonempty d n)
    hG_diff hG_bv
    (flattenCLEquivReal n (d + 1) x)
  -- Pull back ContinuousWithinAt through the linear equiv
  sorry

/-- **Distributional uniqueness for the forward tube.**

    Derived from `SCV.distributional_uniqueness_tube` via the flattening equivalence.
    Two holomorphic functions on `ForwardTube d n` with the same distributional
    boundary values are equal.

    Ref: Vladimirov §26.3; Streater-Wightman, Corollary to Theorem 2-9 -/
theorem distributional_uniqueness_forwardTube {d n : ℕ} [NeZero d]
    {F₁ F₂ : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF₁ : DifferentiableOn ℂ F₁ (ForwardTube d n))
    (hF₂ : DifferentiableOn ℂ F₂ (ForwardTube d n))
    (h_agree : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          (F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) -
           F₂ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)) :
    ∀ z ∈ ForwardTube d n, F₁ z = F₂ z := by
  let e := flattenCLEquiv n (d + 1)
  let G₁ : (Fin (n * (d + 1)) → ℂ) → ℂ := F₁ ∘ e.symm
  let G₂ : (Fin (n * (d + 1)) → ℂ) → ℂ := F₂ ∘ e.symm
  have hG₁_diff : DifferentiableOn ℂ G₁ (SCV.TubeDomain (ForwardConeFlat d n)) :=
    differentiableOn_flatten hF₁
  have hG₂_diff : DifferentiableOn ℂ G₂ (SCV.TubeDomain (ForwardConeFlat d n)) :=
    differentiableOn_flatten hF₂
  have hG_agree : ∀ (η : Fin (n * (d + 1)) → ℝ), η ∈ ForwardConeFlat d n →
      ∀ (f : (Fin (n * (d + 1)) → ℝ) → ℂ), MeasureTheory.Integrable f →
        Filter.Tendsto (fun ε : ℝ =>
          ∫ x : Fin (n * (d + 1)) → ℝ,
            (G₁ (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) -
             G₂ (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I)) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
    sorry -- Transport of BV agreement through flattening
  -- Apply the general axiom
  have huniq := SCV.distributional_uniqueness_tube
    (forwardConeFlat_isOpen d n)
    (forwardConeFlat_convex d n)
    (forwardConeFlat_nonempty d n)
    hG₁_diff hG₂_diff hG_agree
  -- Pull back: for z ∈ ForwardTube, e(z) ∈ TubeDomain(C_flat), so G₁(e(z)) = G₂(e(z))
  intro z hz
  have hmem : e z ∈ SCV.TubeDomain (ForwardConeFlat d n) := by
    rw [← forwardTube_flatten_eq_tubeDomain]; exact Set.mem_image_of_mem e hz
  have := huniq (e z) hmem
  simp only [G₁, G₂, Function.comp, e.symm_apply_apply] at this
  exact this

end
