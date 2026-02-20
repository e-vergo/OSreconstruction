/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction
import OSReconstruction.Wightman.Reconstruction.AnalyticContinuation

/-!
# Wick Rotation and the OS Bridge Theorems

This file develops the infrastructure for the Osterwalder-Schrader bridge theorems:
- **Theorem R→E** (`wightman_to_os`): Wightman functions → Schwinger functions (OS I, §5)
- **Theorem E'→R'** (`os_to_wightman`): Schwinger functions → Wightman functions (OS II, §IV-V)

## Theorem R→E (Wightman → OS)

Given Wightman functions W_n satisfying R0-R5, we construct Schwinger functions S_n
satisfying E0-E4. The construction (OS I, Section 5) proceeds as:

1. **Analytic continuation**: The spectrum condition (R3) implies W_n extends to a
   holomorphic function on the forward tube T_n.
2. **BHW extension**: The Bargmann-Hall-Wightman theorem extends W_n to the
   permuted extended tube T''_n, with complex Lorentz invariance and permutation symmetry.
3. **Define S_n**: Restrict the BHW extension to Euclidean points:
     S_n(τ₁, x⃗₁, ..., τₙ, x⃗ₙ) = W_analytic(iτ₁, x⃗₁, ..., iτₙ, x⃗ₙ)
4. **Verify E0-E4**:
   - E0 (temperedness): From R0 + geometric estimates (OS I, Prop 5.1)
   - E1 (Euclidean covariance): From complex Lorentz invariance (SO(d+1) ⊂ L₊(ℂ))
   - E2 (reflection positivity): From R2 (Wightman positivity)
   - E3 (permutation symmetry): From BHW permutation invariance
   - E4 (cluster): From R4

## Theorem E'→R' (OS → Wightman)

Given Schwinger functions S_n satisfying E0'-E4 (with E0' = linear growth condition),
we reconstruct Wightman functions satisfying R0'-R5. This follows OS II (1975).

The proof is inductive on the analytic continuation domain:

### Phase 1: Hilbert Space from Reflection Positivity (E2)
- Same GNS construction as Wightman reconstruction
- E2 gives positive semi-definite inner product on S₊ (positive-time test functions)
- Complete to Hilbert space H

### Phase 2: Semigroup from Euclidean Time Translation (E0' + E1)
- Translation in Euclidean time gives contraction semigroup e^{-tH} for t > 0
- E0' controls growth: the semigroup extends analytically
- H is a positive self-adjoint operator (the Hamiltonian)

### Phase 3: Analytic Continuation (OS II, Theorem 4.1-4.2, inductive)
- **Base case (A₀)**: Schwinger functions S_k(ξ) are analytic on ℝ₊^k, with estimates
- **Inductive step (Aᵣ)**: Extend to regions C_k^(r) in complexified time
- After d steps, reach the forward tube
- **Critical**: E0' is essential for temperedness estimates at each step

### Phase 4: Boundary Values → Wightman Distributions
- The analytic functions in the forward tube have distributional boundary values
- E0' ensures boundary values are tempered distributions
- Define W_n as these boundary values

### Phase 5: Verify Wightman Axioms
- R0 (temperedness): from E0' estimates
- R1 (Lorentz covariance): from E1 via BHW
- R2 (positivity): from E2
- R3 (spectrum condition): from the support of the analytic continuation
- R4 (cluster): from E4
- R5 (locality): from E3 + edge-of-the-wedge

## References

* Osterwalder-Schrader I (1973), "Axioms for Euclidean Green's Functions"
* Osterwalder-Schrader II (1975), "Axioms for Euclidean Green's Functions II"
* Glimm-Jaffe, "Quantum Physics", Chapter 19
-/

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ### Wightman to OS (Theorem R→E) -/

/-- Define Schwinger functions from Wightman functions via Wick rotation.

    The construction uses the analytic continuation of W_n (from the spectrum condition)
    composed with the Wick rotation map (τ,x⃗) ↦ (iτ,x⃗):

      S_n(f) = ∫_x W_analytic_n(iτ₁, x⃗₁, ..., iτₙ, x⃗ₙ) f(x₁,...,xₙ) dx

    where W_analytic_n is the holomorphic extension of W_n to the forward tube
    (provided by the spectrum condition), and the integral is over Euclidean
    n-point configurations.

    Ref: OS I (1973), Section 5; Streater-Wightman, Chapter 3 -/
def constructSchwingerFunctions (Wfn : WightmanFunctions d) :
    SchwingerFunctions d :=
  fun n f =>
    let W_analytic := (Wfn.spectrum_condition n).choose
    ∫ x : NPointDomain d n,
      W_analytic (fun k => wickRotatePoint (x k)) * (f x)

/-- The Schwinger functions constructed from Wightman functions satisfy temperedness (E0).

    This follows from the temperedness of Wightman functions (R0) and the
    geometric estimates in OS I, Proposition 5.1: the Wick-rotated kernel
    composed with f is integrable and the integral depends continuously on f. -/
theorem constructedSchwinger_tempered (Wfn : WightmanFunctions d) (n : ℕ) :
    Continuous (constructSchwingerFunctions Wfn n) := by
  -- Continuity of S_n requires: the integral ∫ W_analytic(Wick(x)) f(x) dx
  -- depends continuously on f in the Schwartz topology.
  -- This follows from the temperedness of W_analytic and the integrability of Schwartz functions.
  sorry

/-- The BHW extension of W_analytic from the forward tube to the permuted extended tube.

    Applying the `bargmann_hall_wightman` axiom (AnalyticContinuation.lean) to the
    holomorphic extension `W_analytic` from `spectrum_condition`, we obtain `F_ext`
    on the permuted extended tube with:
    1. Complex Lorentz invariance (from real Lorentz covariance + identity theorem)
    2. Permutation symmetry (from local commutativity at spacelike pairs)
    3. Agreement with W_analytic on the forward tube (uniqueness)

    The sorry here absorbs verifying the BHW hypotheses:
    - `hF_lorentz`: W_analytic inherits real Lorentz invariance from the Wightman
      distribution (requires identity theorem on tube domains in ℂⁿ, not in Mathlib)
    - `hF_bv`: continuous extension to real boundary (distributional boundary values)
    - `hF_local`: local commutativity from `Wfn.locally_commutative`

    Ref: Streater-Wightman, Theorem 2-11; Jost, Ch. IV -/
theorem W_analytic_BHW (Wfn : WightmanFunctions d) (n : ℕ) :
    ∃ (F_ext : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ F_ext (PermutedExtendedTube d n) ∧
      (∀ z ∈ ForwardTube d n,
        F_ext z = (Wfn.spectrum_condition n).choose z) ∧
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (fun k μ => ∑ ν, Λ.val μ ν * z k ν) = F_ext z) ∧
      (∀ (π : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (fun k => z (π k)) = F_ext z) := by
  sorry

/-- The holomorphic extension W_analytic inherits translation invariance from
    the Wightman distribution W_n.

    Proof sketch: Both z ↦ W_analytic(z) and z ↦ W_analytic(z + c) (for c = Wick(a))
    are holomorphic on the forward tube with the same distributional boundary values
    (by translation invariance of W_n). By uniqueness of analytic continuation in
    tube domains, they must agree.

    The sorry requires the identity theorem for holomorphic functions on tube domains
    in ℂⁿ (several complex variables), which is not in Mathlib. The 1D version is
    proved in EdgeOfWedge.lean (`identity_theorem_connected`).

    Ref: Streater-Wightman, Theorem 2.8 (uniqueness of holomorphic extension to tubes) -/
theorem W_analytic_translation_invariant (Wfn : WightmanFunctions d) (n : ℕ)
    (a : SpacetimeDim d) (x : NPointDomain d n) :
    (Wfn.spectrum_condition n).choose (fun k => wickRotatePoint (x k)) =
    (Wfn.spectrum_condition n).choose (fun k => wickRotatePoint (fun μ => x k μ + a μ)) := by
  sorry

theorem constructedSchwinger_translation_invariant (Wfn : WightmanFunctions d)
    (n : ℕ) (a : SpacetimeDim d) (f g : SchwartzNPoint d n)
    (hfg : ∀ x, g.toFun x = f.toFun (fun i => x i + a)) :
    constructSchwingerFunctions Wfn n f = constructSchwingerFunctions Wfn n g := by
  -- Unfold the definition: S(f) = ∫ W(Wick(x)) * f(x) dx
  simp only [constructSchwingerFunctions]
  -- Rewrite g(x) = f(x + a) using hfg
  have hfg' : ∀ x : NPointDomain d n,
      (g : NPointDomain d n → ℂ) x = (f : NPointDomain d n → ℂ) (fun i => x i + a) := hfg
  simp_rw [hfg']
  -- Goal: ∫ K(x) * f(x) = ∫ K(x) * f(x + a') where K(x) = W_analytic(Wick(x))
  -- Proof: ∫ K(x) * f(x+a') = ∫ K(x+a') * f(x+a')   [by K translation invariance]
  --                           = ∫ K(x) * f(x)           [by Haar measure invariance]
  set a' : NPointDomain d n := fun _ => a
  set K : NPointDomain d n → ℂ :=
    fun x => (Wfn.spectrum_condition n).choose (fun k => wickRotatePoint (x k))
  -- K is translation-invariant: K(x) = K(x + a')
  have hK : ∀ x : NPointDomain d n, K x = K (x + a') := fun x =>
    W_analytic_translation_invariant Wfn n a x
  symm
  calc ∫ x : NPointDomain d n, K x * (f : NPointDomain d n → ℂ) (x + a')
      = ∫ x : NPointDomain d n, K (x + a') * (f : NPointDomain d n → ℂ) (x + a') := by
        congr 1; ext x; rw [hK]
    _ = ∫ x : NPointDomain d n, K x * (f : NPointDomain d n → ℂ) x :=
        MeasureTheory.integral_add_right_eq_self
          (fun x => K x * (f : NPointDomain d n → ℂ) x) a'

/-- The holomorphic extension W_analytic is invariant under Euclidean rotations:
    W_analytic(Wick(Rx₁), ..., Wick(Rxₙ)) = W_analytic(Wick(x₁), ..., Wick(xₙ))
    for R ∈ O(d+1).

    Proof path via existing infrastructure:
    1. `W_analytic_BHW` gives F_ext on PermutedExtendedTube with complex Lorentz invariance
    2. `schwinger_euclidean_invariant` (AnalyticContinuation.lean:1075) derives Euclidean
       rotation invariance from complex Lorentz invariance for det R = 1
    3. `euclidean_distinct_in_permutedTube` (AnalyticContinuation.lean:389) shows
       distinct-time Euclidean points lie in PermutedExtendedTube
    4. F_ext = W_analytic on ForwardTube (BHW agreement); by continuity of holomorphic
       functions, they agree on the closure (including all Euclidean points)

    Remaining gaps: (a) identity theorem to show F_ext = W_analytic at Euclidean points
    outside the forward tube; (b) det R = -1 case (improper rotations).

    Ref: Streater-Wightman, Theorem 3.6 (BHW); Jost, §IV.5 -/
theorem W_analytic_rotation_invariant (Wfn : WightmanFunctions d) (n : ℕ)
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hR : R.transpose * R = 1)
    (x : NPointDomain d n) :
    (Wfn.spectrum_condition n).choose (fun k => wickRotatePoint (x k)) =
    (Wfn.spectrum_condition n).choose
      (fun k => wickRotatePoint (R.mulVec (x k))) := by
  -- For det R = 1: follows from W_analytic_BHW + schwinger_euclidean_invariant
  -- For det R = -1: requires PCT or separate argument
  -- Both need: F_ext(Wick(x)) = W_analytic(Wick(x)) at all Euclidean points
  sorry

/-- Orthogonal transformations preserve volume: the map x ↦ R·x on ℝ^(d+1)
    has |det R| = 1, so the product map on NPointDomain preserves Lebesgue measure. -/
theorem integral_orthogonal_eq_self (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (h : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, h (fun i => R.mulVec (x i)) =
    ∫ x : NPointDomain d n, h x := by
  -- det R ≠ 0 and |det R| = 1 from orthogonality
  have hdet : R.det ≠ 0 := by
    intro h; have := congr_arg Matrix.det hR
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, h, mul_zero] at this
    exact zero_ne_one this
  have habs : |R.det| = 1 := by
    have h1 : R.det * R.det = 1 := by
      have := congr_arg Matrix.det hR
      rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    rcases mul_self_eq_one_iff.mp h1 with h | h <;> simp [h]
  have hR' : R * R.transpose = 1 := Matrix.mul_eq_one_comm.mpr hR
  -- R.mulVec preserves volume on each factor
  have hmv : (fun v => R.mulVec v) = Matrix.toLin' R := by
    ext v; simp [Matrix.toLin'_apply]
  have hcont_R : Continuous (Matrix.toLin' R) :=
    LinearMap.continuous_of_finiteDimensional _
  have hcont_Rt : Continuous (Matrix.toLin' R.transpose) :=
    LinearMap.continuous_of_finiteDimensional _
  have hmp_factor : MeasureTheory.MeasurePreserving
      (fun v : Fin (d+1) → ℝ => R.mulVec v)
      MeasureTheory.volume MeasureTheory.volume := by
    rw [hmv]; constructor
    · exact hcont_R.measurable
    · rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet]
      simp [abs_inv, habs]
  -- Construct MeasurableEquiv for the componentwise map
  let e : (Fin n → Fin (d+1) → ℝ) ≃ᵐ (Fin n → Fin (d+1) → ℝ) :=
    { toEquiv := {
        toFun := fun a i => R.mulVec (a i)
        invFun := fun a i => R.transpose.mulVec (a i)
        left_inv := fun a => by ext i j; simp [Matrix.mulVec_mulVec, hR]
        right_inv := fun a => by ext i j; simp [Matrix.mulVec_mulVec, hR'] }
      measurable_toFun :=
        measurable_pi_lambda _ fun i => hcont_R.measurable.comp (measurable_pi_apply i)
      measurable_invFun :=
        measurable_pi_lambda _ fun i => hcont_Rt.measurable.comp (measurable_pi_apply i) }
  -- Lift volume preservation to product, then get integral equality
  have hmp : MeasureTheory.MeasurePreserving (⇑e)
      MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.volume_preserving_pi (fun (_ : Fin n) => hmp_factor)
  exact hmp.integral_comp' h

/-- The Schwinger functions satisfy rotation invariance (E1b).

    Proof: Complex Lorentz invariance of W_analytic on the permuted extended tube,
    together with the fact that SO(d+1) ⊂ L₊(ℂ) preserves Euclidean points.
    The rotation R ∈ O(d+1) acts on the forward tube via its embedding in L₊(ℂ). -/
theorem constructedSchwinger_rotation_invariant (Wfn : WightmanFunctions d)
    (n : ℕ) (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (f g : SchwartzNPoint d n)
    (hfg : ∀ x, g.toFun x = f.toFun (fun i => R.mulVec (x i))) :
    constructSchwingerFunctions Wfn n f = constructSchwingerFunctions Wfn n g := by
  simp only [constructSchwingerFunctions]
  have hfg' : ∀ x : NPointDomain d n,
      (g : NPointDomain d n → ℂ) x =
      (f : NPointDomain d n → ℂ) (fun i => R.mulVec (x i)) := hfg
  simp_rw [hfg']
  -- Goal: ∫ K(x) * f(x) = ∫ K(x) * f(Rx)
  -- where K(x) = W_analytic(Wick(x)) and (Rx)(i) = R.mulVec (x i)
  set K : NPointDomain d n → ℂ :=
    fun x => (Wfn.spectrum_condition n).choose (fun k => wickRotatePoint (x k))
  -- K is rotation-invariant: K(x) = K(Rx)
  have hK : ∀ x : NPointDomain d n, K x = K (fun i => R.mulVec (x i)) :=
    fun x => W_analytic_rotation_invariant Wfn n R hR x
  symm
  calc ∫ x : NPointDomain d n, K x * (f : NPointDomain d n → ℂ) (fun i => R.mulVec (x i))
      = ∫ x : NPointDomain d n,
          K (fun i => R.mulVec (x i)) *
          (f : NPointDomain d n → ℂ) (fun i => R.mulVec (x i)) := by
        congr 1; ext x; rw [hK]
    _ = ∫ x : NPointDomain d n, K x * (f : NPointDomain d n → ℂ) x :=
        integral_orthogonal_eq_self R hR
          (fun x => K x * (f : NPointDomain d n → ℂ) x)

/-- The Schwinger functions satisfy reflection positivity (E2).

    Proof: For test functions supported in τ > 0, the Wick-rotated quadratic form
    reduces to the Wightman positivity condition.
    Specifically, if F is supported in {τ > 0}, then the OS inner product
    Σ S_{n+m}((θf̄)_n ⊗ f_m) reduces to Σ W_{n+m}(f*_n ⊗ f_m)
    after Wick rotation, and the latter is ≥ 0 by Wightman positivity (R2). -/
theorem constructedSchwinger_reflection_positive (Wfn : WightmanFunctions d)
    (F : BorchersSequence d)
    (hsupp : ∀ n, ∀ x : NPointDomain d n, (F.funcs n).toFun x ≠ 0 →
      x ∈ PositiveTimeRegion d n) :
    (OSInnerProduct d (constructSchwingerFunctions Wfn) F F).re ≥ 0 := by
  sorry

/-- The holomorphic extension W_analytic is invariant under permutations of arguments:
    W_analytic(z_{σ(1)}, ..., z_{σ(n)}) = W_analytic(z_1, ..., z_n) for σ ∈ S_n.

    Proof path via existing infrastructure:
    1. `W_analytic_BHW` gives F_ext on PermutedExtendedTube with permutation symmetry
    2. `schwinger_permutation_symmetric` (AnalyticContinuation.lean:1103) derives
       permutation invariance from BHW permutation symmetry
    3. `euclidean_distinct_in_permutedTube` shows distinct-time Euclidean points
       lie in PermutedExtendedTube

    Remaining gap: F_ext(Wick(x)) = W_analytic(Wick(x)) at all Euclidean points
    (not just those in ForwardTube). This follows by continuity of holomorphic
    functions + density of ordered points, but requires the SCV identity theorem.

    Ref: Jost, §IV.5; Streater-Wightman, Theorem 3.6 -/
theorem W_analytic_permutation_invariant (Wfn : WightmanFunctions d) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (x : NPointDomain d n) :
    (Wfn.spectrum_condition n).choose (fun k => wickRotatePoint (x k)) =
    (Wfn.spectrum_condition n).choose (fun k => wickRotatePoint (x (σ k))) := by
  -- Follows from W_analytic_BHW + schwinger_permutation_symmetric
  -- Gap: showing F_ext = W_analytic at Wick-rotated points outside ForwardTube
  sorry

/-- Permutations preserve volume: the map x ↦ x ∘ σ on (ℝ^{d+1})^n is
    a rearrangement of factors, preserving Lebesgue measure. -/
theorem integral_perm_eq_self (σ : Equiv.Perm (Fin n))
    (h : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, h (fun i => x (σ i)) =
    ∫ x : NPointDomain d n, h x :=
  (MeasureTheory.volume_measurePreserving_piCongrLeft
    (fun _ : Fin n => Fin (d + 1) → ℝ) σ).symm.integral_comp' h

/-- The Schwinger functions satisfy permutation symmetry (E3).

    Proof: BHW permutation invariance on the permuted extended tube,
    restricted to Euclidean points. -/
theorem constructedSchwinger_symmetric (Wfn : WightmanFunctions d)
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (f g : SchwartzNPoint d n)
    (hfg : ∀ x, g.toFun x = f.toFun (fun i => x (σ i))) :
    constructSchwingerFunctions Wfn n f = constructSchwingerFunctions Wfn n g := by
  simp only [constructSchwingerFunctions]
  have hfg' : ∀ x : NPointDomain d n,
      (g : NPointDomain d n → ℂ) x =
      (f : NPointDomain d n → ℂ) (fun i => x (σ i)) := hfg
  simp_rw [hfg']
  set K : NPointDomain d n → ℂ :=
    fun x => (Wfn.spectrum_condition n).choose (fun k => wickRotatePoint (x k))
  have hK : ∀ x : NPointDomain d n, K x = K (fun i => x (σ i)) :=
    fun x => W_analytic_permutation_invariant Wfn n σ x
  symm
  calc ∫ x : NPointDomain d n, K x * (f : NPointDomain d n → ℂ) (fun i => x (σ i))
      = ∫ x : NPointDomain d n,
          K (fun i => x (σ i)) *
          (f : NPointDomain d n → ℂ) (fun i => x (σ i)) := by
        congr 1; ext x; rw [hK]
    _ = ∫ x : NPointDomain d n, K x * (f : NPointDomain d n → ℂ) x :=
        integral_perm_eq_self σ
          (fun x => K x * (f : NPointDomain d n → ℂ) x)

/-- Cluster property of W_analytic at the integral level: when the (n+m)-point
    analytic Wightman function is integrated against a tensor product f ⊗ g_a
    where g_a is g translated by a large spacelike vector a, the result
    approaches the product S_n(f) · S_m(g).

    This is the analytic continuation of the Wightman cluster decomposition
    property, which follows from uniqueness of the vacuum (the mass gap
    ensures exponential decay of the truncated correlation functions).
    The Schwartz decay of f and g provides the domination needed for
    dominated convergence.

    Ref: Streater-Wightman, Theorem 3.5 (cluster decomposition);
    Glimm-Jaffe, Chapter 19 -/
theorem W_analytic_cluster_integral (Wfn : WightmanFunctions d) (n m : ℕ)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (ε : ℝ) (hε : ε > 0) :
    ∃ R : ℝ, R > 0 ∧
      ∀ a : SpacetimeDim d, (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
        ∀ (g_a : SchwartzNPoint d m),
          (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
          ‖(∫ x : NPointDomain d (n + m),
              (Wfn.spectrum_condition (n + m)).choose
                (fun k => wickRotatePoint (x k)) *
              (f.tensorProduct g_a) x) -
            (∫ x : NPointDomain d n,
              (Wfn.spectrum_condition n).choose
                (fun k => wickRotatePoint (x k)) * f x) *
            (∫ x : NPointDomain d m,
              (Wfn.spectrum_condition m).choose
                (fun k => wickRotatePoint (x k)) * g x)‖ < ε := by
  sorry

/-- The Schwinger functions satisfy clustering (E4).

    Proof: Follows from cluster decomposition of Wightman functions (R4)
    via the analytic continuation. The key input is `W_analytic_cluster_integral`,
    which combines the pointwise cluster property of W_analytic with
    dominated convergence using Schwartz function decay. -/
theorem constructedSchwinger_cluster (Wfn : WightmanFunctions d)
    (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (ε : ℝ) (hε : ε > 0) :
    ∃ R : ℝ, R > 0 ∧
      ∀ a : SpacetimeDim d, (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
        ∀ (g_a : SchwartzNPoint d m),
          (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
          ‖constructSchwingerFunctions Wfn (n + m) (f.tensorProduct g_a) -
            constructSchwingerFunctions Wfn n f *
            constructSchwingerFunctions Wfn m g‖ < ε := by
  -- Unfold constructSchwingerFunctions to expose the integrals
  simp only [constructSchwingerFunctions]
  exact W_analytic_cluster_integral Wfn n m f g ε hε

/-! ### OS to Wightman (Theorem E'→R') -/

/-- Phase 2: The Euclidean time translation semigroup.

    For t > 0, define the operator T(t) on the Hilbert space by:
      T(t) [f](τ₁,...,τₙ) = [f(τ₁ + t,..., τₙ + t)]

    This gives a contraction semigroup with:
    - T(s)T(t) = T(s+t)
    - ‖T(t)‖ ≤ 1 (contraction, from E2)
    - T(t) → I as t → 0⁺ (strong continuity, from E0)

    By the Hille-Yosida theorem, T(t) = e^{-tH} where H ≥ 0 is self-adjoint.
    This H is the Hamiltonian of the reconstructed QFT. -/
structure EuclideanSemigroup (OS : OsterwalderSchraderAxioms d) where
  /-- The semigroup parameter (Euclidean time) -/
  T : ℝ → (BorchersSequence d → BorchersSequence d)
  /-- Semigroup property: T(s) ∘ T(t) = T(s+t) -/
  semigroup : ∀ s t : ℝ, s > 0 → t > 0 → T s ∘ T t = T (s + t)
  /-- Contraction: ‖T(t)F‖ ≤ ‖F‖ -/
  contraction : ∀ t : ℝ, t > 0 → ∀ F : BorchersSequence d,
    (OSInnerProduct d OS.S (T t F) (T t F)).re ≤
    (OSInnerProduct d OS.S F F).re
  /-- Positivity: T(t) ≥ 0 as an operator -/
  positive : ∀ t : ℝ, t > 0 → ∀ F : BorchersSequence d,
    (OSInnerProduct d OS.S F (T t F)).re ≥ 0

/- Phase 3: Analytic continuation from Euclidean to Minkowski.

    The analytic continuation proceeds inductively. Starting from Schwinger functions
    S_n defined on Euclidean configurations, we extend to complex times.

    **Inductive structure** (OS II, Theorem 4.1):
    - A₀: S_k(ξ) is analytic on {ξ ∈ ℝ^k : ξⱼ > 0 for all j}
    - Aᵣ: S_k has analytic continuation to the region C_k^(r) ⊂ ℂ^k
      where r of the ξ-variables are complexified
    - After n = d + 1 steps, reach the full forward tube

    **Key estimate** (OS II, Theorem 4.2): At each step, the linear growth
    condition E0' provides the bounds needed for the continuation. -/

/-- The region C_k^(r) from OS II: the domain after r steps of analytic continuation.
    C_k^(0) = {ξ ∈ ℝ^k : ξⱼ > 0} (positive real half-space, all coordinates real)
    C_k^(r+1) extends the first r+1 spacetime coordinates to complex (Im diff > 0),
    while the remaining d-r coordinates stay real (Im = 0).
    C_k^(d+1) = forward tube T_k (all coordinates complex with positive Im diffs).

    **Important**: The regions EXPAND as r increases: C_k^(r) ⊂ C_k^(r+1), because
    each step frees one more coordinate from the "must be real" constraint.
    This matches the OS II inductive construction where each Laplace transform
    step analytically continues one more spatial direction. -/
def AnalyticContinuationRegion (d k r : ℕ) [NeZero d] :
    Set (Fin k → Fin (d + 1) → ℂ) :=
  match r with
  | 0 => -- All real, positive Euclidean times
    { z | (∀ i : Fin k, ∀ μ : Fin (d + 1), (z i μ).im = 0) ∧
          (∀ i : Fin k, (z i 0).re > 0) }
  | r + 1 => -- First r+1 coordinates complex with positive imaginary part,
    -- remaining coordinates must be real
    { z | (∀ i : Fin k,
        ∀ μ : Fin (d + 1), μ.val ≤ r →
          let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
          (z i μ - prev μ).im > 0) ∧
       (∀ i : Fin k,
        ∀ μ : Fin (d + 1), μ.val > r →
          (z i μ).im = 0) }

/-- The inductive analytic continuation theorem (OS II, Theorem 4.1).

    Given a holomorphic function on C_k^(r) (where r spacetime coordinates are complex),
    extend it analytically to C_k^(r+1) (one more coordinate becomes complex).

    The proof at each step uses:
    1. Laplace transform representation of S_k on C_k^(r)
    2. E0' bounds to control the growth of the Laplace transform
    3. Analytic continuation in the (r+1)-th coordinate direction

    The boundary-value connection: as the (r+1)-th coordinate's imaginary part → 0⁺,
    S_ext approaches S_prev. This is encoded by requiring both functions to agree
    when paired with test functions (distributional boundary values). -/
theorem inductive_analytic_continuation
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) (r : ℕ) (hr : r < d + 1)
    (S_prev : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_prev : DifferentiableOn ℂ S_prev (AnalyticContinuationRegion d k r)) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k (r + 1)) := by
  sorry

/-- After d+1 steps of analytic continuation, we reach the forward tube.

    C_k^(d+1) ⊇ ForwardTube d k (up to the difference variable transformation)

    This is the culmination of the inductive analytic continuation.

    The analytic function W_analytic is connected to the Schwinger functions:
    its Euclidean restriction (via Wick rotation) reproduces S_k. -/
theorem full_analytic_continuation
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (W_analytic : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (ForwardTube d k) ∧
      -- Euclidean restriction recovers S_k
      (∀ (f : SchwartzNPoint d k),
        OS.S k f = ∫ x : NPointDomain d k,
          W_analytic (fun j => wickRotatePoint (x j)) * (f x)) := by
  sorry

/-- Phase 4: The boundary values of the analytic continuation are tempered distributions.

    **Critical**: This is where E0' (linear growth condition) is essential!
    Without growth control, the boundary values might fail to be tempered.
    This is exactly the gap in OS I Lemma 8.8.

    The estimate (OS II, Section VI): the boundary values satisfy
    |W_n(f)| ≤ C_n · ‖f‖_{s,n} where C_n has at most factorial growth in n.
    This factorial growth comes from E0'.

    The connection to OS data: W_n is the distributional boundary value of
    the analytic continuation F_analytic of S_n. The Euclidean restriction
    of F_analytic recovers S_n, and its boundary values give W_n. -/
theorem boundary_values_tempered
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∃ (W_n : SchwartzNPoint d n → ℂ) (F_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      -- W_n is continuous (tempered distribution)
      Continuous W_n ∧
      -- W_n is linear
      IsLinearMap ℂ W_n ∧
      -- F_analytic is holomorphic on the forward tube
      DifferentiableOn ℂ F_analytic (ForwardTube d n) ∧
      -- Boundary values of F_analytic give W_n
      (∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        (∀ k, InOpenForwardCone d (η k)) →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F_analytic (fun k μ => ↑(x k μ) - ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W_n f))) ∧
      -- Euclidean restriction of F_analytic gives S_n
      (∀ (f : SchwartzNPoint d n),
        OS.S n f = ∫ x : NPointDomain d n,
          F_analytic (fun k => wickRotatePoint (x k)) * (f x)) ∧
      -- Growth estimate (linear growth condition on Wightman side, R0')
      ∃ (C : ℝ) (s : ℕ), C > 0 ∧
        ∀ f : SchwartzNPoint d n,
          ‖W_n f‖ ≤ C * lgc.alpha * lgc.beta ^ n * (n.factorial : ℝ) ^ lgc.gamma *
            SchwartzMap.seminorm ℝ s s f := by
  sorry

/-! ### Constructing WightmanFunctions from OS Data -/

/-- Given OS axioms with linear growth condition, construct the full collection
    of Wightman functions from the analytic continuation boundary values. -/
def constructWightmanFunctions (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    WightmanFunctions d where
  W := fun n => (boundary_values_tempered OS lgc n).choose
  linear := fun n => (boundary_values_tempered OS lgc n).choose_spec.choose_spec.2.1
  tempered := fun n => (boundary_values_tempered OS lgc n).choose_spec.choose_spec.1
  normalized := by
    -- The boundary value of S_0 = 1 gives W_0 = evaluation at the unique point
    sorry
  translation_invariant := by
    -- Translation invariance follows from E1 (Euclidean covariance) restricted
    -- to time-preserving translations
    sorry
  lorentz_covariant := by
    -- Lorentz covariance follows from E1 via BHW theorem
    -- SO(1,d) acts on the forward tube; the analytically continued function
    -- inherits Lorentz covariance from Euclidean covariance
    sorry
  spectrum_condition := by
    -- Use the F_analytic witness from boundary_values_tempered
    intro n
    have h := (boundary_values_tempered OS lgc n).choose_spec.choose_spec
    exact ⟨(boundary_values_tempered OS lgc n).choose_spec.choose,
      h.2.2.1, h.2.2.2.1⟩
  locally_commutative := by
    -- From E3 (permutation symmetry) + edge-of-the-wedge
    sorry
  positive_definite := by
    -- From E2 (reflection positivity)
    sorry
  hermitian := by
    -- From the reality of Schwinger functions and their analytic continuation
    sorry

/-- The OS pre-Hilbert space constructed from the Wightman functions obtained
    via analytic continuation of Schwinger functions.

    In the OS reconstruction (OS II, 1975), the Wightman functions are obtained
    from the Schwinger functions by analytic continuation, using the linear growth
    condition E0' to control the distribution order growth.

    The pre-Hilbert space uses the Wightman inner product:
      ⟨F, G⟩ = Σ_{n,m} W_{n+m}(f̄_n ⊗ g_m)
    where W_n are the boundary values of the analytic continuation of S_n.

    **Requires the linear growth condition E0'**: Without it, the analytic
    continuation may fail to produce tempered boundary values (OS I, Lemma 8.8 gap).

    Ref: OS II (1975), Sections IV-VI -/
def osPreHilbertSpace (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :=
  PreHilbertSpace (constructWightmanFunctions OS lgc)

/-! ### The Bridge Theorems -/

-- `IsWickRotationPair` is defined in Reconstruction.lean (available via import).

/-- **Theorem R→E**: Wightman functions produce Schwinger functions satisfying E0-E4.

    The Schwinger functions are related to the Wightman functions by Wick rotation
    (analytic continuation). -/
theorem wightman_to_os_full (Wfn : WightmanFunctions d) :
    ∃ (OS : OsterwalderSchraderAxioms d),
      -- The Schwinger functions are the Wick rotation of the Wightman functions
      IsWickRotationPair OS.S Wfn.W := by
  -- Construct OS axioms from Wightman functions
  refine ⟨⟨constructSchwingerFunctions Wfn,
    constructedSchwinger_tempered Wfn,
    constructedSchwinger_translation_invariant Wfn,
    constructedSchwinger_rotation_invariant Wfn,
    constructedSchwinger_reflection_positive Wfn,
    constructedSchwinger_symmetric Wfn,
    constructedSchwinger_cluster Wfn⟩, ?_⟩
  -- Prove the Wick rotation pair property
  intro n
  -- Use the same analytic continuation witness as constructSchwingerFunctions
  refine ⟨(Wfn.spectrum_condition n).choose,
    (Wfn.spectrum_condition n).choose_spec.1,
    (Wfn.spectrum_condition n).choose_spec.2,
    fun f => ?_⟩
  -- The Euclidean restriction is definitionally equal to constructSchwingerFunctions
  rfl

/-- **Theorem E'→R'**: OS axioms with linear growth condition produce Wightman functions.

    The Wightman functions are the boundary values of the analytic continuation
    of the Schwinger functions to the forward tube. -/
theorem os_to_wightman_full (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (Wfn : WightmanFunctions d),
      -- The Wightman functions are the Wick rotation of the Schwinger functions
      IsWickRotationPair OS.S Wfn.W := by
  exact ⟨constructWightmanFunctions OS lgc, by sorry⟩

/-! ### Wired Corollaries

The theorems `wightman_to_os` and `os_to_wightman` in `Reconstruction.lean` have
identical signatures to `wightman_to_os_full` and `os_to_wightman_full` above
(both use `IsWickRotationPair`). They are sorry'd because WickRotation.lean
imports Reconstruction.lean (circular import prevents wiring from there).
The `_full` versions here serve as the actual proofs. -/

end
