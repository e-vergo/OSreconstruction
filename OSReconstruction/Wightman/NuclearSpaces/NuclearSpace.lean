/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Seminorm
import Mathlib.Topology.Algebra.Module.LocallyConvex
import OSReconstruction.Wightman.NuclearSpaces.NuclearOperator

/-!
# Nuclear Spaces

This file defines nuclear spaces using Grothendieck/Pietsch characterization.

## Main Definitions

* `NuclearSpace` - A locally convex space E is nuclear if for every continuous seminorm p,
  there exists a continuous seminorm q ≥ p such that p is "nuclearly dominated" by q.
* `NuclearFrechet` - A nuclear Fréchet space presented via seminorms with nuclear steps.

## Mathematical Background

A locally convex topological vector space E is **nuclear** (Grothendieck) if its topology
is defined by a family of seminorms {p_α} such that for every p_α, there exists p_β ≥ p_α
with the canonical map from the completion of E/ker(p_β) to E/ker(p_α) being a nuclear
operator.

Equivalent characterizations:
1. (Grothendieck) Via nuclear maps between seminorm completions
2. (Pietsch) For every continuous seminorm p, there exist fₙ ∈ E* and cₙ ≥ 0 with
   Σ cₙ < ∞ such that p(x) ≤ Σ |fₙ(x)| · cₙ and each fₙ continuous
3. (Schwartz) Projective limit of Hilbert spaces with Hilbert-Schmidt connecting maps

Key examples: S(ℝⁿ), C^∞(M), distributions, finite-dimensional spaces.
Non-examples: infinite-dimensional Banach spaces.

## References

* Grothendieck, "Produits tensoriels topologiques et espaces nucléaires" (1955)
* Pietsch, "Nuclear Locally Convex Spaces" (1972)
* Trèves, "Topological Vector Spaces, Distributions and Kernels" (1967), Ch. 50
-/

noncomputable section

open scoped NNReal Topology
open Filter

/-! ### Nuclear Space Definition (Pietsch characterization) -/

/-- A locally convex topological vector space over ℝ is **nuclear** if for every continuous
    seminorm p, there exist continuous linear functionals (fₙ : E →L[ℝ] ℝ) and non-negative
    reals (cₙ) with Σ cₙ < ∞, and a continuous seminorm q ≥ p, such that:
    (1) p(x) ≤ Σₙ |fₙ(x)| · cₙ for all x
    (2) |fₙ(x)| ≤ q(x) for all x, n

    This is Pietsch's characterization, equivalent to Grothendieck's definition that
    the canonical map E_q → E_p between seminorm completions is nuclear.

    We follow the `LocallyConvexSpace` pattern in Mathlib for the type class binders. -/
class NuclearSpace (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] : Prop where
  nuclear_dominance : ∀ (p : Seminorm ℝ E), Continuous p →
    ∃ (q : Seminorm ℝ E), Continuous q ∧ (∀ x, p x ≤ q x) ∧
    ∃ (f : ℕ → (E →L[ℝ] ℝ)) (c : ℕ → ℝ),
      (∀ n, 0 ≤ c n) ∧
      Summable c ∧
      (∀ n x, ‖f n x‖ ≤ q x) ∧
      (∀ x, p x ≤ ∑' n, ‖f n x‖ * c n)

/-! ### Basic Properties of Nuclear Spaces -/

namespace NuclearSpace

/-- Helper: the triangle inequality for seminorms on finite sums. -/
private theorem seminorm_finset_sum_le {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : Seminorm ℝ V) {ι : Type*} (s : Finset ι) (g : ι → V) :
    p (∑ i ∈ s, g i) ≤ ∑ i ∈ s, p (g i) := by
  induction s using Finset.cons_induction with
  | empty => simp [map_zero]
  | cons a s has ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    calc p (g a + ∑ i ∈ s, g i) ≤ p (g a) + p (∑ i ∈ s, g i) := map_add_le_add p _ _
      _ ≤ p (g a) + ∑ i ∈ s, p (g i) := by linarith

/-- Helper: evaluation of a finset sum of seminorms distributes. -/
private theorem finset_sum_seminorm_apply {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ι : Type*} (s : Finset ι) (q : ι → Seminorm ℝ V) (x : V) :
    (s.sum q) x = s.sum (fun i => (q i) x) := by
  induction s using Finset.cons_induction with
  | empty => simp [Seminorm.zero_apply]
  | cons a s has ih =>
    rw [Finset.sum_cons, Finset.sum_cons, Seminorm.add_apply, ih]

/-- Finite-dimensional spaces are nuclear.

    The proof uses a basis b₁,...,bₙ with coordinate functionals φᵢ. Given any
    continuous seminorm p, we construct q = p + Σᵢ |φᵢ| as the dominating seminorm,
    and use φᵢ, cᵢ = p(bᵢ) for the nuclear decomposition. The triangle inequality
    p(x) = p(Σ φᵢ(x)·bᵢ) ≤ Σ |φᵢ(x)|·p(bᵢ) provides the nuclear bound. -/
theorem finiteDimensional (V : Type*) [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    [FiniteDimensional ℝ V] [T2Space V] : NuclearSpace V where
  nuclear_dominance := by
    intro p hp
    let d := Module.finrank ℝ V
    let b := Module.finBasis ℝ V
    -- Coordinate seminorms: x ↦ ‖b.coord i x‖
    let coordSemi : Fin d → Seminorm ℝ V :=
      fun i => (normSeminorm ℝ ℝ).comp (b.coord i)
    -- ℓ¹ coordinate seminorm: ell1(x) = Σ_i ‖b.coord i x‖
    let ell1 : Seminorm ℝ V := Finset.univ.sum coordSemi
    -- Helper: ell1 x = Σ_i ‖b.coord i x‖
    have ell1_eq : ∀ x, ell1 x = ∑ i : Fin d, ‖(b.coord i) x‖ := by
      intro x
      rw [show ell1 x = Finset.univ.sum (fun i => coordSemi i x) from
        finset_sum_seminorm_apply _ _ _]
      exact Finset.sum_congr rfl fun i _ => by
        simp only [coordSemi, Seminorm.comp_apply, coe_normSeminorm]
    -- ell1 is continuous
    have ell1_cont : Continuous (⇑ell1 : V → ℝ) := by
      rw [show (⇑ell1 : V → ℝ) = fun x => ∑ i : Fin d, ‖(b.coord i) x‖ from
        funext ell1_eq]
      exact continuous_finset_sum _ fun i _ =>
        continuous_norm.comp (b.coord i).continuous_of_finiteDimensional
    -- Dominating seminorm q = p + ell1
    refine ⟨p + ell1, ?_, ?_, ?_⟩
    · -- q is continuous
      rw [show (⇑(p + ell1) : V → ℝ) = fun x => p x + ell1 x from
        funext (Seminorm.add_apply p ell1)]
      exact Continuous.add hp ell1_cont
    · -- q ≥ p
      intro x; rw [Seminorm.add_apply]; linarith [apply_nonneg ell1 x]
    · -- Nuclear decomposition
      -- Name f and c to make reasoning about dite tractable
      let f : ℕ → (V →L[ℝ] ℝ) := fun k =>
        if h : k < d then
          ⟨b.coord ⟨k, h⟩, (b.coord ⟨k, h⟩).continuous_of_finiteDimensional⟩
        else 0
      let c : ℕ → ℝ := fun k => if h : k < d then p (b ⟨k, h⟩) else 0
      have hf_lt : ∀ k (h : k < d), f k =
          ⟨b.coord ⟨k, h⟩, (b.coord ⟨k, h⟩).continuous_of_finiteDimensional⟩ :=
        fun k h => dif_pos h
      have hf_ge : ∀ k, ¬(k < d) → f k = 0 := fun k h => dif_neg h
      have hc_lt : ∀ k (h : k < d), c k = p (b ⟨k, h⟩) := fun k h => dif_pos h
      have hc_ge : ∀ k, ¬(k < d) → c k = 0 := fun k h => dif_neg h
      refine ⟨f, c, ?_, ?_, ?_, ?_⟩
      · -- c ≥ 0
        intro k
        by_cases h : k < d
        · rw [hc_lt k h]; exact apply_nonneg p _
        · rw [hc_ge k h]
      · -- Summable c (finitely supported)
        exact summable_of_ne_finset_zero (s := Finset.range d)
          (fun k hk => by
            simp only [Finset.mem_range, not_lt] at hk
            exact hc_ge k (not_lt.mpr hk))
      · -- ‖f k x‖ ≤ q x
        intro k x
        by_cases h : k < d
        · -- k < d: ‖b.coord ⟨k,h⟩ x‖ ≤ (p + ell1) x
          rw [hf_lt k h]
          rw [Seminorm.add_apply]
          simp only [ContinuousLinearMap.coe_mk']
          have hle : ‖(b.coord ⟨k, h⟩) x‖ ≤ ell1 x := by
            rw [ell1_eq]
            exact Finset.single_le_sum
              (fun (i : Fin d) _ => norm_nonneg ((b.coord i) x))
              (Finset.mem_univ (⟨k, h⟩ : Fin d))
          linarith [apply_nonneg p x]
        · -- k ≥ d: ‖0 x‖ = 0 ≤ q x
          rw [hf_ge k h]
          simp only [ContinuousLinearMap.zero_apply, norm_zero]
          exact apply_nonneg (p + ell1) x
      · -- p x ≤ Σ' k, ‖f k x‖ * c k
        intro x
        -- Step 1: Triangle inequality: p x ≤ ∑ i : Fin d, ‖(b.coord i) x‖ * p (b i)
        have hdecomp : x = ∑ i : Fin d, (b.coord i x) • (b i) := by
          change x = ∑ i : Fin d, (b.repr x) i • (b i)
          exact (b.sum_repr x).symm
        have hbound : p x ≤ ∑ i : Fin d, ‖(b.coord i) x‖ * p (b i) := by
          calc p x = p (∑ i : Fin d, (b.coord i x) • (b i)) := by
                  conv_lhs => rw [hdecomp]
            _ ≤ ∑ i : Fin d, p ((b.coord i x) • (b i)) := seminorm_finset_sum_le p _ _
            _ = ∑ i : Fin d, ‖(b.coord i) x‖ * p (b i) := by
                apply Finset.sum_congr rfl; intro i _
                exact map_smul_eq_mul p _ _
        -- Step 2: The tsum equals the Fin d sum
        have hzero : ∀ k, ¬(k < d) → ‖f k x‖ * c k = 0 := by
          intro k hk; rw [hf_ge k hk, hc_ge k hk]; simp
        have htsum : ∑' k, ‖f k x‖ * c k =
            (Finset.range d).sum (fun k => ‖f k x‖ * c k) :=
          tsum_eq_sum (fun k hk => by
            simp only [Finset.mem_range, not_lt] at hk
            exact hzero k (not_lt.mpr hk))
        rw [htsum, ← Fin.sum_univ_eq_sum_range]
        -- Convert the Fin d sum terms to match hbound
        have hterm : ∀ (i : Fin d),
            ‖f i.val x‖ * c i.val = ‖(b.coord i) x‖ * p (b i) := by
          intro ⟨k, hk⟩
          simp only [hf_lt k hk, hc_lt k hk, ContinuousLinearMap.coe_mk']
        calc ∑ i : Fin d, ‖f i.val x‖ * c i.val
            = ∑ i : Fin d, ‖(b.coord i) x‖ * p (b i) :=
              Finset.sum_congr rfl (fun i _ => hterm i)
          _ ≥ p x := hbound

/-- A closed subspace of a nuclear space is nuclear. -/
theorem subspace_nuclear (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E]
    [NuclearSpace E] (S : Submodule ℝ E) (_hclosed : IsClosed (S : Set E)) :
    NuclearSpace S := by
  sorry

/-- Countable products of nuclear spaces are nuclear. -/
theorem product_nuclear (ι : Type*) [Countable ι]
    (E : ι → Type*) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)]
    [∀ i, NuclearSpace (E i)] : NuclearSpace (∀ i, E i) := by
  sorry

end NuclearSpace

/-! ### Helper: Linear Functional Continuity from Seminorm Bound -/

/-- A linear functional bounded by a continuous seminorm is continuous
    in a topological additive group.

    This is a standard result in functional analysis: if |φ(x)| ≤ p(x) where
    p is a continuous seminorm, then φ is continuous because for any ε > 0,
    the preimage φ⁻¹((-ε, ε)) contains the open ball {x | p(x) < ε} which
    is a neighborhood of 0. Continuity at 0 gives continuity everywhere
    by translation invariance (TopologicalAddGroup). -/
private lemma linearMap_continuous_of_seminorm_bound
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E]
    (φ : E →ₗ[ℝ] ℝ) (p : Seminorm ℝ E) (hp : Continuous p)
    (hbound : ∀ x, |φ x| ≤ p x) : Continuous φ := by
  -- Continuity at 0 implies continuity for additive group homomorphisms
  apply continuous_of_continuousAt_zero φ.toAddMonoidHom
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  -- The seminorm ball {x | p(x) < ε} is a neighborhood of 0
  apply Eventually.mono (Seminorm.ball_mem_nhds hp hε)
  intro x hx
  simp only [dist_zero_right, Real.norm_eq_abs]
  exact lt_of_le_of_lt (hbound x) (by rwa [sub_zero] at hx)

/-! ### Nuclear Fréchet Space Presentation -/

/-- A nuclear Fréchet space presented as a sequence of seminorms with nuclear steps.
    This is the most practical formulation for QFT applications.

    The space E comes equipped with a countable family of seminorms (pₙ)
    that define its topology, and for each n the "identity" from (E, pₙ₊₁)
    to (E, pₙ) admits a nuclear factorization: there exist linear functionals φₖ
    bounded by pₙ₊₁ and summable coefficients cₖ with pₙ(x) ≤ Σₖ |φₖ(x)| · cₖ.

    For Schwartz space, the pₙ are the Schwartz seminorms involving
    polynomial weights and derivatives.

    The `instIsTopologicalAddGroup` field ensures the topology is compatible
    with the additive group structure, which is needed for continuous linear
    functionals to be well-behaved (e.g., continuity at 0 ⟹ continuity). -/
structure NuclearFrechet where
  /-- The underlying space -/
  Space : Type*
  /-- Additive group structure -/
  instAddCommGroup : AddCommGroup Space
  /-- ℝ-module structure -/
  instModule : Module ℝ Space
  /-- Topology -/
  instTopologicalSpace : TopologicalSpace Space
  /-- The topology is compatible with the additive group structure -/
  instIsTopologicalAddGroup : @IsTopologicalAddGroup Space instTopologicalSpace
    instAddCommGroup.toAddGroup
  /-- The defining family of seminorms (indexed by ℕ) -/
  seminorms : ℕ → Seminorm ℝ Space
  /-- Seminorms are increasing: pₙ ≤ pₙ₊₁ -/
  seminorms_mono : ∀ n x, seminorms n x ≤ seminorms (n + 1) x
  /-- The seminorms separate points (Hausdorff condition) -/
  separating : ∀ x, (∀ n, seminorms n x = 0) → x = 0
  /-- Each defining seminorm is continuous with respect to the topology -/
  continuous_seminorms : ∀ n,
    @Continuous Space ℝ instTopologicalSpace inferInstance (seminorms n)
  /-- Every continuous seminorm on the space is bounded by some defining seminorm
      (the defining seminorms generate the topology). -/
  seminorms_generating : ∀ (p : Seminorm ℝ Space),
    @Continuous Space ℝ instTopologicalSpace inferInstance p →
    ∃ (n : ℕ) (C : ℝ), 0 < C ∧ ∀ x, p x ≤ C * seminorms n x
  /-- Nuclear condition: for each n, pₙ is nuclearly dominated by pₙ₊₁.
      There exist linear functionals bounded by pₙ₊₁ and summable coefficients
      that provide a nuclear-type bound on pₙ.

      Note: The functionals are given as linear maps, but they are automatically
      continuous because they are bounded by the continuous seminorm pₙ₊₁. -/
  nuclear_step : ∀ (n : ℕ),
    ∃ (φ : ℕ → Space →ₗ[ℝ] ℝ) (c : ℕ → ℝ),
      (∀ k, 0 ≤ c k) ∧
      Summable c ∧
      (∀ k x, |φ k x| ≤ seminorms (n + 1) x) ∧
      (∀ x, seminorms n x ≤ ∑' k, |φ k x| * c k)

/-! ### Connection to NuclearSpace class -/

/-- A nuclear Fréchet presentation gives rise to a NuclearSpace instance.

    The key step is that any continuous seminorm p on E is bounded by some
    C * pₙ (by the generating property of the defining seminorms), and then
    the nuclear_step condition for pₙ provides the nuclear decomposition.
    We absorb the constant C into the coefficients and scale pₙ₊₁ to serve
    as the dominating seminorm q. -/
theorem NuclearFrechet.toNuclearSpace (NF : NuclearFrechet) :
    @NuclearSpace NF.Space NF.instAddCommGroup NF.instModule NF.instTopologicalSpace := by
  letI := NF.instAddCommGroup
  letI := NF.instModule
  letI := NF.instTopologicalSpace
  letI := NF.instIsTopologicalAddGroup
  constructor
  intro p hp
  -- Step 1: p ≤ C * pₙ for some n, C > 0
  obtain ⟨n, C, hC, hpbound⟩ := NF.seminorms_generating p hp
  -- Step 2: pₙ has nuclear decomposition from pₙ₊₁
  obtain ⟨φ, c, hc_nn, hc_sum, hφ_bound, hpn_bound⟩ := NF.nuclear_step n
  -- Step 3: q = M * pₙ₊₁ where M = max(1, C) ≥ 1, absorbing the constant
  set M := max 1 C with hM_def
  have hM_pos : (0 : ℝ) < M := lt_of_lt_of_le one_pos (le_max_left 1 C)
  have hM_ge_one : (1 : ℝ) ≤ M := le_max_left 1 C
  have hM_ge_C : C ≤ M := le_max_right 1 C
  -- Construct q as M • pₙ₊₁
  let M_nn : ℝ≥0 := ⟨M, le_of_lt hM_pos⟩
  refine ⟨M_nn • NF.seminorms (n + 1), ?_, ?_, ?_⟩
  -- q is continuous: M * pₙ₊₁ is continuous since pₙ₊₁ is
  · suffices h : Continuous (fun x => M * NF.seminorms (n + 1) x) by
      have : (⇑(M_nn • NF.seminorms (n + 1)) : NF.Space → ℝ) =
          fun x => M * NF.seminorms (n + 1) x := by
        ext x; simp [M_nn, NNReal.smul_def]
      rwa [show @Continuous NF.Space ℝ NF.instTopologicalSpace _ ⇑(M_nn • NF.seminorms (n + 1)) ↔
        @Continuous NF.Space ℝ NF.instTopologicalSpace _ (fun x => M * NF.seminorms (n + 1) x)
        from Iff.intro (fun h => by rwa [← this]) (fun h => by rwa [this])]
    exact continuous_const.mul (NF.continuous_seminorms (n + 1))
  -- q ≥ p: p ≤ C * pₙ ≤ C * pₙ₊₁ ≤ M * pₙ₊₁ = q
  · intro x
    have hsmul : (M_nn • NF.seminorms (n + 1)) x = M * NF.seminorms (n + 1) x := by
      simp [M_nn, NNReal.smul_def]
    rw [hsmul]
    calc p x ≤ C * NF.seminorms n x := hpbound x
    _ ≤ C * NF.seminorms (n + 1) x :=
        mul_le_mul_of_nonneg_left (NF.seminorms_mono n x) (le_of_lt hC)
    _ ≤ M * NF.seminorms (n + 1) x :=
        mul_le_mul_of_nonneg_right hM_ge_C (apply_nonneg _ x)
  -- Nuclear decomposition: fₖ = φₖ (made continuous), c'ₖ = C * cₖ
  · -- Each φₖ is bounded by pₙ₊₁ (continuous), so φₖ is continuous
    have hcont_phi : ∀ k, @Continuous NF.Space ℝ NF.instTopologicalSpace _ (φ k) :=
      fun k => linearMap_continuous_of_seminorm_bound (φ k) (NF.seminorms (n + 1))
        (NF.continuous_seminorms (n + 1)) (hφ_bound k)
    refine ⟨fun k => ⟨φ k, hcont_phi k⟩, fun k => C * c k, ?_, ?_, ?_, ?_⟩
    -- c' ≥ 0
    · intro k; exact mul_nonneg (le_of_lt hC) (hc_nn k)
    -- Summable c': follows from Summable c
    · exact hc_sum.const_smul C
    -- ‖fₖ(x)‖ ≤ q(x): |φₖ(x)| ≤ pₙ₊₁(x) ≤ M * pₙ₊₁(x) = q(x)
    · intro k x
      have hsmul : (M_nn • NF.seminorms (n + 1)) x = M * NF.seminorms (n + 1) x := by
        simp [M_nn, NNReal.smul_def]
      simp only [ContinuousLinearMap.coe_mk', Real.norm_eq_abs]
      rw [hsmul]
      calc |φ k x| ≤ NF.seminorms (n + 1) x := hφ_bound k x
      _ ≤ M * NF.seminorms (n + 1) x :=
          le_mul_of_one_le_left (apply_nonneg _ x) hM_ge_one
    -- p(x) ≤ Σ ‖fₖ(x)‖ * c'ₖ: absorb C into the tsum
    · intro x
      have hpn := hpn_bound x
      simp only [ContinuousLinearMap.coe_mk', Real.norm_eq_abs]
      calc p x ≤ C * NF.seminorms n x := hpbound x
      _ ≤ C * (∑' k, |φ k x| * c k) :=
          mul_le_mul_of_nonneg_left hpn (le_of_lt hC)
      _ = ∑' k, C * (|φ k x| * c k) := by rw [← tsum_mul_left]
      _ = ∑' k, |φ k x| * (C * c k) := by congr 1; ext k; ring

end
