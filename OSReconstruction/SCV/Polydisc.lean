/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Convex.Basic

/-!
# Polydiscs in ℂᵐ

This file defines polydiscs (products of discs) in `Fin m → ℂ` and establishes
their basic topological properties. Polydiscs are the natural domains for
iterated Cauchy integrals in several complex variables.

## Main definitions

* `SCV.Polydisc` — the open polydisc `{z | ∀ i, |zᵢ - cᵢ| < rᵢ}`
* `SCV.closedPolydisc` — the closed polydisc `{z | ∀ i, |zᵢ - cᵢ| ≤ rᵢ}`
* `SCV.distinguishedBoundary` — the torus `{z | ∀ i, |zᵢ - cᵢ| = rᵢ}`

## Main results

* `SCV.polydisc_isOpen` — polydiscs are open
* `SCV.isCompact_closedPolydisc` — closed polydiscs are compact
* `SCV.polydisc_isPreconnected` — polydiscs are connected
* `SCV.polydisc_convex` — polydiscs are convex

## References

* Rudin, W. (1971). *Lectures on the edge-of-the-wedge theorem*. CBMS 6.
* Range, R.M. (1986). *Holomorphic Functions and Integral Representations
  in Several Complex Variables*. Springer.
-/

noncomputable section

open Complex Metric Set Filter Topology

namespace SCV

variable {m : ℕ}

/-! ### Definitions -/

/-- The open polydisc in `Fin m → ℂ` with center `c` and polyradius `r`.
    This is the product of open discs: `{z | ∀ i, |zᵢ - cᵢ| < rᵢ}`. -/
def Polydisc (c : Fin m → ℂ) (r : Fin m → ℝ) : Set (Fin m → ℂ) :=
  { z | ∀ i, z i ∈ Metric.ball (c i) (r i) }

/-- The closed polydisc in `Fin m → ℂ` with center `c` and polyradius `r`.
    This is the product of closed discs: `{z | ∀ i, |zᵢ - cᵢ| ≤ rᵢ}`. -/
def closedPolydisc (c : Fin m → ℂ) (r : Fin m → ℝ) : Set (Fin m → ℂ) :=
  { z | ∀ i, z i ∈ Metric.closedBall (c i) (r i) }

/-- The distinguished boundary (torus) of a polydisc: `{z | ∀ i, |zᵢ - cᵢ| = rᵢ}`.
    This is the Cartesian product of circles, NOT the topological boundary.
    For polydiscs with m ≥ 2, the distinguished boundary is a proper subset
    of the topological boundary. -/
def distinguishedBoundary (c : Fin m → ℂ) (r : Fin m → ℝ) : Set (Fin m → ℂ) :=
  { z | ∀ i, z i ∈ Metric.sphere (c i) (r i) }

/-- A uniform polydisc where all radii are equal. -/
def uniformPolydisc (c : Fin m → ℂ) (R : ℝ) : Set (Fin m → ℂ) :=
  Polydisc c (fun _ => R)

/-! ### Basic set-theoretic properties -/

theorem mem_polydisc_iff {c : Fin m → ℂ} {r : Fin m → ℝ} {z : Fin m → ℂ} :
    z ∈ Polydisc c r ↔ ∀ i, dist (z i) (c i) < r i :=
  Iff.rfl

theorem mem_closedPolydisc_iff {c : Fin m → ℂ} {r : Fin m → ℝ} {z : Fin m → ℂ} :
    z ∈ closedPolydisc c r ↔ ∀ i, dist (z i) (c i) ≤ r i :=
  Iff.rfl

theorem mem_distinguishedBoundary_iff {c : Fin m → ℂ} {r : Fin m → ℝ} {z : Fin m → ℂ} :
    z ∈ distinguishedBoundary c r ↔ ∀ i, dist (z i) (c i) = r i :=
  Iff.rfl

theorem center_mem_polydisc {c : Fin m → ℂ} {r : Fin m → ℝ} (hr : ∀ i, 0 < r i) :
    c ∈ Polydisc c r := by
  intro i; exact Metric.mem_ball_self (hr i)

theorem center_mem_closedPolydisc {c : Fin m → ℂ} {r : Fin m → ℝ} (hr : ∀ i, 0 ≤ r i) :
    c ∈ closedPolydisc c r := by
  intro i; exact Metric.mem_closedBall_self (hr i)

theorem polydisc_subset_closedPolydisc {c : Fin m → ℂ} {r : Fin m → ℝ} :
    Polydisc c r ⊆ closedPolydisc c r :=
  fun _ hz i => Metric.ball_subset_closedBall (hz i)

theorem distinguishedBoundary_subset_closedPolydisc {c : Fin m → ℂ} {r : Fin m → ℝ} :
    distinguishedBoundary c r ⊆ closedPolydisc c r :=
  fun _ hz i => Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp (hz i)))

theorem polydisc_mono {c : Fin m → ℂ} {r₁ r₂ : Fin m → ℝ} (h : ∀ i, r₁ i ≤ r₂ i) :
    Polydisc c r₁ ⊆ Polydisc c r₂ :=
  fun _ hz i => lt_of_lt_of_le (hz i) (h i)

theorem closedPolydisc_mono {c : Fin m → ℂ} {r₁ r₂ : Fin m → ℝ} (h : ∀ i, r₁ i ≤ r₂ i) :
    closedPolydisc c r₁ ⊆ closedPolydisc c r₂ :=
  fun _ hz i => le_trans (hz i) (h i)

/-! ### Polydisc as product set -/

theorem polydisc_eq_pi {c : Fin m → ℂ} {r : Fin m → ℝ} :
    Polydisc c r = Set.univ.pi (fun i => Metric.ball (c i) (r i)) := by
  ext z; simp [Polydisc, Set.mem_pi]

theorem closedPolydisc_eq_pi {c : Fin m → ℂ} {r : Fin m → ℝ} :
    closedPolydisc c r = Set.univ.pi (fun i => Metric.closedBall (c i) (r i)) := by
  ext z; simp [closedPolydisc, Set.mem_pi]

theorem distinguishedBoundary_eq_pi {c : Fin m → ℂ} {r : Fin m → ℝ} :
    distinguishedBoundary c r = Set.univ.pi (fun i => Metric.sphere (c i) (r i)) := by
  ext z; simp [distinguishedBoundary, Set.mem_pi]

/-! ### Topological properties -/

theorem polydisc_isOpen {c : Fin m → ℂ} {r : Fin m → ℝ} :
    IsOpen (Polydisc c r) := by
  rw [polydisc_eq_pi]
  exact isOpen_set_pi Set.finite_univ (fun i _ => Metric.isOpen_ball)

theorem isCompact_closedPolydisc {c : Fin m → ℂ} {r : Fin m → ℝ} :
    IsCompact (closedPolydisc c r) := by
  rw [closedPolydisc_eq_pi]
  exact isCompact_univ_pi (fun i => ProperSpace.isCompact_closedBall (c i) (r i))

theorem isCompact_distinguishedBoundary {c : Fin m → ℂ} {r : Fin m → ℝ} :
    IsCompact (distinguishedBoundary c r) := by
  rw [distinguishedBoundary_eq_pi]
  exact isCompact_univ_pi (fun i => isCompact_sphere (c i) (r i))

theorem polydisc_nonempty {c : Fin m → ℂ} {r : Fin m → ℝ} (hr : ∀ i, 0 < r i) :
    (Polydisc c r).Nonempty :=
  ⟨c, center_mem_polydisc hr⟩

theorem closedPolydisc_nonempty {c : Fin m → ℂ} {r : Fin m → ℝ} (hr : ∀ i, 0 ≤ r i) :
    (closedPolydisc c r).Nonempty :=
  ⟨c, center_mem_closedPolydisc hr⟩

/-! ### Convexity -/

theorem polydisc_convex {c : Fin m → ℂ} {r : Fin m → ℝ} :
    Convex ℝ (Polydisc c r) := by
  rw [polydisc_eq_pi]
  exact convex_pi (fun i _ => convex_ball (c i) (r i))

theorem closedPolydisc_convex {c : Fin m → ℂ} {r : Fin m → ℝ} :
    Convex ℝ (closedPolydisc c r) := by
  rw [closedPolydisc_eq_pi]
  exact convex_pi (fun i _ => convex_closedBall (c i) (r i))

/-! ### Connectedness -/

theorem polydisc_isPreconnected {c : Fin m → ℂ} {r : Fin m → ℝ} :
    IsPreconnected (Polydisc c r) := by
  rw [polydisc_eq_pi]
  exact isPreconnected_univ_pi (fun i => (convex_ball (c i) (r i)).isPreconnected)

theorem polydisc_isConnected {c : Fin m → ℂ} {r : Fin m → ℝ} (hr : ∀ i, 0 < r i) :
    IsConnected (Polydisc c r) :=
  ⟨polydisc_nonempty hr, polydisc_isPreconnected⟩

theorem closedPolydisc_isPreconnected {c : Fin m → ℂ} {r : Fin m → ℝ} :
    IsPreconnected (closedPolydisc c r) := by
  rw [closedPolydisc_eq_pi]
  exact isPreconnected_univ_pi (fun i => (convex_closedBall (c i) (r i)).isPreconnected)

/-! ### Path Connectedness -/

theorem polydisc_isPathConnected {c : Fin m → ℂ} {r : Fin m → ℝ} (hr : ∀ i, 0 < r i) :
    IsPathConnected (Polydisc c r) :=
  (polydisc_convex.isPathConnected (polydisc_nonempty hr))

/-! ### Membership lemmas for coordinate manipulation -/

/-- Updating one coordinate preserves polydisc membership if the new value is in the corresponding ball. -/
theorem mem_polydisc_update {c : Fin m → ℂ} {r : Fin m → ℝ} {z : Fin m → ℂ}
    (hz : z ∈ Polydisc c r) (i : Fin m) {w : ℂ} (hw : w ∈ Metric.ball (c i) (r i)) :
    Function.update z i w ∈ Polydisc c r := by
  intro j
  by_cases hij : j = i
  · subst hij; simp [hw]
  · simp [hij, hz j]

/-- Updating one coordinate of a closed polydisc member preserves membership. -/
theorem mem_closedPolydisc_update {c : Fin m → ℂ} {r : Fin m → ℝ} {z : Fin m → ℂ}
    (hz : z ∈ closedPolydisc c r) (i : Fin m) {w : ℂ} (hw : w ∈ Metric.closedBall (c i) (r i)) :
    Function.update z i w ∈ closedPolydisc c r := by
  intro j
  by_cases hij : j = i
  · subst hij; simp [hw]
  · simp [hij, hz j]

/-! ### Separate holomorphicity on polydiscs -/

/-- A function is separately holomorphic on a polydisc if, for each coordinate `i`
    and each fixed choice of the other coordinates, it is holomorphic in the `i`-th variable. -/
def SeparatelyDifferentiableOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : (Fin m → ℂ) → E) (S : Set (Fin m → ℂ)) : Prop :=
  ∀ (i : Fin m) (z : Fin m → ℂ), z ∈ S →
    DifferentiableAt ℂ (fun w => f (Function.update z i w)) (z i)

/-- The coordinate insertion map `w ↦ z[i := w]` is differentiable (it's affine). -/
theorem differentiableAt_update (z : Fin m → ℂ) (i : Fin m) (w : ℂ) :
    DifferentiableAt ℂ (Function.update z i) w := by
  rw [differentiableAt_pi]
  intro j
  show DifferentiableAt ℂ (fun w => Function.update z i w j) w
  by_cases hij : j = i
  · subst hij; simp only [Function.update_self]; exact differentiableAt_id
  · have : (fun w => Function.update z i w j) = fun _ => z j :=
      funext (fun w => Function.update_of_ne hij w z)
    rw [this]; exact differentiableAt_const _

/-- Joint holomorphicity implies separate holomorphicity. -/
theorem DifferentiableOn.separatelyDifferentiableOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : (Fin m → ℂ) → E}
    {S : Set (Fin m → ℂ)} (hS : IsOpen S) (hf : DifferentiableOn ℂ f S) :
    SeparatelyDifferentiableOn f S := by
  intro i z hz
  have h_update_eq : Function.update z i (z i) = z := Function.update_eq_self i z
  have hf_at : DifferentiableAt ℂ f z := hf.differentiableAt (hS.mem_nhds hz)
  exact (h_update_eq ▸ hf_at).comp (z i) (differentiableAt_update z i (z i))

end SCV
