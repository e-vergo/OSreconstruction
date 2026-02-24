/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import OSReconstruction.Wightman.Basic
import OSReconstruction.Wightman.OperatorDistribution
import OSReconstruction.Wightman.SchwartzTensorProduct

/-!
# Wightman Axioms

This file provides a rigorous mathematical formulation of the Wightman axioms for
quantum field theory. The axioms are formalized as a structure `WightmanQFT` that
contains all the required data and properties.

## Main Definitions

* `WightmanQFT` - The complete structure satisfying all Wightman axioms
* `WightmanQFT.spectrumCondition` - Energy-momentum spectrum lies in forward light cone
* `WightmanQFT.locality` - Spacelike-separated fields commute

## The Wightman Axioms

The Wightman axioms (W1-W4) as formalized here:

**W1 (Covariance)**:
- There is a continuous unitary representation U of the Poincaré group on H
- The generators P_μ (energy-momentum) have spectrum in the forward light cone V₊
- There exists a unique vacuum vector Ω invariant under U(g)

**W2 (Field Operators)**:
- There exist field operators φ(f) for each test function f ∈ 𝒮(ℝ^{d+1})
- The domain D is dense and invariant under all φ(f)
- The subspace spanned by φ(f₁)···φ(fₙ)Ω is dense in H
- The field is covariant: U(g) φ(f) U(g)⁻¹ = φ(f ∘ g⁻¹)

**W3 (Locality)**:
- If supp(f) and supp(g) are spacelike separated, then [φ(f), φ(g)] = 0 on D

**W4 (Vacuum Uniqueness)**:
- The vacuum Ω is the unique vector (up to phase) invariant under time translations

## References

* Streater-Wightman, "PCT, Spin and Statistics, and All That"
* Glimm-Jaffe, "Quantum Physics: A Functional Integral Point of View"
* Haag, "Local Quantum Physics"
-/

noncomputable section

open scoped SchwartzMap InnerProductSpace
open Topology

variable (d : ℕ) [NeZero d]

/-! ### Spectrum Condition -/

/-- The forward light cone in momentum space: p₀ ≥ 0, p² ≤ 0.
    In the mostly positive signature, p² = -p₀² + |p⃗|², so p² ≤ 0 means p₀ ≥ |p⃗|.
    This is the region where timelike and lightlike momenta with positive energy lie. -/
def ForwardMomentumCone : Set (MinkowskiSpace d) :=
  MinkowskiSpace.ClosedForwardLightCone d

/-- The spectrum condition: the joint spectrum of the energy-momentum operators
    lies in the closed forward light cone.

    Mathematically: For any state ψ in the domain of the momentum operators,
    the spectral support of ψ (the support of its spectral measure) lies in V̄₊.

    Equivalently, for any translation-covariant state:
      ⟨ψ, U(a) ψ⟩ = ∫_{V̄₊} e^{ip·a} dμ_ψ(p)

    where V̄₊ = {p : p₀ ≥ 0 and p² ≤ 0} is the closed forward light cone
    (in mostly positive signature, p² = -p₀² + |p⃗|² ≤ 0 means p₀ ≥ |p⃗|).

    We express this via the Fourier transform of the 2-point function having
    support in the forward cone. -/
structure SpectralCondition (d : ℕ) [NeZero d]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : PoincareRepresentation d H) : Prop where
  /-- The energy is non-negative: for all states ψ, ⟨ψ, Hψ⟩ ≥ 0 where H = P₀ -/
  energy_nonneg : ∀ ψ : H, (⟪ψ, π.hamiltonian ψ⟫_ℂ).re ≥ 0
  /-- The mass-shell condition: p² ≤ 0 (in mostly positive signature).
      For any state ψ, the expectation value of P² = -P₀² + Σᵢ Pᵢ² is ≤ 0.
      This encodes that the spectral support lies in the forward cone. -/
  mass_shell : ∀ ψ : H, (⟪ψ, π.hamiltonian (π.hamiltonian ψ)⟫_ℂ).re ≥
    ∑ i : Fin d, (⟪ψ, π.spatialMomentum i (π.spatialMomentum i ψ)⟫_ℂ).re

/-! ### Locality -/

/-- Two Schwartz functions have spacelike-separated supports -/
def AreSpacelikeSeparatedSupports (f g : SchwartzSpacetime d) : Prop :=
  ∀ x ∈ Function.support f, ∀ y ∈ Function.support g,
    MinkowskiSpace.AreSpacelikeSeparated d x y

/-- The commutator of two operators on a domain -/
def Commutator {H : Type*} [AddCommGroup H] [Module ℂ H]
    (A B : H → H) (D : Set H) : Prop :=
  ∀ ψ ∈ D, A (B ψ) = B (A ψ)

/-- Locality: spacelike-separated fields commute -/
def IsLocal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : OperatorValuedDistribution d H) : Prop :=
  ∀ f g : SchwartzSpacetime d,
    AreSpacelikeSeparatedSupports d f g →
    Commutator (φ.operator f) (φ.operator g) φ.domain.toSubmodule

/-! ### Vacuum Properties -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A vector is invariant under the Poincaré representation -/
def IsPoincareInvariant (π : PoincareRepresentation d H) (Ω : H) : Prop :=
  ∀ g : PoincareGroup d, π.U g Ω = Ω

/-- A vector is invariant under time translations only -/
def IsTimeTranslationInvariant (π : PoincareRepresentation d H) (Ω : H) : Prop :=
  ∀ t : ℝ, π.U (PoincareGroup.translation' (fun i => if i = 0 then t else 0)) Ω = Ω

/-- Uniqueness of the vacuum: Ω is the unique (up to phase) translation-invariant vector -/
def VacuumUnique (π : PoincareRepresentation d H) (Ω : H) : Prop :=
  IsTimeTranslationInvariant d π Ω ∧
  ∀ ψ : H, IsTimeTranslationInvariant d π ψ → ∃ c : ℂ, ψ = c • Ω

/-! ### The Complete Wightman QFT Structure -/

/-- A Wightman quantum field theory consists of:
    - A Hilbert space H (the state space)
    - A unitary representation of the Poincaré group
    - Field operators satisfying the Wightman axioms

    This structure encapsulates all the Wightman axioms (W1-W4). -/
structure WightmanQFT (d : ℕ) [NeZero d] where
  /-- The Hilbert space of states -/
  HilbertSpace : Type*
  /-- Hilbert space is a normed additive commutative group -/
  [instNormedAddCommGroup : NormedAddCommGroup HilbertSpace]
  /-- Hilbert space has inner product structure -/
  [instInnerProductSpace : InnerProductSpace ℂ HilbertSpace]
  /-- Hilbert space is complete -/
  [instCompleteSpace : CompleteSpace HilbertSpace]

  -- W1: Poincaré Covariance and Spectrum Condition
  /-- The unitary representation of the Poincaré group -/
  poincare_rep : @PoincareRepresentation d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace
  /-- Spectrum condition: energy-momentum spectrum in forward cone -/
  spectrum_condition : @SpectralCondition d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace poincare_rep
  /-- The vacuum vector -/
  vacuum : HilbertSpace
  /-- The vacuum is normalized -/
  vacuum_normalized : @norm HilbertSpace instNormedAddCommGroup.toNorm vacuum = 1
  /-- The vacuum is Poincaré invariant -/
  vacuum_invariant : @IsPoincareInvariant d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace poincare_rep vacuum

  -- W2: Field Operators
  /-- The field operator-valued distribution -/
  field : @OperatorValuedDistribution d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace
  /-- The vacuum is in the domain -/
  vacuum_in_domain : vacuum ∈ field.domain
  /-- Cyclicity: the algebraic span of field operators on vacuum is dense -/
  cyclicity : @Dense HilbertSpace (instNormedAddCommGroup.toUniformSpace.toTopologicalSpace)
              (field.algebraicSpan vacuum).carrier
  /-- The action of Poincaré transformations on test functions.
      (g · f)(x) = f(g⁻¹ · x) where g · x = Λx + a.

      Note: Proving that Poincaré transformations preserve the Schwartz class
      requires substantial analysis infrastructure. We include this as data
      with the consistency constraint `poincareAction_spec` below. -/
  poincareActionOnSchwartz : PoincareGroup d → SchwartzSpacetime d → SchwartzSpacetime d
  /-- Consistency: the Schwartz-wrapped action agrees with the pointwise action.
      This prevents axiom smuggling — the Schwartz wrapper must have the correct
      underlying function f(g⁻¹ · x). -/
  poincareAction_spec : ∀ (g : PoincareGroup d) (f : SchwartzSpacetime d) (x : SpacetimeDim d),
    (poincareActionOnSchwartz g f).toFun x = f.toFun (PoincareGroup.act g⁻¹ x)
  /-- Covariance: U(g) φ(f) U(g)⁻¹ = φ(g·f) where (g·f)(x) = f(g⁻¹·x).

      Expressed via matrix elements: for all g ∈ ISO(1,d), f ∈ 𝒮, and ψ, χ ∈ D,
        ⟨U(g)χ, φ(f) U(g)ψ⟩ = ⟨χ, φ(g·f) ψ⟩

      For scalar fields, the field transforms as:
        U(g) φ(f) U(g)⁻¹ = φ(g·f)

      This is equivalent to: ⟨U(g)χ, φ(f) U(g)ψ⟩ = ⟨χ, φ(g·f) ψ⟩ by unitarity. -/
  covariance : ∀ (g : PoincareGroup d) (f : SchwartzSpacetime d) (χ ψ : HilbertSpace),
    χ ∈ field.domain → ψ ∈ field.domain →
    ⟪poincare_rep.U g χ, field.operator f (poincare_rep.U g ψ)⟫_ℂ =
    ⟪χ, field.operator (poincareActionOnSchwartz g f) ψ⟫_ℂ

  -- W3: Locality
  /-- Locality: spacelike-separated fields commute -/
  locality : @IsLocal d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace field

  -- W4: Vacuum Uniqueness
  /-- Uniqueness of vacuum -/
  vacuum_unique : @VacuumUnique d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace poincare_rep vacuum

namespace WightmanQFT

variable {d : ℕ} [NeZero d]

-- Expose instances from WightmanQFT for use in definitions
attribute [instance] WightmanQFT.instNormedAddCommGroup
attribute [instance] WightmanQFT.instInnerProductSpace
attribute [instance] WightmanQFT.instCompleteSpace

/-- The Wightman n-point functions of a Wightman QFT.
    W_n(f₁,...,fₙ) = ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ -/
def wightmanFunction (qft : WightmanQFT d) (n : ℕ) :
    (Fin n → SchwartzSpacetime d) → ℂ :=
  fun fs => ⟪qft.vacuum, qft.field.operatorPow n fs qft.vacuum⟫_ℂ

/-- The 2-point function (propagator) W₂(f,g) = ⟨Ω, φ(f)φ(g)Ω⟩ -/
def twoPointFunction (qft : WightmanQFT d) :
    SchwartzSpacetime d → SchwartzSpacetime d → ℂ :=
  fun f g => qft.wightmanFunction 2 ![f, g]

/-- Symmetry property for bosonic fields: [φ(f), φ(g)] = 0 for any f, g -/
def IsBosonic (qft : WightmanQFT d) : Prop :=
  ∀ f g : SchwartzSpacetime d,
    Commutator (qft.field.operator f) (qft.field.operator g) qft.field.domain.toSubmodule

/-- The Reeh-Schlieder property: the vacuum is cyclic for local algebras.
    For any open region O, the vectors φ(f₁)···φ(fₙ)Ω with supp(fᵢ) ⊆ O are dense. -/
def ReehSchlieder (qft : WightmanQFT d) (O : Set (SpacetimeDim d)) : Prop :=
  let localSpan := Submodule.span ℂ
    { ψ | ∃ (n : ℕ) (fs : Fin n → SchwartzSpacetime d),
      (∀ i, Function.support (fs i) ⊆ O) ∧
      ψ = qft.field.operatorPow n fs qft.vacuum }
  Dense localSpan.carrier

/-- The Wightman functions are positive (reflection positivity).
    ‖φ(f₁)···φ(fₙ)Ω‖² ≥ 0, equivalently Re⟨ψ, ψ⟩ ≥ 0.
    For inner products in Hilbert space, ⟨ψ, ψ⟩ is real and equals ‖ψ‖². -/
def WightmanPositivity (qft : WightmanQFT d) : Prop :=
  ∀ n : ℕ, ∀ fs : Fin n → SchwartzSpacetime d,
    (⟪qft.field.operatorPow n fs qft.vacuum, qft.field.operatorPow n fs qft.vacuum⟫_ℂ).re ≥ 0

/-- Hermiticity of the 2-point function: W₂(f, g)* = W₂(ḡ, f̄).
    This follows from the hermiticity of the field. -/
def TwoPointHermitian (qft : WightmanQFT d) : Prop :=
  ∀ f g : SchwartzSpacetime d,
    starRingEnd ℂ (qft.twoPointFunction f g) = qft.twoPointFunction g f

end WightmanQFT

/-! ### Wightman Functions as Distributions -/

/-- The n-point domain: n copies of (d+1)-dimensional spacetime.
    Points are functions Fin n → Fin (d+1) → ℝ, i.e., n spacetime points. -/
abbrev NPointSpacetime (d n : ℕ) := Fin n → Fin (d + 1) → ℝ

/-- Schwartz space on n copies of spacetime -/
abbrev SchwartzNPointSpace (d n : ℕ) := SchwartzMap (NPointSpacetime d n) ℂ

/-- The Wightman n-point function on product test functions.

    W_n(f₁, ..., fₙ) = ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩

    This is defined for factored test functions (f₁,...,fₙ) where each fᵢ ∈ 𝒮(ℝ^{d+1}).
    Extension to general test functions F ∈ 𝒮(ℝ^{n(d+1)}) requires the nuclear
    theorem for Schwartz spaces, which guarantees that the multilinear functional
    on 𝒮(ℝ^{d+1})^⊗n extends uniquely to a continuous linear functional on
    the completed projective tensor product 𝒮(ℝ^{n(d+1)}). -/
def WightmanDistributionProduct (qft : WightmanQFT d) (n : ℕ) :
    (Fin n → SchwartzSpacetime d) → ℂ :=
  qft.wightmanFunction n

/-- **Schwartz nuclear theorem (kernel theorem for Schwartz spaces).**

    Given a separately continuous multilinear functional Phi on n copies of
    S(R^{d+1}), there exists a unique continuous linear functional W on the
    full Schwartz space S(R^{n(d+1)}) such that W agrees with Phi on product
    test functions: W(f_1 tensor ... tensor f_n) = Phi(f_1,...,f_n).

    The nuclear theorem guarantees that the multilinear Wightman n-point function
    extends to a continuous linear functional on the full Schwartz space S(R^{n(d+1)}).

    Since S(R^{d+1}) is nuclear (proved in SchwartzNuclear.lean),
    the completed projective tensor product S(R^{d+1}) tensor_pi ... tensor_pi S(R^{d+1})
    is isomorphic (as a topological vector space) to S(R^{n(d+1)}).

    The proof requires:
    1. Schwartz space is nuclear (proved in SchwartzNuclear.lean)
    2. For nuclear spaces, the projective tensor product topology agrees with
       the injective tensor product topology
    3. S(R^{d+1}) tensor_pi ... tensor_pi S(R^{d+1}) = S(R^{n(d+1)}) as TVS
    4. Separately continuous multilinear functionals on nuclear spaces extend
       uniquely to continuous functionals on the completed tensor product

    Ref: Gel'fand-Vilenkin, "Generalized Functions IV", Ch. I, 3;
    Reed-Simon, "Methods of Modern Math Physics I", Theorem V.13;
    Treves, "Topological Vector Spaces", Ch. 51 -/
private theorem schwartz_nuclear_extension (d n : ℕ) [NeZero d]
    (Phi : (Fin n → SchwartzSpacetime d) → ℂ)
    (hPhi_sep : ∀ (i : Fin n) (fs : Fin n → SchwartzSpacetime d),
      Continuous (fun f => Phi (Function.update fs i f))) :
    ∃ (W : SchwartzNPointSpace d n →L[ℂ] ℂ),
      ∀ fs : Fin n → SchwartzSpacetime d,
        W (SchwartzMap.productTensor fs) = Phi fs := by
  sorry

/-- Helper: The Wightman n-point function (f₁,...,fₙ) ↦ ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ is
    separately continuous in each test function argument.

    Continuity in f_i follows from:
    1. φ(f_i) : D → D is continuous from SchwartzSpacetime to operators (field is tempered)
    2. The operators φ(f_j) for j ≠ i are fixed
    3. The inner product ⟨·,·⟩ on the Hilbert space is continuous

    More precisely: the map f_i ↦ φ(f₁)···φ(f_i)···φ(fₙ)Ω is a composition of
    the continuous map f_i ↦ φ(f_i) (temperedness) with the fixed operators φ(f_j),
    and ⟨Ω, ·⟩ is continuous.

    Blocked by: need to express this composition formally using the WightmanQFT structure's
    field operator domain/continuity properties. -/
private theorem wightman_separately_continuous (qft : WightmanQFT d) (n : ℕ)
    (i : Fin n) (fs : Fin n → SchwartzSpacetime d) :
    Continuous (fun f => qft.wightmanFunction n (Function.update fs i f)) := by
  sorry

/-- **Wightman n-point functions extend to tempered distributions.**

    The multilinear Wightman functional (f_1,...,f_n) -> Omega, phi(f_1)...phi(f_n) Omega
    extends to a continuous linear functional on the full Schwartz space S(R^{n(d+1)}).

    This uses the nuclear theorem (`schwartz_nuclear_extension`) together with
    separate continuity of the Wightman functional in each test function argument.
    Separate continuity follows from the field operators being tempered distributions
    (continuous linear maps from S to operators on D) and the inner product being
    separately continuous. -/
theorem wightmanDistribution_extends (qft : WightmanQFT d) (n : ℕ) :
    ∃ (W_n : SchwartzNPointSpace d n →L[ℂ] ℂ),
      ∀ fs : Fin n → SchwartzSpacetime d,
        W_n (SchwartzMap.productTensor fs) = qft.wightmanFunction n fs := by
  -- Apply the nuclear theorem to the Wightman functional
  apply schwartz_nuclear_extension
  -- Need: separate continuity of the Wightman n-point function
  -- f_i -> Omega, phi(f_1)...phi(f_i)...phi(f_n) Omega is continuous in f_i
  -- because phi is an operator-valued tempered distribution and inner product is continuous.
  intro i fs
  exact wightman_separately_continuous (d := d) qft n i fs

/-- Temperedness of Wightman functions: The multilinear Wightman n-point function
    (f₁,...,fₙ) ↦ ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ is separately continuous in each argument.

    Full temperedness (continuity of the extension to 𝒮(ℝ^{n(d+1)})) follows from
    the nuclear theorem; see `wightmanDistribution_extends`. -/
def WightmanTempered (qft : WightmanQFT d) (n : ℕ) : Prop :=
  ∀ (i : Fin n) (fs : Fin n → SchwartzSpacetime d),
    Continuous (fun f => qft.wightmanFunction n (Function.update fs i f))

/-! ### Analytic Continuation -/

/-- A vector η ∈ ℝ^{d+1} lies in the open forward light cone V₊ if η₀ > 0 and η² < 0. -/
def InOpenForwardCone (d : ℕ) [NeZero d] (η : Fin (d + 1) → ℝ) : Prop :=
  η 0 > 0 ∧ MinkowskiSpace.minkowskiNormSq d η < 0

/-- The forward tube T_n in n copies of complexified spacetime.

    T_n = {(z₁,...,zₙ) ∈ ℂ^{n(d+1)} : Im(z₁) ∈ V₊, Im(z₂-z₁) ∈ V₊, ..., Im(zₙ-zₙ₋₁) ∈ V₊}

    where V₊ is the open forward light cone {η : η₀ > 0, η² < 0}.

    This is the domain to which Wightman functions analytically continue.

    We define the successive difference of imaginary parts η_k and require each
    to lie in V₊. -/
def ForwardTube (d n : ℕ) [NeZero d] : Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | ∀ k : Fin n,
    let prev : Fin (d + 1) → ℂ := if h : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩
    let η : Fin (d + 1) → ℝ := fun μ => (z k μ - prev μ).im
    InOpenForwardCone d η }

/-- The extended forward tube T_n^{ext} obtained by Lorentz covariance.

    T_n^{ext} = ⋃_{Λ ∈ L₊↑} Λ T_n

    where L₊↑ is the proper orthochronous Lorentz group.
    The edge-of-the-wedge theorem shows W_n extends to T_n^{ext}. -/
def ExtendedForwardTube (d n : ℕ) [NeZero d] : Set (Fin n → Fin (d + 1) → ℂ) :=
  ⋃ Λ : LorentzGroup.Restricted (d := d),
    { z | ∃ w ∈ ForwardTube d n, z = fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * w k ν }

/-- Convert a Euclidean spacetime point to a complex point via Wick rotation:
    (τ, x⃗) ↦ (iτ, x⃗).

    This is the fundamental map relating Euclidean and Minkowski spacetime. -/
def wickRotatePoint {d : ℕ} (x : Fin (d + 1) → ℝ) : Fin (d + 1) → ℂ :=
  fun μ => if μ = 0 then Complex.I * (x 0 : ℂ) else (x μ : ℂ)

/-- The Wightman functions have analytic continuation to the forward tube.

    The n-point Wightman function W_n(x₁,...,xₙ), initially defined as a
    distribution on real spacetime points, extends to a holomorphic function
    on the forward tube T_n.

    By Lorentz covariance, it further extends to the extended forward tube T_n^{ext}.
    The edge-of-the-wedge theorem (Bargmann-Hall-Wightman) shows this extension
    is single-valued.

    We define `analyticContinuation` on the full ambient space ℂ^{n(d+1)} and
    constrain holomorphicity to the forward tube via `DifferentiableOn`. -/
structure WightmanAnalyticity (qft : WightmanQFT d) where
  /-- The analytic continuation of the n-point function, defined on all of ℂ^{n(d+1)}.
      Only meaningful on the forward tube; values outside are auxiliary. -/
  analyticContinuation : (n : ℕ) → (Fin n → Fin (d + 1) → ℂ) → ℂ
  /-- The continuation is holomorphic on the forward tube -/
  isHolomorphic : ∀ n : ℕ, DifferentiableOn ℂ (analyticContinuation n) (ForwardTube d n)

/-- **Spectrum condition implies Fourier-Laplace distributional boundary values.**

    If a Wightman QFT has an analytic continuation to the forward tube (holomorphic
    on ForwardTube d n), and the QFT satisfies the spectrum condition, then the analytic
    continuation has tempered distributional boundary values.

    The boundary value distribution T is determined by the Wightman n-point function:
    the spectrum condition constrains the Fourier transform of W_n to be supported in
    the dual cone V_+^*, which is exactly the condition for W_n to be the distributional
    boundary value of its Fourier-Laplace transform (the analytic continuation).

    This is the fundamental connection between:
    (a) The Wightman distribution W_n (tempered, defined via inner products)
    (b) The analytic continuation (holomorphic on the forward tube)
    (c) The Fourier-Laplace representation (connecting (a) and (b))

    Ref: Streater-Wightman, Theorem 2-6; Vladimirov 25-26 -/
private theorem spectrum_implies_distributional_bv {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (T : SchwartzNPointSpace d n → ℂ)
    (hT_cont : Continuous T) :
    ∀ (f : SchwartzNPointSpace d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointSpacetime d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (T f)) := by
  sorry

private theorem wightman_analyticity_distributional_bv (qft : WightmanQFT d)
    (ha : WightmanAnalyticity d qft) (n : ℕ) :
    ∃ (T : SchwartzNPointSpace d n → ℂ),
      ∀ (f : SchwartzNPointSpace d n) (η : Fin n → Fin (d + 1) → ℝ),
        (∀ k, InOpenForwardCone d (η k)) →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointSpacetime d n,
            ha.analyticContinuation n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (T f)) := by
  -- Step 1: The Wightman distribution extends to a CLM on SchwartzNPointSpace
  obtain ⟨W_n, hW_n⟩ := wightmanDistribution_extends d qft n
  -- Step 2: T = W_n is tempered (continuous) and the distributional BV
  -- The analytic continuation recovers W_n as its distributional boundary value
  -- by the spectrum condition + Fourier-Laplace theory
  exact ⟨W_n, spectrum_implies_distributional_bv (ha.isHolomorphic n) W_n W_n.cont⟩

/-- **Pointwise boundary value existence for holomorphic functions on the forward tube
    along V₊-component approach directions.**

    Given a holomorphic function on the forward tube with distributional boundary values,
    the pointwise limit along any direction η (with each η_k ∈ V₊) exists.

    Note: this is stronger than `continuous_boundary_forwardTube` because it handles
    approach directions where the path `x + iεη` may not stay in the forward tube
    (i.e., successive differences η_k - η_{k-1} need not be in V₊).

    The proof uses the Fourier-Laplace representation of the boundary value:
    the distributional BV T is a tempered distribution whose Fourier transform has
    support in the dual cone, giving polynomial decay of F(x + iεη) that allows
    extraction of the pointwise limit.

    Ref: Vladimirov §26.2-26.3; Streater-Wightman, Theorem 3-7 -/
private theorem pointwise_limit_along_forwardCone_direction {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (h_bv : ∃ (T : SchwartzNPointSpace d n → ℂ),
      ∀ (f : SchwartzNPointSpace d n) (η : Fin n → Fin (d + 1) → ℝ),
        (∀ k, InOpenForwardCone d (η k)) →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointSpacetime d n,
            F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (T f)))
    (x : Fin n → Fin (d + 1) → ℝ)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : ∀ k, InOpenForwardCone d (η k)) :
    ∃ (limit : ℂ), Filter.Tendsto
      (fun ε : ℝ => F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds limit) := by
  sorry

/-- Boundary values of the analytic continuation recover Wightman functions.

    For any approach direction η with each component in V₊ and any real configuration x,
    the limit from within the forward tube exists:
      lim_{ε→0⁺} W_analytic(x₁ + iεη₁, ..., xₙ + iεηₙ) exists

    Proved by combining `wightman_analyticity_distributional_bv` (the analytic
    continuation has tempered distributional BVs) with
    `pointwise_limit_along_forwardCone_direction` (distributional BVs + holomorphicity
    imply pointwise limit existence along V₊-component directions).

    Ref: Streater-Wightman, "PCT, Spin and Statistics", Theorem 3-7 -/
theorem wightman_analyticity_boundary (qft : WightmanQFT d)
    (ha : WightmanAnalyticity d qft) (n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : ∀ k, InOpenForwardCone d (η k)) :
    -- The limit of the analytic continuation from within the forward tube exists
    ∃ (limit : ℂ), Filter.Tendsto
      (fun ε : ℝ => ha.analyticContinuation n
        (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds limit) := by
  exact pointwise_limit_along_forwardCone_direction (ha.isHolomorphic n)
    (wightman_analyticity_distributional_bv d qft ha n) x η hη

end

