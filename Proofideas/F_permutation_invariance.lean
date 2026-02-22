/-
# Proof Strategy: F_permutation_invariance

## Status (2026-02-22)

### Key insight from Gemini consultation:
**The standard BHW proof does NOT use the edge-of-the-wedge theorem for the
permutation step.** Instead, it uses:
1. Complex Lorentz invariance → extend F to the extended tube T'_n
2. Jost's lemma: totally spacelike real configurations ("Jost points") lie in T'_n
3. Locality: F = F∘σ on the Jost set (by hF_local at real spacelike configurations)
4. Identity theorem: F = F∘σ propagates from the Jost set to the full domain

### Why EOW doesn't directly apply (analysis from 2026-02-22):
The permuted tube σ·FT is NOT the "opposite tube" T(-C) of FT = T(C) in the
edge-of-the-wedge sense. Specifically, for σ = swap(i, i+1) in position variables:
- FT condition at i+1: Im(z_{i+1} - z_i) ∈ V⁺
- σ·FT condition at i+1: Im(z_i - z_{i+1}) = -Im(z_{i+1} - z_i) ∈ V⁺  (sign flip ✓)
- σ·FT condition at i: Im(z_{i+1} - z_{i-1}) = Im(ζ_i + ζ_{i+1}) ∈ V⁺  (MIXES variables!)
- σ·FT condition at i+2: Im(z_{i+2} - z_i) = Im(ζ_{i+1} + ζ_{i+2}) ∈ V⁺  (MIXES variables!)

The mixing at positions i and i+2 means:
- f⁻(ξ) for Im(ξ) ∈ -V⁺ is only defined when Im(ζ_i) + Im(ξ) ∈ V⁺, which
  constrains |Im(ξ)| relative to Im(ζ_i). So f⁻ is NOT defined on all of T(-V⁺).
- Our formalized EOW theorem requires f⁻ on the ENTIRE negative tube T(-V⁺).
- No choice of "subcone" works because V⁺ is unbounded and the constraint is
  parameter-dependent, not scale-invariant.

## Proof strategy: Jost point approach (NO EOW needed)

### Setup
- F holomorphic on FT, real Lorentz invariant, continuous boundary values (hF_bv),
  local commutativity (hF_local).
- Complex Lorentz invariance: F(Λ·z) = F(z) for z, Λ·z ∈ FT. (PROVED modulo orbitSet)
- extendF defined on ExtendedTube T'_n = ⋃_Λ Λ·FT, with extendF = F on FT.
  (PROVED: `extendF_eq_on_forwardTube`, `extendF_preimage_eq`)

### Step 1: Holomorphicity of extendF on T'_n
**Status: Needs proof (straightforward from existing infrastructure)**

Use the same inverse chart argument as BHW Property 1:
For z ∈ T'_n, write z = Λ₀·w₀ with w₀ ∈ FT.
Set ψ(z) = Λ₀⁻¹·z (so ψ(z₀) = w₀ ∈ FT).
Then extendF(z) = F(ψ(z)) near z₀ (by well-definedness of extendF).
Since F is holomorphic on FT and ψ is holomorphic, extendF is holomorphic near z₀.

### Step 2: Jost's lemma — totally spacelike configurations lie in T'_n
**Status: KEY NEW INFRASTRUCTURE NEEDED**

**Definition (Jost set)**:
  J = {x ∈ ℝ^{n(d+1)} : all pairwise differences x_a - x_b are spacelike}
    = {x : ∀ a b, a ≠ b → ∑_μ η_μ (x_a^μ - x_b^μ)² < 0}

Equivalently (for the consecutive-difference formulation):
  J = {x : ∀ λ ∈ ℝ^n with λ ≥ 0, ∑λ > 0, (∑_k λ_k ζ_k)² < 0}
where ζ_k = x_k - x_{k-1}.

**Jost's lemma**: J ⊆ T'_n.

**Proof sketch (Jost 1965, Streater-Wightman Theorem 2-10)**:
For x ∈ J, all difference vectors ζ_k are spacelike. There exists a complex Lorentz
transformation Λ ∈ SO⁺(1,d;ℂ) that "rotates" the spacelike vectors into the
forward light cone.

Specifically, for a single spacelike vector ζ with ζ² < 0:
- There exists a real Lorentz boost that makes ζ purely spatial: ζ = (0, ξ_1, ..., ξ_d).
- Then exp(iθ J₀₁) with tan(θ) = ξ₁/|ξ| (a complex rotation in the 01-plane)
  maps ζ to a vector with Im in V⁺.

For n-1 difference vectors simultaneously:
- Use complex Lorentz transformations to rotate ALL differences ζ_1, ..., ζ_{n-1}
  so that each Im(Λ·ζ_k) ∈ V⁺.
- The key constraint is that Λ is a SINGLE complex Lorentz transformation
  (not different ones for each k).
- This works because the totally spacelike condition ensures no "interference"
  between the rotations.

**Infrastructure needed for Jost's lemma**:
- Pure imaginary rotations (complex boosts): exp(iθ · J_μν) for real θ
- The forward light cone condition in terms of Minkowski inner products
- Matrix exponential properties for so(1,d;ℂ)

### Step 3: Boundary value agreement — extendF(x) = F(x_ℂ) on J
**Status: Straightforward from continuity**

For x ∈ J, x is a real point on the boundary of FT.
- x is a limit point of FT: take z_n = x + iε_n η where η has all differences in V⁺.
  Then z_n ∈ FT and z_n → x as ε_n → 0.
- extendF is holomorphic (hence continuous) on T'_n and J ⊆ T'_n (by Jost's lemma).
- extendF = F on FT, so lim extendF(z_n) = lim F(z_n) = F(x_ℂ) (by hF_bv).
- By continuity of extendF at x: extendF(x) = lim extendF(z_n) = F(x_ℂ).

### Step 4: Locality on J — extendF(σ·x) = extendF(x)
**Status: Straightforward from hF_local**

For x ∈ J and σ = swap(i, i+1):
- x has (x_{i+1} - x_i)² < 0 (spacelike), so hF_local gives F(σ·x_ℂ) = F(x_ℂ).
- σ·x ∈ J (J is permutation-invariant since "all pairs spacelike" is symmetric).
- extendF(σ·x) = F(σ·x_ℂ) (by Step 3 applied to σ·x).
- extendF(x) = F(x_ℂ) (by Step 3).
- Therefore extendF(σ·x) = F(σ·x_ℂ) = F(x_ℂ) = extendF(x). ✓

### Step 5: Gluing — define H on T'_n ∪ σ(T'_n)
**Status: Needs identity theorem on totally real submanifolds**

Define:
  H(z) = extendF(z)          for z ∈ T'_n
  H(z) = extendF(σ⁻¹·z)     for z ∈ σ(T'_n)

For this to be well-defined, we need:
On T'_n ∩ σ(T'_n): extendF(z) = extendF(σ⁻¹·z).
Equivalently: extendF(σ·z) = extendF(z) for z ∈ T'_n ∩ σ⁻¹(T'_n).

Proof:
- On J ⊂ T'_n ∩ σ⁻¹(T'_n): this is Step 4. ✓
- The function f(z) = extendF(z) - extendF(σ·z) is holomorphic on T'_n ∩ σ⁻¹(T'_n).
- f = 0 on J, which is an open subset of ℝ^{n(d+1)} (a totally real submanifold).
- By the identity theorem for totally real submanifolds: f = 0 on the connected
  component of T'_n ∩ σ⁻¹(T'_n) containing J.

**Identity theorem for totally real submanifolds**:
If g is holomorphic on open connected D ⊂ ℂ^m and g = 0 on an open subset
V ⊂ D ∩ ℝ^m, then g = 0 on D.

Proof: At x₀ ∈ V, g is analytic with Taylor expansion g(z) = Σ_α c_α (z - x₀)^α.
For real z near x₀: g(z) = 0, so all c_α = 0 (uniqueness of real power series).
Hence g = 0 in a complex neighborhood of x₀. By the standard identity theorem
(for functions vanishing on an open set), g = 0 on the connected component.

### Step 6: Lorentz invariance of H
**Status: Same T-set argument as complex_lorentz_invariance (modulo orbitSet sorry)**

H is holomorphic on D = T'_n ∪ σ(T'_n), which is:
- Open (union of open sets) ✓
- Connected (T'_n and σ(T'_n) are connected, their intersection T'_n ∩ σ(T'_n) ⊃ J ≠ ∅) ✓

H is real Lorentz invariant on D:
- On T'_n: H = extendF, which is real Lorentz invariant (real Lorentz preserves FT,
  hence T'_n, and extendF is defined via complex_lorentz_invariance which implies
  real Lorentz invariance).
- On σ(T'_n): H = extendF∘σ⁻¹. Real Lorentz Λ commutes with σ:
  H(Λ·z) = extendF(σ⁻¹·(Λ·z)) = extendF(Λ·(σ⁻¹·z)) = extendF(σ⁻¹·z) = H(z). ✓

Apply the T-set argument (same as complex_lorentz_invariance) to H on D:
- T = {Λ : ∀ z ∈ D, Λ·z ∈ D → H(Λ·z) = H(z)}
- 1 ∈ T (trivial)
- T closed, T ∩ U open, T^c ⊆ U
- U connected (modulo orbit set sorry for D, which follows from orbit set sorry for FT
  since FT ⊆ D and orbit sets of D ⊇ orbit sets of FT)
- Therefore T = G.

**This step requires the orbit set sorry (same as complex_lorentz_invariance).
It does NOT introduce any new sorry.**

### Step 7: Conclude F_permutation_invariance
**Status: Straightforward**

Given w ∈ FT and Γ·(σ·w) ∈ FT:
1. Set u = σ·w.
2. Γ·u ∈ FT ⊂ T'_n ⊂ D.
3. σ·w = u. We need u ∈ D. Since Γ·u ∈ FT ⊂ T'_n, and u = Γ⁻¹·(Γ·u):
   u ∈ Γ⁻¹·T'_n = T'_n (since T'_n is Lorentz-invariant). So u ∈ T'_n ⊂ D. ✓
   Also u = σ·w, and w ∈ FT ⊂ T'_n ⊂ σ(T'_n) [NO! w ∈ T'_n does NOT imply w ∈ σ(T'_n)].
   But u ∈ σ(FT) ⊂ σ(T'_n) ⊂ D. ✓

4. By Lorentz invariance of H (Step 6): H(Γ·u) = H(u).
5. H(Γ·u) = extendF(Γ·u) = F(Γ·u) = F(Γ·(σ·w))
   [since Γ·u ∈ FT ⊂ T'_n and H = extendF on T'_n and extendF = F on FT].
6. H(u) = extendF(σ⁻¹·u) = extendF(w) = F(w)
   [since u ∈ σ(T'_n) and H = extendF∘σ⁻¹ on σ(T'_n), and σ⁻¹·u = σ·(σ·w) = w ∈ FT].
7. Therefore F(Γ·(σ·w)) = F(w). ✓

For general τ (product of adjacent transpositions): induction. Decompose τ = σ_m ∘ ... ∘ σ_1,
extend one transposition at a time (each step adds one more σ(T'_n) to the domain D).

## Required infrastructure (ordered by priority)

### Priority 1: Jost's lemma
- Define Jost set J (totally spacelike real configurations)
- Prove J ⊆ ExtendedTube
- This requires: complex boosts exp(iθ J_{μν}) mapping spacelike → forward timelike
- Estimated: 200-400 LOC

### Priority 2: Identity theorem for totally real submanifolds
- If f holomorphic on connected open D ⊂ ℂ^m and f = 0 on open V ⊂ D ∩ ℝ^m, then f = 0 on D.
- Follows from: f analytic at x₀ ∈ V, f|_ℝ = 0 near x₀ ⟹ Taylor coefficients = 0 ⟹ f = 0 near x₀.
- We may already have enough in SCV/IdentityTheorem.lean (analytic functions vanishing on thick sets).
- Estimated: 50-100 LOC

### Priority 3: Holomorphicity of extendF on ExtendedTube
- Same chart argument as BHW Property 1 but for extendF (not fullExtendF).
- Uses complex_lorentz_invariance for well-definedness.
- Estimated: 50-80 LOC

### Priority 4: Boundary value agreement
- extendF(x) = F(x_ℂ) for x ∈ J (Jost point, limit of FT)
- Continuity argument: extendF is continuous on T'_n, F is continuous at boundary (hF_bv).
- Estimated: 30-50 LOC

### Priority 5: Connectedness of T'_n ∩ σ⁻¹(T'_n)
- Needed for the identity theorem step (Step 5).
- T'_n ∩ σ⁻¹(T'_n) is open and contains J (nonempty).
- Need: the connected component containing J also contains FT ∩ σ⁻¹(T'_n).
- This may follow from T'_n being path-connected + J being "reachable" from FT.
- NOTE: Even if this connectivity is hard, we only need it for the SPECIFIC points
  appearing in the F_permutation_invariance hypothesis (where Γ·(σ·w) ∈ FT).
  These points ARE in T'_n ∩ σ⁻¹(T'_n) by the argument in Step 7.
- Estimated: 50-150 LOC (depending on approach)

## Dependency summary

```
Jost's lemma (Priority 1, main new work)
    │
    ├── J ⊆ ExtendedTube
    │
    ├── Locality on J (Step 4, easy from hF_local)
    │
    └── Boundary value agreement (Priority 4, continuity)
            │
            ▼
Identity theorem for totally real (Priority 2)
    │
    ▼
Gluing (Step 5): extendF∘σ = extendF on T'_n ∩ σ⁻¹(T'_n)
    │
    ▼
Lorentz invariance of H (Step 6, reuses T-set argument, modulo orbitSet sorry)
    │
    ▼
F_permutation_invariance (Step 7, conclusion)
```

## Key difference from previous approach

**Previous approach** (abandoned): Apply edge-of-the-wedge directly to F and F∘σ on
the forward and permuted tubes. BLOCKED because the permuted tube is NOT T(-C).

**New approach** (Jost point): Use complex Lorentz invariance to reach Jost points
(real, spacelike), where locality gives F = F∘σ. Propagate by identity theorem.
NO edge-of-the-wedge needed for this step!

The EOW theorem is still used elsewhere (e.g., the proved `edge_of_the_wedge` axiom
replacement), but NOT for the BHW permutation step.

## Impact on PET preconnected (sorry #3)

PET = T''_n = ⋃_τ ⋃_Λ Λ·(τ·FT).

The same Jost point argument shows: J ⊂ T'_n ∩ σ(T'_n) for each σ. So the
different "sectors" σ_k(T'_n) all contain J. Since T'_n ∪ σ(T'_n) is connected
(sharing J), iterating gives T''_n is connected.

More precisely: PET = T'_n ∪ ⋃_σ σ(T'_n). Each σ(T'_n) is connected, and
T'_n ∩ σ(T'_n) ⊃ J ≠ ∅. So the union is connected.

This means PET preconnected follows from:
1. T'_n is connected (equivalent to SO⁺(1,d;ℂ) × FT connected).
2. Jost's lemma: J ⊂ T'_n ∩ σ(T'_n) for each σ.

So **Jost's lemma is the key infrastructure for BOTH F_permutation_invariance AND
PET preconnected**. Proving Jost's lemma would reduce all 3 Connectedness.lean sorrys
to just `orbitSet_isPreconnected`.
-/
