# Bargmann-Hall-Wightman Theorem: Gap Analysis

## Status Summary

The Bargmann-Hall-Wightman (BHW) theorem (`bargmann_hall_wightman` in
`AnalyticContinuation.lean`) **cannot be proved** with current Mathlib/Lean 4
infrastructure. It is promoted to a named axiom.

## What the Theorem Says

Given a holomorphic function F on the forward tube T_n that is:
1. Invariant under the real restricted Lorentz group L+^up
2. Satisfies local commutativity at spacelike-separated points

Then F extends to a holomorphic function F_ext on the permuted extended tube
T''_n, and the extension is:
1. Invariant under the full complex Lorentz group L+(C)
2. Symmetric under all permutations of the arguments

## Proof Structure

The proof has 4 steps:

| Step | Description | Status |
|------|-------------|--------|
| **1. Real -> Complex Lorentz** | Analytic continuation: F(Lambda*z) = F(z) for real Lambda extends to complex Lambda | **BLOCKED** |
| **2. Jost point matching** | Local commutativity gives F(pi*x) = F(x) at spacelike real points | **Available** (jost_lemma proved, hF_local hypothesis) |
| **3. Edge-of-the-wedge** | Glue functions on adjacent permuted tubes across Jost point boundaries | **Available** (edge_of_the_wedge axiom) |
| **4. Iterate over S_n** | Cover all permutations via adjacent transpositions | Feasible (combinatorics) |

## The Hard Blocker: Step 1

### What's needed

Step 1 requires proving that real Lorentz invariance implies complex Lorentz
invariance. The argument is:

1. **L+(C) is connected**: The proper complex Lorentz group SO+(1,d;C) is a
   connected complex Lie group. This is a non-trivial topological result —
   the real Lorentz group SO+(1,d;R) has 4 connected components, but its
   complexification is connected.

2. **Holomorphicity of the group action**: For fixed z in the forward tube,
   the map Lambda -> F(Lambda*z) is holomorphic on L+(C).

3. **Identity theorem on connected complex manifolds**: Since F(Lambda*z) = F(z)
   for all Lambda in the real Lorentz group (a totally real submanifold of
   L+(C)), and L+(C) is connected, the identity theorem gives F(Lambda*z) = F(z)
   for ALL Lambda in L+(C).

### What's missing from Mathlib

| Component | Description | Estimated effort |
|-----------|-------------|------------------|
| **Connectedness of SO+(1,d;C)** | Topological result about complex Lie groups | 300-500 LOC |
| **Complex manifold structure of L+(C)** | L+(C) as a complex analytic manifold | 500+ LOC |
| **Identity theorem on manifolds** | Extension of identity theorem from C^n to complex manifolds | 200-400 LOC |
| **Holomorphicity of group action** | Lambda -> F(Lambda*z) is holomorphic | 200-300 LOC |

**Total estimated effort: 1200-1700 LOC** of complex Lie group theory and
several complex variables not present in Mathlib.

## Available Infrastructure

The following components ARE available:

- `ComplexLorentzGroup d` — structure definition with metric-preserving and
  det = 1 conditions
- `ComplexLorentzGroup.ofReal` — embedding of real Lorentz group (proved)
- `ComplexLorentzGroup.ofEuclidean` — embedding of Euclidean rotations (proved)
- `ForwardTube`, `ComplexExtendedForwardTube`, `PermutedExtendedTube` —
  tube domain hierarchy (defined)
- `ForwardTube_subset_ComplexExtended` — inclusion (proved)
- `ComplexExtended_subset_Permuted` — inclusion (proved)
- `jost_lemma` — spacelike separation at Jost points (proved)
- `edge_of_the_wedge` — axiom (available for Step 3)

## Mathematical Correctness of the Axiom

The BHW theorem is a well-established result in axiomatic QFT:

- **Original proof**: Bargmann, Hall, and Wightman (1957)
- **Standard reference**: Streater & Wightman, *PCT, Spin and Statistics*,
  Theorem 2-11 and surrounding discussion
- **Also**: Jost (1965), *The General Theory of Quantized Fields*, Ch. IV

The axiom statement matches the standard formulation:
- **Hypotheses**: holomorphicity on forward tube, real Lorentz invariance,
  local commutativity at adjacent transpositions
- **Conclusion**: extension to permuted extended tube with complex Lorentz
  invariance and full permutation symmetry

The axiom is a true mathematical theorem whose proof requires infrastructure
(complex Lie group theory) not available in Mathlib.

## Impact on Project

BHW is sorry #2 on the critical path. It blocks:
- Sorry #6 (`constructedSchwinger_symmetric`) — E3 symmetry in R->E direction
- Sorry #13 (`lorentz_covariant`) — Lorentz covariance extraction in E->R
- Sorry #15 (`locally_commutative`) — Locality extraction in E->R

Promoting it to an axiom unblocks these downstream results (they can now
use BHW as a black box).

## References

- Bargmann, V., Hall, D., and Wightman, A.S. (1957). *On the group of
  analytic continuation of Wightman functions*. Nuovo Cimento 5, 1-14.
- Jost, R. (1965). *The General Theory of Quantized Fields*. AMS, Ch. IV.
- Streater, R.F. and Wightman, A.S. (2000). *PCT, Spin and Statistics, and
  All That*. Princeton University Press, Theorem 2-11.
