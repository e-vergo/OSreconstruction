/-
Helper lemmas for self-adjoint idempotent operators.
These lemmas are used in the spectral projection multiplicativity proof.

This file should NOT import SpectralTheoremViaRMK - instead, that file
imports this one.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Analysis.InnerProductSpace.Positive

open scoped InnerProductSpace ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace SelfAdjointIdempotent

/-!
## Norm-squared equals inner product for self-adjoint idempotent operators

For a self-adjoint idempotent projection P, we have ‖Px‖² = Re⟨x, Px⟩.
-/

omit [CompleteSpace H] in
/-- For any x: Re⟨x, x⟩ = ‖x‖² -/
lemma inner_self_re_eq_norm_sq (x : H) :
    (@inner ℂ H _ x x).re = ‖x‖^2 := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x
  simp only [h, sq, Complex.mul_re]
  simp [Complex.ofReal_re, Complex.ofReal_im]

/-- For self-adjoint idempotent P: ‖Px‖² = Re⟨x, Px⟩ -/
lemma norm_sq_eq_inner_re_of_selfAdjoint_idempotent
    (P : H →L[ℂ] H) (hP_adj : P.adjoint = P) (hP_idem : P.comp P = P) (x : H) :
    ‖P x‖^2 = (@inner ℂ H _ x (P x)).re := by
  have hre : (@inner ℂ H _ (P x) (P x)).re = ‖P x‖^2 := inner_self_re_eq_norm_sq (P x)
  have hcomp : (P ∘L P) x = P x := by rw [hP_idem]
  calc ‖P x‖^2
      = (@inner ℂ H _ (P x) (P x)).re := hre.symm
    _ = (@inner ℂ H _ x (P (P x))).re := by
        -- Use adjoint_inner_right: ⟨x, A† y⟩ = ⟨A x, y⟩
        -- So ⟨x, P† (Px)⟩ = ⟨Px, Px⟩, and P† = P gives ⟨x, P(Px)⟩ = ⟨Px, Px⟩
        have heq : @inner ℂ H _ (P x) (P x) = @inner ℂ H _ x (P (P x)) := by
          rw [← ContinuousLinearMap.adjoint_inner_right P x (P x), hP_adj]
        rw [heq]
    _ = (@inner ℂ H _ x ((P ∘L P) x)).re := rfl
    _ = (@inner ℂ H _ x (P x)).re := by rw [hcomp]

omit [CompleteSpace H] in
/-- Helper to convert between .re notations -/
lemma inner_re_eq_rclike_re (x y : H) :
    (@inner ℂ H _ x y).re = RCLike.re (@inner ℂ H _ x y) := rfl

omit [CompleteSpace H] in
/-- Conjugate symmetry for real parts -/
lemma inner_re_conj_symm (x y : H) :
    (@inner ℂ H _ x y).re = (@inner ℂ H _ y x).re := by
  calc (@inner ℂ H _ x y).re
      = (starRingEnd ℂ (@inner ℂ H _ y x)).re := by rw [inner_conj_symm x y]
    _ = (@inner ℂ H _ y x).re := Complex.conj_re _

omit [CompleteSpace H] in
/-- If P ≤ Q in the Loewner order, then Re⟨x, Px⟩ ≤ Re⟨x, Qx⟩ -/
lemma loewner_le_inner_re (P Q : H →L[ℂ] H) (hle : P ≤ Q) (x : H) :
    (@inner ℂ H _ x (P x)).re ≤ (@inner ℂ H _ x (Q x)).re := by
  rw [ContinuousLinearMap.le_def] at hle
  have h := hle.2 x
  rw [ContinuousLinearMap.reApplyInnerSelf] at h
  have hsub_eq : (Q - P) x = Q x - P x := ContinuousLinearMap.sub_apply Q P x
  rw [hsub_eq, inner_sub_left, map_sub] at h
  have heq1 : (@inner ℂ H _ x (P x)).re = RCLike.re (@inner ℂ H _ (P x) x) := by
    calc (@inner ℂ H _ x (P x)).re
        = (starRingEnd ℂ (@inner ℂ H _ (P x) x)).re := by rw [inner_conj_symm x (P x)]
      _ = (@inner ℂ H _ (P x) x).re := Complex.conj_re _
      _ = RCLike.re (@inner ℂ H _ (P x) x) := rfl
  have heq2 : (@inner ℂ H _ x (Q x)).re = RCLike.re (@inner ℂ H _ (Q x) x) := by
    calc (@inner ℂ H _ x (Q x)).re
        = (starRingEnd ℂ (@inner ℂ H _ (Q x) x)).re := by rw [inner_conj_symm x (Q x)]
      _ = (@inner ℂ H _ (Q x) x).re := Complex.conj_re _
      _ = RCLike.re (@inner ℂ H _ (Q x) x) := rfl
  rw [heq1, heq2]
  linarith

/-- For self-adjoint idempotent P, Q with P ≤ Q: ‖Px‖ ≤ ‖Qx‖ -/
lemma norm_le_of_loewner_le
    (P Q : H →L[ℂ] H)
    (hP_adj : P.adjoint = P) (hP_idem : P.comp P = P)
    (hQ_adj : Q.adjoint = Q) (hQ_idem : Q.comp Q = Q)
    (hle : P ≤ Q) (x : H) :
    ‖P x‖ ≤ ‖Q x‖ := by
  have hinner_le := loewner_le_inner_re P Q hle x
  have h1 : ‖P x‖^2 = (@inner ℂ H _ x (P x)).re :=
    norm_sq_eq_inner_re_of_selfAdjoint_idempotent P hP_adj hP_idem x
  have h2 : ‖Q x‖^2 = (@inner ℂ H _ x (Q x)).re :=
    norm_sq_eq_inner_re_of_selfAdjoint_idempotent Q hQ_adj hQ_idem x
  rw [← h1, ← h2] at hinner_le
  have h := Real.sqrt_le_sqrt hinner_le
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  exact h

end SelfAdjointIdempotent
