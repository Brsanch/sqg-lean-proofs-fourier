/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under MIT license.
Authors: Bryan Sanchez

# Sobolev embedding `Ḣˢ(𝕋²) ⊂ L∞(𝕋²)` for `s > 1`

The homogeneous Sobolev seminorm is the Fourier-side `∑' k, |k|^{2s}·‖f̂(k)‖²`,
with `|·|` the ℓ∞ lattice norm on ℤ².  For `s > d/2 = 1`, Cauchy–Schwarz
against the convergent lattice zeta sum `∑' k≠0, |k|^{-2s}` gives
`‖f‖_{L∞} ≤ C_s · (|f̂(0)| + ‖f‖_{Ḣˢ})`.
-/

import FourierAnalysis.LittlewoodPaley.Bernstein

namespace FourierAnalysis

open UnitAddTorus

/-- Homogeneous Sobolev seminorm squared on `𝕋²`: `‖f‖²_{Ḣˢ}`.

The `k = 0` term vanishes for `s > 0` because `lInfNorm 0 = 0` and
`(0 : ℝ) ^ (2s) = 0` for `s > 0`. -/
noncomputable def hsSeminormSq (s : ℝ) (f : 𝕋² → ℂ) : ℝ :=
  ∑' k : Fin 2 → ℤ, (lInfNorm k : ℝ) ^ (2 * s) * ‖mFourierCoeff f k‖ ^ 2

/-- The Ḣˢ seminorm-squared is nonnegative. -/
lemma hsSeminormSq_nonneg (s : ℝ) (f : 𝕋² → ℂ) : 0 ≤ hsSeminormSq s f := by
  unfold hsSeminormSq
  refine tsum_nonneg (fun k => ?_)
  have h1 : (0 : ℝ) ≤ (lInfNorm k : ℝ) ^ (2 * s) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h2 : (0 : ℝ) ≤ ‖mFourierCoeff f k‖ ^ 2 := sq_nonneg _
  exact mul_nonneg h1 h2

end FourierAnalysis
