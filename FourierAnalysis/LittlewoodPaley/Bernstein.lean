/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under MIT license.
Authors: Bryan Sanchez

# Bernstein-type inequalities on `𝕋²`

Pointwise bounds for the dyadic Fourier projector `lpProjector`.
The primary inequality (to follow via Cauchy–Schwarz + the
cardinality estimate `card_dyadicAnnulus_succ_le_four_pow`):

`‖Δ_N f‖_{L^∞} ≤ C · 2^N · ‖Δ_N f‖_{L²}`.

This file currently contains the triangle-inequality precursor.
-/

import FourierAnalysis.LittlewoodPaley.Dyadic

namespace FourierAnalysis

open UnitAddTorus

/-- Pointwise triangle-inequality bound on the dyadic projector. -/
theorem norm_lpProjector_le (N : ℕ) (f : 𝕋² → ℂ) (x : 𝕋²) :
    ‖lpProjector N f x‖ ≤ ∑ k ∈ dyadicAnnulus N, ‖mFourierCoeff f k‖ := by
  unfold lpProjector
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun k _ => ?_)
  rw [norm_smul]
  have h1 : ‖(mFourier k : 𝕋² → ℂ) x‖ ≤ 1 :=
    calc ‖(mFourier k : 𝕋² → ℂ) x‖
        ≤ ‖mFourier (d := Fin 2) k‖ := (mFourier k).norm_coe_le_norm x
      _ = 1 := mFourier_norm
  calc ‖mFourierCoeff f k‖ * ‖(mFourier k : 𝕋² → ℂ) x‖
      ≤ ‖mFourierCoeff f k‖ * 1 := by
        exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖mFourierCoeff f k‖ := by ring

end FourierAnalysis
