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

/-- Cauchy–Schwarz form: the squared pointwise value of the projector is
bounded by the shell cardinality times the sum of squared Fourier moduli. -/
theorem sq_norm_lpProjector_le (N : ℕ) (f : 𝕋² → ℂ) (x : 𝕋²) :
    ‖lpProjector N f x‖ ^ 2 ≤
      (dyadicAnnulus N).card * ∑ k ∈ dyadicAnnulus N, ‖mFourierCoeff f k‖ ^ 2 := by
  have h1 := norm_lpProjector_le N f x
  have h2 : (0 : ℝ) ≤ ‖lpProjector N f x‖ := norm_nonneg _
  calc ‖lpProjector N f x‖ ^ 2
      ≤ (∑ k ∈ dyadicAnnulus N, ‖mFourierCoeff f k‖) ^ 2 :=
        pow_le_pow_left₀ h2 h1 2
    _ ≤ (dyadicAnnulus N).card * ∑ k ∈ dyadicAnnulus N, ‖mFourierCoeff f k‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq

/-- Bernstein-type bound on the dyadic shell at level `N+1`:
the squared pointwise value is controlled by `4^(N+2)` times the
sum of squared Fourier moduli over the shell. -/
theorem sq_norm_lpProjector_succ_le (N : ℕ) (f : 𝕋² → ℂ) (x : 𝕋²) :
    ‖lpProjector (N + 1) f x‖ ^ 2 ≤
      (4 * 4 ^ (N + 1) : ℝ) *
        ∑ k ∈ dyadicAnnulus (N + 1), ‖mFourierCoeff f k‖ ^ 2 := by
  have hcard : ((dyadicAnnulus (N + 1)).card : ℝ) ≤ 4 * 4 ^ (N + 1) := by
    exact_mod_cast card_dyadicAnnulus_succ_le_four_pow N
  have hnn : (0 : ℝ) ≤
      ∑ k ∈ dyadicAnnulus (N + 1), ‖mFourierCoeff f k‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc ‖lpProjector (N + 1) f x‖ ^ 2
      ≤ (dyadicAnnulus (N + 1)).card *
          ∑ k ∈ dyadicAnnulus (N + 1), ‖mFourierCoeff f k‖ ^ 2 :=
        sq_norm_lpProjector_le (N + 1) f x
    _ ≤ (4 * 4 ^ (N + 1) : ℝ) *
          ∑ k ∈ dyadicAnnulus (N + 1), ‖mFourierCoeff f k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcard hnn

end FourierAnalysis
