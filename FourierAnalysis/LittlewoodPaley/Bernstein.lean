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

/-- Pointwise triangle bound on the partial sum: sum of projector norms. -/
theorem norm_lpPartialSum_le (N : ℕ) (f : 𝕋² → ℂ) (x : 𝕋²) :
    ‖lpPartialSum N f x‖ ≤
      ∑ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖ := by
  unfold lpPartialSum
  exact norm_sum_le _ _

/-- Cauchy–Schwarz form on the partial sum: squared norm is bounded by
`(N+1) · ∑ ‖Δ_j f x‖²`. -/
theorem sq_norm_lpPartialSum_le (N : ℕ) (f : 𝕋² → ℂ) (x : 𝕋²) :
    ‖lpPartialSum N f x‖ ^ 2 ≤
      (N + 1 : ℕ) * ∑ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖ ^ 2 := by
  have hle := norm_lpPartialSum_le N f x
  have hnn : (0 : ℝ) ≤ ‖lpPartialSum N f x‖ := norm_nonneg _
  calc ‖lpPartialSum N f x‖ ^ 2
      ≤ (∑ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖) ^ 2 :=
        pow_le_pow_left₀ hnn hle 2
    _ ≤ (Finset.range (N + 1)).card *
          ∑ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ = (N + 1 : ℕ) * ∑ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖ ^ 2 := by
        rw [Finset.card_range]

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

/-- `(2 * 2^m)^2 = 4 * 4^m` in ℝ. -/
private lemma two_two_pow_sq_eq_four_four_pow (m : ℕ) :
    ((2 * (2 : ℝ) ^ m)) ^ 2 = 4 * 4 ^ m := by
  have h : ((2 : ℝ) ^ m) ^ 2 = 4 ^ m := by
    exact_mod_cast two_pow_sq_eq_four_pow m
  calc ((2 * (2 : ℝ) ^ m)) ^ 2
      = 4 * ((2 : ℝ) ^ m) ^ 2 := by ring
    _ = 4 * 4 ^ m := by rw [h]

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

/-- Square-root form of the shell-level Bernstein bound. -/
theorem norm_lpProjector_succ_le (N : ℕ) (f : 𝕋² → ℂ) (x : 𝕋²) :
    ‖lpProjector (N + 1) f x‖ ≤
      (2 * 2 ^ (N + 1) : ℝ) *
        Real.sqrt (∑ k ∈ dyadicAnnulus (N + 1), ‖mFourierCoeff f k‖ ^ 2) := by
  have hnn : (0 : ℝ) ≤ ‖lpProjector (N + 1) f x‖ := norm_nonneg _
  have hC : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ (N + 1) := by positivity
  have hCsq : (0 : ℝ) ≤ (2 * (2 : ℝ) ^ (N + 1)) ^ 2 := sq_nonneg _
  calc ‖lpProjector (N + 1) f x‖
      = Real.sqrt (‖lpProjector (N + 1) f x‖ ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((4 * 4 ^ (N + 1) : ℝ) *
          ∑ k ∈ dyadicAnnulus (N + 1), ‖mFourierCoeff f k‖ ^ 2) :=
        Real.sqrt_le_sqrt (sq_norm_lpProjector_succ_le N f x)
    _ = Real.sqrt ((2 * (2 : ℝ) ^ (N + 1)) ^ 2 *
          ∑ k ∈ dyadicAnnulus (N + 1), ‖mFourierCoeff f k‖ ^ 2) := by
        rw [two_two_pow_sq_eq_four_four_pow]
    _ = 2 * (2 : ℝ) ^ (N + 1) *
          Real.sqrt (∑ k ∈ dyadicAnnulus (N + 1), ‖mFourierCoeff f k‖ ^ 2) := by
        rw [Real.sqrt_mul hCsq, Real.sqrt_sq hC]

/-- Under square-summability of the Fourier coefficients, the shell-level
squared-moduli sum is bounded by the total tsum. -/
theorem sum_shell_sq_mFourierCoeff_le_tsum (f : 𝕋² → ℂ) (N : ℕ)
    (hsum : Summable (fun k : Fin 2 → ℤ => ‖mFourierCoeff f k‖ ^ 2)) :
    ∑ k ∈ dyadicAnnulus N, ‖mFourierCoeff f k‖ ^ 2 ≤
      ∑' k : Fin 2 → ℤ, ‖mFourierCoeff f k‖ ^ 2 :=
  hsum.sum_le_tsum (dyadicAnnulus N) (fun _ _ => sq_nonneg _)

/-- Bernstein on the shell at level `N+1` in terms of the total tsum of
squared Fourier moduli.  Under square-summability, the tsum equals
`∫ ‖f‖²` by `hasSum_sq_mFourierCoeff`. -/
theorem sq_norm_lpProjector_succ_le_tsum (f : 𝕋² → ℂ) (N : ℕ) (x : 𝕋²)
    (hsum : Summable (fun k : Fin 2 → ℤ => ‖mFourierCoeff f k‖ ^ 2)) :
    ‖lpProjector (N + 1) f x‖ ^ 2 ≤
      (4 * 4 ^ (N + 1) : ℝ) *
        ∑' k : Fin 2 → ℤ, ‖mFourierCoeff f k‖ ^ 2 := by
  have hnn : (0 : ℝ) ≤ 4 * 4 ^ (N + 1) := by positivity
  calc ‖lpProjector (N + 1) f x‖ ^ 2
      ≤ (4 * 4 ^ (N + 1) : ℝ) *
          ∑ k ∈ dyadicAnnulus (N + 1), ‖mFourierCoeff f k‖ ^ 2 :=
        sq_norm_lpProjector_succ_le N f x
    _ ≤ (4 * 4 ^ (N + 1) : ℝ) *
          ∑' k : Fin 2 → ℤ, ‖mFourierCoeff f k‖ ^ 2 :=
        mul_le_mul_of_nonneg_left
          (sum_shell_sq_mFourierCoeff_le_tsum f (N + 1) hsum) hnn

/-- Square-root form of the tsum Bernstein: `‖Δ_{N+1} f x‖ ≤ 2·2^(N+1) · √(∑' ‖f̂‖²)`.
Combined with `hasSum_sq_mFourierCoeff` this reproduces the classical
`‖Δ_{N+1} f‖_{L∞} ≤ 2·2^(N+1) · ‖f‖_{L²}` for `f ∈ L²`. -/
theorem norm_lpProjector_succ_le_tsum (f : 𝕋² → ℂ) (N : ℕ) (x : 𝕋²)
    (hsum : Summable (fun k : Fin 2 → ℤ => ‖mFourierCoeff f k‖ ^ 2)) :
    ‖lpProjector (N + 1) f x‖ ≤
      (2 * 2 ^ (N + 1) : ℝ) *
        Real.sqrt (∑' k : Fin 2 → ℤ, ‖mFourierCoeff f k‖ ^ 2) := by
  have htsum_nn : (0 : ℝ) ≤ ∑' k : Fin 2 → ℤ, ‖mFourierCoeff f k‖ ^ 2 :=
    tsum_nonneg (fun _ => sq_nonneg _)
  have hshell_le : Real.sqrt (∑ k ∈ dyadicAnnulus (N + 1), ‖mFourierCoeff f k‖ ^ 2) ≤
      Real.sqrt (∑' k : Fin 2 → ℤ, ‖mFourierCoeff f k‖ ^ 2) :=
    Real.sqrt_le_sqrt (sum_shell_sq_mFourierCoeff_le_tsum f (N + 1) hsum)
  have hC : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ (N + 1) := by positivity
  calc ‖lpProjector (N + 1) f x‖
      ≤ (2 * 2 ^ (N + 1) : ℝ) *
          Real.sqrt (∑ k ∈ dyadicAnnulus (N + 1), ‖mFourierCoeff f k‖ ^ 2) :=
        norm_lpProjector_succ_le N f x
    _ ≤ (2 * 2 ^ (N + 1) : ℝ) *
          Real.sqrt (∑' k : Fin 2 → ℤ, ‖mFourierCoeff f k‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hshell_le hC

end FourierAnalysis
