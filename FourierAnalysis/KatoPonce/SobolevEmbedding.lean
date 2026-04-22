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

/-- Lattice zeta constant: `∑' k ≠ 0, |k|_∞^{-2s}`.  Converges for `s > 1`
(dimension 2).  This is the dual quantity controlling the Cauchy–Schwarz
bound in the Sobolev embedding. -/
noncomputable def latticeZetaSq (s : ℝ) : ℝ :=
  ∑' k : Fin 2 → ℤ, if k = 0 then 0 else (lInfNorm k : ℝ) ^ (-(2 * s))

lemma latticeZetaSq_nonneg (s : ℝ) : 0 ≤ latticeZetaSq s := by
  unfold latticeZetaSq
  refine tsum_nonneg (fun k => ?_)
  split_ifs with hk
  · exact le_refl _
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- The 2D Fourier coefficient of the zero function vanishes at every mode. -/
lemma mFourierCoeff_zero_fn (k : Fin 2 → ℤ) :
    mFourierCoeff (0 : 𝕋² → ℂ) k = 0 := by
  unfold mFourierCoeff
  simp

/-- The Ḣˢ seminorm of the zero function vanishes. -/
lemma hsSeminormSq_zero (s : ℝ) : hsSeminormSq s (0 : 𝕋² → ℂ) = 0 := by
  unfold hsSeminormSq
  simp [mFourierCoeff_zero_fn]

/-- Per-shell lattice zeta contribution: the sum of `|k|^{-2s}` over the
dyadic shell at level `N+1` is at most `4 · 4^(N+1) · 2^(-2s·N)`, using
the cardinality bound and the ℓ∞ lower bound `|k|_∞ ≥ 2^N` on the shell. -/
lemma sum_shell_rpow_neg_le (N : ℕ) (s : ℝ) (hs : 0 < s) :
    ∑ k ∈ dyadicAnnulus (N + 1), (lInfNorm k : ℝ) ^ (-(2 * s)) ≤
      (4 * 4 ^ (N + 1) : ℝ) * (2 ^ N : ℝ) ^ (-(2 * s)) := by
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  -- Each term is bounded by the same maximum: `(2^N)^(-2s)` since
  -- `|k|_∞ ≥ 2^N` on the shell and `(·)^(-2s)` is decreasing for `s > 0`.
  have hbound : ∀ k ∈ dyadicAnnulus (N + 1),
      (lInfNorm k : ℝ) ^ (-(2 * s)) ≤ ((2 : ℝ) ^ N) ^ (-(2 * s)) := by
    intro k hk
    rw [mem_dyadicAnnulus_succ] at hk
    have hlo : ((2 : ℝ) ^ N) ≤ (lInfNorm k : ℝ) := by
      have : (2 ^ N : ℕ) ≤ lInfNorm k := hk.1
      exact_mod_cast this
    have hk_pos : (0 : ℝ) < (lInfNorm k : ℝ) := lt_of_lt_of_le hpow_pos hlo
    have h2s_neg : -(2 * s) ≤ 0 := by linarith
    -- Monotonicity: for nonneg base, `x ↦ x^(-2s)` is decreasing.
    exact Real.rpow_le_rpow_of_nonpos hpow_pos hlo h2s_neg
  calc ∑ k ∈ dyadicAnnulus (N + 1), (lInfNorm k : ℝ) ^ (-(2 * s))
      ≤ ∑ k ∈ dyadicAnnulus (N + 1), ((2 : ℝ) ^ N) ^ (-(2 * s)) :=
        Finset.sum_le_sum hbound
    _ = (dyadicAnnulus (N + 1)).card * ((2 : ℝ) ^ N) ^ (-(2 * s)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * 4 ^ (N + 1) : ℝ) * ((2 : ℝ) ^ N) ^ (-(2 * s)) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast card_dyadicAnnulus_succ_le_four_pow N
        · exact Real.rpow_nonneg (le_of_lt hpow_pos) _

end FourierAnalysis
