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



/-- The Ḣˢ seminorm of the zero function vanishes. -/
lemma hsSeminormSq_zero (s : ℝ) : hsSeminormSq s (0 : 𝕋² → ℂ) = 0 := by
  unfold hsSeminormSq
  simp [mFourierCoeff_zero_fn]

/-- The Ḣˢ seminorm-squared is homogeneous of degree 2 in scalar multiplication. -/
lemma hsSeminormSq_smul (s : ℝ) (c : ℂ) (f : 𝕋² → ℂ) :
    hsSeminormSq s (c • f) = ‖c‖ ^ 2 * hsSeminormSq s f := by
  unfold hsSeminormSq
  rw [← tsum_mul_left]
  congr 1
  funext k
  rw [mFourierCoeff_smul, norm_smul]
  ring

/-- The Ḣˢ seminorm-squared is invariant under negation. -/
@[simp] lemma hsSeminormSq_neg (s : ℝ) (f : 𝕋² → ℂ) :
    hsSeminormSq s (-f) = hsSeminormSq s f := by
  have h : (-f : 𝕋² → ℂ) = ((-1 : ℂ) • f) := by
    funext t; simp
  rw [h, hsSeminormSq_smul]
  simp

/-- Scalar bound on the Ḣˢ seminorm: if `‖c‖ ≤ 1`, then scalar multiplication
by `c` does not increase the seminorm. -/
lemma hsSeminormSq_smul_le (s : ℝ) (c : ℂ) (f : 𝕋² → ℂ) (hc : ‖c‖ ≤ 1) :
    hsSeminormSq s (c • f) ≤ hsSeminormSq s f := by
  rw [hsSeminormSq_smul]
  have hnn := hsSeminormSq_nonneg s f
  calc ‖c‖ ^ 2 * hsSeminormSq s f
      ≤ 1 ^ 2 * hsSeminormSq s f :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hc 2) hnn
    _ = hsSeminormSq s f := by ring

/-- `Real.rpow` form of the per-shell bound using the identity
`4^(N+1) · (2^N)^(-2s) · 4 = 16 · 2^(2N(1-s))` (expressed as rpow). -/
private lemma rpow_shell_simplify (N : ℕ) (s : ℝ) :
    (4 * 4 ^ (N + 1) : ℝ) * ((2 : ℝ) ^ N) ^ (-(2 * s)) =
      16 * (2 : ℝ) ^ (2 * (1 - s) * (N : ℝ)) := by
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h2_nn : (0 : ℝ) ≤ 2 := le_of_lt h2_pos
  have h1 : ((2 : ℝ) ^ N) ^ (-(2 * s)) = (2 : ℝ) ^ (-(2 * s) * (N : ℝ)) := by
    rw [show ((2 : ℝ) ^ N) = (2 : ℝ) ^ ((N : ℝ)) from (Real.rpow_natCast 2 N).symm,
        ← Real.rpow_mul h2_nn]
    ring_nf
  have h2 : (4 : ℝ) * 4 ^ (N + 1) = 16 * (2 : ℝ) ^ (2 * (N : ℝ)) := by
    rw [pow_succ]
    rw [show (4 : ℝ) ^ N = (2 : ℝ) ^ (2 * (N : ℝ)) by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num,
          show ((2:ℝ)^2)^N = ((2:ℝ)^(2*(N:ℝ))) from ?_]
      rw [← Real.rpow_natCast ((2 : ℝ)^2) N, ← Real.rpow_natCast 2 2,
          ← Real.rpow_mul h2_nn]
      push_cast; ring_nf]
    ring
  rw [h1, h2]
  rw [mul_assoc, mul_assoc, ← Real.rpow_add h2_pos]
  ring_nf

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

/-- Per-shell bound in geometric form: the shell at level `N+1` contributes
at most `16 · 2^(2N(1-s))` to the lattice zeta. -/
theorem sum_shell_rpow_neg_le_geometric (N : ℕ) (s : ℝ) (hs : 0 < s) :
    ∑ k ∈ dyadicAnnulus (N + 1), (lInfNorm k : ℝ) ^ (-(2 * s)) ≤
      16 * (2 : ℝ) ^ (2 * (1 - s) * (N : ℝ)) :=
  (sum_shell_rpow_neg_le N s hs).trans (le_of_eq (rpow_shell_simplify N s))

/-- For `s > 1`, the per-shell lattice-zeta contributions are summable
(bounded by a convergent geometric series with ratio `2^(2(1-s)) < 1`). -/
theorem summable_shell_rpow_neg (s : ℝ) (hs : 1 < s) :
    Summable (fun N : ℕ =>
      ∑ k ∈ dyadicAnnulus (N + 1), (lInfNorm k : ℝ) ^ (-(2 * s))) := by
  have hs_pos : 0 < s := by linarith
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h2_nn : (0 : ℝ) ≤ 2 := le_of_lt h2_pos
  have h2_one_lt : (1 : ℝ) < 2 := by norm_num
  have hr : (2 : ℝ) ^ (2 * (1 - s)) < 1 := by
    rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) from (Real.rpow_zero 2).symm]
    exact Real.rpow_lt_rpow_of_exponent_lt h2_one_lt (by linarith)
  have hr_pos : 0 < (2 : ℝ) ^ (2 * (1 - s)) := Real.rpow_pos_of_pos h2_pos _
  have hr_nn : 0 ≤ (2 : ℝ) ^ (2 * (1 - s)) := le_of_lt hr_pos
  have hpow_conv : ∀ N : ℕ,
      (2 : ℝ) ^ (2 * (1 - s) * (N : ℝ)) = ((2 : ℝ) ^ (2 * (1 - s))) ^ N := by
    intro N
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (2 * (1 - s))) N,
        ← Real.rpow_mul h2_nn]
  have hgeo : Summable (fun N : ℕ => 16 * (2 : ℝ) ^ (2 * (1 - s) * (N : ℝ))) := by
    simp_rw [hpow_conv]
    exact (summable_geometric_of_lt_one hr_nn hr).mul_left 16
  refine Summable.of_nonneg_of_le ?_ ?_ hgeo
  · intro N
    exact Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · intro N
    exact sum_shell_rpow_neg_le_geometric N s hs_pos

/-- Triangle form of Sobolev embedding: for continuous `f` with summable
Fourier coefficients, `‖f(x)‖ ≤ ∑' k, ‖f̂(k)‖`.  Combined with
`summable_shell_rpow_neg` for `s > 1` and Cauchy–Schwarz against the
lattice zeta, this gives the classical `‖f‖_{L∞} ≤ C_s · ‖f‖_{Ḣˢ}`. -/
theorem norm_apply_le_tsum_mFourierCoeff
    (f : C(𝕋², ℂ))
    (hsum : Summable (mFourierCoeff (d := Fin 2) f))
    (x : 𝕋²) :
    ‖f x‖ ≤ ∑' k : Fin 2 → ℤ, ‖mFourierCoeff f k‖ := by
  have hs : HasSum (fun k : Fin 2 → ℤ => mFourierCoeff f k • mFourier k x) (f x) :=
    hasSum_mFourier_series_apply_of_summable hsum x
  have hnorm_sum : Summable (fun k : Fin 2 → ℤ => ‖mFourierCoeff f k • mFourier k x‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hsum.norm
    intro k
    rw [norm_smul]
    have h1 : ‖(mFourier k : 𝕋² → ℂ) x‖ ≤ 1 :=
      calc ‖(mFourier k : 𝕋² → ℂ) x‖
          ≤ ‖mFourier (d := Fin 2) k‖ := (mFourier k).norm_coe_le_norm x
        _ = 1 := mFourier_norm
    calc ‖mFourierCoeff f k‖ * ‖(mFourier k : 𝕋² → ℂ) x‖
        ≤ ‖mFourierCoeff f k‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖mFourierCoeff f k‖ := by ring
  rw [← hs.tsum_eq]
  refine (norm_tsum_le_tsum_norm hnorm_sum).trans ?_
  refine Summable.tsum_le_tsum (fun k => ?_) hnorm_sum hsum.norm
  rw [norm_smul]
  have h1 : ‖(mFourier k : 𝕋² → ℂ) x‖ ≤ 1 :=
    calc ‖(mFourier k : 𝕋² → ℂ) x‖
        ≤ ‖mFourier (d := Fin 2) k‖ := (mFourier k).norm_coe_le_norm x
      _ = 1 := mFourier_norm
  calc ‖mFourierCoeff f k‖ * ‖(mFourier k : 𝕋² → ℂ) x‖
      ≤ ‖mFourierCoeff f k‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖mFourierCoeff f k‖ := by ring

/-- Convenience: given a bound `B` on the sum of Fourier-coefficient moduli,
the function is pointwise bounded by `B`. -/
theorem norm_apply_le_of_tsum_bound
    (f : C(𝕋², ℂ))
    (hsum : Summable (mFourierCoeff (d := Fin 2) f))
    {B : ℝ}
    (hB : ∑' k : Fin 2 → ℤ, ‖mFourierCoeff f k‖ ≤ B)
    (x : 𝕋²) :
    ‖f x‖ ≤ B :=
  (norm_apply_le_tsum_mFourierCoeff f hsum x).trans hB

end FourierAnalysis
