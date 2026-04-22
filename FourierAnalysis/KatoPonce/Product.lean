/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under MIT license.
Authors: Bryan Sanchez

# Kato–Ponce product bound on `𝕋²`

The Kato–Ponce fractional Leibniz inequality
`‖Jˢ(fg)‖_{L²} ≤ C·(‖f‖_{L∞}·‖g‖_{Ḣˢ} + ‖g‖_{L∞}·‖f‖_{Ḣˢ})` is proved
by decomposing `fg` via Bony (see `FourierAnalysis.Paraproduct.Defs`)
and bounding each piece via Bernstein + Parseval.

This file collects the partial-level triangle steps; the L² bounds
themselves live in `FourierAnalysis.Paraproduct.Bounds`.
-/

import FourierAnalysis.Paraproduct.Bounds

namespace FourierAnalysis

open UnitAddTorus

/-- Pointwise triangle bound on the product of partial sums via Bony. -/
theorem norm_lpPartialSum_product_le_bony (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    ‖lpPartialSum N f x * lpPartialSum N g x‖ ≤
      ‖paraproductPartial N f g x‖ +
        ‖paraproductPartial N g f x‖ +
        ‖remainderPartial N f g x‖ := by
  rw [bony_partial]
  exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

/-- Squared-norm Cauchy–Schwarz form: the squared product norm is bounded by
three times the sum of squared piece norms. -/
theorem sq_norm_lpPartialSum_product_le (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    ‖lpPartialSum N f x * lpPartialSum N g x‖ ^ 2 ≤
      3 * (‖paraproductPartial N f g x‖ ^ 2 +
            ‖paraproductPartial N g f x‖ ^ 2 +
            ‖remainderPartial N f g x‖ ^ 2) := by
  have hle := norm_lpPartialSum_product_le_bony N f g x
  have hnn : (0 : ℝ) ≤ ‖lpPartialSum N f x * lpPartialSum N g x‖ := norm_nonneg _
  have hcs : (‖paraproductPartial N f g x‖ + ‖paraproductPartial N g f x‖ +
              ‖remainderPartial N f g x‖) ^ 2 ≤
      3 * (‖paraproductPartial N f g x‖ ^ 2 +
            ‖paraproductPartial N g f x‖ ^ 2 +
            ‖remainderPartial N f g x‖ ^ 2) := by
    nlinarith [sq_nonneg (‖paraproductPartial N f g x‖ - ‖paraproductPartial N g f x‖),
               sq_nonneg (‖paraproductPartial N f g x‖ - ‖remainderPartial N f g x‖),
               sq_nonneg (‖paraproductPartial N g f x‖ - ‖remainderPartial N f g x‖)]
  exact (pow_le_pow_left₀ hnn hle 2).trans hcs

/-- Structural Kato–Ponce wrapper: given pointwise bounds on each Bony piece,
the product of partial sums is bounded by their sum.  Downstream consumers
discharge `B1, B2, B3` via Bernstein + paraproduct estimates. -/
theorem norm_lpPartialSum_product_le_of_bony_bounds
    (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²)
    {B1 B2 B3 : ℝ}
    (hB1 : ‖paraproductPartial N f g x‖ ≤ B1)
    (hB2 : ‖paraproductPartial N g f x‖ ≤ B2)
    (hB3 : ‖remainderPartial N f g x‖ ≤ B3) :
    ‖lpPartialSum N f x * lpPartialSum N g x‖ ≤ B1 + B2 + B3 := by
  refine (norm_lpPartialSum_product_le_bony _ _ _ _).trans ?_
  linarith

/-- Squared version of the structural Kato–Ponce bound, chaining into the
Cauchy–Schwarz form. -/
theorem sq_norm_lpPartialSum_product_le_of_sq_bony_bounds
    (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²)
    {B1 B2 B3 : ℝ}
    (hB1 : ‖paraproductPartial N f g x‖ ^ 2 ≤ B1)
    (hB2 : ‖paraproductPartial N g f x‖ ^ 2 ≤ B2)
    (hB3 : ‖remainderPartial N f g x‖ ^ 2 ≤ B3) :
    ‖lpPartialSum N f x * lpPartialSum N g x‖ ^ 2 ≤ 3 * (B1 + B2 + B3) := by
  refine (sq_norm_lpPartialSum_product_le _ _ _ _).trans ?_
  have : (0 : ℝ) ≤ (3 : ℝ) := by norm_num
  nlinarith

end FourierAnalysis
