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

end FourierAnalysis
