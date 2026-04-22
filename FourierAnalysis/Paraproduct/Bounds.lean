/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under MIT license.
Authors: Bryan Sanchez

# Paraproduct bounds on `𝕋²`

Pointwise and dyadic estimates for the Bony paraproduct and remainder.
-/

import FourierAnalysis.Paraproduct.Defs

namespace FourierAnalysis

open UnitAddTorus

/-- Pointwise triangle bound on the paraproduct. -/
theorem norm_paraproductPartial_le (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    ‖paraproductPartial N f g x‖ ≤
      ∑ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
              (fun p => p.1 + 3 ≤ p.2),
        ‖lpProjector p.1 f x‖ * ‖lpProjector p.2 g x‖ := by
  rw [paraproductPartial_eq_sum_filter]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun p _ => ?_)
  rw [norm_mul]

/-- Pointwise triangle bound on the remainder. -/
theorem norm_remainderPartial_le (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    ‖remainderPartial N f g x‖ ≤
      ∑ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
              (fun p => Nat.dist p.1 p.2 ≤ 2),
        ‖lpProjector p.1 f x‖ * ‖lpProjector p.2 g x‖ := by
  unfold remainderPartial
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun p _ => ?_)
  rw [norm_mul]

end FourierAnalysis
