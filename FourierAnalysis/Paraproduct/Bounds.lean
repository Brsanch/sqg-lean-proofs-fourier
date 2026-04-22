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

/-- Direct triangle bound on the paraproduct in its original ordered form
(sum over `M` with coefficient `‖S_{M-3} f‖ · ‖Δ_M g‖`). -/
theorem norm_paraproductPartial_direct_le (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    ‖paraproductPartial N f g x‖ ≤
      ∑ M ∈ Finset.Ico 3 (N + 1),
        ‖lpPartialSum (M - 3) f x‖ * ‖lpProjector M g x‖ := by
  unfold paraproductPartial
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun M _ => ?_)
  rw [norm_mul]

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

/-- Cauchy–Schwarz form on the paraproduct: the squared pointwise value is
controlled by the shell-pair count times the sum of squared shell-product
moduli. -/
theorem sq_norm_paraproductPartial_le (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    ‖paraproductPartial N f g x‖ ^ 2 ≤
      ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
          (fun p => p.1 + 3 ≤ p.2)).card *
        ∑ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
                (fun p => p.1 + 3 ≤ p.2),
          (‖lpProjector p.1 f x‖ * ‖lpProjector p.2 g x‖) ^ 2 := by
  have h1 := norm_paraproductPartial_le N f g x
  have h2 : (0 : ℝ) ≤ ‖paraproductPartial N f g x‖ := norm_nonneg _
  calc ‖paraproductPartial N f g x‖ ^ 2
      ≤ (∑ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
                (fun p => p.1 + 3 ≤ p.2),
          ‖lpProjector p.1 f x‖ * ‖lpProjector p.2 g x‖) ^ 2 :=
        pow_le_pow_left₀ h2 h1 2
    _ ≤ _ := sq_sum_le_card_mul_sum_sq

/-- The paraproduct filter is a subset of `range(N+1)²`, hence bounded by `(N+1)²`. -/
lemma card_paraproduct_filter_le (N : ℕ) :
    ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
        (fun p => p.1 + 3 ≤ p.2)).card ≤ (N + 1) ^ 2 := by
  refine (Finset.card_le_card (Finset.filter_subset _ _)).trans ?_
  rw [Finset.card_product, Finset.card_range]
  exact le_of_eq (by ring)

/-- The remainder filter is a subset of `range(N+1)²`, hence bounded by `(N+1)²`. -/
lemma card_remainder_filter_le (N : ℕ) :
    ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
        (fun p => Nat.dist p.1 p.2 ≤ 2)).card ≤ (N + 1) ^ 2 := by
  refine (Finset.card_le_card (Finset.filter_subset _ _)).trans ?_
  rw [Finset.card_product, Finset.card_range]
  exact le_of_eq (by ring)

/-- Cauchy–Schwarz form on the remainder. -/
theorem sq_norm_remainderPartial_le (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    ‖remainderPartial N f g x‖ ^ 2 ≤
      ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
          (fun p => Nat.dist p.1 p.2 ≤ 2)).card *
        ∑ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
                (fun p => Nat.dist p.1 p.2 ≤ 2),
          (‖lpProjector p.1 f x‖ * ‖lpProjector p.2 g x‖) ^ 2 := by
  have h1 := norm_remainderPartial_le N f g x
  have h2 : (0 : ℝ) ≤ ‖remainderPartial N f g x‖ := norm_nonneg _
  calc ‖remainderPartial N f g x‖ ^ 2
      ≤ (∑ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
                (fun p => Nat.dist p.1 p.2 ≤ 2),
          ‖lpProjector p.1 f x‖ * ‖lpProjector p.2 g x‖) ^ 2 :=
        pow_le_pow_left₀ h2 h1 2
    _ ≤ _ := sq_sum_le_card_mul_sum_sq

/-- Loose bound on the paraproduct: combines the card bound `≤ (N+1)²` with the
Cauchy–Schwarz form. -/
theorem sq_norm_paraproductPartial_loose_le (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    ‖paraproductPartial N f g x‖ ^ 2 ≤
      ((N + 1) ^ 2 : ℕ) *
        ∑ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
                (fun p => p.1 + 3 ≤ p.2),
          (‖lpProjector p.1 f x‖ * ‖lpProjector p.2 g x‖) ^ 2 := by
  refine (sq_norm_paraproductPartial_le N f g x).trans ?_
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast card_paraproduct_filter_le N
  · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Loose bound on the remainder: analogous to `sq_norm_paraproductPartial_loose_le`. -/
theorem sq_norm_remainderPartial_loose_le (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    ‖remainderPartial N f g x‖ ^ 2 ≤
      ((N + 1) ^ 2 : ℕ) *
        ∑ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
                (fun p => Nat.dist p.1 p.2 ≤ 2),
          (‖lpProjector p.1 f x‖ * ‖lpProjector p.2 g x‖) ^ 2 := by
  refine (sq_norm_remainderPartial_le N f g x).trans ?_
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast card_remainder_filter_le N
  · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

end FourierAnalysis
