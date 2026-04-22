/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under MIT license.
Authors: Bryan Sanchez

# Paraproduct bounds on `𝕋²`

Pointwise and dyadic estimates for the Bony paraproduct and remainder.
-/

import FourierAnalysis.Paraproduct.Defs
import FourierAnalysis.LittlewoodPaley.Bernstein

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

/-- If both factor sequences are zero on all shells, the paraproduct vanishes. -/
lemma paraproductPartial_eq_zero_of_lpProjector_zero
    (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²)
    (hf : ∀ j, j ≤ N → lpProjector j f x = 0) :
    paraproductPartial N f g x = 0 := by
  unfold paraproductPartial
  refine Finset.sum_eq_zero (fun M hM => ?_)
  rw [Finset.mem_Ico] at hM
  have : lpPartialSum (M - 3) f x = 0 := by
    unfold lpPartialSum
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    exact hf j (by omega)
  rw [this, zero_mul]

/-- If `g`'s dyadic projections vanish up to level `N`, the remainder vanishes. -/
lemma remainderPartial_eq_zero_of_lpProjector_zero_right
    (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²)
    (hg : ∀ j, j ≤ N → lpProjector j g x = 0) :
    remainderPartial N f g x = 0 := by
  unfold remainderPartial
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
  obtain ⟨⟨_, hp2⟩, _⟩ := hp
  rw [hg p.2 (by omega)]
  ring

/-! ### Parseval-style pointwise bounds via Bernstein

The following lemmas control pointwise-squared values by Fourier-side
sums of squared moduli, using the Bernstein-type bound
`sq_norm_lpProjector_succ_le`.  They are the finite-level substitutes
for the classical `∫ ‖S_N f‖² ≤ ∑ ‖f̂‖²` identity: the pointwise
squared bound follows the same Cauchy–Schwarz structure, aggregated
shell-by-shell. -/

/-- Shell-indexed Bernstein: squared pointwise bound on `lpPartialSum N f x`
in terms of the sum of per-shell cardinalities times per-shell squared
Fourier moduli.  Aggregates `sq_norm_lpProjector_le` across all shells. -/
theorem sq_norm_lpPartialSum_shell_le (N : ℕ) (f : 𝕋² → ℂ) (x : 𝕋²) :
    ‖lpPartialSum N f x‖ ^ 2 ≤
      (N + 1 : ℕ) *
        ∑ j ∈ Finset.range (N + 1),
          (dyadicAnnulus j).card *
            ∑ k ∈ dyadicAnnulus j, ‖mFourierCoeff f k‖ ^ 2 := by
  refine (sq_norm_lpPartialSum_le N f x).trans ?_
  apply mul_le_mul_of_nonneg_left
  · refine Finset.sum_le_sum (fun j _ => ?_)
    exact sq_norm_lpProjector_le j f x
  · exact_mod_cast Nat.zero_le _

/-- AM–GM / Cauchy–Schwarz pointwise bound on a product of projector norms:
`(‖Δ_a f x‖ · ‖Δ_b g x‖)² ≤ card(shell a) · card(shell b) · (∑_{shell a} ‖f̂‖²) · (∑_{shell b} ‖ĝ‖²)`.
Product form of `sq_norm_lpProjector_le` on two independent shells. -/
lemma sq_lpProjector_mul_lpProjector_le (a b : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    (‖lpProjector a f x‖ * ‖lpProjector b g x‖) ^ 2 ≤
      ((dyadicAnnulus a).card * (dyadicAnnulus b).card : ℕ) *
        ((∑ k ∈ dyadicAnnulus a, ‖mFourierCoeff f k‖ ^ 2) *
          ∑ m ∈ dyadicAnnulus b, ‖mFourierCoeff g m‖ ^ 2) := by
  have ha := sq_norm_lpProjector_le a f x
  have hb := sq_norm_lpProjector_le b g x
  have hna : (0 : ℝ) ≤ ‖lpProjector a f x‖ := norm_nonneg _
  have hnb : (0 : ℝ) ≤ ‖lpProjector b g x‖ := norm_nonneg _
  have hna2 : (0 : ℝ) ≤ ‖lpProjector a f x‖ ^ 2 := sq_nonneg _
  have hsumA : (0 : ℝ) ≤
      (dyadicAnnulus a).card * ∑ k ∈ dyadicAnnulus a, ‖mFourierCoeff f k‖ ^ 2 := by
    have h1 : (0 : ℝ) ≤ ((dyadicAnnulus a).card : ℝ) := by exact_mod_cast Nat.zero_le _
    have h2 : (0 : ℝ) ≤ ∑ k ∈ dyadicAnnulus a, ‖mFourierCoeff f k‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    exact mul_nonneg h1 h2
  calc (‖lpProjector a f x‖ * ‖lpProjector b g x‖) ^ 2
      = ‖lpProjector a f x‖ ^ 2 * ‖lpProjector b g x‖ ^ 2 := by ring
    _ ≤ ((dyadicAnnulus a).card *
            ∑ k ∈ dyadicAnnulus a, ‖mFourierCoeff f k‖ ^ 2) *
          ‖lpProjector b g x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right ha (sq_nonneg _)
    _ ≤ ((dyadicAnnulus a).card *
            ∑ k ∈ dyadicAnnulus a, ‖mFourierCoeff f k‖ ^ 2) *
          ((dyadicAnnulus b).card *
            ∑ m ∈ dyadicAnnulus b, ‖mFourierCoeff g m‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hb hsumA
    _ = ((dyadicAnnulus a).card * (dyadicAnnulus b).card : ℕ) *
          ((∑ k ∈ dyadicAnnulus a, ‖mFourierCoeff f k‖ ^ 2) *
            ∑ m ∈ dyadicAnnulus b, ‖mFourierCoeff g m‖ ^ 2) := by
        push_cast; ring

/-- **L² paraproduct bound (Parseval form).**  The squared pointwise value of
the paraproduct is controlled by a filtered sum over shell pairs `(a, b)`
with `a + 3 ≤ b`, with per-pair Bernstein weights `card(shell_a) · card(shell_b)`
and per-shell squared-Fourier moduli products.  Combines
`sq_norm_paraproductPartial_loose_le` with
`sq_lpProjector_mul_lpProjector_le`. -/
theorem sq_norm_paraproductPartial_le_l2 (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    ‖paraproductPartial N f g x‖ ^ 2 ≤
      ((N + 1) ^ 2 : ℕ) *
        ∑ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
                (fun p => p.1 + 3 ≤ p.2),
          ((dyadicAnnulus p.1).card * (dyadicAnnulus p.2).card : ℕ) *
            ((∑ k ∈ dyadicAnnulus p.1, ‖mFourierCoeff f k‖ ^ 2) *
              ∑ m ∈ dyadicAnnulus p.2, ‖mFourierCoeff g m‖ ^ 2) := by
  refine (sq_norm_paraproductPartial_loose_le N f g x).trans ?_
  apply mul_le_mul_of_nonneg_left
  · refine Finset.sum_le_sum (fun p _ => ?_)
    exact sq_lpProjector_mul_lpProjector_le p.1 p.2 f g x
  · exact_mod_cast Nat.zero_le _

/-- **L² remainder bound (Parseval form).**  The squared pointwise value of
the remainder is controlled by a filtered sum over shell pairs `(a, b)`
with `Nat.dist a b ≤ 2`, with per-pair Bernstein weights. -/
theorem sq_norm_remainderPartial_le_l2 (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    ‖remainderPartial N f g x‖ ^ 2 ≤
      ((N + 1) ^ 2 : ℕ) *
        ∑ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
                (fun p => Nat.dist p.1 p.2 ≤ 2),
          ((dyadicAnnulus p.1).card * (dyadicAnnulus p.2).card : ℕ) *
            ((∑ k ∈ dyadicAnnulus p.1, ‖mFourierCoeff f k‖ ^ 2) *
              ∑ m ∈ dyadicAnnulus p.2, ‖mFourierCoeff g m‖ ^ 2) := by
  refine (sq_norm_remainderPartial_loose_le N f g x).trans ?_
  apply mul_le_mul_of_nonneg_left
  · refine Finset.sum_le_sum (fun p _ => ?_)
    exact sq_lpProjector_mul_lpProjector_le p.1 p.2 f g x
  · exact_mod_cast Nat.zero_le _

end FourierAnalysis
