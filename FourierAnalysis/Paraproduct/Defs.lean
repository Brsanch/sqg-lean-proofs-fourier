/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under MIT license.
Authors: Bryan Sanchez

# Bony paraproduct on `𝕋²`

Definitions of the low-times-high paraproduct `T_f g` and the
symmetric remainder `R(f, g)`.  Bony's decomposition `f·g = T_f g +
T_g f + R(f, g)` is the basis of the Kato–Ponce commutator estimate.
-/

import FourierAnalysis.LittlewoodPaley.Dyadic

namespace FourierAnalysis

open UnitAddTorus

/-- Finite Bony paraproduct `T^{≤N}_f g` truncated at frequency level `N`:
`∑_{3 ≤ M ≤ N} S_{M-3}(f) · Δ_M(g)` where `S_K = lpPartialSum K` and
`Δ_M = lpProjector M`. -/
noncomputable def paraproductPartial (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) : ℂ :=
  ∑ M ∈ Finset.Ico 3 (N + 1), lpPartialSum (M - 3) f x * lpProjector M g x

/-- Finite symmetric remainder `R^{≤N}(f, g)`: the double sum of
`Δ_M(f)·Δ_{M'}(g)` over `(M, M') ∈ [0, N]²` with `|M - M'| ≤ 2`. -/
noncomputable def remainderPartial (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) : ℂ :=
  ∑ p ∈ ((Finset.range (N + 1)).product (Finset.range (N + 1))).filter
          (fun p => Nat.dist p.1 p.2 ≤ 2),
    lpProjector p.1 f x * lpProjector p.2 g x

/-- The paraproduct is zero when truncated below level 3 (empty index set). -/
lemma paraproductPartial_of_lt_three {N : ℕ} (hN : N < 3) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    paraproductPartial N f g x = 0 := by
  unfold paraproductPartial
  rw [Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty]

/-- Recursive step: the paraproduct at level `N+1` adds the `(N+1)`-th dyadic term. -/
lemma paraproductPartial_succ {N : ℕ} (hN : 3 ≤ N + 1) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    paraproductPartial (N + 1) f g x =
      paraproductPartial N f g x +
        lpPartialSum (N + 1 - 3) f x * lpProjector (N + 1) g x := by
  unfold paraproductPartial
  rw [show Finset.Ico 3 (N + 1 + 1) = insert (N + 1) (Finset.Ico 3 (N + 1)) from ?_,
      Finset.sum_insert (by simp)]
  · ring
  · ext x; simp [Finset.mem_Ico, Finset.mem_insert]; omega

/-- The product of two dyadic partial sums factorises as a double sum of projector
products.  This is the entry point to Bony's decomposition `f·g = T_f g + T_g f + R`. -/
lemma lpPartialSum_mul_lpPartialSum (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    lpPartialSum N f x * lpPartialSum N g x =
      ∑ M ∈ Finset.range (N + 1), ∑ M' ∈ Finset.range (N + 1),
        lpProjector M f x * lpProjector M' g x := by
  unfold lpPartialSum
  exact Finset.sum_mul_sum _ _ _ _

/-- The paraproduct written as a restricted double sum over the "low × high"
index set `{(j, M) : 0 ≤ j ≤ M - 3, 3 ≤ M ≤ N}`. -/
lemma paraproductPartial_eq_double_sum (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    paraproductPartial N f g x =
      ∑ M ∈ Finset.Ico 3 (N + 1), ∑ j ∈ Finset.range (M - 2),
        lpProjector j f x * lpProjector M g x := by
  unfold paraproductPartial lpPartialSum
  refine Finset.sum_congr rfl (fun M hM => ?_)
  rw [Finset.sum_mul]
  rw [show M - 3 + 1 = M - 2 by
        rw [Finset.mem_Ico] at hM; omega]

/-- The paraproduct as a filtered sum over `range(N+1) × range(N+1)`, with
filter predicate `p.1 + 3 ≤ p.2` (the "low × high" index set). -/
lemma paraproductPartial_eq_sum_filter (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    paraproductPartial N f g x =
      ∑ p ∈ ((Finset.range (N + 1)).product (Finset.range (N + 1))).filter
              (fun p => p.1 + 3 ≤ p.2),
        lpProjector p.1 f x * lpProjector p.2 g x := by
  rw [paraproductPartial_eq_double_sum, Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun y => (y.2, y.1))
    (fun q => ⟨q.2, q.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_sigma, Finset.mem_Ico, Finset.mem_range] at hy
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
    simp only [Finset.mem_sigma, Finset.mem_Ico, Finset.mem_range]
    omega
  · intro _ _; rfl
  · intro _ _; rfl
  · intro _ _; rfl

end FourierAnalysis
