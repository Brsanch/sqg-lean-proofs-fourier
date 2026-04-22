/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under MIT license.
Authors: Bryan Sanchez

# Kato–Ponce commutator estimate on `𝕋²`

The partial commutator `[S_N, M_f] g = S_N(fg) - f · S_N(g)` measures
the failure of `S_N` to commute with pointwise multiplication by `f`.

This file collects pointwise identities at the partial (truncated)
level.  The full commutator estimate
`‖[Jˢ, f·∇]g‖_{L²} ≤ C·(‖∇f‖_{L∞}·‖g‖_{Ḣˢ} + ‖f‖_{Ḣˢ}·‖∇g‖_{L∞})`
in the limit `N → ∞` uses the Bony decomposition from
`FourierAnalysis.Paraproduct.Defs` and the Bernstein bounds from
`FourierAnalysis.LittlewoodPaley.Bernstein`.
-/

import FourierAnalysis.Paraproduct.Bounds
import FourierAnalysis.KatoPonce.Product
import FourierAnalysis.LittlewoodPaley.Bernstein

namespace FourierAnalysis

open UnitAddTorus

/-- Partial commutator at level `N`: `[S_N, M_f] g x := S_N(f·g) x - f x · S_N(g) x`. -/
noncomputable def partialCommutator (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) : ℂ :=
  lpPartialSum N (fun t => f t * g t) x - f x * lpPartialSum N g x

/-- Triangle bound on the partial commutator. -/
theorem norm_partialCommutator_le (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    ‖partialCommutator N f g x‖ ≤
      ‖lpPartialSum N (fun t => f t * g t) x‖ + ‖f x * lpPartialSum N g x‖ := by
  unfold partialCommutator
  exact norm_sub_le _ _

/-- If `g` is the zero function, the partial commutator vanishes pointwise. -/
@[simp] lemma partialCommutator_zero_right (N : ℕ) (f : 𝕋² → ℂ) (x : 𝕋²) :
    partialCommutator N f (0 : 𝕋² → ℂ) x = 0 := by
  unfold partialCommutator
  have h1 : (fun t : 𝕋² => f t * (0 : 𝕋² → ℂ) t) = 0 := by funext t; simp
  rw [h1]
  simp

/-- If `f` is the zero function, the partial commutator vanishes pointwise. -/
@[simp] lemma partialCommutator_zero_left (N : ℕ) (g : 𝕋² → ℂ) (x : 𝕋²) :
    partialCommutator N (0 : 𝕋² → ℂ) g x = 0 := by
  unfold partialCommutator
  have h1 : (fun t : 𝕋² => (0 : 𝕋² → ℂ) t * g t) = 0 := by funext t; simp
  rw [h1]
  simp

/-- Structural Kato–Ponce commutator bound: given pointwise bounds on
`S_N(f·g)` and on `f · S_N(g)`, the partial commutator is bounded by
their sum.  Downstream use: combine Bony-based bounds on `S_N(f·g)`
with direct bounds on `f · S_N(g)` from Bernstein. -/
theorem norm_partialCommutator_le_of_bounds
    (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²)
    {A B : ℝ}
    (hA : ‖lpPartialSum N (fun t => f t * g t) x‖ ≤ A)
    (hB : ‖f x * lpPartialSum N g x‖ ≤ B) :
    ‖partialCommutator N f g x‖ ≤ A + B :=
  (norm_partialCommutator_le N f g x).trans (add_le_add hA hB)

/-- Scalar linearity of the partial commutator in the left argument. -/
lemma partialCommutator_smul_left (N : ℕ) (c : ℂ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    partialCommutator N (c • f) g x = c • partialCommutator N f g x := by
  unfold partialCommutator
  have h1 : (fun t : 𝕋² => (c • f) t * g t) = c • (fun t : 𝕋² => f t * g t) := by
    funext t; simp [Pi.smul_apply, smul_eq_mul]; ring
  rw [h1, lpPartialSum_smul]
  simp [Pi.smul_apply, smul_eq_mul, mul_sub]
  ring

/-- Scalar linearity of the partial commutator in the right argument. -/
lemma partialCommutator_smul_right (N : ℕ) (f : 𝕋² → ℂ) (c : ℂ) (g : 𝕋² → ℂ) (x : 𝕋²) :
    partialCommutator N f (c • g) x = c • partialCommutator N f g x := by
  unfold partialCommutator
  have h1 : (fun t : 𝕋² => f t * (c • g) t) = c • (fun t : 𝕋² => f t * g t) := by
    funext t; simp [Pi.smul_apply, smul_eq_mul]; ring
  rw [h1]
  simp_rw [lpPartialSum_smul]
  simp [smul_eq_mul, mul_sub]
  ring

/-- Antisymmetry identity: the swapped commutator difference equals
`g(x)·S_N(f)(x) - f(x)·S_N(g)(x)`.  This is the source of the
commutator cancellation in Kato–Ponce. -/
lemma partialCommutator_sub_swap (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    partialCommutator N f g x - partialCommutator N g f x =
      g x * lpPartialSum N f x - f x * lpPartialSum N g x := by
  unfold partialCommutator
  have h : (fun t : 𝕋² => g t * f t) = (fun t => f t * g t) := by
    funext t; ring
  rw [h]
  ring

/-- Projector-level triangle bound on the partial commutator. -/
theorem norm_partialCommutator_via_projectors (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    ‖partialCommutator N f g x‖ ≤
      (∑ j ∈ Finset.range (N + 1),
          ‖lpProjector j (fun t => f t * g t) x‖) +
        ‖f x‖ * (∑ j ∈ Finset.range (N + 1), ‖lpProjector j g x‖) := by
  refine (norm_partialCommutator_le N f g x).trans ?_
  refine add_le_add (norm_lpPartialSum_le _ _ _) ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_lpPartialSum_le _ _ _) (norm_nonneg _)

/-- **Bony expansion of the partial commutator.**  Decomposes
`partialCommutator N f g x = S_N(f·g)(x) - f(x) · S_N(g)(x)` as

`partialCommutator N f g x =
  [S_N(f·g)(x) - S_N(f)(x) · S_N(g)(x)]
    - paraproductPartial N f g x
    - paraproductPartial N g f x
    - remainderPartial N f g x
    + (S_N(f)(x) - f x) · S_N(g)(x)`

using Bony's partial identity `bony_partial` on the `S_N(f) · S_N(g)`
intermediate.  The lead bracket `S_N(f·g) - S_N(f)·S_N(g)` encodes the
high-frequency correction vanishing in the `N → ∞` limit. -/
theorem partialCommutator_eq_bony_expansion (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    partialCommutator N f g x =
      (lpPartialSum N (fun t => f t * g t) x -
          lpPartialSum N f x * lpPartialSum N g x)
        - paraproductPartial N f g x
        - paraproductPartial N g f x
        - remainderPartial N f g x
        + (lpPartialSum N f x - f x) * lpPartialSum N g x := by
  unfold partialCommutator
  have hbony := bony_partial N f g x
  linear_combination -hbony

/-- Triangle bound on the partial commutator via the Bony expansion. -/
theorem norm_partialCommutator_le_bony (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    ‖partialCommutator N f g x‖ ≤
      ‖lpPartialSum N (fun t => f t * g t) x -
          lpPartialSum N f x * lpPartialSum N g x‖
        + ‖paraproductPartial N f g x‖
        + ‖paraproductPartial N g f x‖
        + ‖remainderPartial N f g x‖
        + ‖(lpPartialSum N f x - f x) * lpPartialSum N g x‖ := by
  rw [partialCommutator_eq_bony_expansion]
  have h1 : ‖(lpPartialSum N (fun t => f t * g t) x -
                lpPartialSum N f x * lpPartialSum N g x) -
              paraproductPartial N f g x -
              paraproductPartial N g f x -
              remainderPartial N f g x +
              (lpPartialSum N f x - f x) * lpPartialSum N g x‖ ≤
      ‖(lpPartialSum N (fun t => f t * g t) x -
            lpPartialSum N f x * lpPartialSum N g x) -
          paraproductPartial N f g x -
          paraproductPartial N g f x -
          remainderPartial N f g x‖ +
        ‖(lpPartialSum N f x - f x) * lpPartialSum N g x‖ :=
    norm_add_le _ _
  have h2 : ‖(lpPartialSum N (fun t => f t * g t) x -
                lpPartialSum N f x * lpPartialSum N g x) -
              paraproductPartial N f g x -
              paraproductPartial N g f x -
              remainderPartial N f g x‖ ≤
      ‖(lpPartialSum N (fun t => f t * g t) x -
            lpPartialSum N f x * lpPartialSum N g x) -
          paraproductPartial N f g x -
          paraproductPartial N g f x‖ +
        ‖remainderPartial N f g x‖ := by
    simpa [sub_eq_add_neg, norm_neg] using
      (norm_sub_le
        ((lpPartialSum N (fun t => f t * g t) x -
            lpPartialSum N f x * lpPartialSum N g x) -
          paraproductPartial N f g x -
          paraproductPartial N g f x) (remainderPartial N f g x))
  have h3 : ‖(lpPartialSum N (fun t => f t * g t) x -
                lpPartialSum N f x * lpPartialSum N g x) -
              paraproductPartial N f g x -
              paraproductPartial N g f x‖ ≤
      ‖(lpPartialSum N (fun t => f t * g t) x -
            lpPartialSum N f x * lpPartialSum N g x) -
          paraproductPartial N f g x‖ +
        ‖paraproductPartial N g f x‖ := by
    simpa [sub_eq_add_neg, norm_neg] using
      (norm_sub_le
        ((lpPartialSum N (fun t => f t * g t) x -
            lpPartialSum N f x * lpPartialSum N g x) -
          paraproductPartial N f g x) (paraproductPartial N g f x))
  have h4 : ‖(lpPartialSum N (fun t => f t * g t) x -
                lpPartialSum N f x * lpPartialSum N g x) -
              paraproductPartial N f g x‖ ≤
      ‖lpPartialSum N (fun t => f t * g t) x -
            lpPartialSum N f x * lpPartialSum N g x‖ +
        ‖paraproductPartial N f g x‖ := by
    simpa [sub_eq_add_neg, norm_neg] using
      (norm_sub_le
        (lpPartialSum N (fun t => f t * g t) x -
            lpPartialSum N f x * lpPartialSum N g x)
        (paraproductPartial N f g x))
  linarith

end FourierAnalysis
