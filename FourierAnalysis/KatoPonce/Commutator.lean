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

/-- **Two-term split of the partial commutator.**

`partialCommutator N f g x =
  [S_N(f·g)(x) - S_N(f)(x) · S_N(g)(x)]   +   (S_N(f)(x) - f x) · S_N(g)(x)`

The first bracket is the "product-of-partial-sums" defect: `S_N` doesn't
commute with multiplication, and this defect drives the high-frequency
contribution to the commutator.  The second term is a "tail" that
vanishes as `N → ∞` when `f` has summable Fourier coefficients. -/
theorem partialCommutator_eq_split (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    partialCommutator N f g x =
      (lpPartialSum N (fun t => f t * g t) x -
          lpPartialSum N f x * lpPartialSum N g x)
        + (lpPartialSum N f x - f x) * lpPartialSum N g x := by
  unfold partialCommutator
  ring

/-- **Bony expansion of the partial commutator.**  Decomposes
`partialCommutator N f g x` as

`partialCommutator N f g x =
  S_N(f·g)(x)
    - paraproductPartial N f g x
    - paraproductPartial N g f x
    - remainderPartial N f g x
    + (S_N(f)(x) - f x) · S_N(g)(x)`

obtained by substituting `S_N(f)·S_N(g) = paraproductPartial N f g +
paraproductPartial N g f + remainderPartial N f g` (via `bony_partial`)
into the two-term split `partialCommutator_eq_split`.  This is the
Bony form used to split the commutator into three dyadic pieces plus
a pure "tail" contribution `(S_N(f) - f)·S_N(g)`. -/
theorem partialCommutator_eq_bony_expansion (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    partialCommutator N f g x =
      lpPartialSum N (fun t => f t * g t) x
        - paraproductPartial N f g x
        - paraproductPartial N g f x
        - remainderPartial N f g x
        + (lpPartialSum N f x - f x) * lpPartialSum N g x := by
  unfold partialCommutator
  have hbony := bony_partial N f g x
  -- Goal: S_N(fg) - f·B = S_N(fg) - P1 - P2 - R + (A - f)·B.
  -- Expand (A - f)·B = A·B - f·B, use hbony: A·B = P1 + P2 + R.
  linear_combination -hbony

/-- Triangle bound on the partial commutator via the Bony expansion. -/
theorem norm_partialCommutator_le_bony (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    ‖partialCommutator N f g x‖ ≤
      ‖lpPartialSum N (fun t => f t * g t) x‖
        + ‖paraproductPartial N f g x‖
        + ‖paraproductPartial N g f x‖
        + ‖remainderPartial N f g x‖
        + ‖(lpPartialSum N f x - f x) * lpPartialSum N g x‖ := by
  rw [partialCommutator_eq_bony_expansion]
  -- Abbreviate the five pieces.
  set S := lpPartialSum N (fun t => f t * g t) x
  set P1 := paraproductPartial N f g x
  set P2 := paraproductPartial N g f x
  set R := remainderPartial N f g x
  set T := (lpPartialSum N f x - f x) * lpPartialSum N g x
  -- Goal: ‖S - P1 - P2 - R + T‖ ≤ ‖S‖ + ‖P1‖ + ‖P2‖ + ‖R‖ + ‖T‖.
  calc ‖S - P1 - P2 - R + T‖
      = ‖S + (-P1) + (-P2) + (-R) + T‖ := by
        have h : S - P1 - P2 - R + T = S + (-P1) + (-P2) + (-R) + T := by ring
        rw [h]
    _ ≤ ‖S + (-P1) + (-P2) + (-R)‖ + ‖T‖ := norm_add_le _ _
    _ ≤ ‖S + (-P1) + (-P2)‖ + ‖(-R)‖ + ‖T‖ := by
        have := norm_add_le (S + (-P1) + (-P2)) (-R); linarith
    _ ≤ ‖S + (-P1)‖ + ‖(-P2)‖ + ‖(-R)‖ + ‖T‖ := by
        have := norm_add_le (S + (-P1)) (-P2); linarith
    _ ≤ ‖S‖ + ‖(-P1)‖ + ‖(-P2)‖ + ‖(-R)‖ + ‖T‖ := by
        have := norm_add_le S (-P1); linarith
    _ = ‖S‖ + ‖P1‖ + ‖P2‖ + ‖R‖ + ‖T‖ := by
        simp [norm_neg]

/-! ### Paraproduct piece: `T_f g` bound for the commutator

The low-times-high paraproduct contribution to the commutator is
`T^{≤N}_f g (x) = ∑_{3 ≤ M ≤ N} S_{M-3}(f)(x) · Δ_M(g)(x)`.  In the
Kato–Ponce commutator estimate this piece is bounded by
`‖f‖_{L∞} · (∑_M ‖Δ_M g x‖)`.  We encode the `L∞`-style bound on
`S_{M-3}(f)(x)` as an abstract hypothesis `Mf` satisfied by any
ambient `L∞` bound on `f` via `norm_lpPartialSum_le` + triangle. -/

/-- Paraproduct piece bounded by a uniform bound on the low-frequency
factor times the sum of high-frequency projector norms. -/
theorem norm_paraproductPartial_le_of_low_bound
    (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) {Mf : ℝ}
    (hf : ∀ M ∈ Finset.Ico 3 (N + 1), ‖lpPartialSum (M - 3) f x‖ ≤ Mf)
    (hMf : 0 ≤ Mf) :
    ‖paraproductPartial N f g x‖ ≤
      Mf * ∑ M ∈ Finset.Ico 3 (N + 1), ‖lpProjector M g x‖ := by
  refine (norm_paraproductPartial_direct_le N f g x).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun M hM => ?_)
  calc ‖lpPartialSum (M - 3) f x‖ * ‖lpProjector M g x‖
      ≤ Mf * ‖lpProjector M g x‖ :=
        mul_le_mul_of_nonneg_right (hf M hM) (norm_nonneg _)

/-- Uniform `L∞`-style bound on all dyadic partial sums of `f` at a
point, given a uniform bound on the shell-projector sums.  This is the
"triangle-level" replacement for `‖f‖_{L∞}` in the commutator estimate. -/
lemma norm_lpPartialSum_le_of_uniform
    (N : ℕ) (f : 𝕋² → ℂ) (x : 𝕋²) {Mf : ℝ}
    (hf : ∑ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖ ≤ Mf)
    (K : ℕ) (hK : K ≤ N) :
    ‖lpPartialSum K f x‖ ≤ Mf := by
  refine (norm_lpPartialSum_le K f x).trans ?_
  refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_).trans hf
  · intro j hj
    rw [Finset.mem_range] at hj ⊢
    omega
  · intro _ _ _
    exact norm_nonneg _

/-- Paraproduct piece bounded by the cumulative `L∞`-style bound on `f`
(the sum of all shell-projector norms up to level `N`) times the sum
of high-frequency projectors of `g`. -/
theorem norm_paraproductPartial_le_of_cumulative_bound
    (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) {Mf : ℝ}
    (hf : ∑ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖ ≤ Mf)
    (hMf : 0 ≤ Mf) :
    ‖paraproductPartial N f g x‖ ≤
      Mf * ∑ M ∈ Finset.Ico 3 (N + 1), ‖lpProjector M g x‖ := by
  refine norm_paraproductPartial_le_of_low_bound N f g x ?_ hMf
  intro M hM
  rw [Finset.mem_Ico] at hM
  exact norm_lpPartialSum_le_of_uniform N f x hf (M - 3) (by omega)

end FourierAnalysis
