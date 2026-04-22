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
import FourierAnalysis.KatoPonce.SobolevEmbedding
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

/-! ### Symmetric paraproduct piece: `T_g f` bound

The "swapped" paraproduct `paraproductPartial N g f x` is bounded by
the same low/high structure with `f` and `g` exchanged. -/

/-- Symmetric paraproduct piece bounded by a cumulative `L∞`-style
bound on `g` times the sum of high-frequency projectors of `f`. -/
theorem norm_paraproductPartial_swap_le_of_cumulative_bound
    (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) {Mg : ℝ}
    (hg : ∑ j ∈ Finset.range (N + 1), ‖lpProjector j g x‖ ≤ Mg)
    (hMg : 0 ≤ Mg) :
    ‖paraproductPartial N g f x‖ ≤
      Mg * ∑ M ∈ Finset.Ico 3 (N + 1), ‖lpProjector M f x‖ :=
  norm_paraproductPartial_le_of_cumulative_bound N g f x hg hMg

/-! ### Remainder piece: `R(f, g)` bound

The symmetric remainder `remainderPartial N f g x` is bounded by the
product of shell-projector factors on the diagonal band `|M - M'| ≤ 2`. -/

/-- Remainder bounded by a product of shell-level bounds on `f` and `g`:
for any uniform bounds `‖Δ_j f x‖ ≤ Af` and `‖Δ_j g x‖ ≤ Ag` across
`j ≤ N`, the remainder is bounded by `(diagonal-band card) · (Af · Ag)`. -/
theorem norm_remainderPartial_le_of_shell_bounds
    (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) {Af Ag : ℝ}
    (hAf : ∀ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖ ≤ Af)
    (hAg : ∀ j ∈ Finset.range (N + 1), ‖lpProjector j g x‖ ≤ Ag)
    (hAf_nn : 0 ≤ Af) :
    ‖remainderPartial N f g x‖ ≤
      ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
          (fun p => Nat.dist p.1 p.2 ≤ 2)).card * (Af * Ag) := by
  refine (norm_remainderPartial_le N f g x).trans ?_
  have hsum_const :
      ((((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
          (fun p => Nat.dist p.1 p.2 ≤ 2)).card : ℝ) * (Af * Ag)) =
        ∑ _p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
                (fun p => Nat.dist p.1 p.2 ≤ 2), Af * Ag := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hsum_const]
  refine Finset.sum_le_sum (fun p hp => ?_)
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
  obtain ⟨⟨h1, h2⟩, _⟩ := hp
  have hp1 : p.1 ∈ Finset.range (N + 1) := Finset.mem_range.mpr h1
  have hp2 : p.2 ∈ Finset.range (N + 1) := Finset.mem_range.mpr h2
  exact mul_le_mul (hAf p.1 hp1) (hAg p.2 hp2) (norm_nonneg _) hAf_nn

/-- For any `j ∈ range (N+1)`, `‖Δ_j f x‖ ≤ ∑_{k ≤ N} ‖Δ_k f x‖`. -/
lemma norm_lpProjector_le_cumulative (N : ℕ) (f : 𝕋² → ℂ) (x : 𝕋²) (j : ℕ)
    (hj : j ∈ Finset.range (N + 1)) :
    ‖lpProjector j f x‖ ≤ ∑ k ∈ Finset.range (N + 1), ‖lpProjector k f x‖ :=
  Finset.single_le_sum (f := fun k => ‖lpProjector k f x‖)
    (fun _ _ => norm_nonneg _) hj

/-- Remainder bounded by the product of the cumulative shell-sums of `f` and
`g`, weighted by the diagonal-band cardinality. -/
theorem norm_remainderPartial_le_of_cumulative_bounds
    (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    ‖remainderPartial N f g x‖ ≤
      ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
          (fun p => Nat.dist p.1 p.2 ≤ 2)).card *
        ((∑ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖) *
          ∑ j ∈ Finset.range (N + 1), ‖lpProjector j g x‖) :=
  norm_remainderPartial_le_of_shell_bounds N f g x
    (fun j hj => norm_lpProjector_le_cumulative N f x j hj)
    (fun j hj => norm_lpProjector_le_cumulative N g x j hj)
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

/-! ### Combined Kato–Ponce partial-level structural bound

Chaining the Bony-expanded triangle bound with the three piece bounds
(paraproduct + symmetric + remainder) yields a structural commutator
estimate at the partial level.  The `L∞` control on `f` and `g`
enters via cumulative shell-sum hypotheses; the final bound has five
pieces, matching the classical Kato–Ponce structure up to the
pointwise-tail term `(S_N(f) - f)·S_N(g)`. -/

/-- **Kato–Ponce commutator bound at the partial level.**

Given cumulative shell-sum bounds on `f` and `g`, and pointwise control
on `S_N(f·g)` and the tail `(S_N(f) - f)·S_N(g)`, the partial
commutator is bounded by the sum of:

- the pointwise `S_N(f·g)` value (`Sfg`);
- the paraproduct-T piece (`Mf` times the shell-sum of `g`);
- the symmetric-T piece (`Mg` times the shell-sum of `f`);
- the remainder piece (diagonal-band cardinality times `Mf·Mg`);
- the tail `‖(S_N(f) - f)·S_N(g) x‖` (encoding the `N → ∞` limit). -/
theorem norm_partialCommutator_structural_le
    (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) {Mf Mg : ℝ}
    (hf : ∑ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖ ≤ Mf)
    (hg : ∑ j ∈ Finset.range (N + 1), ‖lpProjector j g x‖ ≤ Mg)
    (hMf : 0 ≤ Mf) (hMg : 0 ≤ Mg) :
    ‖partialCommutator N f g x‖ ≤
      ‖lpPartialSum N (fun t => f t * g t) x‖
        + Mf * ∑ M ∈ Finset.Ico 3 (N + 1), ‖lpProjector M g x‖
        + Mg * ∑ M ∈ Finset.Ico 3 (N + 1), ‖lpProjector M f x‖
        + ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
              (fun p => Nat.dist p.1 p.2 ≤ 2)).card * (Mf * Mg)
        + ‖(lpPartialSum N f x - f x) * lpPartialSum N g x‖ := by
  refine (norm_partialCommutator_le_bony N f g x).trans ?_
  have hP1 := norm_paraproductPartial_le_of_cumulative_bound N f g x hf hMf
  have hP2 := norm_paraproductPartial_swap_le_of_cumulative_bound N f g x hg hMg
  have hR : ‖remainderPartial N f g x‖ ≤
      ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
          (fun p => Nat.dist p.1 p.2 ≤ 2)).card * (Mf * Mg) := by
    refine norm_remainderPartial_le_of_shell_bounds N f g x ?_ ?_ hMf
    · intro j hj
      exact (norm_lpProjector_le_cumulative N f x j hj).trans hf
    · intro j hj
      exact (norm_lpProjector_le_cumulative N g x j hj).trans hg
  linarith

/-! ### Shell-sum → `hsSeminormSq` bridge

For `j ≥ 1`, every mode `k` in `dyadicAnnulus j` has `lInfNorm k ≥ 2^(j-1) ≥ 1`,
so `(2^(j-1))^(2s) · ‖f̂(k)‖² ≤ (lInfNorm k)^(2s) · ‖f̂(k)‖²`.  Summing
and bounding by the full `hsSeminormSq` gives
`∑ k ∈ shell j, ‖f̂(k)‖² ≤ (2^(j-1))^(-2s) · hsSeminormSq s f`. -/

/-- Pointwise lower bound on the `Ḣˢ`-weight on the shell at level `N+1`:
for any `k` with `2^N ≤ lInfNorm k`, we have
`(2^N)^(2s) · ‖f̂(k)‖² ≤ (lInfNorm k)^(2s) · ‖f̂(k)‖²` when `0 ≤ 2s`. -/
private lemma pow_shell_le_rpow_lInfNorm (N : ℕ) (s : ℝ) (hs : 0 < s)
    (k : Fin 2 → ℤ) (hk : 2 ^ N ≤ lInfNorm k) :
    ((2 : ℝ) ^ N) ^ (2 * s) ≤ (lInfNorm k : ℝ) ^ (2 * s) := by
  have hpow_nn : (0 : ℝ) ≤ (2 : ℝ) ^ N := by positivity
  have hlo : ((2 : ℝ) ^ N) ≤ (lInfNorm k : ℝ) := by exact_mod_cast hk
  have h2s_nn : (0 : ℝ) ≤ 2 * s := by linarith
  exact Real.rpow_le_rpow hpow_nn hlo h2s_nn

/-- **Shell-sum → `Ḣˢ` bridge.**  For `s > 0` and `N ≥ 0`, the unweighted
square-sum of Fourier coefficients on `dyadicAnnulus (N+1)` is bounded by
`(2^N)^(-2s) · hsSeminormSq s f`. -/
theorem sum_shell_sq_le_hsSeminormSq_weighted
    (N : ℕ) (s : ℝ) (hs : 0 < s) (f : 𝕋² → ℂ)
    (hsum : Summable (fun k' : Fin 2 → ℤ =>
      (lInfNorm k' : ℝ) ^ (2 * s) * ‖mFourierCoeff f k'‖ ^ 2)) :
    ∑ k ∈ dyadicAnnulus (N + 1), ‖mFourierCoeff f k‖ ^ 2 ≤
      ((2 : ℝ) ^ N) ^ (-(2 * s)) * hsSeminormSq s f := by
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hpow_rpow_pos : (0 : ℝ) < ((2 : ℝ) ^ N) ^ (2 * s) :=
    Real.rpow_pos_of_pos hpow_pos _
  have hsum_weighted_shell_le_tot :
      ∑ k ∈ dyadicAnnulus (N + 1),
          (lInfNorm k : ℝ) ^ (2 * s) * ‖mFourierCoeff f k‖ ^ 2 ≤
      hsSeminormSq s f := by
    refine hsum.sum_le_tsum _ (fun k _ =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _))
  -- Pointwise: (2^N)^(2s) · ‖f̂(k)‖² ≤ (lInfNorm k)^(2s) · ‖f̂(k)‖².
  have hpoint : ∀ k ∈ dyadicAnnulus (N + 1),
      ((2 : ℝ) ^ N) ^ (2 * s) * ‖mFourierCoeff f k‖ ^ 2 ≤
        (lInfNorm k : ℝ) ^ (2 * s) * ‖mFourierCoeff f k‖ ^ 2 := by
    intro k hk
    rw [mem_dyadicAnnulus_succ] at hk
    exact mul_le_mul_of_nonneg_right
      (pow_shell_le_rpow_lInfNorm N s hs k hk.1) (sq_nonneg _)
  have hweighted_shell_le :
      ((2 : ℝ) ^ N) ^ (2 * s) *
          ∑ k ∈ dyadicAnnulus (N + 1), ‖mFourierCoeff f k‖ ^ 2 ≤
        ∑ k ∈ dyadicAnnulus (N + 1),
          (lInfNorm k : ℝ) ^ (2 * s) * ‖mFourierCoeff f k‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpoint
  -- Combine: (2^N)^(2s) · shell_sum ≤ hsSeminormSq s f.
  have hshell_le_hs :
      ((2 : ℝ) ^ N) ^ (2 * s) *
          ∑ k ∈ dyadicAnnulus (N + 1), ‖mFourierCoeff f k‖ ^ 2 ≤
        hsSeminormSq s f :=
    hweighted_shell_le.trans hsum_weighted_shell_le_tot
  -- Divide by (2^N)^(2s): shell_sum ≤ (2^N)^(-2s) · hsSeminormSq s f.
  have hid : ((2 : ℝ) ^ N) ^ (-(2 * s)) * hsSeminormSq s f =
      (((2 : ℝ) ^ N) ^ (2 * s))⁻¹ * hsSeminormSq s f := by
    rw [Real.rpow_neg (le_of_lt hpow_pos)]
  rw [hid]
  calc ∑ k ∈ dyadicAnnulus (N + 1), ‖mFourierCoeff f k‖ ^ 2
      = (((2 : ℝ) ^ N) ^ (2 * s))⁻¹ *
          (((2 : ℝ) ^ N) ^ (2 * s) *
            ∑ k ∈ dyadicAnnulus (N + 1), ‖mFourierCoeff f k‖ ^ 2) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpow_rpow_pos), one_mul]
    _ ≤ (((2 : ℝ) ^ N) ^ (2 * s))⁻¹ * hsSeminormSq s f := by
        refine mul_le_mul_of_nonneg_left hshell_le_hs ?_
        exact inv_nonneg.mpr (le_of_lt hpow_rpow_pos)

end FourierAnalysis
