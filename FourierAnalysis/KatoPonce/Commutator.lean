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

/-! ### Cumulative Bernstein → `hsSeminormSq` wrapper

Applying the shell Bernstein bound
`‖Δ_{N+1} f x‖² ≤ 4·4^(N+1) · ∑_{shell N+1} ‖f̂(k)‖²` on each shell and
then the shell-sum → `Ḣˢ` bridge gives
`‖Δ_{N+1} f x‖² ≤ 4·4^(N+1) · (2^N)^(-2s) · hsSeminormSq s f`.
Summing over shells `1 ≤ j ≤ N+1` yields a geometric-series bound by
`hsSeminormSq s f` alone for `s > 1`. -/

/-- Shell-level combined Bernstein + `Ḣˢ` bridge at shell `N+1`:
`‖Δ_{N+1} f x‖² ≤ (4·4^(N+1)) · (2^N)^(-2s) · hsSeminormSq s f`. -/
theorem sq_norm_lpProjector_succ_le_hsSeminormSq
    (N : ℕ) (s : ℝ) (hs : 0 < s) (f : 𝕋² → ℂ) (x : 𝕋²)
    (hsum : Summable (fun k' : Fin 2 → ℤ =>
      (lInfNorm k' : ℝ) ^ (2 * s) * ‖mFourierCoeff f k'‖ ^ 2)) :
    ‖lpProjector (N + 1) f x‖ ^ 2 ≤
      (4 * 4 ^ (N + 1) : ℝ) * ((2 : ℝ) ^ N) ^ (-(2 * s)) *
        hsSeminormSq s f := by
  have hnn : (0 : ℝ) ≤ 4 * (4 : ℝ) ^ (N + 1) := by positivity
  have hshell := sum_shell_sq_le_hsSeminormSq_weighted N s hs f hsum
  calc ‖lpProjector (N + 1) f x‖ ^ 2
      ≤ (4 * 4 ^ (N + 1) : ℝ) *
          ∑ k ∈ dyadicAnnulus (N + 1), ‖mFourierCoeff f k‖ ^ 2 :=
        sq_norm_lpProjector_succ_le N f x
    _ ≤ (4 * 4 ^ (N + 1) : ℝ) *
          (((2 : ℝ) ^ N) ^ (-(2 * s)) * hsSeminormSq s f) :=
        mul_le_mul_of_nonneg_left hshell hnn
    _ = (4 * 4 ^ (N + 1) : ℝ) * ((2 : ℝ) ^ N) ^ (-(2 * s)) *
          hsSeminormSq s f := by ring

/-- Per-shell coefficient simplified to geometric form:
`4·4^(N+1) · (2^N)^(-2s) = 16 · 2^(2(1-s)·N)`. -/
private lemma shell_coeff_eq_geometric (N : ℕ) (s : ℝ) :
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

/-- **Cumulative Bernstein → `Ḣˢ` wrapper.**  For `s > 1`, the sum of
squared projector norms over shells `1 ≤ j ≤ N+1` is bounded by
`(∑_{j=0}^N 16·2^(2(1-s)j)) · hsSeminormSq s f`. -/
theorem cumulative_bernstein_le_hsSeminormSq
    (N : ℕ) (s : ℝ) (hs : 1 < s) (f : 𝕋² → ℂ) (x : 𝕋²)
    (hsum : Summable (fun k' : Fin 2 → ℤ =>
      (lInfNorm k' : ℝ) ^ (2 * s) * ‖mFourierCoeff f k'‖ ^ 2)) :
    ∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) f x‖ ^ 2 ≤
      (∑ j ∈ Finset.range (N + 1),
          16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ))) *
        hsSeminormSq s f := by
  have hs_pos : 0 < s := by linarith
  have hhs_nn : 0 ≤ hsSeminormSq s f := hsSeminormSq_nonneg s f
  have hshell : ∀ j ∈ Finset.range (N + 1),
      ‖lpProjector (j + 1) f x‖ ^ 2 ≤
        16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ)) * hsSeminormSq s f := by
    intro j _
    have hbase := sq_norm_lpProjector_succ_le_hsSeminormSq j s hs_pos f x hsum
    have heq := shell_coeff_eq_geometric j s
    calc ‖lpProjector (j + 1) f x‖ ^ 2
        ≤ (4 * 4 ^ (j + 1) : ℝ) * ((2 : ℝ) ^ j) ^ (-(2 * s)) *
            hsSeminormSq s f := hbase
      _ = 16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ)) * hsSeminormSq s f := by
          rw [heq]
  calc ∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) f x‖ ^ 2
      ≤ ∑ j ∈ Finset.range (N + 1),
          16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ)) * hsSeminormSq s f :=
        Finset.sum_le_sum hshell
    _ = (∑ j ∈ Finset.range (N + 1),
            16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ))) *
          hsSeminormSq s f := by
        rw [Finset.sum_mul]

/-- The per-shell geometric coefficient is nonnegative (trivial). -/
lemma shell_geom_coeff_nonneg (s : ℝ) (j : ℕ) :
    0 ≤ 16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ)) := by
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h1 : 0 ≤ (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos h2_pos _)
  linarith

/-- The cumulative geometric constant `∑_{j=0}^N 16·2^(2(1-s)j)` is
nonnegative. -/
lemma cumulative_geom_coeff_nonneg (N : ℕ) (s : ℝ) :
    0 ≤ ∑ j ∈ Finset.range (N + 1),
          16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ)) := by
  refine Finset.sum_nonneg (fun j _ => ?_)
  exact shell_geom_coeff_nonneg s j

/-! ### Quantitative L² Kato–Ponce commutator bound

Combining the cumulative-Bernstein → `Ḣˢ` wrapper with Cauchy–Schwarz
gives a linear-sum bound
`∑_{j=0}^N ‖Δ_{j+1} f x‖ ≤ √((N+1) · C(N,s)) · √(hsSeminormSq s f)`.
Substituting this into `norm_partialCommutator_structural_le` yields
a pointwise partial-level commutator estimate in terms of the `Ḣˢ`
seminorms of `f` and `g`. -/

/-- Cauchy–Schwarz on the linear projector sum: the squared linear-sum
over shells `1 ≤ j ≤ N+1` is bounded by `(N+1) · ∑ ‖Δ_{j+1} f x‖²`. -/
theorem sq_sum_lpProjector_succ_le_card_mul_sum_sq
    (N : ℕ) (f : 𝕋² → ℂ) (x : 𝕋²) :
    (∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) f x‖) ^ 2 ≤
      (N + 1 : ℕ) * ∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) f x‖ ^ 2 := by
  calc (∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) f x‖) ^ 2
      ≤ (Finset.range (N + 1)).card *
          ∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) f x‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ = (N + 1 : ℕ) * ∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) f x‖ ^ 2 := by
        rw [Finset.card_range]

/-- **Linear-sum → `Ḣˢ` bridge.**  For `s > 1`, the cumulative linear
projector-sum `∑_{j=0}^N ‖Δ_{j+1} f x‖` is bounded by
`√((N+1) · C(N,s) · hsSeminormSq s f)` where `C(N,s)` is the
cumulative geometric coefficient. -/
theorem sum_lpProjector_succ_le_sqrt_hsSeminormSq
    (N : ℕ) (s : ℝ) (hs : 1 < s) (f : 𝕋² → ℂ) (x : 𝕋²)
    (hsum : Summable (fun k' : Fin 2 → ℤ =>
      (lInfNorm k' : ℝ) ^ (2 * s) * ‖mFourierCoeff f k'‖ ^ 2)) :
    ∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) f x‖ ≤
      Real.sqrt ((N + 1 : ℕ) *
        (∑ j ∈ Finset.range (N + 1),
          16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ))) *
          hsSeminormSq s f) := by
  have hsum_nn : 0 ≤ ∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) f x‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hcum := cumulative_bernstein_le_hsSeminormSq N s hs f x hsum
  have hCS := sq_sum_lpProjector_succ_le_card_mul_sum_sq N f x
  have hN_nn : (0 : ℝ) ≤ (N + 1 : ℕ) := by positivity
  have hC_nn : 0 ≤ ∑ j ∈ Finset.range (N + 1),
      16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ)) := cumulative_geom_coeff_nonneg N s
  have hhs_nn : 0 ≤ hsSeminormSq s f := hsSeminormSq_nonneg s f
  have hchained :
      (∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) f x‖) ^ 2 ≤
        (N + 1 : ℕ) *
          ((∑ j ∈ Finset.range (N + 1),
              16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ))) *
            hsSeminormSq s f) :=
    hCS.trans (mul_le_mul_of_nonneg_left hcum hN_nn)
  have hrhs_nn :
      (0 : ℝ) ≤ (N + 1 : ℕ) *
        (∑ j ∈ Finset.range (N + 1),
          16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ))) *
          hsSeminormSq s f :=
    mul_nonneg (mul_nonneg hN_nn hC_nn) hhs_nn
  have hsq_form :
      (∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) f x‖) ^ 2 ≤
        (N + 1 : ℕ) *
          (∑ j ∈ Finset.range (N + 1),
            16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ))) *
          hsSeminormSq s f := by
    calc (∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) f x‖) ^ 2
        ≤ (N + 1 : ℕ) *
            ((∑ j ∈ Finset.range (N + 1),
                16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ))) *
              hsSeminormSq s f) := hchained
      _ = (N + 1 : ℕ) *
            (∑ j ∈ Finset.range (N + 1),
              16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ))) *
            hsSeminormSq s f := by ring
  calc ∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) f x‖
      = Real.sqrt ((∑ j ∈ Finset.range (N + 1),
            ‖lpProjector (j + 1) f x‖) ^ 2) := (Real.sqrt_sq hsum_nn).symm
    _ ≤ Real.sqrt ((N + 1 : ℕ) *
            (∑ j ∈ Finset.range (N + 1),
              16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ))) *
            hsSeminormSq s f) := Real.sqrt_le_sqrt hsq_form

/-- Linear cumulative shell-sum over `Finset.Ico 3 (N+1)` is dominated by
the cumulative shell-sum over `Finset.range (N+1)` of shifted shells
`j+1`.  Proof: the map `M ↦ M` embeds `Ico 3 (N+1)` into the image of
`j ↦ j+1` on `range (N+1)` (which is `Ico 1 (N+2)`), so the RHS has
more nonneg terms. -/
theorem sum_Ico_lpProjector_le_range_shifted
    (N : ℕ) (f : 𝕋² → ℂ) (x : 𝕋²) :
    ∑ M ∈ Finset.Ico 3 (N + 1), ‖lpProjector M f x‖ ≤
      ∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) f x‖ := by
  -- Rewrite the shifted sum as a sum over `Finset.Ico 1 (N+2)`.
  have hshift :
      ∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) f x‖ =
        ∑ M ∈ Finset.Ico 1 (N + 2), ‖lpProjector M f x‖ := by
    rw [show (Finset.Ico 1 (N + 2)) = (Finset.range (N + 1)).image (· + 1) by
      ext m
      simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
      constructor
      · intro ⟨h1, h2⟩
        refine ⟨m - 1, ?_, ?_⟩
        · omega
        · omega
      · rintro ⟨j, hj, rfl⟩
        omega]
    rw [Finset.sum_image (fun a _ b _ hab => by omega)]
  rw [hshift]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro M hM
    rw [Finset.mem_Ico] at hM ⊢
    omega
  · intro _ _ _
    exact norm_nonneg _

/-- Full linear cumulative `range (N+1)` projector-sum dominates the
partial `Ico 3 (N+1)` sum.  Useful for bounding the paraproduct piece
via a Ḣˢ-weighted Cauchy-Schwarz. -/
theorem sum_Ico_lpProjector_le_range
    (N : ℕ) (f : 𝕋² → ℂ) (x : 𝕋²) :
    ∑ M ∈ Finset.Ico 3 (N + 1), ‖lpProjector M f x‖ ≤
      ∑ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖ := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
  intro M hM
  rw [Finset.mem_Ico] at hM
  rw [Finset.mem_range]
  omega

/-- **Quantitative L² Kato–Ponce partial commutator bound.**

Substituting Ḣˢ-derived bounds into the structural estimate:
given hypotheses `Mf, Mg` controlling the `L∞`-style cumulative
projector-sums of `f` and `g`, and the Ḣˢ-derived linear bound
`∑_{j=0}^N ‖Δ_{j+1} g x‖ ≤ Kg` (respectively `Kf` for `f`), the partial
commutator is bounded pointwise by the five-term structural sum. -/
theorem norm_partialCommutator_le_hs
    (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²)
    {Mf Mg Kf Kg Sfg T : ℝ}
    (hf : ∑ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖ ≤ Mf)
    (hg : ∑ j ∈ Finset.range (N + 1), ‖lpProjector j g x‖ ≤ Mg)
    (hMf : 0 ≤ Mf) (hMg : 0 ≤ Mg)
    (hKf : ∑ M ∈ Finset.Ico 3 (N + 1), ‖lpProjector M f x‖ ≤ Kf)
    (hKg : ∑ M ∈ Finset.Ico 3 (N + 1), ‖lpProjector M g x‖ ≤ Kg)
    (hSfg : ‖lpPartialSum N (fun t => f t * g t) x‖ ≤ Sfg)
    (hTail : ‖(lpPartialSum N f x - f x) * lpPartialSum N g x‖ ≤ T) :
    ‖partialCommutator N f g x‖ ≤
      Sfg + Mf * Kg + Mg * Kf +
        ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
              (fun p => Nat.dist p.1 p.2 ≤ 2)).card * (Mf * Mg) + T := by
  have hstruct := norm_partialCommutator_structural_le N f g x hf hg hMf hMg
  have hP1 : Mf * ∑ M ∈ Finset.Ico 3 (N + 1), ‖lpProjector M g x‖ ≤ Mf * Kg :=
    mul_le_mul_of_nonneg_left hKg hMf
  have hP2 : Mg * ∑ M ∈ Finset.Ico 3 (N + 1), ‖lpProjector M f x‖ ≤ Mg * Kf :=
    mul_le_mul_of_nonneg_left hKf hMg
  linarith

/-- **Quantitative paraproduct-piece bound via `Ḣˢ`.**

Combines `norm_paraproductPartial_le_of_cumulative_bound`
(paraproduct ≤ `Mf · Σ_M ‖Δ_M g x‖`) with the shift + `Ḣˢ`-linear-sum
bound to replace `Σ_M ‖Δ_M g x‖` by `√(C(N,s) · hsSeminormSq s g)`. -/
theorem norm_paraproductPartial_le_hs
    (N : ℕ) (s : ℝ) (hs : 1 < s) (f g : 𝕋² → ℂ) (x : 𝕋²)
    {Mf : ℝ}
    (hf : ∑ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖ ≤ Mf)
    (hMf : 0 ≤ Mf)
    (hgsum : Summable (fun k' : Fin 2 → ℤ =>
      (lInfNorm k' : ℝ) ^ (2 * s) * ‖mFourierCoeff g k'‖ ^ 2)) :
    ‖paraproductPartial N f g x‖ ≤
      Mf * Real.sqrt ((N + 1 : ℕ) *
        (∑ j ∈ Finset.range (N + 1),
          16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ))) *
          hsSeminormSq s g) := by
  have hpp := norm_paraproductPartial_le_of_cumulative_bound N f g x hf hMf
  have hshift := sum_Ico_lpProjector_le_range_shifted N g x
  have hsqrt := sum_lpProjector_succ_le_sqrt_hsSeminormSq N s hs g x hgsum
  calc ‖paraproductPartial N f g x‖
      ≤ Mf * ∑ M ∈ Finset.Ico 3 (N + 1), ‖lpProjector M g x‖ := hpp
    _ ≤ Mf * ∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) g x‖ :=
        mul_le_mul_of_nonneg_left hshift hMf
    _ ≤ Mf * Real.sqrt ((N + 1 : ℕ) *
          (∑ j ∈ Finset.range (N + 1),
            16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ))) *
            hsSeminormSq s g) :=
        mul_le_mul_of_nonneg_left hsqrt hMf

/-- Squared form of the paraproduct-piece bound.  Squaring the linear
bound gives `‖paraproductPartial N f g x‖² ≤ Mf² · C(N,s) · hsSeminormSq s g`
directly (the `Real.sqrt` is absorbed back by `Real.sq_sqrt`). -/
theorem sq_norm_paraproductPartial_le_hs
    (N : ℕ) (s : ℝ) (hs : 1 < s) (f g : 𝕋² → ℂ) (x : 𝕋²)
    {Mf : ℝ}
    (hf : ∑ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖ ≤ Mf)
    (hMf : 0 ≤ Mf)
    (hgsum : Summable (fun k' : Fin 2 → ℤ =>
      (lInfNorm k' : ℝ) ^ (2 * s) * ‖mFourierCoeff g k'‖ ^ 2)) :
    ‖paraproductPartial N f g x‖ ^ 2 ≤
      Mf ^ 2 * ((N + 1 : ℕ) *
        (∑ j ∈ Finset.range (N + 1),
          16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ))) *
          hsSeminormSq s g) := by
  have hlin := norm_paraproductPartial_le_hs N s hs f g x hf hMf hgsum
  have hpp_nn : 0 ≤ ‖paraproductPartial N f g x‖ := norm_nonneg _
  have hrhs_nn : (0 : ℝ) ≤ (N + 1 : ℕ) *
      (∑ j ∈ Finset.range (N + 1),
        16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ))) *
        hsSeminormSq s g := by
    refine mul_nonneg (mul_nonneg ?_ ?_) (hsSeminormSq_nonneg s g)
    · exact_mod_cast Nat.zero_le _
    · exact cumulative_geom_coeff_nonneg N s
  have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt ((N + 1 : ℕ) *
      (∑ j ∈ Finset.range (N + 1),
        16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ))) *
        hsSeminormSq s g) := Real.sqrt_nonneg _
  have hrhs_mul_nn : (0 : ℝ) ≤ Mf *
      Real.sqrt ((N + 1 : ℕ) *
        (∑ j ∈ Finset.range (N + 1),
          16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ))) *
        hsSeminormSq s g) := mul_nonneg hMf hsqrt_nn
  calc ‖paraproductPartial N f g x‖ ^ 2
      ≤ (Mf * Real.sqrt ((N + 1 : ℕ) *
          (∑ j ∈ Finset.range (N + 1),
            16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ))) *
          hsSeminormSq s g)) ^ 2 := pow_le_pow_left₀ hpp_nn hlin 2
    _ = Mf ^ 2 * ((N + 1 : ℕ) *
          (∑ j ∈ Finset.range (N + 1),
            16 * (2 : ℝ) ^ (2 * (1 - s) * (j : ℝ))) *
          hsSeminormSq s g) := by
        rw [mul_pow, Real.sq_sqrt hrhs_nn]

/-! ### Uniform-in-`N` geometric-series prefactor

For `ε > 0`, the partial sum `∑_{j=0}^{N} 2^(-ε·j)` is bounded uniformly
in `N` by `(1 - 2^(-ε))⁻¹`.  This is the first factor in the dyadic-
weighted Cauchy–Schwarz estimate that removes the `(N+1)` factor from
the quantitative Kato–Ponce commutator bound. -/

/-- The geometric-series ratio `2^(-ε)` is in `[0, 1)` for `ε > 0`. -/
private lemma two_rpow_neg_eps_lt_one {ε : ℝ} (hε : 0 < ε) :
    (2 : ℝ) ^ (-ε) < 1 := by
  have h2_one_lt : (1 : ℝ) < 2 := by norm_num
  rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) from (Real.rpow_zero 2).symm]
  exact Real.rpow_lt_rpow_of_exponent_lt h2_one_lt (by linarith)

/-- The geometric-series ratio `2^(-ε)` is positive. -/
private lemma two_rpow_neg_eps_pos (ε : ℝ) : (0 : ℝ) < (2 : ℝ) ^ (-ε) :=
  Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _

/-- Summability of the geometric series `j ↦ 2^(-ε·j)` (as a real-valued
ℕ-indexed sum) for `ε > 0`.  This is the key `HasSum`-free form used in
the partial-sum bound. -/
theorem summable_two_rpow_neg_eps {ε : ℝ} (hε : 0 < ε) :
    Summable (fun j : ℕ => (2 : ℝ) ^ (-ε * (j : ℝ))) := by
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h2_nn : (0 : ℝ) ≤ 2 := le_of_lt h2_pos
  have hr_lt : (2 : ℝ) ^ (-ε) < 1 := two_rpow_neg_eps_lt_one hε
  have hr_pos : 0 < (2 : ℝ) ^ (-ε) := two_rpow_neg_eps_pos ε
  have hr_nn : 0 ≤ (2 : ℝ) ^ (-ε) := le_of_lt hr_pos
  have hid : ∀ j : ℕ,
      (2 : ℝ) ^ (-ε * (j : ℝ)) = ((2 : ℝ) ^ (-ε)) ^ j := by
    intro j
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-ε)) j, ← Real.rpow_mul h2_nn]
  simp_rw [hid]
  exact summable_geometric_of_lt_one hr_nn hr_lt

/-- **Uniform-in-`N` partial geometric-sum bound.**  For `ε > 0`, the
partial sum of `2^(-ε·j)` over `j ∈ range (N+1)` is bounded by
`(1 - 2^(-ε))⁻¹`, independent of `N`. -/
theorem geometric_two_neg_eps_partial_le {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), (2 : ℝ) ^ (-ε * (j : ℝ)) ≤
      (1 - (2 : ℝ) ^ (-ε))⁻¹ := by
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h2_nn : (0 : ℝ) ≤ 2 := le_of_lt h2_pos
  have hr_lt : (2 : ℝ) ^ (-ε) < 1 := two_rpow_neg_eps_lt_one hε
  have hr_pos : 0 < (2 : ℝ) ^ (-ε) := two_rpow_neg_eps_pos ε
  have hr_nn : 0 ≤ (2 : ℝ) ^ (-ε) := le_of_lt hr_pos
  have hsum := summable_two_rpow_neg_eps hε
  have htsum : ∑' j : ℕ, (2 : ℝ) ^ (-ε * (j : ℝ)) = (1 - (2 : ℝ) ^ (-ε))⁻¹ := by
    have hid : ∀ j : ℕ,
        (2 : ℝ) ^ (-ε * (j : ℝ)) = ((2 : ℝ) ^ (-ε)) ^ j := by
      intro j
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (-ε)) j, ← Real.rpow_mul h2_nn]
    simp_rw [hid]
    exact tsum_geometric_of_lt_one hr_nn hr_lt
  calc ∑ j ∈ Finset.range (N + 1), (2 : ℝ) ^ (-ε * (j : ℝ))
      ≤ ∑' j : ℕ, (2 : ℝ) ^ (-ε * (j : ℝ)) :=
        hsum.sum_le_tsum _
          (fun j _ => le_of_lt (Real.rpow_pos_of_pos h2_pos _))
    _ = (1 - (2 : ℝ) ^ (-ε))⁻¹ := htsum

/-- The prefactor `(1 - 2^(-ε))⁻¹` is positive for `ε > 0`. -/
lemma geometric_two_neg_eps_prefactor_pos {ε : ℝ} (hε : 0 < ε) :
    0 < (1 - (2 : ℝ) ^ (-ε))⁻¹ := by
  have hlt : (2 : ℝ) ^ (-ε) < 1 := two_rpow_neg_eps_lt_one hε
  have hpos : 0 < 1 - (2 : ℝ) ^ (-ε) := by linarith
  exact inv_pos.mpr hpos

/-- The prefactor `(1 - 2^(-ε))⁻¹` is nonnegative for `ε > 0`. -/
lemma geometric_two_neg_eps_prefactor_nonneg {ε : ℝ} (hε : 0 < ε) :
    0 ≤ (1 - (2 : ℝ) ^ (-ε))⁻¹ :=
  le_of_lt (geometric_two_neg_eps_prefactor_pos hε)

/-! ### Dyadic-weighted Cauchy–Schwarz: uniform-in-`N` linear-sum bound

Write `‖Δ_{j+1} f x‖ = 2^(-α·j/2) · (2^(α·j/2) · ‖Δ_{j+1} f x‖)` with
`α = s - 1 > 0`.  Cauchy–Schwarz gives
`(∑ j, ‖Δ_{j+1} f x‖)² ≤ (∑ j, 2^(-α·j)) · (∑ j, 2^(α·j) · ‖Δ_{j+1} f x‖²)`.
The first factor is bounded by `(1 - 2^(-α))⁻¹`.  For the second factor,
`sq_norm_lpProjector_succ_le_hsSeminormSq` combined with the shell-
coefficient identity gives `‖Δ_{j+1} f x‖² ≤ 16·2^(2(1-s)·j)·hsSeminormSq s f`.
Multiplying by `2^(α·j) = 2^((s-1)·j)` yields `16·2^(-α·j)·hsSeminormSq`,
whose partial sum is again bounded by `16·(1-2^(-α))⁻¹·hsSeminormSq`.

Product: `C_α² · hsSeminormSq s f` with `C_α := 4·(1-2^(-α))⁻¹` after
absorbing the `√16 = 4`. -/

/-- Weighted per-shell bound: `2^(α·j) · ‖Δ_{j+1} f x‖² ≤ 16·2^(-α·j)·hsSeminormSq s f`
for `α = s - 1 > 0`.  Proof: combine the Ḣˢ shell bound with the
identity `α + 2(1-s) = -α`. -/
private lemma weighted_shell_sq_bound (N : ℕ) (s : ℝ) (hs : 1 < s) (f : 𝕋² → ℂ)
    (x : 𝕋²)
    (hsum : Summable (fun k' : Fin 2 → ℤ =>
      (lInfNorm k' : ℝ) ^ (2 * s) * ‖mFourierCoeff f k'‖ ^ 2)) :
    (2 : ℝ) ^ ((s - 1) * (N : ℝ)) * ‖lpProjector (N + 1) f x‖ ^ 2 ≤
      16 * (2 : ℝ) ^ (-(s - 1) * (N : ℝ)) * hsSeminormSq s f := by
  have hs_pos : 0 < s := by linarith
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have hhs_nn : 0 ≤ hsSeminormSq s f := hsSeminormSq_nonneg s f
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((s - 1) * (N : ℝ)) :=
    Real.rpow_pos_of_pos h2_pos _
  have hpow_nn : (0 : ℝ) ≤ (2 : ℝ) ^ ((s - 1) * (N : ℝ)) := le_of_lt hpow_pos
  -- Shell bound: ‖Δ_{N+1}‖² ≤ 16 · 2^(2(1-s)N) · hsSeminormSq.
  have hbase := sq_norm_lpProjector_succ_le_hsSeminormSq N s hs_pos f x hsum
  have heq := shell_coeff_eq_geometric N s
  have hshell : ‖lpProjector (N + 1) f x‖ ^ 2 ≤
      16 * (2 : ℝ) ^ (2 * (1 - s) * (N : ℝ)) * hsSeminormSq s f := by
    calc ‖lpProjector (N + 1) f x‖ ^ 2
        ≤ (4 * 4 ^ (N + 1) : ℝ) * ((2 : ℝ) ^ N) ^ (-(2 * s)) *
            hsSeminormSq s f := hbase
      _ = 16 * (2 : ℝ) ^ (2 * (1 - s) * (N : ℝ)) * hsSeminormSq s f := by
          rw [heq]
  -- Multiply by 2^((s-1)·N) ≥ 0.
  have hmul : (2 : ℝ) ^ ((s - 1) * (N : ℝ)) * ‖lpProjector (N + 1) f x‖ ^ 2 ≤
      (2 : ℝ) ^ ((s - 1) * (N : ℝ)) *
        (16 * (2 : ℝ) ^ (2 * (1 - s) * (N : ℝ)) * hsSeminormSq s f) :=
    mul_le_mul_of_nonneg_left hshell hpow_nn
  -- Simplify: 2^((s-1)N) · 2^(2(1-s)N) = 2^((s-1 - 2(s-1))N) = 2^(-(s-1)N).
  have hexp :
      (2 : ℝ) ^ ((s - 1) * (N : ℝ)) * (2 : ℝ) ^ (2 * (1 - s) * (N : ℝ)) =
        (2 : ℝ) ^ (-(s - 1) * (N : ℝ)) := by
    rw [← Real.rpow_add h2_pos]
    congr 1
    ring
  calc (2 : ℝ) ^ ((s - 1) * (N : ℝ)) * ‖lpProjector (N + 1) f x‖ ^ 2
      ≤ (2 : ℝ) ^ ((s - 1) * (N : ℝ)) *
          (16 * (2 : ℝ) ^ (2 * (1 - s) * (N : ℝ)) * hsSeminormSq s f) := hmul
    _ = 16 *
          ((2 : ℝ) ^ ((s - 1) * (N : ℝ)) *
            (2 : ℝ) ^ (2 * (1 - s) * (N : ℝ))) * hsSeminormSq s f := by ring
    _ = 16 * (2 : ℝ) ^ (-(s - 1) * (N : ℝ)) * hsSeminormSq s f := by
        rw [hexp]

/-- Summed weighted shell bound: the `α`-weighted sum of squared
projector norms is bounded uniformly in `N` by
`16·(1-2^(-α))⁻¹·hsSeminormSq s f`, with `α = s - 1 > 0`. -/
theorem sum_weighted_sq_lpProjector_le_uniform
    (N : ℕ) (s : ℝ) (hs : 1 < s) (f : 𝕋² → ℂ) (x : 𝕋²)
    (hsum : Summable (fun k' : Fin 2 → ℤ =>
      (lInfNorm k' : ℝ) ^ (2 * s) * ‖mFourierCoeff f k'‖ ^ 2)) :
    ∑ j ∈ Finset.range (N + 1),
        (2 : ℝ) ^ ((s - 1) * (j : ℝ)) * ‖lpProjector (j + 1) f x‖ ^ 2 ≤
      16 * (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹ * hsSeminormSq s f := by
  have hα : 0 < s - 1 := by linarith
  have hhs_nn : 0 ≤ hsSeminormSq s f := hsSeminormSq_nonneg s f
  have hprefac_nn : 0 ≤ (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹ :=
    geometric_two_neg_eps_prefactor_nonneg hα
  -- Bound each term by the weighted shell bound.
  have hstep : ∀ j ∈ Finset.range (N + 1),
      (2 : ℝ) ^ ((s - 1) * (j : ℝ)) * ‖lpProjector (j + 1) f x‖ ^ 2 ≤
        16 * (2 : ℝ) ^ (-(s - 1) * (j : ℝ)) * hsSeminormSq s f := by
    intro j _
    exact weighted_shell_sq_bound j s hs f x hsum
  have hsum_step : ∑ j ∈ Finset.range (N + 1),
        (2 : ℝ) ^ ((s - 1) * (j : ℝ)) * ‖lpProjector (j + 1) f x‖ ^ 2 ≤
      ∑ j ∈ Finset.range (N + 1),
        16 * (2 : ℝ) ^ (-(s - 1) * (j : ℝ)) * hsSeminormSq s f :=
    Finset.sum_le_sum hstep
  -- Factor out 16 · hsSeminormSq and apply the partial geometric bound.
  have hfactor :
      ∑ j ∈ Finset.range (N + 1),
        16 * (2 : ℝ) ^ (-(s - 1) * (j : ℝ)) * hsSeminormSq s f =
        16 * hsSeminormSq s f *
          ∑ j ∈ Finset.range (N + 1), (2 : ℝ) ^ (-(s - 1) * (j : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hgeo :=
    geometric_two_neg_eps_partial_le (ε := s - 1) hα N
  have hmul_nn : 0 ≤ 16 * hsSeminormSq s f :=
    mul_nonneg (by norm_num) hhs_nn
  calc ∑ j ∈ Finset.range (N + 1),
          (2 : ℝ) ^ ((s - 1) * (j : ℝ)) * ‖lpProjector (j + 1) f x‖ ^ 2
      ≤ ∑ j ∈ Finset.range (N + 1),
          16 * (2 : ℝ) ^ (-(s - 1) * (j : ℝ)) * hsSeminormSq s f := hsum_step
    _ = 16 * hsSeminormSq s f *
          ∑ j ∈ Finset.range (N + 1), (2 : ℝ) ^ (-(s - 1) * (j : ℝ)) :=
        hfactor
    _ ≤ 16 * hsSeminormSq s f * (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹ :=
        mul_le_mul_of_nonneg_left hgeo hmul_nn
    _ = 16 * (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹ * hsSeminormSq s f := by ring

/-- **Dyadic-weighted Cauchy–Schwarz: uniform-in-`N` linear-sum bound.**

For `s > 1`, the cumulative linear projector-sum over shells
`1 ≤ j ≤ N+1` is bounded by a constant depending only on `s`
(independent of `N`), times `√(hsSeminormSq s f)`:

`(∑_{j=0}^N ‖Δ_{j+1} f x‖)² ≤ 16·(1-2^(-(s-1)))⁻² · hsSeminormSq s f`.

This is the key removal of the `(N+1)` factor from
`sum_lpProjector_succ_le_sqrt_hsSeminormSq`. -/
theorem sum_lpProjector_succ_le_sqrt_hsSeminormSq_uniform
    (N : ℕ) (s : ℝ) (hs : 1 < s) (f : 𝕋² → ℂ) (x : 𝕋²)
    (hsum : Summable (fun k' : Fin 2 → ℤ =>
      (lInfNorm k' : ℝ) ^ (2 * s) * ‖mFourierCoeff f k'‖ ^ 2)) :
    (∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) f x‖) ^ 2 ≤
      16 * ((1 - (2 : ℝ) ^ (-(s - 1)))⁻¹) ^ 2 * hsSeminormSq s f := by
  have hα : 0 < s - 1 := by linarith
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h2_nn : (0 : ℝ) ≤ 2 := le_of_lt h2_pos
  have hhs_nn : 0 ≤ hsSeminormSq s f := hsSeminormSq_nonneg s f
  have hprefac_nn : 0 ≤ (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹ :=
    geometric_two_neg_eps_prefactor_nonneg hα
  -- Set A_j := 2^(-(s-1)·j/2), B_j := 2^((s-1)·j/2) · ‖Δ_{j+1} f x‖.
  -- Then A_j · B_j = ‖Δ_{j+1} f x‖, A_j² = 2^(-(s-1)·j),
  -- B_j² = 2^((s-1)·j) · ‖Δ_{j+1} f x‖².
  set A : ℕ → ℝ := fun j => (2 : ℝ) ^ (-(s - 1) / 2 * (j : ℝ))
  set B : ℕ → ℝ := fun j =>
    (2 : ℝ) ^ ((s - 1) / 2 * (j : ℝ)) * ‖lpProjector (j + 1) f x‖
  -- Identity A_j · B_j = ‖Δ_{j+1} f x‖.
  have hAB : ∀ j : ℕ, A j * B j = ‖lpProjector (j + 1) f x‖ := by
    intro j
    simp only [A, B]
    rw [← mul_assoc]
    rw [show (2 : ℝ) ^ (-(s - 1) / 2 * (j : ℝ)) *
            (2 : ℝ) ^ ((s - 1) / 2 * (j : ℝ)) = 1 by
      rw [← Real.rpow_add h2_pos]
      rw [show -(s - 1) / 2 * (j : ℝ) + (s - 1) / 2 * (j : ℝ) = 0 by ring]
      exact Real.rpow_zero _]
    rw [one_mul]
  -- A_j² = 2^(-(s-1)·j).
  have hA_sq : ∀ j : ℕ, A j ^ 2 = (2 : ℝ) ^ (-(s - 1) * (j : ℝ)) := by
    intro j
    simp only [A]
    rw [sq, ← Real.rpow_add h2_pos]
    congr 1
    ring
  -- B_j² = 2^((s-1)·j) · ‖Δ_{j+1} f x‖².
  have hB_sq : ∀ j : ℕ, B j ^ 2 =
      (2 : ℝ) ^ ((s - 1) * (j : ℝ)) * ‖lpProjector (j + 1) f x‖ ^ 2 := by
    intro j
    simp only [B]
    rw [mul_pow]
    congr 1
    rw [sq, ← Real.rpow_add h2_pos]
    congr 1
    ring
  -- Cauchy-Schwarz: (∑ A_j · B_j)² ≤ (∑ A_j²) · (∑ B_j²).
  have hCS :
      (∑ j ∈ Finset.range (N + 1), A j * B j) ^ 2 ≤
        (∑ j ∈ Finset.range (N + 1), A j ^ 2) *
          ∑ j ∈ Finset.range (N + 1), B j ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ A B
  -- Rewrite ∑ A_j · B_j = ∑ ‖Δ_{j+1}‖, ∑ A_j² via hA_sq, ∑ B_j² via hB_sq.
  have hlhs : ∑ j ∈ Finset.range (N + 1), A j * B j =
      ∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) f x‖ :=
    Finset.sum_congr rfl (fun j _ => hAB j)
  have hA_sum : ∑ j ∈ Finset.range (N + 1), A j ^ 2 =
      ∑ j ∈ Finset.range (N + 1), (2 : ℝ) ^ (-(s - 1) * (j : ℝ)) :=
    Finset.sum_congr rfl (fun j _ => hA_sq j)
  have hB_sum : ∑ j ∈ Finset.range (N + 1), B j ^ 2 =
      ∑ j ∈ Finset.range (N + 1),
        (2 : ℝ) ^ ((s - 1) * (j : ℝ)) * ‖lpProjector (j + 1) f x‖ ^ 2 :=
    Finset.sum_congr rfl (fun j _ => hB_sq j)
  -- Bounds on ∑ A_j² and ∑ B_j².
  have hA_bound :
      ∑ j ∈ Finset.range (N + 1), (2 : ℝ) ^ (-(s - 1) * (j : ℝ)) ≤
        (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹ :=
    geometric_two_neg_eps_partial_le (ε := s - 1) hα N
  have hB_bound :
      ∑ j ∈ Finset.range (N + 1),
        (2 : ℝ) ^ ((s - 1) * (j : ℝ)) * ‖lpProjector (j + 1) f x‖ ^ 2 ≤
        16 * (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹ * hsSeminormSq s f :=
    sum_weighted_sq_lpProjector_le_uniform N s hs f x hsum
  -- Combine.
  have hA_sum_nn :
      (0 : ℝ) ≤ ∑ j ∈ Finset.range (N + 1), A j ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hB_sum_nn :
      (0 : ℝ) ≤ ∑ j ∈ Finset.range (N + 1), B j ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [hlhs] at hCS
  rw [hA_sum] at hCS
  rw [hB_sum] at hCS
  -- hCS: (∑ ‖Δ‖)² ≤ (∑ 2^(-α·j)) · (∑ 2^(α·j) · ‖Δ‖²).
  -- Bound RHS by (1-2^(-α))⁻¹ · (16·(1-2^(-α))⁻¹·hsSeminormSq).
  have hrhs_bound :
      (∑ j ∈ Finset.range (N + 1), (2 : ℝ) ^ (-(s - 1) * (j : ℝ))) *
          ∑ j ∈ Finset.range (N + 1),
            (2 : ℝ) ^ ((s - 1) * (j : ℝ)) * ‖lpProjector (j + 1) f x‖ ^ 2 ≤
        (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹ *
          (16 * (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹ * hsSeminormSq s f) := by
    have hA_sum_rw := hA_sum  -- for clarity; unused but keeps proof aligned
    have hsum_B_nn :
        (0 : ℝ) ≤ ∑ j ∈ Finset.range (N + 1),
          (2 : ℝ) ^ ((s - 1) * (j : ℝ)) * ‖lpProjector (j + 1) f x‖ ^ 2 := by
      refine Finset.sum_nonneg (fun j _ => ?_)
      refine mul_nonneg ?_ (sq_nonneg _)
      exact le_of_lt (Real.rpow_pos_of_pos h2_pos _)
    have h1 := mul_le_mul_of_nonneg_right hA_bound hsum_B_nn
    have hprefac_mul_nn : 0 ≤ (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹ := hprefac_nn
    have h2 := mul_le_mul_of_nonneg_left hB_bound hprefac_mul_nn
    linarith
  -- Combine hCS + hrhs_bound + final ring simplification.
  calc (∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) f x‖) ^ 2
      ≤ (∑ j ∈ Finset.range (N + 1), (2 : ℝ) ^ (-(s - 1) * (j : ℝ))) *
          ∑ j ∈ Finset.range (N + 1),
            (2 : ℝ) ^ ((s - 1) * (j : ℝ)) * ‖lpProjector (j + 1) f x‖ ^ 2 := hCS
    _ ≤ (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹ *
          (16 * (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹ * hsSeminormSq s f) := hrhs_bound
    _ = 16 * ((1 - (2 : ℝ) ^ (-(s - 1)))⁻¹) ^ 2 * hsSeminormSq s f := by ring

/-! ### Uniform-in-`N` quantitative Kato–Ponce commutator

Plugging the dyadic-weighted `sum_lpProjector_succ_le_sqrt_hsSeminormSq_uniform`
into `norm_paraproductPartial_le_of_cumulative_bound` gives a paraproduct
bound whose constant depends only on `s`.  The resulting partial commutator
estimate drops the `(N+1)` factor on the paraproduct and swap pieces. -/

/-- **Uniform-in-`N` paraproduct piece.**  For `s > 1`, the paraproduct
`paraproductPartial N f g x` is bounded by
`Mf · 4·(1-2^(-(s-1)))⁻¹ · √(hsSeminormSq s g)`, uniformly in `N`. -/
theorem norm_paraproductPartial_le_hs_uniform
    (N : ℕ) (s : ℝ) (hs : 1 < s) (f g : 𝕋² → ℂ) (x : 𝕋²)
    {Mf : ℝ}
    (hf : ∑ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖ ≤ Mf)
    (hMf : 0 ≤ Mf)
    (hgsum : Summable (fun k' : Fin 2 → ℤ =>
      (lInfNorm k' : ℝ) ^ (2 * s) * ‖mFourierCoeff g k'‖ ^ 2)) :
    ‖paraproductPartial N f g x‖ ≤
      Mf * (4 * (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹) *
        Real.sqrt (hsSeminormSq s g) := by
  have hα : 0 < s - 1 := by linarith
  have hprefac_nn : 0 ≤ (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹ :=
    geometric_two_neg_eps_prefactor_nonneg hα
  have hhs_nn : 0 ≤ hsSeminormSq s g := hsSeminormSq_nonneg s g
  have hpp := norm_paraproductPartial_le_of_cumulative_bound N f g x hf hMf
  have hshift := sum_Ico_lpProjector_le_range_shifted N g x
  -- Square-root form of the uniform-in-N CS bound on ∑ ‖Δ_{j+1} g x‖.
  have hCS_sq :=
    sum_lpProjector_succ_le_sqrt_hsSeminormSq_uniform N s hs g x hgsum
  -- Take square roots: ∑ ‖Δ‖ ≤ √(16·C²·hs) = 4·C·√hs.
  have hsum_nn :
      (0 : ℝ) ≤ ∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) g x‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hrhs_nn : (0 : ℝ) ≤
      16 * ((1 - (2 : ℝ) ^ (-(s - 1)))⁻¹) ^ 2 * hsSeminormSq s g :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hhs_nn
  have hlin :
      ∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) g x‖ ≤
        4 * (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹ *
          Real.sqrt (hsSeminormSq s g) := by
    have hsqrt_le :
        Real.sqrt ((∑ j ∈ Finset.range (N + 1),
            ‖lpProjector (j + 1) g x‖) ^ 2) ≤
          Real.sqrt (16 *
              ((1 - (2 : ℝ) ^ (-(s - 1)))⁻¹) ^ 2 * hsSeminormSq s g) :=
      Real.sqrt_le_sqrt hCS_sq
    rw [Real.sqrt_sq hsum_nn] at hsqrt_le
    -- Rewrite RHS sqrt: √(16·C²·hs) = 4·C·√hs.
    have hrhs_eq :
        Real.sqrt (16 * ((1 - (2 : ℝ) ^ (-(s - 1)))⁻¹) ^ 2 *
            hsSeminormSq s g) =
          4 * (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹ *
            Real.sqrt (hsSeminormSq s g) := by
      rw [show (16 : ℝ) * ((1 - (2 : ℝ) ^ (-(s - 1)))⁻¹) ^ 2 *
              hsSeminormSq s g =
            (4 * (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹) ^ 2 *
              hsSeminormSq s g by ring]
      rw [Real.sqrt_mul (sq_nonneg _),
          Real.sqrt_sq (mul_nonneg (by norm_num) hprefac_nn)]
    rw [hrhs_eq] at hsqrt_le
    exact hsqrt_le
  calc ‖paraproductPartial N f g x‖
      ≤ Mf * ∑ M ∈ Finset.Ico 3 (N + 1), ‖lpProjector M g x‖ := hpp
    _ ≤ Mf * ∑ j ∈ Finset.range (N + 1), ‖lpProjector (j + 1) g x‖ :=
        mul_le_mul_of_nonneg_left hshift hMf
    _ ≤ Mf * (4 * (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹ *
          Real.sqrt (hsSeminormSq s g)) :=
        mul_le_mul_of_nonneg_left hlin hMf
    _ = Mf * (4 * (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹) *
          Real.sqrt (hsSeminormSq s g) := by ring

/-- **Uniform-in-`N` quantitative Kato–Ponce partial commutator bound.**

The paraproduct and swap pieces of the Bony-expanded commutator
(`paraproductPartial N f g` and `paraproductPartial N g f`) are bounded
by constants independent of `N`.  Writing
`C_s := 4·(1-2^(-(s-1)))⁻¹` for the `s`-only prefactor, the commutator is
bounded by

`‖partialCommutator N f g x‖ ≤
  Sfg + Mf · C_s · √(hsSeminormSq s g) + Mg · C_s · √(hsSeminormSq s f)
      + card_diag · (Mf · Mg) + T`

where `Sfg, T` encode the pointwise `S_N(f·g)` value and tail (both
discharged by ambient Sobolev-embedding hypotheses downstream).  This
drops the `(N+1)` factor from `norm_partialCommutator_le_hs`. -/
theorem norm_partialCommutator_le_hs_uniform
    (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) (s : ℝ) (hs : 1 < s)
    {Mf Mg Sfg T : ℝ}
    (hf : ∑ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖ ≤ Mf)
    (hg : ∑ j ∈ Finset.range (N + 1), ‖lpProjector j g x‖ ≤ Mg)
    (hMf : 0 ≤ Mf) (hMg : 0 ≤ Mg)
    (hfsum : Summable (fun k' : Fin 2 → ℤ =>
      (lInfNorm k' : ℝ) ^ (2 * s) * ‖mFourierCoeff f k'‖ ^ 2))
    (hgsum : Summable (fun k' : Fin 2 → ℤ =>
      (lInfNorm k' : ℝ) ^ (2 * s) * ‖mFourierCoeff g k'‖ ^ 2))
    (hSfg : ‖lpPartialSum N (fun t => f t * g t) x‖ ≤ Sfg)
    (hTail : ‖(lpPartialSum N f x - f x) * lpPartialSum N g x‖ ≤ T) :
    ‖partialCommutator N f g x‖ ≤
      Sfg
        + Mf * (4 * (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹) *
            Real.sqrt (hsSeminormSq s g)
        + Mg * (4 * (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹) *
            Real.sqrt (hsSeminormSq s f)
        + ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
              (fun p => Nat.dist p.1 p.2 ≤ 2)).card * (Mf * Mg) + T := by
  have hbony := norm_partialCommutator_le_bony N f g x
  have hpp := norm_paraproductPartial_le_hs_uniform N s hs f g x hf hMf hgsum
  have hps := norm_paraproductPartial_le_hs_uniform N s hs g f x hg hMg hfsum
  have hR : ‖remainderPartial N f g x‖ ≤
      ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
          (fun p => Nat.dist p.1 p.2 ≤ 2)).card * (Mf * Mg) := by
    refine norm_remainderPartial_le_of_shell_bounds N f g x ?_ ?_ hMf
    · intro j hj
      exact (norm_lpProjector_le_cumulative N f x j hj).trans hf
    · intro j hj
      exact (norm_lpProjector_le_cumulative N g x j hj).trans hg
  linarith

/-! ### Uniform-in-`N` remainder piece via double cumulative sum

The diagonal-band filter `{(j,k) : |j - k| ≤ 2}` is a subset of the full
product `range(N+1) × range(N+1)`.  Summing the nonnegative product
`‖Δ_j f x‖ · ‖Δ_k g x‖` over the filter is therefore dominated by the
full double sum, which factors as `(∑_j ‖Δ_j f x‖) · (∑_k ‖Δ_k g x‖)`.
This eliminates the `(N+1)²` cardinality factor entirely from the
remainder bound: the final bound is `Mf · Mg`, uniform in `N`. -/

/-- **Remainder piece bounded by a double cumulative product.**  The
triangle-bounded remainder sum over the diagonal band is dominated by
the full product `(∑_j ‖Δ_j f x‖) · (∑_k ‖Δ_k g x‖)`. -/
theorem norm_remainderPartial_le_by_cumulative_product
    (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) :
    ‖remainderPartial N f g x‖ ≤
      (∑ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖) *
        ∑ k ∈ Finset.range (N + 1), ‖lpProjector k g x‖ := by
  refine (norm_remainderPartial_le N f g x).trans ?_
  -- Product of sums = double sum over `range × range`.
  have hprod :
      (∑ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖) *
          ∑ k ∈ Finset.range (N + 1), ‖lpProjector k g x‖ =
        ∑ p ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
          ‖lpProjector p.1 f x‖ * ‖lpProjector p.2 g x‖ := by
    rw [Finset.sum_product]
    rw [Finset.sum_mul_sum]
  rw [hprod]
  -- Filter ⊆ product; nonneg terms; conclude via sum-subset monotonicity.
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · exact Finset.filter_subset _ _
  · intro p _ _
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- **Remainder bounded by `Mf · Mg`, uniformly in `N`.**  Given
cumulative shell-sum bounds `hf`, `hg` (the same hypotheses used by the
paraproduct-piece uniform bound), the remainder is bounded pointwise by
`Mf · Mg` with no cardinality factor. -/
theorem norm_remainderPartial_le_uniform
    (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) {Mf Mg : ℝ}
    (hf : ∑ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖ ≤ Mf)
    (hg : ∑ j ∈ Finset.range (N + 1), ‖lpProjector j g x‖ ≤ Mg)
    (hMf : 0 ≤ Mf) :
    ‖remainderPartial N f g x‖ ≤ Mf * Mg := by
  refine (norm_remainderPartial_le_by_cumulative_product N f g x).trans ?_
  -- Goal: (∑ f) * (∑ g) ≤ Mf * Mg.
  have hg_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (N + 1), ‖lpProjector j g x‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc (∑ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖) *
          ∑ k ∈ Finset.range (N + 1), ‖lpProjector k g x‖
      ≤ Mf * ∑ k ∈ Finset.range (N + 1), ‖lpProjector k g x‖ :=
        mul_le_mul_of_nonneg_right hf hg_nn
    _ ≤ Mf * Mg := mul_le_mul_of_nonneg_left hg hMf

/-! ### Fully-uniform-in-`N` quantitative Kato–Ponce commutator

Combining the uniform-in-`N` paraproduct bound
`norm_paraproductPartial_le_hs_uniform` with the uniform-in-`N` remainder
bound `norm_remainderPartial_le_uniform` yields a Kato–Ponce commutator
estimate in which every explicit factor depends only on `s` (via the
prefactor `C_s = 4 · (1 - 2^(-(s-1)))⁻¹`) and the caller-supplied
`L∞`/tail bounds `Mf, Mg, Sfg, T`.  No `(N+1)`-growing factor appears.

The `Sfg` and `T` fields remain abstract hypotheses to be discharged by
the caller from ambient Sobolev-embedding bounds (see e.g.
`norm_le_tsum_mFourierCoeff` in `KatoPonce/SobolevEmbedding.lean`). -/

/-- **Fully-uniform-in-`N` Kato–Ponce partial commutator bound.**

Every explicit prefactor depends only on `s` and the caller-supplied
bounds `Mf, Mg, Sfg, T`:

`‖partialCommutator N f g x‖ ≤
   Sfg + Mf · C_s · √(Ḣˢ_g) + Mg · C_s · √(Ḣˢ_f) + Mf · Mg + T`

with `C_s := 4·(1-2^(-(s-1)))⁻¹`.  Dropping the `(N+1)²`-scale cardinality
from `norm_partialCommutator_le_hs_uniform`. -/
theorem norm_partialCommutator_le_hs_fully_uniform
    (N : ℕ) (f g : 𝕋² → ℂ) (x : 𝕋²) (s : ℝ) (hs : 1 < s)
    {Mf Mg Sfg T : ℝ}
    (hf : ∑ j ∈ Finset.range (N + 1), ‖lpProjector j f x‖ ≤ Mf)
    (hg : ∑ j ∈ Finset.range (N + 1), ‖lpProjector j g x‖ ≤ Mg)
    (hMf : 0 ≤ Mf) (hMg : 0 ≤ Mg)
    (hfsum : Summable (fun k' : Fin 2 → ℤ =>
      (lInfNorm k' : ℝ) ^ (2 * s) * ‖mFourierCoeff f k'‖ ^ 2))
    (hgsum : Summable (fun k' : Fin 2 → ℤ =>
      (lInfNorm k' : ℝ) ^ (2 * s) * ‖mFourierCoeff g k'‖ ^ 2))
    (hSfg : ‖lpPartialSum N (fun t => f t * g t) x‖ ≤ Sfg)
    (hTail : ‖(lpPartialSum N f x - f x) * lpPartialSum N g x‖ ≤ T) :
    ‖partialCommutator N f g x‖ ≤
      Sfg
        + Mf * (4 * (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹) *
            Real.sqrt (hsSeminormSq s g)
        + Mg * (4 * (1 - (2 : ℝ) ^ (-(s - 1)))⁻¹) *
            Real.sqrt (hsSeminormSq s f)
        + Mf * Mg + T := by
  have hbony := norm_partialCommutator_le_bony N f g x
  have hpp := norm_paraproductPartial_le_hs_uniform N s hs f g x hf hMf hgsum
  have hps := norm_paraproductPartial_le_hs_uniform N s hs g f x hg hMg hfsum
  have hR := norm_remainderPartial_le_uniform N f g x hf hg hMf
  linarith

end FourierAnalysis
