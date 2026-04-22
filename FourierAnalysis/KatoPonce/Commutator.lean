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
lemma partialCommutator_zero_right (N : ℕ) (f : 𝕋² → ℂ) (x : 𝕋²) :
    partialCommutator N f (0 : 𝕋² → ℂ) x = 0 := by
  unfold partialCommutator
  have h1 : (fun t : 𝕋² => f t * (0 : 𝕋² → ℂ) t) = 0 := by funext t; simp
  rw [h1]
  simp [lpPartialSum, lpProjector]

end FourierAnalysis
