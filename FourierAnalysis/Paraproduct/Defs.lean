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

end FourierAnalysis
