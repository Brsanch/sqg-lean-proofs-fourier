/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under MIT license.
Authors: Bryan Sanchez

Dyadic Fourier projectors on 𝕋².

**Contents (planned, ~600 LOC):**
- `dyadicAnnulus N : Finset (Fin 2 → ℤ)` — lattice annulus
  `{k : 2^{N-1} ≤ ‖k‖_{ℓ∞} < 2^N}`.
- `lpProjector N f` — Fourier truncation of `f ∈ L²(𝕋²)` to
  `dyadicAnnulus N`.
- `lpPartialSum N f := Σ_{k ≤ N} lpProjector k f`.
- L^p bounds `‖Δ_N f‖_{L^p} ≤ C · ‖f‖_{L^p}` for `p ∈ [1, ∞]`.
- Fourier-side computation: `(Δ_N f)̂(m) = 1_{m ∈ annulus N} · f̂(m)`.

This file is a placeholder for incremental Path B work.
-/

import Mathlib

namespace FourierAnalysis

-- TODO: move concrete Δ_N content here from sqg-lean-proofs §11.1–§11.4.
-- The current in-tree definitions rely on `rieszTorusMeasureSpace` local
-- instance; first step is a clean `scoped` instance in this package so
-- the sqg-lean-proofs consumer can `open scoped FourierAnalysis`.

end FourierAnalysis
