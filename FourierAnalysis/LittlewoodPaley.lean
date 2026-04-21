/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under MIT license.
Authors: Bryan Sanchez

Littlewood–Paley dyadic decomposition on 𝕋² (and, eventually, ℝᵈ).

## Roadmap

- `Dyadic.lean`       — dyadic annuli `{2^(N-1) ≤ |k| < 2^N}` on ℤᵈ,
                         projectors `Δ_N`, partial sums `S_N`, and their
                         basic L^p bounds.
- `Bernstein.lean`    — Bernstein inequality
                         `‖Δ_N f‖_{L∞} ≤ C · 2^{Nd/2} · ‖Δ_N f‖_{L²}`.
- `Completeness.lean` — `f = Σ_N Δ_N f` in L²(𝕋²).

This module imports only mathlib — no SQG-specific content.
-/

import FourierAnalysis.LittlewoodPaley.Dyadic
import FourierAnalysis.LittlewoodPaley.Bernstein
