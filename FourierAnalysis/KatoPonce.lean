/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under MIT license.
Authors: Bryan Sanchez

Kato–Ponce fractional Leibniz + commutator estimates on 𝕋².

## Roadmap

- `Product.lean`       — Kato–Ponce product bound
  `‖Jˢ(f·g)‖_{L²} ≤ C·(‖f‖_{L∞}·‖g‖_{Ḣˢ} + ‖g‖_{L∞}·‖f‖_{Ḣˢ})`
  for `s > 0`.
- `Commutator.lean`    — Kato–Ponce commutator bound
  `‖[Jˢ, f·∇]g‖_{L²} ≤ C·(‖∇f‖_{L∞}·‖g‖_{Ḣˢ} + ‖f‖_{Ḣˢ}·‖∇g‖_{L∞})`
  for `s > 0` (this is the form SQG energy needs).
- `SobolevEmbedding.lean` — Ḣˢ ⊂ L∞ on 𝕋² for s > d/2 = 1, via
  Bernstein + dyadic summation.

Depends on `FourierAnalysis.LittlewoodPaley` and
`FourierAnalysis.Paraproduct`.

**Downstream consumers** (planned):
- `sqg-lean-proofs` Item 5 Path B closure (~500 LOC plumbing).
- NS project Kato–Ponce applications.
- Euler project Kato–Ponce applications.
- MHD project Kato–Ponce applications.
-/

import FourierAnalysis.Paraproduct
import FourierAnalysis.KatoPonce.Product
import FourierAnalysis.KatoPonce.Commutator
import FourierAnalysis.KatoPonce.SobolevEmbedding
