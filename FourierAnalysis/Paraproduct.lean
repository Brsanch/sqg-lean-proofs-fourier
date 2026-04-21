/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under MIT license.
Authors: Bryan Sanchez

Bony paraproduct decomposition on 𝕋².

## Roadmap

- `Defs.lean`   — paraproduct `T_f g` (low-high), remainder `R(f,g)`
                   (high-high), and the Bony identity
                   `f · g = T_f g + T_g f + R(f, g)`.
- `Bounds.lean` — three classical bounds:
  * `‖T_f g‖_{Ḣˢ}   ≤ C · ‖f‖_{L∞} · ‖g‖_{Ḣˢ}`
  * `‖T_g f‖_{Ḣˢ}   ≤ C · ‖g‖_{L∞} · ‖f‖_{Ḣˢ}`
  * `‖R(f, g)‖_{Ḣˢ} ≤ C · ‖f‖_{L∞} · ‖g‖_{Ḣˢ}` (for s > d/2 = 1)

Depends on `FourierAnalysis.LittlewoodPaley`.
-/

import FourierAnalysis.LittlewoodPaley
import FourierAnalysis.Paraproduct.Defs
import FourierAnalysis.Paraproduct.Bounds
