/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under MIT license.
Authors: Bryan Sanchez

Bony paraproduct definitions.

**Contents (planned, ~200 LOC):**

- `paraproduct f g := Σ_N S_{N-2} f · Δ_N g` — the "low-high" term
  (f's low frequencies modulate g's dyadic components).
- `paraRemainder f g := Σ_{|N-M|≤1} Δ_N f · Δ_M g` — the "high-high"
  diagonal remainder.
- Bony identity: `f * g = T_f g + T_g f + R(f, g)` in L²(𝕋²).

Classical Fourier-side definitions of the Bony decomposition.
-/

import FourierAnalysis.LittlewoodPaley

namespace FourierAnalysis

-- TODO: Bony paraproduct + remainder + identity.

end FourierAnalysis
