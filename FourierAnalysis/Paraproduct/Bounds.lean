/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under MIT license.
Authors: Bryan Sanchez

Classical paraproduct bounds on 𝕋².

**Contents (planned, ~400 LOC):**

1. `paraproduct_Hs_le`: `‖T_f g‖_{Ḣˢ} ≤ C · ‖f‖_{L∞} · ‖g‖_{Ḣˢ}`.
2. `paraproduct_swap_Hs_le`: `‖T_g f‖_{Ḣˢ} ≤ C · ‖g‖_{L∞} · ‖f‖_{Ḣˢ}`.
3. `paraRemainder_Hs_le`: `‖R(f,g)‖_{Ḣˢ} ≤ C · ‖f‖_{L∞} · ‖g‖_{Ḣˢ}`
   (needs `s > d/2 = 1` on 𝕋²).

All three follow from:
- Bernstein (from `FourierAnalysis.LittlewoodPaley.Bernstein`)
- Dyadic orthogonality on Ḣˢ: `‖f‖²_{Ḣˢ} ≈ Σ_N 2^{2Ns}·‖Δ_N f‖²_{L²}`

These are the classical ingredients for the Kato–Ponce commutator.
-/

import FourierAnalysis.Paraproduct.Defs

namespace FourierAnalysis

-- TODO: three paraproduct bounds.

end FourierAnalysis
