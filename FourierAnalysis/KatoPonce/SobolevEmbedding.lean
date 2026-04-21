/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under MIT license.
Authors: Bryan Sanchez

Sobolev embedding `Ḣˢ(𝕋²) ⊂ L∞(𝕋²)` for `s > 1`.

**Contents (planned, ~200 LOC):**

`sobolev_Linf_of_Hs : ‖f‖_{L∞} ≤ C_s · ‖f‖_{Ḣˢ}` for every
`f ∈ Ḣˢ(𝕋²)` with `s > d/2 = 1`.

Proof: dyadic decomposition + Bernstein + summation of geometric
series.  The constant `C_s` depends on `s` and diverges as `s → 1`.

**Why needed for SQG:** the commutator Kato–Ponce bound uses
`‖∇f‖_{L∞}` on the RHS; Sobolev embedding
`Ḣ^{s+1} ⊂ L∞` (needs `s+1 > 1`, i.e., `s > 0`) lets us control
`‖∇f‖_{L∞}` by the Ḣˢ seminorm of f plus one derivative.  For the
SQG chain, we specifically use `s > 1` to control `‖∇θ‖_{L∞}` by
`‖θ‖_{Ḣˢ}`.

Depends on `FourierAnalysis.LittlewoodPaley.Bernstein`.
-/

import FourierAnalysis.LittlewoodPaley

namespace FourierAnalysis

-- TODO: Sobolev L∞ embedding.

end FourierAnalysis
