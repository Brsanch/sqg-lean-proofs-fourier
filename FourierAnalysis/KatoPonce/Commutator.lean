/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under MIT license.
Authors: Bryan Sanchez

Kato–Ponce commutator estimate on 𝕋².

**Contents (planned, ~500 LOC):**

`kato_ponce_commutator :
  ‖[Jˢ, f · ∇]g‖_{L²} ≤ C·(‖∇f‖_{L∞}·‖g‖_{Ḣˢ} + ‖f‖_{Ḣˢ}·‖∇g‖_{L∞})`

where `[Jˢ, f·∇]g = Jˢ(f·∇g) − f·∇(Jˢg)`.

**Why this is the harder form:** the product Kato–Ponce is a trivial
consequence of Bony decomposition; the commutator requires a delicate
symbol-calculus argument (Coifman–Meyer type) that the MAIN term
`f·∇(Jˢg)` cancels, leaving a remainder controllable by
gradient-type L∞ bounds without a full derivative loss.

**Why SQG needs this form rather than the product form:** the Galerkin
energy estimate
`d/dt ‖θ‖²_{Ḣˢ} = -2·Re⟨Jˢθ, Jˢ(u·∇θ)⟩ = -2·Re⟨Jˢθ, [Jˢ, u·∇]θ⟩`
(the main term vanishes because `u` is divergence-free), gives
`|d/dt ‖θ‖²_{Ḣˢ}| ≤ C·‖∇θ‖_{L∞}·‖θ‖²_{Ḣˢ}`, which is LINEAR in
the Ḣˢ energy and closes under BKM-integral via Grönwall.  The
product Kato–Ponce applied directly would lose a derivative.

**Classical references:**
- Kato, T.; Ponce, G. *Commutator estimates and the Euler and
  Navier–Stokes equations.* Comm. Pure Appl. Math. 41 (1988).
- Coifman, R.; Meyer, Y. *Nonlinear harmonic analysis, operator
  theory, and P.D.E.* (1978) — paraproduct techniques.

Depends on `FourierAnalysis.Paraproduct` and `.LittlewoodPaley`.
-/

import FourierAnalysis.Paraproduct

namespace FourierAnalysis

-- TODO: Kato–Ponce commutator estimate.  This is the key Path B
-- classical content blocking sqg-lean-proofs Item 5 unconditional
-- closure.

end FourierAnalysis
