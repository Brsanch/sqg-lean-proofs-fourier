# Fourier Analysis — Lean 4 Classical Content

A Lean 4 + mathlib formalization of classical Fourier analysis on 𝕋²:
Littlewood–Paley decomposition, Bony paraproducts, Kato–Ponce fractional
Leibniz and commutator estimates, and the Sobolev embedding `Ḣˢ ⊂ L∞`
for `s > d/2`.

This package is **upstream of several PDE projects**:
- [sqg-lean-proofs](https://github.com/Brsanch/sqg-lean-proofs) —
  Surface Quasi-Geostrophic regularity (consumes the Kato–Ponce / `Ḣˢ`
  machinery and the `d = 2` lattice-zeta bound).
- [ns-lean-proofs](https://github.com/Brsanch/ns-lean-proofs) —
  Navier–Stokes BLW chain (consumes the spatial-argmax primitive and the
  `d = 3` lattice-zeta bound).
- (Planned) Euler / MHD classical content.

Beyond the Fourier machinery, the package also holds two general
active-scalar primitives shared by both consumers above: a
domain-polymorphic spatial argmax (`ArgmaxFromDecay.lean`) and an
arbitrary-dimension lattice Epstein-zeta bound (`LatticeZeta.lean`).

## Status

**~2800 LOC, CI green.**  Littlewood–Paley decomposition, Bony
paraproduct identity with L² (Parseval) bounds, **quantitative
Ḣˢ-valued Kato–Ponce commutator bounds uniform-in-N** via dyadic-
weighted Cauchy–Schwarz, and homogeneous Sobolev infrastructure
are all in-tree.  The downstream `sqg-lean-proofs` repository
additionally machine-verifies Rellich–Kondrachov compact embedding
`H¹(𝕋²) ⊂⊂ L²` in Fourier form and the inverse Fourier transform
`Lp from Fourier coefficients` via mathlib's `mFourierBasis`.

## Module contents

```
FourierAnalysis/
  ArgmaxFromDecay.lean    -- domain-polymorphic compactness-via-decay
                             spatial argmax: continuous f : X → ℝ on any
                             [TopologicalSpace X] that decays to 0 at the
                             cocompact filter and is positive somewhere
                             attains its global max.
  LatticeZeta.lean        -- arbitrary-dimension lattice Epstein-zeta
                             bound: ∀ finite A ⊆ ℤᵈ\{0}, ∑ ‖a‖⁻ᵖ ≤
                             2·d·3^{d-1}·ζ(p-(d-1)) for d ≥ 1, p > d
                             (ℓ∞ annular shells). Instantiated at d=2
                             (SQG) and d=3 (NS).
  LittlewoodPaley/
    Dyadic.lean           -- 𝕋² = UnitAddTorus (Fin 2), ℓ∞ lattice,
                             dyadic annuli/balls, Fourier projector
                             Δ_N and partial sum S_N, pointwise
                             convergence from mathlib's HasSum.
    Bernstein.lean        -- triangle, Cauchy–Schwarz, explicit
                             4^(N+1) / sqrt forms of the Bernstein
                             bound; Parseval bridge via Summable.
  Paraproduct/
    Defs.lean             -- paraproductPartial N f g,
                             remainderPartial N f g, ordered and
                             filtered sum forms, and Bony's partial
                             decomposition f·g = T_f g + T_g f + R.
    Bounds.lean           -- triangle + Cauchy–Schwarz shell bounds,
                             L² paraproduct + remainder bounds via
                             Parseval, L∞×L² bilinear wrapper.
  KatoPonce/
    Product.lean          -- structural product bounds.
    Commutator.lean       -- partialCommutator N f g with Bony
                             expansion identity, four-piece
                             triangle bound, structural Kato–Ponce,
                             quantitative Ḣˢ-valued bound, and
                             **uniform-in-N fully-uniform bound**
                             via dyadic-weighted Cauchy–Schwarz.
    SobolevEmbedding.lean -- hsSeminormSq, lattice zeta, geometric
                             convergence at s > 1, and the triangle
                             version of Ḣˢ ⊂ L∞.
```

## Downstream consumption

Both `sqg-lean-proofs` and `ns-lean-proofs` require it via git:

```toml
[[require]]
name = "fourier_analysis"
git = "https://github.com/Brsanch/sqg-lean-proofs-fourier.git"
rev = "main"
```

```lean
import FourierAnalysis.KatoPonce.Commutator   -- Ḣˢ / Kato–Ponce (SQG)
import FourierAnalysis.ArgmaxFromDecay        -- spatial argmax (NS + SQG)
import FourierAnalysis.LatticeZeta            -- lattice Epstein-zeta (NS + SQG)
open FourierAnalysis
```

## Build

```bash
lake exe cache get
lake build
```

## License

MIT.
