# Fourier Analysis — Lean 4 Classical Content

A Lean 4 + mathlib formalization of classical Fourier analysis on 𝕋²:
Littlewood–Paley decomposition, Bony paraproducts, Kato–Ponce fractional
Leibniz and commutator estimates, and the Sobolev embedding `Ḣˢ ⊂ L∞`
for `s > d/2`.

This package is **upstream of several PDE projects**:
- [sqg-lean-proofs](https://github.com/Brsanch/sqg-lean-proofs) —
  Surface Quasi-Geostrophic regularity.
- (Planned) Navier–Stokes regularity classical content.
- (Planned) Euler regularity classical content.
- (Planned) MHD classical content.

## Status

**~1880 LOC, CI green.**  Littlewood–Paley decomposition, Bony
paraproduct identity with L² bounds, Kato–Ponce commutator at the
partial level, and homogeneous Sobolev infrastructure are all
in-tree.  Remaining work targets the L² Kato–Ponce commutator
quantitative bound (Coifman–Meyer–style) and downstream plumbing
in consuming projects.

## Module contents

```
FourierAnalysis/
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
    Commutator.lean       -- partialCommutator N f g with
                             Bony expansion identity, four-piece
                             triangle bound, and structural
                             Kato–Ponce estimate combining the
                             paraproduct + swap + remainder pieces.
    SobolevEmbedding.lean -- hsSeminormSq, lattice zeta, geometric
                             convergence at s > 1, and the triangle
                             version of Ḣˢ ⊂ L∞.
```

## Downstream consumption

```toml
# sqg-lean-proofs/lakefile.toml
[[require]]
name = "fourier_analysis"
path = "../sqg-lean-proofs-fourier"  # or git URL
```

```lean
import FourierAnalysis.KatoPonce.Commutator
open FourierAnalysis
```

## Build

```bash
lake exe cache get
lake build
```

## License

MIT.
