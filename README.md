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

## Status — SKELETON

All source files are placeholder stubs.  The development plan is
documented in each file's header comment.

**Total planned content:** ~1500 LOC across three major modules.

## Module layout

```
FourierAnalysis.lean
FourierAnalysis/
  LittlewoodPaley.lean              -- aggregator
  LittlewoodPaley/
    Dyadic.lean                     -- Δ_N, S_N, L^p bounds  (~600 LOC)
    Bernstein.lean                  -- Bernstein inequality  (~150 LOC)
  Paraproduct.lean                  -- aggregator
  Paraproduct/
    Defs.lean                       -- T_f g, R(f,g), Bony id (~200 LOC)
    Bounds.lean                     -- three classical bounds (~400 LOC)
  KatoPonce.lean                    -- aggregator
  KatoPonce/
    Product.lean                    -- Kato–Ponce product     (~200 LOC)
    Commutator.lean                 -- Kato–Ponce commutator  (~500 LOC)
    SobolevEmbedding.lean           -- Ḣˢ ⊂ L∞ for s > d/2    (~200 LOC)
```

## Downstream consumption

```toml
# sqg-lean-proofs/lakefile.toml
[[require]]
name = "fourier_analysis"
path = "../sqg-lean-proofs-fourier"  # or git URL
```

```lean
-- downstream usage
import FourierAnalysis.KatoPonce.Commutator
open FourierAnalysis

-- kato_ponce_commutator : ‖[Jˢ, f·∇]g‖_{L²} ≤ …
```

## Build

```bash
lake exe cache get
lake build
```

## License

MIT.
