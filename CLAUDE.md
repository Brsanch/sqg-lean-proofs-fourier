# sqg-lean-proofs-fourier — workflow notes

Lessons migrated from the upstream `sqg-lean-proofs` work.  Read before
starting any Lean editing session.

## Platform / build

- **No local builds.**  The host machine's apfsd will kernel-panic under
  leantar bursts (`lake exe cache get`) or parallel `lake build`.  CI is
  the only compilation path.  Do not run `lake build`, `lake env lean`,
  or `lake exe cache get` locally.
- **CI flow.**  Edit → commit → push → `gh run view <id> --log-failed` →
  repeat.  Typical build <4 min on warm cache.
- **Toolchain.** `leanprover/lean4:v4.29.0`, mathlib `v4.29.0`.  `omega`
  handles `Int.natAbs` and `Nat.max` at this version.

## Diagnose BEFORE bumping heartbeats

If CI reports `(deterministic) timeout at whnf, maximum number of
heartbeats (N) has been reached`, add these three lines above the
failing declaration and push:

```lean
set_option maxHeartbeats 400000 in
set_option diagnostics true in
set_option diagnostics.threshold 100 in
theorem foo ... := ...
```

Read the `[reduction]` counts literally.  Declarations unfolded 100k+
times ARE the loop — patch those specific names.

Common root causes:

| Diagnostic signature | Root cause | Fix |
|---|---|---|
| `Int.rec` / `Nat.rec` / `List.range` at millions | Finset/Multiset with symbolic index | `attribute [local irreducible] myDef` |
| `dite` + `decidable_of_iff` + `Multiset.decidableForallMultiset` at 100k+ | DecidableEq synthesis walking underlying Multiset | Mark the Prop-level predicate locally irreducible |
| One instance 50k+ uses | Instance-search loop | Explicit instance at call site |

**Do NOT** iterate on `maxHeartbeats` bumps.  Each is a wasted CI cycle.

## DecidableEq and `Fin 2 → ℤ`

`[DecidableEq (Fin 2 → ℤ)]` as an explicit theorem parameter introduces
a fresh `inst✝` that is propositionally but not definitionally equal to
the default `decidablePiFintype` used at structure-field elaboration.
Symptom: `isDefEq` timeout at `.bound` / `.field` applications on a
consuming theorem.

**Default rule:** when a theorem consumes a structure field whose type
mentions a `DecidableEq`-parametrised helper (e.g. `trigPolyProduct`,
`modeConvolution`, any `∑ k ∈ ...` over `Fin d → ℤ`), do NOT add
`[DecidableEq (Fin d → ℤ)]` to the theorem signature.  Use `classical`
in the body instead — default instance synthesis then picks
`decidablePiFintype` uniformly at every use site.

`convert` (not `exact`) at the leaf spot handles any residual
instance-mismatch subsingleton-equal cases.

## Tactic patterns that bit the dev loop

- **`Finset.Ioo` / `Fintype.piFinset`** pull in classical ordering →
  any `def` built on them must be `noncomputable`.  `def lInfBall` and
  `def dyadicAnnulus` are both noncomputable in `Dyadic.lean`.
- **`pow_succ` matches the OUTERMOST `^`** first.  To unfold an inner
  `2^(m+1)`, use `rw [pow_succ (a := 2) (n := m)]` or an intermediate
  `have h : (2:ℕ)^(m+1) = 2^m * 2 := pow_succ 2 m`.
- **`(2:ℕ)^2 = 4`** is *not* `rfl` at a calc-step boundary under
  mathlib's `Monoid.npow`.  Use `norm_num` or an explicit
  `show (2:ℕ)^2 = 4 from rfl` inside the tactic block.
- **`ring` works on `ℕ`** for polynomial identities like
  `(x * 2)^2 = x^2 * 4`, treating `2^m` as a variable.  Prefer `ring`
  over hand-chasing `mul_pow` / `pow_succ` sequences.
- **`omega` auto-destructures conjunctions in the goal** but NOT
  always in hypotheses.  If `omega` fails on `h0 : A ∧ B`, first
  `obtain ⟨h0l, h0r⟩ := h0`.
- **`Fin.forall_fin_two`** converts `∀ i : Fin 2, P i` into
  `P 0 ∧ P 1`, after which `omega` sees everything.  Use instead of
  `fin_cases i` inside iff proofs — `fin_cases` leaves the goal in a
  β-reduced form omega can't always read (`k ((fun i ↦ i) ⟨0, _⟩)`).

## mathlib name traps (v4.29.0)

- `memℓp_gen_iff` — correct name for
  `Memℓp f p ↔ Summable (fun i => ‖f i‖ ^ p.toReal)`.  NOT
  `memℓp_two_iff_summable_sq_norm` (doesn't exist).  Apply with `.mpr`,
  not `rw`.
- `Lp.coeFn_sub f g` — a.e. pointwise, not point-equality.  Use
  `filter_upwards` + `integral_congr_ae` for Lp-integral manipulation.
- `mFourierCoeffLM` — the `LinearMap` form; `map_sub` works on this,
  not on `mFourierCoeff` directly.
- `ENNReal` ASCII parses cleanly; the Unicode `ℝ≥0∞` can trigger
  tokenization + instance-synthesis failures.
- `ENNReal.toReal_ofNat` — simplifies `(n : ENNReal).toReal = (n : ℝ)`
  for numeric literals before `norm_num`.

## Workflow rules

- **One push per narrow change.**  Don't bundle unrelated edits.
- **Read the error FIRST.**  The usual failure is an elementary pattern
  mismatch visible from the `error:` lines — no need to spawn a
  diagnostic for those.  Diagnostics are for *timeouts*, not for "rw
  failed" or "unsolved goal after straightforward tactic".
- **Don't restructure blind.**  Unbundling structures, splitting
  theorems, renaming locals without diagnostic data is a guessing game
  that burns CI minutes.
- **Mathlib naming is case-sensitive and sometimes surprising.**  Check
  with `Grep` before guessing.
