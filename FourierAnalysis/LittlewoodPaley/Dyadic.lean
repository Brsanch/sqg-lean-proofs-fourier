/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under MIT license.
Authors: Bryan Sanchez

Dyadic Fourier projectors on 𝕋².

**Contents (planned, ~600 LOC):**
- `dyadicAnnulus N : Finset (Fin 2 → ℤ)` — lattice annulus
  `{k : 2^{N-1} ≤ ‖k‖_{ℓ∞} < 2^N}` (with base case `N = 0` → `{0}`).
- `lpProjector N f` — Fourier truncation of `f ∈ L²(𝕋²)` to
  `dyadicAnnulus N`.
- `lpPartialSum N f := Σ_{k ≤ N} lpProjector k f`.
- L^p bounds `‖Δ_N f‖_{L^p} ≤ C · ‖f‖_{L^p}` for `p ∈ [1, ∞]`.
- Fourier-side computation: `(Δ_N f)̂(m) = 1_{m ∈ annulus N} · f̂(m)`.

### Phase 1 — this file (current)

- ℓ∞ norm on the integer lattice `ℤ²`.
- Open ℓ∞ balls `lInfBall R = {k : ‖k‖_∞ < R}` as `Finset`s.
- Dyadic annuli as set differences of balls.
- Membership characterisation and basic cardinality bound.

Measure-theoretic structure on `𝕋² = Fin 2 → AddCircle (1 : ℝ)` is
inherited from mathlib's `Pi.measureSpace` + `AddCircle.measureSpace`;
downstream files need only `open scoped FourierAnalysis` to pick up
the `𝕋²` notation.
-/

import Mathlib

namespace FourierAnalysis

/-! ### 2D torus notation -/

/-- The 2D flat torus `𝕋² = (ℝ / ℤ)²`.  Measure-theoretic structure is
inherited from mathlib (product of Haar on `AddCircle (1 : ℝ)`). -/
scoped notation "𝕋²" => Fin 2 → AddCircle (1 : ℝ)

/-! ### ℓ∞ norm on ℤ² -/

/-- ℓ∞ norm of a 2D integer lattice point, valued in `ℕ`. -/
def lInfNorm (k : Fin 2 → ℤ) : ℕ :=
  max (k 0).natAbs (k 1).natAbs

@[simp] lemma lInfNorm_zero : lInfNorm (0 : Fin 2 → ℤ) = 0 := by
  simp [lInfNorm]

lemma lInfNorm_eq_zero {k : Fin 2 → ℤ} (h : lInfNorm k = 0) : k = 0 := by
  have h0 : k 0 = 0 := by
    have hn0 : (k 0).natAbs = 0 := by unfold lInfNorm at h; omega
    exact Int.natAbs_eq_zero.mp hn0
  have h1 : k 1 = 0 := by
    have hn1 : (k 1).natAbs = 0 := by unfold lInfNorm at h; omega
    exact Int.natAbs_eq_zero.mp hn1
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-! ### Lattice ℓ∞ balls on ℤ² -/

/-- Open ℓ∞ ball on `ℤ²`: `{k : ‖k‖_∞ < R}`, as a `Finset`. -/
noncomputable def lInfBall (R : ℕ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Ioo (-(R : ℤ)) R)

lemma mem_lInfBall {R : ℕ} {k : Fin 2 → ℤ} :
    k ∈ lInfBall R ↔ lInfNorm k < R := by
  simp only [lInfBall, Fintype.mem_piFinset, Finset.mem_Ioo, lInfNorm, max_lt_iff,
             Fin.forall_fin_two]
  omega

@[simp] lemma lInfBall_zero : lInfBall 0 = ∅ := by
  ext k; simp [mem_lInfBall]

lemma lInfBall_subset {R S : ℕ} (hRS : R ≤ S) : lInfBall R ⊆ lInfBall S := by
  intro k hk
  rw [mem_lInfBall] at hk ⊢
  omega

/-! ### Dyadic annuli on ℤ² -/

/-- Dyadic annulus on the integer lattice `ℤ²`.

- For `N = 0`: the low-frequency block `{k : ‖k‖_∞ < 1} = {0}`.
- For `N ≥ 1`: the shell `{k : 2^{N-1} ≤ ‖k‖_∞ < 2^N}`.
-/
noncomputable def dyadicAnnulus : ℕ → Finset (Fin 2 → ℤ)
  | 0     => {0}
  | N + 1 => lInfBall (2 ^ (N + 1)) \ lInfBall (2 ^ N)

lemma mem_dyadicAnnulus_zero {k : Fin 2 → ℤ} :
    k ∈ dyadicAnnulus 0 ↔ k = 0 := by
  simp [dyadicAnnulus]

lemma mem_dyadicAnnulus_succ {N : ℕ} {k : Fin 2 → ℤ} :
    k ∈ dyadicAnnulus (N + 1) ↔ 2 ^ N ≤ lInfNorm k ∧ lInfNorm k < 2 ^ (N + 1) := by
  simp only [dyadicAnnulus, Finset.mem_sdiff, mem_lInfBall, not_lt]
  tauto

/-- Dyadic shells of different indices are disjoint. -/
lemma dyadicAnnulus_disjoint_of_lt {M N : ℕ} (hMN : M < N) :
    Disjoint (dyadicAnnulus M) (dyadicAnnulus N) := by
  rw [Finset.disjoint_left]
  intro k hkM hkN
  rcases M with _ | M'
  · -- M = 0 ⇒ k = 0; shell N ≥ 1 requires ‖k‖_∞ ≥ 2^{N-1} ≥ 1, contradiction.
    rw [mem_dyadicAnnulus_zero] at hkM
    subst hkM
    rcases N with _ | N'
    · exact absurd hMN (lt_irrefl 0)
    · rw [mem_dyadicAnnulus_succ, lInfNorm_zero] at hkN
      have hpow : 1 ≤ 2 ^ N' := Nat.one_le_two_pow
      omega
  · rcases N with _ | N'
    · exact absurd hMN (Nat.not_lt_zero _)
    · rw [mem_dyadicAnnulus_succ] at hkM hkN
      have hpow : (2 : ℕ) ^ (M' + 1) ≤ 2 ^ N' := by
        apply Nat.pow_le_pow_right (by norm_num)
        omega
      omega

/-- Cardinality bound: a dyadic shell is contained in a ball. -/
lemma card_dyadicAnnulus_succ_le (N : ℕ) :
    (dyadicAnnulus (N + 1)).card ≤ (lInfBall (2 ^ (N + 1))).card := by
  refine Finset.card_le_card ?_
  intro k hk
  simp only [dyadicAnnulus, Finset.mem_sdiff] at hk
  exact hk.1

/-! ### Lattice cardinality closed forms

Each coordinate factor `Finset.Ioo (-R, R) ⊂ ℤ` has cardinality `2R - 1`
for `R ≥ 1` (and `0` for `R = 0`).  The 2D ball is the product. -/

lemma card_lInfBall_le (R : ℕ) : (lInfBall R).card ≤ (2 * R) ^ 2 := by
  rw [lInfBall, Fintype.card_piFinset, Fin.prod_univ_two]
  have h : (Finset.Ioo (-(R : ℤ)) R).card ≤ 2 * R := by
    rw [Int.card_Ioo]
    omega
  calc (Finset.Ioo (-(R : ℤ)) R).card * (Finset.Ioo (-(R : ℤ)) R).card
      ≤ (2 * R) * (2 * R) := Nat.mul_le_mul h h
    _ = (2 * R) ^ 2 := by ring

/-- Auxiliary: `(2^m)^2 = 4^m` in ℕ. -/
private lemma two_pow_sq_eq_four_pow (m : ℕ) : ((2 : ℕ) ^ m) ^ 2 = 4 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have step : ((2 : ℕ) ^ (m + 1)) ^ 2 = ((2 : ℕ) ^ m) ^ 2 * 4 := by
        rw [pow_succ]; ring
      rw [step, ih, ← pow_succ]

/-- Dyadic shell size is `O(4^N)` uniformly (needed for Bernstein). -/
lemma card_dyadicAnnulus_succ_le_four_pow (N : ℕ) :
    (dyadicAnnulus (N + 1)).card ≤ 4 * 4 ^ (N + 1) := by
  calc (dyadicAnnulus (N + 1)).card
      ≤ (lInfBall (2 ^ (N + 1))).card := card_dyadicAnnulus_succ_le N
    _ ≤ (2 * 2 ^ (N + 1)) ^ 2 := card_lInfBall_le _
    _ = 4 * 4 ^ (N + 1) := by
        rw [mul_pow, two_pow_sq_eq_four_pow]; norm_num

end FourierAnalysis
