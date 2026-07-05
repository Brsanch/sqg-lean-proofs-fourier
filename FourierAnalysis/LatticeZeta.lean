-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib

/-!
# Arbitrary-dimension lattice Epstein-zeta bound (shared active-scalar primitive)

For every dimension `d ≥ 1`, real exponent `p > d`, and finite `A ⊆ ℤ^d \ {0}`:

  `∑_{a ∈ A} ‖a‖^{-p} ≤ latticeZetaConstD d p`,

where `‖·‖ = latticeNormD` is the Euclidean norm on `ℤ^d = (Fin d → ℤ)` and

  `latticeZetaConstD d p := 2·d·3^{d-1} · ∑'_{k} k^{-(p-(d-1))}`

(finite because `p > d ⟹ p-(d-1) > 1`, a `p`-series). Proved unconditionally,
zero axioms.

This is the single theorem that both downstream lattice-sum witnesses instantiate:

* **SQG** (`sqg-lean-proofs`): `d = 2`, `p = 2s` (`s > 1`) — the `𝕋²` Riesz /
  Ḣˢ Banach-algebra lattice-zeta constant.
* **NS** (`ns-lean-proofs`): `d = 3`, `p = s` (`s > 3`) — the `𝕋³` periodic
  Biot–Savart torus-correction Epstein-zeta sum.

## Strategy (ℓ∞ annular shells)

Partition `ℤ^d \ {0}` by `ℓ∞`-radius `k`. The shell `{‖·‖_∞ = k}` lies in the
union over the `d` coordinate directions of `{m : |m_i| = k}`, each of size
`2·(2k+1)^{d-1}`, so `|shell k| ≤ 2·d·(2k+1)^{d-1} ≤ 2·d·3^{d-1}·k^{d-1}` (for
`k ≥ 1`), while every shell point has Euclidean norm `≥ k`. Hence the shell sum
is `≤ 2·d·3^{d-1}·k^{-(p-(d-1))}`; summing the disjoint shells over any finite
`A` and comparing with the `tsum` gives the bound.
-/

namespace FourierAnalysis

open scoped BigOperators

variable {d : ℕ}

/-! ### Euclidean lattice norm on `ℤ^d` -/

noncomputable def latticeNormSqD (n : Fin d → ℤ) : ℝ := ∑ i, (n i : ℝ) ^ 2
noncomputable def latticeNormD (n : Fin d → ℤ) : ℝ := Real.sqrt (latticeNormSqD n)

lemma latticeNormD_nonneg (n : Fin d → ℤ) : 0 ≤ latticeNormD n := Real.sqrt_nonneg _

lemma abs_coord_le_latticeNormD (n : Fin d → ℤ) (j : Fin d) :
    |(n j : ℝ)| ≤ latticeNormD n := by
  have h_sq : (n j : ℝ) ^ 2 ≤ latticeNormSqD n :=
    Finset.single_le_sum (f := fun i => (n i : ℝ) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  calc |(n j : ℝ)| = Real.sqrt ((n j : ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (latticeNormSqD n) := Real.sqrt_le_sqrt h_sq
    _ = latticeNormD n := rfl

/-! ### Annular `ℓ∞`-shell in `ℤ^d` -/

noncomputable def annularShellD (k : ℕ) : Finset (Fin d → ℤ) :=
  (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
    (fun m => m ≠ 0 ∧ ∃ i, |m i| = (k : ℤ))

lemma mem_annularShellD_iff (k : ℕ) (m : Fin d → ℤ) :
    m ∈ annularShellD k ↔
      (∀ i, |m i| ≤ (k : ℤ)) ∧ m ≠ 0 ∧ ∃ i, |m i| = (k : ℤ) := by
  unfold annularShellD
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨hIcc, hne, hex⟩; exact ⟨fun i => abs_le.mpr (hIcc i), hne, hex⟩
  · rintro ⟨hmax, hne, hex⟩
    exact ⟨fun i => ⟨(abs_le.mp (hmax i)).1, (abs_le.mp (hmax i)).2⟩, hne, hex⟩

lemma latticeNormD_ge_of_mem (k : ℕ) (m : Fin d → ℤ) (hm : m ∈ annularShellD k) :
    (k : ℝ) ≤ latticeNormD m := by
  rw [mem_annularShellD_iff] at hm
  obtain ⟨_, _, i, hi⟩ := hm
  have h_abs : |(m i : ℝ)| = (k : ℝ) := by
    have : ((|m i| : ℤ) : ℝ) = ((k : ℤ) : ℝ) := by exact_mod_cast hi
    simpa [Int.cast_abs] using this
  calc (k : ℝ) = |(m i : ℝ)| := h_abs.symm
    _ ≤ latticeNormD m := abs_coord_le_latticeNormD m i

/-! ### Cardinality bound: `|shell k| ≤ 2·d·(2k+1)^{d-1}` -/

lemma card_annularShellD_le (k : ℕ) :
    (annularShellD (d := d) k).card ≤ 2 * d * (2 * k + 1) ^ (d - 1) := by
  classical
  -- shell ⊆ ⋃ i, {m : |m i| = k}
  have h_sub : annularShellD (d := d) k ⊆
      Finset.univ.biUnion (fun i : Fin d =>
        (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
          (fun m => |m i| = (k : ℤ))) := by
    intro m hm
    rw [mem_annularShellD_iff] at hm
    obtain ⟨hIcc, _, i, hi⟩ := hm
    rw [Finset.mem_biUnion]
    refine ⟨i, Finset.mem_univ i, ?_⟩
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    exact ⟨fun j => Finset.mem_Icc.mpr (abs_le.mp (hIcc j)), hi⟩
  refine le_trans (Finset.card_le_card h_sub) ?_
  refine le_trans Finset.card_biUnion_le ?_
  -- each single-coordinate slice ≤ 2·(2k+1)^{d-1}
  have h_each : ∀ i : Fin d,
      ((Fintype.piFinset fun _ : Fin d => Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
        (fun m => |m i| = (k : ℤ))).card ≤ 2 * (2 * k + 1) ^ (d - 1) := by
    intro i
    have hsplit :
        (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
            (fun m => |m i| = (k : ℤ))
          = (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
            (fun m => m i = (k : ℤ) ∨ m i = -(k : ℤ)) := by
      apply Finset.filter_congr
      intro m _
      rw [abs_eq (by positivity : (0 : ℤ) ≤ (k : ℤ))]
    rw [hsplit, Finset.filter_or]
    refine le_trans (Finset.card_union_le _ _) ?_
    have hpt : ∀ a : ℤ,
        ((Fintype.piFinset fun _ : Fin d => Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
          (fun m => m i = a)).card ≤ (2 * k + 1) ^ (d - 1) := by
      intro a
      by_cases ha : a ∈ Finset.Icc (-(k : ℤ)) (k : ℤ)
      · rw [Fintype.card_filter_piFinset_eq_of_mem
          (s := fun _ : Fin d => Finset.Icc (-(k : ℤ)) (k : ℤ)) i ha, Finset.prod_const]
        have herase : ((Finset.univ : Finset (Fin d)).erase i).card = d - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
        rw [herase, Int.card_Icc]
        have htoNat : ((k : ℤ) + 1 - -(k : ℤ)).toNat = 2 * k + 1 := by omega
        rw [htoNat]
      · rw [Fintype.filter_piFinset_of_notMem
          (fun _ : Fin d => Finset.Icc (-(k : ℤ)) (k : ℤ)) i a ha, Finset.card_empty]
        positivity
    have h1 := hpt (k : ℤ)
    have h2 := hpt (-(k : ℤ))
    omega
  refine le_trans (Finset.sum_le_sum (fun i _ => h_each i)) (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-! ### Per-shell rpow bound -/

lemma sum_annularShellD_rpow_le {p : ℝ} (hd : 1 ≤ d) (hp : (d : ℝ) < p)
    {k : ℕ} (hk : 1 ≤ k) :
    ∑ m ∈ annularShellD (d := d) k, (latticeNormD m) ^ (-p)
      ≤ (2 * (d : ℝ) * (3 : ℝ) ^ (d - 1)) * (1 / (k : ℝ) ^ (p - ((d : ℝ) - 1))) := by
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have hk_nn : (0 : ℝ) ≤ k := le_of_lt hk_pos
  have hp_nn : (0 : ℝ) ≤ p := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  -- pointwise ‖m‖^{-p} ≤ k^{-p}
  have h_pw : ∀ m ∈ annularShellD (d := d) k, (latticeNormD m) ^ (-p) ≤ (k : ℝ) ^ (-p) := by
    intro m hm
    have h_lb : (k : ℝ) ≤ latticeNormD m := latticeNormD_ge_of_mem k m hm
    have h_pos : 0 < latticeNormD m := lt_of_lt_of_le hk_pos h_lb
    rw [Real.rpow_neg hk_nn, Real.rpow_neg (le_of_lt h_pos)]
    exact inv_anti₀ (Real.rpow_pos_of_pos hk_pos _) (Real.rpow_le_rpow hk_nn h_lb hp_nn)
  -- nat card bound composed with the pow bound
  have h_card_nat : (annularShellD (d := d) k).card
      ≤ 2 * d * 3 ^ (d - 1) * k ^ (d - 1) := by
    refine le_trans (card_annularShellD_le k) ?_
    have hpow : (2 * k + 1) ^ (d - 1) ≤ 3 ^ (d - 1) * k ^ (d - 1) := by
      calc (2 * k + 1) ^ (d - 1) ≤ (3 * k) ^ (d - 1) :=
            Nat.pow_le_pow_left (by omega) _
        _ = 3 ^ (d - 1) * k ^ (d - 1) := by rw [Nat.mul_pow]
    calc 2 * d * (2 * k + 1) ^ (d - 1)
        ≤ 2 * d * (3 ^ (d - 1) * k ^ (d - 1)) := by
          exact Nat.mul_le_mul_left _ hpow
      _ = 2 * d * 3 ^ (d - 1) * k ^ (d - 1) := by ring
  -- combine k^{d-1} · k^{-p} = k^{-(p-(d-1))}
  have h_pow_real : (k : ℝ) ^ (d - 1) * (k : ℝ) ^ (-p) = 1 / (k : ℝ) ^ (p - ((d : ℝ) - 1)) := by
    rw [← Real.rpow_natCast (k : ℝ) (d - 1), ← Real.rpow_add hk_pos]
    have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub hd, Nat.cast_one]
    rw [show ((d - 1 : ℕ) : ℝ) + (-p) = -(p - ((d : ℝ) - 1)) by rw [hcast]; ring]
    rw [Real.rpow_neg hk_nn, inv_eq_one_div]
  have h_card_real : ((annularShellD (d := d) k).card : ℝ)
      ≤ 2 * (d : ℝ) * (3 : ℝ) ^ (d - 1) * (k : ℝ) ^ (d - 1) := by
    have := h_card_nat
    push_cast at this ⊢
    exact_mod_cast this
  calc ∑ m ∈ annularShellD (d := d) k, (latticeNormD m) ^ (-p)
      ≤ ∑ _m ∈ annularShellD (d := d) k, (k : ℝ) ^ (-p) := Finset.sum_le_sum h_pw
    _ = ((annularShellD (d := d) k).card : ℝ) * (k : ℝ) ^ (-p) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (d : ℝ) * (3 : ℝ) ^ (d - 1) * (k : ℝ) ^ (d - 1)) * (k : ℝ) ^ (-p) := by
        apply mul_le_mul_of_nonneg_right h_card_real (Real.rpow_nonneg hk_nn _)
    _ = (2 * (d : ℝ) * (3 : ℝ) ^ (d - 1)) * (1 / (k : ℝ) ^ (p - ((d : ℝ) - 1))) := by
        rw [mul_assoc, h_pow_real]

/-! ### The lattice-zeta constant and the main bound -/

noncomputable def latticeZetaConstD (d : ℕ) (p : ℝ) : ℝ :=
  (2 * (d : ℝ) * (3 : ℝ) ^ (d - 1)) * ∑' (k : ℕ), 1 / ((k : ℝ) ^ (p - ((d : ℝ) - 1)))

lemma latticeZetaConstD_nonneg (d : ℕ) (p : ℝ) : 0 ≤ latticeZetaConstD d p := by
  unfold latticeZetaConstD
  apply mul_nonneg
  · positivity
  · exact tsum_nonneg (fun k => div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-! ### Shell-index function -/

noncomputable def shellOfD (m : Fin d → ℤ) : ℕ :=
  Finset.univ.sup (fun i => (|m i|).toNat)

lemma shellOfD_pos_of_ne_zero (m : Fin d → ℤ) (hm : m ≠ 0) : 1 ≤ shellOfD m := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hm
  have hi' : m i ≠ 0 := hi
  have h1 : 1 ≤ (|m i|).toNat := by have := abs_pos.mpr hi'; omega
  have h2 : (|m i|).toNat ≤ shellOfD m :=
    Finset.le_sup (f := fun j => (|m j|).toNat) (Finset.mem_univ i)
  exact le_trans h1 h2

lemma mem_annularShellD_shellOf (hd : 1 ≤ d) (m : Fin d → ℤ) (hm : m ≠ 0) :
    m ∈ annularShellD (shellOfD m) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [mem_annularShellD_iff]
  refine ⟨?_, hm, ?_⟩
  · intro i
    have h_cast : ((|m i|).toNat : ℤ) = |m i| := Int.toNat_of_nonneg (abs_nonneg _)
    have h_le : (|m i|).toNat ≤ shellOfD m :=
      Finset.le_sup (f := fun j => (|m j|).toNat) (Finset.mem_univ i)
    calc |m i| = ((|m i|).toNat : ℤ) := h_cast.symm
      _ ≤ ((shellOfD m : ℕ) : ℤ) := by exact_mod_cast h_le
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun i => (|m i|).toNat)
    refine ⟨i, ?_⟩
    have h_cast : ((|m i|).toNat : ℤ) = |m i| := Int.toNat_of_nonneg (abs_nonneg _)
    have : shellOfD m = (|m i|).toNat := hi
    rw [this]; exact h_cast.symm

lemma annularShellD_disjoint {k₁ k₂ : ℕ} (hne : k₁ ≠ k₂) :
    Disjoint (annularShellD (d := d) k₁) (annularShellD (d := d) k₂) := by
  rw [Finset.disjoint_left]
  intro m hm1 hm2
  rw [mem_annularShellD_iff] at hm1 hm2
  obtain ⟨hI1, _, i, hi⟩ := hm1
  obtain ⟨hI2, _, j, hj⟩ := hm2
  apply hne
  have hik₂ : |m i| ≤ (k₂ : ℤ) := hI2 i
  have hjk₁ : |m j| ≤ (k₁ : ℤ) := hI1 j
  have hz : (k₁ : ℤ) = (k₂ : ℤ) := by omega
  exact_mod_cast hz

/-- **Main bound (arbitrary dimension `d ≥ 1`).** For `p > d`, every finite
`A ⊆ ℤ^d \ {0}` satisfies `∑_{a ∈ A} ‖a‖^{-p} ≤ latticeZetaConstD d p`.
Unconditional, zero axioms. -/
theorem latticeSum_le_latticeZetaConstD (hd : 1 ≤ d) {p : ℝ} (hp : (d : ℝ) < p)
    (A : Finset (Fin d → ℤ)) (hA0 : (0 : Fin d → ℤ) ∉ A) :
    ∑ a ∈ A, (latticeNormD a) ^ (-p) ≤ latticeZetaConstD d p := by
  classical
  set K : Finset ℕ := A.image shellOfD with hK_def
  have h_sub : A ⊆ K.biUnion (annularShellD (d := d)) := by
    intro m hm
    have hm_ne : m ≠ 0 := fun h => hA0 (h ▸ hm)
    rw [Finset.mem_biUnion]
    exact ⟨shellOfD m, Finset.mem_image.mpr ⟨m, hm, rfl⟩,
      mem_annularShellD_shellOf hd m hm_ne⟩
  have h_nn : ∀ a : Fin d → ℤ, 0 ≤ (latticeNormD a) ^ (-p) :=
    fun a => Real.rpow_nonneg (latticeNormD_nonneg a) _
  have h_ext : ∑ a ∈ A, (latticeNormD a) ^ (-p)
      ≤ ∑ a ∈ K.biUnion (annularShellD (d := d)), (latticeNormD a) ^ (-p) :=
    Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun a _ _ => h_nn a)
  have h_pairwise : (↑K : Set ℕ).PairwiseDisjoint (annularShellD (d := d)) :=
    fun _ _ _ _ hne => annularShellD_disjoint hne
  have h_biUnion :
      ∑ a ∈ K.biUnion (annularShellD (d := d)), (latticeNormD a) ^ (-p)
        = ∑ k ∈ K, ∑ a ∈ annularShellD (d := d) k, (latticeNormD a) ^ (-p) :=
    Finset.sum_biUnion h_pairwise
  rw [h_biUnion] at h_ext
  have h_k_pos : ∀ k ∈ K, 1 ≤ k := by
    intro k hk
    rw [hK_def, Finset.mem_image] at hk
    obtain ⟨m, hm, rfl⟩ := hk
    exact shellOfD_pos_of_ne_zero m (fun h => hA0 (h ▸ hm))
  have h_shell : ∀ k ∈ K,
      ∑ a ∈ annularShellD (d := d) k, (latticeNormD a) ^ (-p)
        ≤ (2 * (d : ℝ) * (3 : ℝ) ^ (d - 1)) * (1 / (k : ℝ) ^ (p - ((d : ℝ) - 1))) :=
    fun k hk => sum_annularShellD_rpow_le hd hp (h_k_pos k hk)
  have h_ssum :
      ∑ k ∈ K, ∑ a ∈ annularShellD (d := d) k, (latticeNormD a) ^ (-p)
        ≤ ∑ k ∈ K, (2 * (d : ℝ) * (3 : ℝ) ^ (d - 1)) * (1 / (k : ℝ) ^ (p - ((d : ℝ) - 1))) :=
    Finset.sum_le_sum h_shell
  have h_summ : Summable (fun k : ℕ => 1 / ((k : ℝ) ^ (p - ((d : ℝ) - 1)))) := by
    rw [Real.summable_one_div_nat_rpow]; linarith
  have h_nn_f : ∀ k : ℕ, 0 ≤ 1 / ((k : ℝ) ^ (p - ((d : ℝ) - 1))) :=
    fun k => div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have h_tsum : ∑ k ∈ K, 1 / ((k : ℝ) ^ (p - ((d : ℝ) - 1)))
      ≤ ∑' (k : ℕ), 1 / ((k : ℝ) ^ (p - ((d : ℝ) - 1))) :=
    h_summ.sum_le_tsum K (fun k _ => h_nn_f k)
  have hc_nn : (0 : ℝ) ≤ 2 * (d : ℝ) * (3 : ℝ) ^ (d - 1) := by positivity
  calc ∑ a ∈ A, (latticeNormD a) ^ (-p)
      ≤ ∑ k ∈ K, ∑ a ∈ annularShellD (d := d) k, (latticeNormD a) ^ (-p) := h_ext
    _ ≤ ∑ k ∈ K, (2 * (d : ℝ) * (3 : ℝ) ^ (d - 1)) * (1 / (k : ℝ) ^ (p - ((d : ℝ) - 1))) := h_ssum
    _ = (2 * (d : ℝ) * (3 : ℝ) ^ (d - 1)) * ∑ k ∈ K, 1 / ((k : ℝ) ^ (p - ((d : ℝ) - 1))) := by
        rw [Finset.mul_sum]
    _ ≤ (2 * (d : ℝ) * (3 : ℝ) ^ (d - 1)) * ∑' (k : ℕ), 1 / ((k : ℝ) ^ (p - ((d : ℝ) - 1))) :=
        mul_le_mul_of_nonneg_left h_tsum hc_nn
    _ = latticeZetaConstD d p := by rw [latticeZetaConstD]

end FourierAnalysis
