-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib

/-!
# Spatial argmax existence from decay-at-infinity (shared active-scalar primitive)

A continuous function `f : X → ℝ` on **any** topological space `X` that tends to
`0` at the `cocompact` filter and is strictly positive somewhere attains its
global maximum. This is the **compactness-via-decay** lemma that every
active-scalar regularity argument needs to produce a spatial argmax of a
sup-normed field (e.g. `|ω|²` for 3D Navier–Stokes, `|∇θ|²` for SQG, a level-set
curvature extremum, …).

It lives in this shared package (rather than in any one downstream repo) because
it is genuinely domain-polymorphic: the proof uses only `cocompact`,
`isCompact_singleton`, and `IsCompact.exists_isMaxOn`, so it requires nothing
beyond `[TopologicalSpace X]`. Downstream `require`rs (`sqg-lean-proofs`,
`ns-lean-proofs`, and future Euler/MHD work) instantiate `X` at their own
domain (`Fin 3 → ℝ`, a torus `𝕋ᵈ`, `ℝᵈ`, …) and add the field-specific
specialization on top.

## Strategy

* From `Tendsto f (cocompact X) (𝓝 0)`: outside some compact set `K`,
  `f < f y₀ / 2`.
* `K ∪ {y₀}` is compact and nonempty.
* `IsCompact.exists_isMaxOn` gives a max `xStar` on `K ∪ {y₀}`.
* `f xStar ≥ f y₀ > f y₀ / 2 > f y` for `y ∉ K`, so `xStar` is the global max.
-/

namespace FourierAnalysis

open Filter Topology

/-- **Spatial argmax from decay at infinity (continuous case).**

    Given a continuous `f : X → ℝ` on any topological space `X` that tends to `0`
    at the `cocompact` filter and is strictly positive at some `y₀`, there exists
    `xStar : X` at which `f` achieves its maximum over the whole space.

    Domain-polymorphic: only `[TopologicalSpace X]` is required. The
    strict-positivity hypothesis ensures the global max is strictly positive
    (hence not attained "at infinity" where `f → 0`). -/
theorem exists_argmax_of_continuous_tendsto_zero
    {X : Type*} [TopologicalSpace X]
    {f : X → ℝ}
    (hf_cont : Continuous f)
    (hf_decay : Tendsto f (cocompact X) (𝓝 0))
    {y₀ : X} (hy₀_pos : 0 < f y₀) :
    ∃ xStar : X, ∀ y : X, f y ≤ f xStar := by
  -- Step 1: from the decay, find a compact `K` with `f < f y₀ / 2` outside it.
  have h_eps : 0 < f y₀ / 2 := half_pos hy₀_pos
  have h_decay_form :
      ∀ᶠ y in cocompact X, |f y - 0| < f y₀ / 2 := by
    have := (Metric.tendsto_nhds.mp hf_decay) (f y₀ / 2) h_eps
    simpa using this
  rw [Filter.eventually_iff] at h_decay_form
  rw [Filter.mem_cocompact] at h_decay_form
  obtain ⟨K, hK_cpt, hK_sub⟩ := h_decay_form
  -- Step 2: `K ∪ {y₀}` is compact and nonempty.
  have hKy₀_cpt : IsCompact (K ∪ {y₀}) := hK_cpt.union isCompact_singleton
  have hKy₀_ne : (K ∪ {y₀}).Nonempty := ⟨y₀, Or.inr rfl⟩
  -- Step 3: max on `K ∪ {y₀}` exists by compactness + continuity.
  obtain ⟨xStar, hxStar_in, hxStar_max⟩ :=
    hKy₀_cpt.exists_isMaxOn hKy₀_ne hf_cont.continuousOn
  refine ⟨xStar, ?_⟩
  intro y
  by_cases hy_in : y ∈ K ∪ {y₀}
  · exact hxStar_max hy_in
  · have hy_notin_K : y ∉ K := fun h => hy_in (Or.inl h)
    have hy_in_compl : y ∈ (Kᶜ : Set X) := hy_notin_K
    have h_y_decay : |f y - 0| < f y₀ / 2 := hK_sub hy_in_compl
    have h_fy_lt : f y < f y₀ / 2 := by
      have := abs_lt.mp h_y_decay
      linarith
    have h_fy₀_le : f y₀ ≤ f xStar := hxStar_max (Or.inr rfl)
    linarith

end FourierAnalysis
