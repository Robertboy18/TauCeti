/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Regularity of the lifted directional derivative

Let `f` be a `C^(m+1)` map from an open subset `U` of a normed space `F` into a manifold `M`.
Fixing a direction `ξ : F`, the map sending `z ∈ U` to the tangent vector `df_z ξ` at `f z`, seen
as a point of the tangent bundle `TM`, is `C^m` on `U`.  This is the bundled directional derivative
`ContMDiff.contMDiff_tangentMap` restricted to the constant section `z ↦ (z, ξ)` of `TF = F × F`,
with the within-set derivative replaced by the unrestricted one because `U` is open.

The typical use is a family of curves `f (s, t)` in `M`: the partial velocities `∂f/∂s` and
`∂f/∂t`, lifted to `TM`, inherit one degree of regularity less than `f`, so that smooth functions
of them on `TM`, such as a Riemannian inner product, are as regular as one expects.

## Main results

* `ContMDiffOn.contMDiffOn_mk_mfderiv_apply`: the lifted directional derivative of a `C^(m+1)`
  map on an open set is `C^m` there.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The constant section `z ↦ (z, ξ)` of the tangent bundle of a normed space is analytic. -/
private theorem contMDiff_mk_const (ξ : F) :
    ContMDiff 𝓘(𝕜, F) 𝓘(𝕜, F).tangent ω
      (fun z : F ↦ (TotalSpace.mk' F z ξ : TangentBundle 𝓘(𝕜, F) F)) := by
  intro z
  rw [contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_id, ?_⟩
  refine (contMDiffAt_const (c := ξ)).congr_of_eventuallyEq ?_
  filter_upwards with r
  rw [trivializationAt_model_space_apply]

end TauCeti.Manifold

namespace ContMDiffOn

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **The lifted directional derivative of a `C^(m+1)` map is `C^m`.** If `f` is `C^n` on an open
set `U` of a normed space and `m + 1 ≤ n`, then for every fixed direction `ξ` the map
`z ↦ (f z, df_z ξ)` into the tangent bundle is `C^m` on `U`. -/
theorem contMDiffOn_mk_mfderiv_apply {f : F → M} {U : Set F} {m n : ℕ∞ω}
    (hf : ContMDiffOn 𝓘(𝕜, F) I n f U) (hmn : m + 1 ≤ n) (hU : IsOpen U) (ξ : F) :
    ContMDiffOn 𝓘(𝕜, F) I.tangent m
      (fun z ↦ TotalSpace.mk' E (f z) (mfderiv 𝓘(𝕜, F) I f z ξ)) U := by
  have htangent := hf.contMDiffOn_tangentMapWithin hmn hU.uniqueMDiffOn
  have hcomp := htangent.comp
    ((TauCeti.Manifold.contMDiff_mk_const (𝕜 := 𝕜) ξ).contMDiffOn.of_le le_top)
    (fun z hz ↦ hz)
  refine hcomp.congr fun z hz ↦ ?_
  simp only [Function.comp_apply, tangentMapWithin, mfderivWithin_of_isOpen hU hz]

end ContMDiffOn

end
