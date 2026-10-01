/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The product decomposition along a linear isometry

A linear isometry `f : E →ₗᵢ[ℝ] F` into a finite-dimensional inner product space identifies `F`
with the product of `E` and the orthogonal complement of the range of `f`, by
`(u, w) ↦ f u + w`. Read through this identification, `f` itself is the inclusion `u ↦ (u, 0)` of
the first factor. This is the normal form in which Mathlib's `Manifold.IsImmersionAt` asks for a
map to be written in charts, so this decomposition is what exhibits a linear isometry, and the maps
of spheres and balls it induces, as immersions.

A linear isometry also carries the orthogonal complement of a vector into the orthogonal
complement of its image, compatibly with the orthogonal projections; this is how it transports
the stereographic charts of unit spheres.

## Main definitions

* `LinearIsometry.prodOrthogonalRangeEquiv`: the continuous linear equivalence
  `E × (range f)ᗮ ≃L[ℝ] F` given by `(u, w) ↦ f u + w`.
* `LinearIsometry.orthogonalComplementSingletonMap`: the restriction of a linear isometry to a map
  `(ℝ ∙ v)ᗮ →ₗᵢ[ℝ] (ℝ ∙ w)ᗮ`, where `w` is the image of `v`.

## Main results

* `LinearIsometry.starProjection_orthogonalComplement_singleton_map`: a linear isometry commutes
  with the orthogonal projections onto the complements of a vector and of its image.
-/

public section

noncomputable section

namespace LinearIsometry

open Module

open scoped InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

/-- A linear isometry commutes with the orthogonal projections onto the orthogonal complement of a
vector `v` and onto the orthogonal complement of its image `w`. -/
theorem starProjection_orthogonalComplement_singleton_map (f : E →ₗᵢ[ℝ] F) {v : E} {w : F}
    (hw : f v = w) (y : E) : (ℝ ∙ w)ᗮ.starProjection (f y) = f ((ℝ ∙ v)ᗮ.starProjection y) := by
  subst hw
  simp only [Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton,
    f.inner_map_map, f.norm_map, map_sub, map_smul]

/-- A linear isometry `f` maps the orthogonal complement of `v` into the orthogonal complement of
`f v`. -/
theorem map_mem_orthogonal_singleton (f : E →ₗᵢ[ℝ] F) {v : E} {w : F} (hw : f v = w) {y : E}
    (hy : y ∈ (ℝ ∙ v)ᗮ) : f y ∈ (ℝ ∙ w)ᗮ := by
  subst hw
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hy ⊢
  rwa [f.inner_map_map]

/-- The restriction of a linear isometry `f` to a linear isometry from the orthogonal complement
of `v` to the orthogonal complement of its image `w`. -/
def orthogonalComplementSingletonMap (f : E →ₗᵢ[ℝ] F) {v : E} {w : F} (hw : f v = w) :
    (ℝ ∙ v)ᗮ →ₗᵢ[ℝ] (ℝ ∙ w)ᗮ where
  toLinearMap := (f.toLinearMap.domRestrict (ℝ ∙ v)ᗮ).codRestrict (ℝ ∙ w)ᗮ fun y ↦
    f.map_mem_orthogonal_singleton hw y.2
  norm_map' y := f.norm_map y

@[simp]
theorem coe_orthogonalComplementSingletonMap_apply (f : E →ₗᵢ[ℝ] F) {v : E} {w : F} (hw : f v = w)
    (y : (ℝ ∙ v)ᗮ) : (f.orthogonalComplementSingletonMap hw y : F) = f y :=
  (rfl)

variable [FiniteDimensional ℝ F]

/-- A linear isometry `f : E →ₗᵢ[ℝ] F` into a finite-dimensional space identifies the product of
`E` with the orthogonal complement of the range of `f` with `F`, by `(u, w) ↦ f u + w`. -/
def prodOrthogonalRangeEquiv (f : E →ₗᵢ[ℝ] F) :
    (E × (LinearMap.range f.toLinearMap)ᗮ) ≃L[ℝ] F :=
  haveI : FiniteDimensional ℝ E := FiniteDimensional.of_injective f.toLinearMap f.injective
  ((f.equivRange.toLinearEquiv.prodCongr (LinearEquiv.refl ℝ _)).trans
    (Submodule.prodEquivOfIsCompl _ _
      (Submodule.isCompl_orthogonal _))).toContinuousLinearEquiv

@[simp]
theorem prodOrthogonalRangeEquiv_apply (f : E →ₗᵢ[ℝ] F) (u : E)
    (w : (LinearMap.range f.toLinearMap)ᗮ) : f.prodOrthogonalRangeEquiv (u, w) = f u + w := by
  rfl

/-- Through `LinearIsometry.prodOrthogonalRangeEquiv`, the linear isometry `f` is the inclusion of
the first factor. -/
theorem prodOrthogonalRangeEquiv_apply_zero (f : E →ₗᵢ[ℝ] F) (u : E) :
    f.prodOrthogonalRangeEquiv (u, 0) = f u := by
  simp

end LinearIsometry
