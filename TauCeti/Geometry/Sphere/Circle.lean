/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Complex.Circle
public import TauCeti.Geometry.Sphere.LinearIsometry

/-!
# Identification of the unit circle in two-dimensional Euclidean space with the complex circle

The unit sphere `sphere (0 : EuclideanSpace ℝ (Fin 2)) 1` is isometric to Mathlib's complex unit
circle `Circle = {z : ℂ | ‖z‖ = 1}` via the standard orthonormal basis isometry
`Complex.orthonormalBasisOneI`.

The circle is also the boundary of the closed unit disc of `ℂ`; `Circle.toClosedBall` records
that inclusion, the boundary parametrization along which a knot presentation is read off a slice
disc.

## Main declarations

* `Circle.toClosedBall`: a point of the unit circle, as a point of the closed unit disc of `ℂ`.
* `TauCeti.EuclideanSpace.sphereIsometryEquivCircle`: the isometry equivalence between the unit
  circle in two-dimensional Euclidean space and `Circle`.
* `TauCeti.EuclideanSpace.sphereHomeomorphCircle`: the homeomorphism between the unit circle in
  two-dimensional Euclidean space and `Circle`.
* `TauCeti.EuclideanSpace.coe_sphereIsometryEquivCircle_apply`: forward evaluation of the
  isometry equivalence on underlying points.
* `TauCeti.EuclideanSpace.coe_sphereHomeomorphCircle_apply`: forward evaluation of the
  homeomorphism on underlying points.
* `TauCeti.EuclideanSpace.coe_sphereIsometryEquivCircle_symm_apply`: backward evaluation of the
  isometry equivalence on underlying points.
* `TauCeti.EuclideanSpace.coe_sphereHomeomorphCircle_symm_apply`: backward evaluation of the
  homeomorphism on underlying points.
* `TauCeti.EuclideanSpace.sphereIsometryEquivCircle_neg`: the isometry equivalence negates under
  the antipodal map.
* `TauCeti.EuclideanSpace.sphereHomeomorphCircle_neg`: the homeomorphism negates under
  the antipodal map.
-/

public section

namespace Circle

open Metric

/-- A point of the unit circle, as a point of the closed unit disc of `ℂ`: the inclusion of the
circle as the boundary of the disc. -/
def toClosedBall (z : Circle) : closedBall (0 : ℂ) 1 :=
  ⟨z, mem_closedBall_zero_iff.2 (norm_coe z).le⟩

@[simp]
theorem coe_toClosedBall (z : Circle) : (z.toClosedBall : ℂ) = z :=
  (rfl)

theorem toClosedBall_injective : Function.Injective toClosedBall := fun z w h ↦
  ext (by simpa using Subtype.ext_iff.1 h)

theorem continuous_toClosedBall : Continuous toClosedBall :=
  continuous_induced_rng.2 continuous_subtype_val

/-- The points of the closed unit disc of `ℂ` of norm one are exactly the points of the circle. -/
theorem range_toClosedBall :
    Set.range toClosedBall = {x : closedBall (0 : ℂ) 1 | ‖(x : ℂ)‖ = 1} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    simp
  · intro hx
    exact ⟨⟨x, mem_sphere_zero_iff_norm.2 hx⟩, Subtype.ext rfl⟩

end Circle

namespace TauCeti

open Metric
open scoped EuclideanSpace

namespace EuclideanSpace

noncomputable section

/-- The unit circle in two-dimensional real Euclidean space is isometric to Mathlib's complex
unit circle `Circle`.

Note: `Circle` is by definition the unit sphere `sphere (0 : ℂ) 1` in `ℂ`
(via `Submonoid.unitSphere ℂ`), so the metric and topological instances agree definitionally
with those on `sphere (0 : ℂ) 1`. The type ascription `Circle` is therefore definitionally equal
to `sphere (0 : ℂ) 1`. -/
def sphereIsometryEquivCircle :
    sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ᵢ Circle :=
  LinearIsometryEquiv.unitSphereIsometryEquiv Complex.orthonormalBasisOneI.repr.symm

/-- The unit circle in two-dimensional real Euclidean space is homeomorphic to Mathlib's complex
unit circle `Circle`. -/
def sphereHomeomorphCircle :
    sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ Circle :=
  sphereIsometryEquivCircle.toHomeomorph

/-- The Euclidean-circle isometry is the standard orthonormal-coordinate isometry on
underlying points. -/
@[simp]
lemma coe_sphereIsometryEquivCircle_apply
    (x : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    (sphereIsometryEquivCircle x : ℂ) = Complex.orthonormalBasisOneI.repr.symm x :=
  LinearIsometryEquiv.coe_unitSphereIsometryEquiv_apply Complex.orthonormalBasisOneI.repr.symm x

/-- The Euclidean-circle homeomorphism is the standard orthonormal-coordinate isometry on
underlying points. -/
@[simp]
lemma coe_sphereHomeomorphCircle_apply
    (x : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    (sphereHomeomorphCircle x : ℂ) = Complex.orthonormalBasisOneI.repr.symm x :=
  coe_sphereIsometryEquivCircle_apply x

/-- The inverse Euclidean-circle isometry is the standard coordinate representation on
underlying points. -/
@[simp]
lemma coe_sphereIsometryEquivCircle_symm_apply (z : Circle) :
    (sphereIsometryEquivCircle.symm z : EuclideanSpace ℝ (Fin 2)) =
      Complex.orthonormalBasisOneI.repr (z : ℂ) := by
  apply Complex.orthonormalBasisOneI.repr.symm.injective
  rw [← coe_sphereIsometryEquivCircle_apply, IsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.symm_apply_apply]

/-- The inverse Euclidean-circle homeomorphism is the standard coordinate representation on
underlying points. -/
@[simp]
lemma coe_sphereHomeomorphCircle_symm_apply (z : Circle) :
    (sphereHomeomorphCircle.symm z : EuclideanSpace ℝ (Fin 2)) =
      Complex.orthonormalBasisOneI.repr (z : ℂ) :=
  coe_sphereIsometryEquivCircle_symm_apply z

/-- The Euclidean-circle isometry negates under the antipodal map. -/
@[simp]
lemma sphereIsometryEquivCircle_neg
    (x : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    sphereIsometryEquivCircle (-x) = -(sphereIsometryEquivCircle x) := by
  ext
  simp [map_neg]

/-- The Euclidean-circle homeomorphism negates under the antipodal map. -/
@[simp]
lemma sphereHomeomorphCircle_neg
    (x : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    sphereHomeomorphCircle (-x) = -(sphereHomeomorphCircle x) :=
  sphereIsometryEquivCircle_neg x

end

end EuclideanSpace

end TauCeti
