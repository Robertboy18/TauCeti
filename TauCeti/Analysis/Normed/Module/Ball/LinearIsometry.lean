/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Linear isometries of the closed unit ball

A linear isometry preserves norms, so it maps the closed unit ball into the closed unit ball and
the unit sphere into the unit sphere. This file records the restriction to the closed unit ball,
independently of any manifold structure: it is a topological embedding, and it meets the unit
sphere exactly in the image of the unit sphere. These are the point-set facts behind the smooth
embedding of closed balls induced by a linear isometry, the flat disc that a great circle bounds.

## Main definitions

* `LinearIsometry.unitClosedBallMap`: the restriction of a linear isometry to the closed unit
  balls.

## Main results

* `LinearIsometry.isometry_unitClosedBallMap`, `LinearIsometry.isEmbedding_unitClosedBallMap`:
  the restriction is an isometry, hence a topological embedding.
* `LinearIsometry.norm_unitClosedBallMap_eq_one_iff`: the restriction maps a point to the unit
  sphere exactly when the point lies on the unit sphere.
-/

public section

open Metric

namespace LinearIsometry

variable {R E F : Type*} [Semiring R] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [Module R E] [Module R F]

/-- A linear isometry maps the closed unit ball into the closed unit ball. -/
theorem map_mem_closedBall_zero_one (f : E →ₗᵢ[R] F) {x : E} (hx : x ∈ closedBall (0 : E) 1) :
    f x ∈ closedBall (0 : F) 1 := by
  simpa using hx

/-- The restriction of a linear isometry to the closed unit balls. -/
def unitClosedBallMap (f : E →ₗᵢ[R] F) (x : closedBall (0 : E) 1) : closedBall (0 : F) 1 :=
  ⟨f x, f.map_mem_closedBall_zero_one x.2⟩

@[simp]
theorem coe_unitClosedBallMap_apply (f : E →ₗᵢ[R] F) (x : closedBall (0 : E) 1) :
    (f.unitClosedBallMap x : F) = f x :=
  (rfl)

/-- The restriction of a linear isometry to the closed unit balls is an isometry. -/
theorem isometry_unitClosedBallMap (f : E →ₗᵢ[R] F) : Isometry f.unitClosedBallMap :=
  Isometry.of_dist_eq fun x y => by simp [Subtype.dist_eq]

/-- The restriction of a linear isometry to the closed unit balls is a topological embedding. -/
theorem isEmbedding_unitClosedBallMap (f : E →ₗᵢ[R] F) :
    Topology.IsEmbedding f.unitClosedBallMap := by
  exact f.isometry_unitClosedBallMap.isEmbedding

/-- The restriction of a linear isometry to the closed unit balls is continuous. -/
theorem continuous_unitClosedBallMap (f : E →ₗᵢ[R] F) : Continuous f.unitClosedBallMap :=
  f.isEmbedding_unitClosedBallMap.continuous

/-- The restriction of a linear isometry to the closed unit balls maps a point to the unit sphere
exactly when the point lies on the unit sphere. -/
@[simp]
theorem norm_unitClosedBallMap_eq_one_iff (f : E →ₗᵢ[R] F) (x : closedBall (0 : E) 1) :
    ‖(f.unitClosedBallMap x : F)‖ = 1 ↔ ‖(x : E)‖ = 1 := by
  simp

end LinearIsometry
