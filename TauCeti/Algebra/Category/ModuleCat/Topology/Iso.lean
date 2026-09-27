/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic

/-!
# Isomorphisms in `TopModuleCat` with a discrete target

A morphism of topological modules whose target carries the discrete topology is an isomorphism of
`TopModuleCat R` as soon as the underlying morphism of modules is one
(`TopModuleCat.isIso_of_isIso_forget₂_map`): the inverse is continuous because its source is
discrete. This is the counterpart, for the forgetful functor to `ModuleCat R` and under
discreteness of the target, of Mathlib's `(forget₂ (TopModuleCat R) TopCat).ReflectsIsomorphisms`.
It turns Mathlib's invertibility results for the homology of forgotten cochain complexes into
isomorphisms of discrete cohomology modules.
-/

public section

open CategoryTheory

namespace TopModuleCat

variable {R : Type*} [Ring R] [TopologicalSpace R]

/-- A morphism of topological modules into a discrete module is an isomorphism as soon as its
underlying morphism of modules is one: the inverse is continuous because its source is discrete. -/
theorem isIso_of_isIso_forget₂_map {X Y : TopModuleCat R} [DiscreteTopology Y] (f : X ⟶ Y)
    [IsIso ((forget₂ (TopModuleCat R) (ModuleCat R)).map f)] : IsIso f := by
  let e : X ≃L[R] Y :=
    { (asIso ((forget₂ (TopModuleCat R) (ModuleCat R)).map f)).toLinearEquiv with
      continuous_toFun := f.hom.continuous
      continuous_invFun := continuous_of_discreteTopology }
  have hf : f = (ofIso e).hom := by
    ext x
    rfl
  rw [hf]
  infer_instance

end TopModuleCat
