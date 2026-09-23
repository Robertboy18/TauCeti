/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite generation and projectivity under restriction of scalars

Restriction of scalars along a ring homomorphism `f : R →+* S` keeps the underlying abelian
group of a module and only changes which ring acts on it. This file records when the two
finiteness properties defining `K₀(proj R)` and `G₀(mod R)` survive it.

* Along a **surjective** ring homomorphism, finite generation is preserved and reflected: every
  scalar of `S` is the image of a scalar of `R`, so the `S`-span and the `R`-span of a set
  coincide.
* Along a ring **isomorphism**, projectivity is preserved and reflected: the identity of the
  module is then a semilinear equivalence between the two module structures.

## Main definitions

* `ModuleCat.restrictScalarsSemilinearMap`: the identity of a module, as a semilinear map from its
  restriction of scalars.

## Main results

* `ModuleCat.finite_restrictScalars_iff` and `ModuleCat.isFG_restrictScalars_iff`: finite
  generation is invariant under restriction of scalars along a surjective ring homomorphism.
* `ModuleCat.projective_restrictScalars_iff`: projectivity is invariant under restriction of
  scalars along a ring isomorphism.
-/

public section

open CategoryTheory

universe v u₁ u₂

namespace ModuleCat

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]

/-- The identity map of an `S`-module `M`, as an `f`-semilinear map from `M` with scalars
restricted along `f : R →+* S` to `M` itself. -/
def restrictScalarsSemilinearMap (f : R →+* S) (M : ModuleCat.{v} S) :
    (restrictScalars f).obj M →ₛₗ[f] M where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' r m := restrictScalars.smul_def f r m

@[simp]
theorem restrictScalarsSemilinearMap_apply (f : R →+* S) (M : ModuleCat.{v} S)
    (m : (restrictScalars f).obj M) :
    restrictScalarsSemilinearMap f M m = m :=
  (rfl)

theorem restrictScalarsSemilinearMap_bijective (f : R →+* S) (M : ModuleCat.{v} S) :
    Function.Bijective (restrictScalarsSemilinearMap f M) :=
  Function.bijective_id

/-- **Finite generation along a surjective ring homomorphism.** Restricting scalars along a
surjective ring homomorphism preserves and reflects finite generation: every scalar of `S` is the
image of a scalar of `R`, so the two spans of a set agree. -/
theorem finite_restrictScalars_iff (f : R →+* S) (hf : Function.Surjective f)
    (M : ModuleCat.{v} S) :
    Module.Finite R ((restrictScalars f).obj M) ↔ Module.Finite S M :=
  haveI : RingHomSurjective f := ⟨hf⟩
  LinearMap.finite_iff_of_bijective (restrictScalarsSemilinearMap f M)
    (restrictScalarsSemilinearMap_bijective f M)

/-- Restricting scalars along a surjective ring homomorphism preserves and reflects the object
property of being finitely generated. -/
theorem isFG_restrictScalars_iff (f : R →+* S) (hf : Function.Surjective f)
    (M : ModuleCat.{v} S) :
    isFG R ((restrictScalars f).obj M) ↔ isFG S M := by
  rw [isFG_iff, isFG_iff, finite_restrictScalars_iff f hf]

/-- **Projectivity along a ring isomorphism.** Restricting scalars along a ring isomorphism
preserves and reflects projectivity: the identity is a semilinear equivalence between the two
module structures, and projectivity transports along semilinear equivalences. -/
theorem projective_restrictScalars_iff (e : R ≃+* S) (M : ModuleCat.{v} S) :
    Module.Projective R ((restrictScalars e.toRingHom).obj M) ↔ Module.Projective S M := by
  have : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  have : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e
  let φ : (restrictScalars e.toRingHom).obj M ≃ₛₗ[e.toRingHom] M :=
    { restrictScalarsSemilinearMap e.toRingHom M with
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact ⟨fun _ ↦ Module.Projective.of_equiv φ, fun _ ↦ Module.Projective.of_equiv φ.symm⟩

end ModuleCat
