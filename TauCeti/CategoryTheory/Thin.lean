/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.InducedCategory

/-!
# Thin categories: opposites, induced categories and structured arrows

A category is thin (`Quiver.IsThin`) when there is at most one morphism between any two objects.
Mathlib records that functor categories into a thin category are thin and that every functor out of
a thin category is faithful. This file records three further closure properties: the opposite of a
thin quiver is thin, a category induced along a map into a thin category is thin, and the category
of structured arrows into a thin category is thin.

The motivating instance is the category of members of a family `B` of opens of a topological
space lying below a fixed open, `StructuredArrow V (inducedFunctor (Subtype.val : B → Opens X)).op`,
which indexes the limits describing a presheaf adapted to `B`. Thinness makes the commutativity
conditions of morphisms of structured arrows, and the functor laws of functors between such index
categories, instances of `Subsingleton.elim`.

## Main results

* `TauCeti.Quiver.instIsThinOpposite`: the opposite of a thin quiver is thin.
* `TauCeti.CategoryTheory.instIsThinInducedCategory`: a category induced along a map into a thin
  category is thin.
* `TauCeti.CategoryTheory.instIsThinStructuredArrow`: structured arrows into a thin category form a
  thin category.
-/

public section

namespace TauCeti

universe v₁ v₂ u₁ u₂

/-- The opposite of a thin quiver is thin. -/
instance Quiver.instIsThinOpposite {V : Type u₁} [Quiver.{v₁} V] [Quiver.IsThin V] :
    Quiver.IsThin Vᵒᵖ :=
  fun _ _ ↦ ⟨fun _ _ ↦ Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩

namespace CategoryTheory

open _root_.CategoryTheory

/-- A category induced along a map into a thin category is thin. -/
instance instIsThinInducedCategory {C : Type u₁} {D : Type u₂} [Category.{v₂} D] [Quiver.IsThin D]
    (F : C → D) : Quiver.IsThin (InducedCategory D F) :=
  fun _ _ ↦ ⟨fun _ _ ↦ InducedCategory.hom_ext (Subsingleton.elim _ _)⟩

/-- Structured arrows into a thin category form a thin category. -/
instance instIsThinStructuredArrow {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Quiver.IsThin C] (S : D) (T : C ⥤ D) : Quiver.IsThin (StructuredArrow S T) :=
  fun _ _ ↦ ⟨fun a b ↦ StructuredArrow.hom_ext a b (Subsingleton.elim _ _)⟩

end CategoryTheory

end TauCeti

end
