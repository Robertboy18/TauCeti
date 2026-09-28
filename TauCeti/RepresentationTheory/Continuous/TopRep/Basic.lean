/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.TopRep

/-!
# Morphisms of topological representations on elements

Mathlib evaluates the identity and the composite of morphisms of topological representations on
elements (`TopRep.id_apply`, `TopRep.comp_apply`). This file adds the transport
`CategoryTheory.eqToHom` along an equality of objects: on elements it is the cast along the
equality of the underlying types (`TopRep.eqToHom_apply`). This evaluates a transport when the
equality of objects is not definitional, for instance when it identifies two constructions of a
representation whose operators agree only propositionally.
-/

public section

namespace TopRep

open CategoryTheory

variable {k : Type*} [Ring k] [TopologicalSpace k] {G : Type*} [Monoid G]

/-- **Transport along an equality of representations is the cast of elements** along the equality
of the underlying types. -/
theorem eqToHom_apply {A B : TopRep k G} (e : A = B) (a : A) :
    (eqToHom e : A ⟶ B) a = cast (congrArg TopRep.V e) a := by
  subst e
  rfl

end TopRep
