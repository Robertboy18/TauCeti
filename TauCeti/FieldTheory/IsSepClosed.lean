/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed

/-!
# Separable closures in a tower

A separable closure of `K` is a separable closure of every intermediate extension `L` of the
tower `K ⊆ L ⊆ E`: separable closedness is a property of the field `E` alone, and an element
separable over `K` is separable over `L`. Mathlib records `IsSepClosure` only for the base of a
tower, so this file supplies the step up the tower.

The statement is a theorem rather than an instance because the base field `K` does not appear in
its conclusion, so instance search could not find it.

## Main results

* `TauCeti.isSepClosure_tower_top`: `IsSepClosure K E` implies `IsSepClosure L E` for every
  intermediate extension `L`.
-/

public section

namespace TauCeti

/-- **A separable closure of `K` is a separable closure of every intermediate extension `L`**:
separable closedness is a property of the field alone, and separability over `K` implies
separability over `L`. -/
theorem isSepClosure_tower_top (K L E : Type*) [Field K] [Field L] [Field E] [Algebra K L]
    [Algebra K E] [Algebra L E] [IsScalarTower K L E] [IsSepClosure K E] : IsSepClosure L E :=
  ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K L E⟩

end TauCeti
