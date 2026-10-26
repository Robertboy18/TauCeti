/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Fixed Lie subalgebras

The fixed vectors of a Lie endomorphism form a Lie subalgebra. Its underlying submodule is
Mathlib's `LinearMap.fixedSubmodule`, so fixed-module coordinates apply to this native carrier.
-/

public section

namespace LieHom

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The fixed vectors of a Lie endomorphism, with their inherited Lie bracket. -/
def fixedSubalgebra (f : L →ₗ⁅R⁆ L) : LieSubalgebra R L :=
  { f.toLinearMap.fixedSubmodule with
    lie_mem' := by
      intro x y hx hy
      apply LinearMap.mem_fixedSubmodule_iff.mpr
      have hx' : f x = x := LinearMap.mem_fixedSubmodule_iff.mp hx
      have hy' : f y = y := LinearMap.mem_fixedSubmodule_iff.mp hy
      simpa only [coe_toLinearMap, hx', hy'] using (map_lie f x y) }

/-- Membership in the fixed Lie subalgebra is the fixed-point equation. -/
@[simp]
theorem mem_fixedSubalgebra (f : L →ₗ⁅R⁆ L) (x : L) :
    x ∈ f.fixedSubalgebra ↔ f x = x :=
  Iff.rfl

/-- The underlying submodule is the existing linear fixed submodule. -/
@[simp]
theorem fixedSubalgebra_toSubmodule (f : L →ₗ⁅R⁆ L) :
    f.fixedSubalgebra.toSubmodule = f.toLinearMap.fixedSubmodule := by
  ext x
  rfl

end LieHom
