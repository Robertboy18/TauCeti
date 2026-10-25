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

The fixed submodule of a Lie endomorphism is closed under brackets. Intertwining
homomorphisms restrict to these subalgebras, and intertwining equivalences restrict
with the expected inverse. This is the fixed-carrier and transport interface used by
the native Serre diagram actions in ReductiveGroups 9A.1b.
-/

@[expose] public section

variable {R L M N : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]
  [LieRing N] [LieAlgebra R N]

namespace LieHom

/-- The Lie subalgebra fixed by an endomorphism, with the native fixed submodule. -/
def fixedSubalgebra (f : L →ₗ⁅R⁆ L) : LieSubalgebra R L where
  __ := f.toLinearMap.fixedSubmodule
  lie_mem' {x y} hx hy := by
    change f x = x at hx
    change f y = y at hy
    change f ⁅x, y⁆ = ⁅x, y⁆
    rw [map_lie, hx, hy]

@[simp]
theorem mem_fixedSubalgebra {f : L →ₗ⁅R⁆ L} {x : L} :
    x ∈ f.fixedSubalgebra ↔ f x = x :=
  Iff.rfl

@[simp]
theorem fixedSubalgebra_toSubmodule (f : L →ₗ⁅R⁆ L) :
    f.fixedSubalgebra.toSubmodule = f.toLinearMap.fixedSubmodule :=
  rfl

/-- Fixed elements form the kernel of the difference of the underlying linear maps.
The difference need not itself be a Lie homomorphism. -/
theorem fixedSubalgebra_eq_ker (f : L →ₗ⁅R⁆ L) :
    f.fixedSubalgebra.toSubmodule = LinearMap.ker (f.toLinearMap - LinearMap.id) :=
  LinearMap.fixedSubmodule_eq_ker _

@[simp]
theorem apply_coe_fixedSubalgebra (f : L →ₗ⁅R⁆ L) (x : f.fixedSubalgebra) :
    f (x : L) = x :=
  x.property

variable {f : L →ₗ⁅R⁆ L} {g : M →ₗ⁅R⁆ M} {k : N →ₗ⁅R⁆ N}

/-- An intertwining homomorphism restricts to the fixed Lie subalgebras. -/
def restrictFixed (u : L →ₗ⁅R⁆ M) (h : g.comp u = u.comp f) :
    f.fixedSubalgebra →ₗ⁅R⁆ g.fixedSubalgebra where
  __ := (u.toLinearMap.comp f.fixedSubalgebra.toSubmodule.subtype).codRestrict
    g.fixedSubalgebra.toSubmodule fun x => by
      change g (u x) = u x
      calc
        g (u x) = u (f x) := congr_fun h x
        _ = u x := congrArg u x.property
  map_lie' {x y} := Subtype.ext (u.map_lie x y)

@[simp]
theorem coe_restrictFixed (u : L →ₗ⁅R⁆ M) (h : g.comp u = u.comp f)
    (x : f.fixedSubalgebra) : (restrictFixed u h x : M) = u x :=
  rfl

@[simp]
theorem restrictFixed_id (f : L →ₗ⁅R⁆ L) :
    restrictFixed (f := f) (g := f) (LieHom.id : L →ₗ⁅R⁆ L) rfl = LieHom.id :=
  rfl

/-- Restriction preserves composition of intertwining maps. -/
theorem restrictFixed_comp (u : L →ₗ⁅R⁆ M) (v : M →ₗ⁅R⁆ N)
    (hu : g.comp u = u.comp f) (hv : k.comp v = v.comp g) :
    restrictFixed (f := f) (g := k) (v.comp u) (by
      ext x
      exact (congr_fun hv (u x)).trans (congrArg v (congr_fun hu x))) =
      (restrictFixed v hv).comp (restrictFixed u hu) :=
  rfl

end LieHom

namespace LieEquiv

variable {f : L →ₗ⁅R⁆ L} {g : M →ₗ⁅R⁆ M}

/-- An intertwining equivalence restricts to an equivalence of fixed Lie subalgebras. -/
def restrictFixed (e : L ≃ₗ⁅R⁆ M) (h : g.comp e.toLieHom = e.toLieHom.comp f) :
    f.fixedSubalgebra ≃ₗ⁅R⁆ g.fixedSubalgebra where
  toLieHom := LieHom.restrictFixed e.toLieHom h
  invFun y := ⟨e.symm y, by
    apply e.injective
    calc
      e (f (e.symm y)) = g (e (e.symm y)) := (LieHom.congr_fun h _).symm
      _ = e (e.symm y) := by rw [e.apply_symm_apply]; exact y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)

@[simp]
theorem coe_restrictFixed (e : L ≃ₗ⁅R⁆ M) (h : g.comp e.toLieHom = e.toLieHom.comp f)
    (x : f.fixedSubalgebra) : (e.restrictFixed h x : M) = e x :=
  rfl

@[simp]
theorem coe_restrictFixed_symm (e : L ≃ₗ⁅R⁆ M)
    (h : g.comp e.toLieHom = e.toLieHom.comp f) (y : g.fixedSubalgebra) :
    ((e.restrictFixed h).symm y : L) = e.symm y :=
  rfl

/-- Restricting the inverse gives the inverse of the restricted equivalence. -/
@[simp]
theorem restrictFixed_symm (e : L ≃ₗ⁅R⁆ M)
    (h : g.comp e.toLieHom = e.toLieHom.comp f) :
    (e.restrictFixed h).symm = e.symm.restrictFixed (f := g) (g := f) (by
      ext y
      apply e.injective
      simpa using (LieHom.congr_fun h (e.symm y)).symm) := by
  ext y
  rfl

end LieEquiv
