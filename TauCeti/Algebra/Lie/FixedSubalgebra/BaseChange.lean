/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.BaseChange.Hom
public import TauCeti.Algebra.Lie.FixedSubalgebra.Basic

/-!
# Flat scalar extension of fixed Lie subalgebras

The tensor extension of the fixed subalgebra maps into the fixed subalgebra of the
extended endomorphism. Mathlib's flat tensor equalizer theorem makes this comparison
an equivalence over a flat coefficient algebra. Both the comparison and its inverse
are natural under intertwining maps.

Flatness is essential: negation on the zero-bracket Lie algebra `ℤ` has no nonzero
fixed element, whereas after extension to `ZMod 2` every element is fixed.
-/

@[expose] public section

open TensorProduct

variable {R L M : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]
  (S : Type*) [CommRing S] [Algebra R S]

namespace LieHom

variable (f : L →ₗ⁅R⁆ L)

/-- The canonical map from extended fixed elements to fixed extended elements. -/
def fixedBaseChange :
    S ⊗[R] f.fixedSubalgebra →ₗ⁅S⁆ (f.baseChange S).fixedSubalgebra where
  __ := (f.fixedSubalgebra.incl.baseChange S).toLinearMap.codRestrict
    (f.baseChange S).fixedSubalgebra.toSubmodule fun x => by
      change f.baseChange S (f.fixedSubalgebra.incl.baseChange S x) =
        f.fixedSubalgebra.incl.baseChange S x
      induction x with
      | tmul s x => simp
      | add x y hx hy => simp [hx, hy]
  map_lie' {x y} := Subtype.ext ((f.fixedSubalgebra.incl.baseChange S).map_lie x y)

@[simp]
theorem coe_fixedBaseChange (x : S ⊗[R] f.fixedSubalgebra) :
    (fixedBaseChange S f x : S ⊗[R] L) = f.fixedSubalgebra.incl.baseChange S x :=
  rfl

theorem fixedBaseChange_tmul (s : S) (x : f.fixedSubalgebra) :
    (fixedBaseChange S f (s ⊗ₜ[R] x) : S ⊗[R] L) = s ⊗ₜ[R] (x : L) := by
  simp [coe_fixedBaseChange]

private theorem fixedBaseChange_bijective [Module.Flat R S] :
    Function.Bijective (fixedBaseChange S f) := by
  constructor
  · have hinj : Function.Injective (f.fixedSubalgebra.incl.baseChange S) := by
      change Function.Injective ⇑(f.fixedSubalgebra.incl.baseChange S).toLinearMap
      rw [coe_baseChange]
      exact Module.Flat.lTensor_preserves_injective_linearMap
        f.fixedSubalgebra.toSubmodule.subtype Subtype.val_injective
    intro x y h
    apply hinj
    exact congrArg Subtype.val h
  · intro y
    have hy : (y : S ⊗[R] L) ∈ LinearMap.range
        (AlgebraTensorModule.lTensor S S f.fixedSubalgebra.toSubmodule.subtype) := by
      change (y : S ⊗[R] L) ∈ LinearMap.range (AlgebraTensorModule.lTensor S S
        (LinearMap.eqLocus f.toLinearMap LinearMap.id).subtype)
      rw [← Module.Flat.eqLocus_lTensor_eq S S f.toLinearMap LinearMap.id]
      change LinearMap.baseChange S f.toLinearMap y =
        LinearMap.baseChange S (LinearMap.id : L →ₗ[R] L) y
      rw [LinearMap.baseChange_id, ← coe_baseChange]
      exact y.property
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, Subtype.ext ?_⟩
    rw [coe_fixedBaseChange]
    change (f.fixedSubalgebra.incl.baseChange S).toLinearMap x = y
    rw [coe_baseChange]
    exact hx

/-- Fixed Lie subalgebras commute with flat scalar extension. -/
noncomputable def fixedBaseChangeEquiv [Module.Flat R S] :
    S ⊗[R] f.fixedSubalgebra ≃ₗ⁅S⁆ (f.baseChange S).fixedSubalgebra :=
  LieEquiv.ofBijective (fixedBaseChange S f) (by exact fixedBaseChange_bijective S f)

@[simp]
theorem fixedBaseChangeEquiv_apply [Module.Flat R S] (x : S ⊗[R] f.fixedSubalgebra) :
    fixedBaseChangeEquiv S f x = fixedBaseChange S f x :=
  rfl

/-- The inverse comparison still maps to the given element under the extended inclusion. -/
@[simp]
theorem incl_fixedBaseChangeEquiv_symm [Module.Flat R S]
    (x : (f.baseChange S).fixedSubalgebra) :
    f.fixedSubalgebra.incl.baseChange S ((fixedBaseChangeEquiv S f).symm x) = x := by
  rw [← coe_fixedBaseChange, ← fixedBaseChangeEquiv_apply, LieEquiv.apply_symm_apply]

variable {f} {g : M →ₗ⁅R⁆ M} (u : L →ₗ⁅R⁆ M) (h : g.comp u = u.comp f)

include h in
/-- Scalar extension preserves the intertwining equation. -/
theorem baseChange_intertwines :
    (g.baseChange S).comp (u.baseChange S) = (u.baseChange S).comp (f.baseChange S) := by
  rw [← baseChange_comp, h, baseChange_comp]

/-- The fixed-subalgebra comparison is natural under intertwining maps. -/
theorem fixedBaseChange_natural :
    (fixedBaseChange S g).comp ((restrictFixed u h).baseChange S) =
      (restrictFixed (u.baseChange S) (baseChange_intertwines S u h)).comp
        (fixedBaseChange S f) := by
  apply LieHom.ext
  intro x
  apply Subtype.ext
  induction x with
  | tmul s x => simp [LieHom.comp_apply]
  | add x y hx hy => simp_all

/-- The inverses of the flat comparison equivalences form the reverse naturality square. -/
theorem fixedBaseChangeEquiv_symm_natural [Module.Flat R S]
    (x : (f.baseChange S).fixedSubalgebra) :
    (restrictFixed u h).baseChange S ((fixedBaseChangeEquiv S f).symm x) =
      (fixedBaseChangeEquiv S g).symm
        (restrictFixed (u.baseChange S) (baseChange_intertwines S u h) x) := by
  apply (LieEquiv.eq_symm_apply _).2
  simpa only [LieHom.comp_apply, ← fixedBaseChangeEquiv_apply, LieEquiv.apply_symm_apply]
    using congr_fun (fixedBaseChange_natural S u h) ((fixedBaseChangeEquiv S f).symm x)

end LieHom
