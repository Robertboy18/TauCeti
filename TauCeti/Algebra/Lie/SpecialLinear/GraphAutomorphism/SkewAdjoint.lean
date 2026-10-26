/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Subalgebra.Fixed
public import TauCeti.Algebra.Lie.SpecialLinear.GraphAutomorphism
public import TauCeti.LinearAlgebra.Matrix.SkewAdjoint

/-!
# The native type-A fixed Lie algebra as skew-adjoint matrices

When `2` is invertible, the fixed Lie subalgebra of the native type-A graph automorphism is
Lie equivalent to the matrices skew-adjoint for the inverse signed reversal form. Both maps
retain the underlying matrix. The inverse uses the existing trace-zero theorem for
skew-adjoint matrices; no change of form or classification is involved.
-/

public section

open Matrix LieAlgebra.SpecialLinear

namespace TauCeti

variable (r : ℕ) (A : Type*) [CommRing A] [Invertible (2 : A)]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The native fixed special linear Lie algebra is the skew-adjoint matrix Lie algebra for
the inverse signed reversal form. Both directions retain the underlying matrix. -/
def typeASpecialLinearFixedSkewAdjointEquiv :
    (typeASpecialLinearGraphAutomorphism r A).toLieHom.fixedSubalgebra ≃ₗ⁅A⁆
      skewAdjointMatricesLieSubalgebra
        ((typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A)⁻¹) where
  toFun X := ⟨X.val.val, by
    simpa only [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule] using
      (typeASpecialLinearGraphAutomorphism_eq_self_iff r A X.val).mp
        ((LieHom.mem_fixedSubalgebra _ _).mp X.property)⟩
  invFun Y := by
    have hY :
        ((typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A)⁻¹).IsSkewAdjoint
          Y.val := by
      simpa only [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule] using
        Y.property
    have hF : IsUnit
        ((typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A)⁻¹) := by
      rw [← GeneralLinearGroup.coe_inv]
      exact ((typeAGraphConjugator r A)⁻¹).isUnit
    let X : sl (Fin (r + 1)) A := ⟨Y.val,
      Matrix.IsSkewAdjoint.trace_eq_zero hF hY⟩
    exact ⟨X, (LieHom.mem_fixedSubalgebra _ _).mpr
      ((typeASpecialLinearGraphAutomorphism_eq_self_iff r A X).mpr hY)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := by
    intro X Y
    rfl

/-- The forward equivalence retains the underlying matrix of a fixed trace-zero element. -/
@[simp]
theorem typeASpecialLinearFixedSkewAdjointEquiv_apply
    (X : (typeASpecialLinearGraphAutomorphism r A).toLieHom.fixedSubalgebra) :
    (typeASpecialLinearFixedSkewAdjointEquiv r A X :
      Matrix (Fin (r + 1)) (Fin (r + 1)) A) = X.val.val := by
  ext i j
  rfl

/-- The inverse equivalence retains the underlying skew-adjoint matrix. -/
@[simp]
theorem typeASpecialLinearFixedSkewAdjointEquiv_symm_apply
    (Y : skewAdjointMatricesLieSubalgebra
      ((typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A)⁻¹)) :
    ((typeASpecialLinearFixedSkewAdjointEquiv r A).symm Y).val.val = Y.val := by
  ext i j
  rfl

end TauCeti
