/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.GroupAction.SubMulAction
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import Mathlib.Algebra.Group.Action.End
import Mathlib.Data.Fintype.Perm

/-!
# Orthogonal actions on quadratic level sets

The orthogonal group acts on each level set of its quadratic map. If that level set spans the
module, the associated permutation representation is faithful. Finiteness of the level set then
implies finiteness of the orthogonal group.
-/

public section

namespace QuadraticMap

open TauCeti.QuadraticMap

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- A level set of a quadratic map, invariant under its orthogonal group. -/
def orthogonalLevelSet (Q : QuadraticMap R M N) (c : N) :
    SubMulAction (orthogonalGroup Q) M where
  carrier := {x | Q x = c}
  smul_mem' g _ hx := (map_app_of_mem_orthogonalGroup g.property _).trans hx

/-- Membership in the invariant level set is the defining quadratic equation. -/
@[simp]
theorem mem_orthogonalLevelSet_iff (Q : QuadraticMap R M N) (c : N) (x : M) :
    x ∈ orthogonalLevelSet Q c ↔ Q x = c := by
  simp only [orthogonalLevelSet]
  rfl

/-- The permutation action of the orthogonal group on a quadratic level set. -/
def orthogonalLevelPermHom (Q : QuadraticMap R M N) (c : N) :
    orthogonalGroup Q →* Equiv.Perm (orthogonalLevelSet Q c) :=
  MulAction.toPermHom _ _

/-- The level-set action is evaluation of the underlying linear equivalence. -/
@[simp]
theorem orthogonalLevelPermHom_apply (Q : QuadraticMap R M N) (c : N)
    (g : orthogonalGroup Q) (x : orthogonalLevelSet Q c) :
    ↑(orthogonalLevelPermHom Q c g x) = (g : M ≃ₗ[R] M) x := by
  simp only [orthogonalLevelPermHom]
  rfl

/-- The inverse level-set permutation is the restriction of the inverse linear equivalence. -/
@[simp]
theorem orthogonalLevelPermHom_symm_apply (Q : QuadraticMap R M N) (c : N)
    (g : orthogonalGroup Q) (x : orthogonalLevelSet Q c) :
    ↑((orthogonalLevelPermHom Q c g).symm x) = (g : M ≃ₗ[R] M).symm x := by
  simp only [orthogonalLevelPermHom]
  rfl

/-- The kernel consists exactly of orthogonal maps fixing the level set pointwise. -/
theorem mem_orthogonalLevelPermHom_ker_iff (Q : QuadraticMap R M N) (c : N)
    (g : orthogonalGroup Q) :
    g ∈ (orthogonalLevelPermHom Q c).ker ↔
      ∀ x, Q x = c → (g : M ≃ₗ[R] M) x = x := by
  change orthogonalLevelPermHom Q c g = 1 ↔ _
  constructor
  · intro h x hx
    exact congrArg Subtype.val (Equiv.congr_fun h ⟨x, hx⟩)
  · intro h
    ext x
    exact h x x.property

/-- Spanning is sufficient for faithfulness of the level-set action. -/
theorem faithfulSMul_orthogonalLevelSet (Q : QuadraticMap R M N) (c : N)
    (hspan : Submodule.span R {x | Q x = c} = ⊤) :
    FaithfulSMul (orthogonalGroup Q) (orthogonalLevelSet Q c) :=
  SubMulAction.faithfulSMul_of_span_eq_top _ hspan

/-- A spanning level set gives an injective permutation representation. -/
theorem orthogonalLevelPermHom_injective (Q : QuadraticMap R M N) (c : N)
    (hspan : Submodule.span R {x | Q x = c} = ⊤) :
    Function.Injective (orthogonalLevelPermHom Q c) := by
  let := faithfulSMul_orthogonalLevelSet Q c hspan
  simpa only [orthogonalLevelPermHom, MulAction.coe_toPermHom] using
    (MulAction.toPerm_injective (α := orthogonalGroup Q) (β := orthogonalLevelSet Q c))

/-- An orthogonal group with a finite spanning level set is finite. -/
theorem finite_orthogonalGroup_of_finite_levelSet (Q : QuadraticMap R M N) (c : N)
    (hfinite : Set.Finite {x | Q x = c})
    (hspan : Submodule.span R {x | Q x = c} = ⊤) : Finite (orthogonalGroup Q) := by
  let : Finite (orthogonalLevelSet Q c) := hfinite.to_subtype
  exact Finite.of_injective _ (orthogonalLevelPermHom_injective Q c hspan)

end QuadraticMap
