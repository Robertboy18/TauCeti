/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FixedSubmodule.BaseChange
public import TauCeti.LinearAlgebra.WeightedCycle.Family.Signed
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Integral fixed bases of signed cycle families

Positive signed cycles give an integral basis of the fixed submodule. Scalar
extension preserves these vectors; negative cycles can contribute additional
fixed vectors when the coefficient ring has nonzero `2`-torsion.
-/

public section

open TensorProduct TauCeti.WeightedCycle

namespace Module.Basis

@[instance_reducible]
private def intTwoTorsionUnique : Unique (Submodule.torsionBy ℤ ℤ 2) where
  default := 0
  uniq x := by
    apply Subtype.ext
    have hx := x.property
    change (2 : ℤ) * x.val = 0 at hx
    exact (mul_eq_zero.mp hx).resolve_left (by norm_num)

variable {V ι J : Type*} {n : J → ℕ} [AddCommGroup V] [Finite J]
variable (b : Module.Basis ι ℤ V) (e : (Σ j, Fin (n j + 1)) ≃ ι)
  (ε : ∀ j, Fin (n j + 1) → ℤ) (hε : ∀ j i, ε j i = 1 ∨ ε j i = -1)
  (f : V →ₗ[ℤ] V)
  (h : ∀ j i, f (b (e ⟨j, i⟩)) = ε j i • b (e ⟨j, finRotate (n j + 1) i⟩))

/-- Integral fixed vectors are determined by the initial coefficients on positive cycles. -/
noncomputable def fixedEquivPositiveSignedFamily :
    f.fixedSubmodule ≃ₗ[ℤ] ({j // (∏ i, ε j i) = 1} → ℤ) := by
  letI := intTwoTorsionUnique
  exact (b.fixedEquivSignedFamily e ε hε f h).trans LinearEquiv.prodUnique

/-- Positive integral fixed coordinates read the original initial basis coefficients. -/
@[simp]
theorem fixedEquivPositiveSignedFamily_apply (v : f.fixedSubmodule)
    (j : {j // (∏ i, ε j i) = 1}) :
    b.fixedEquivPositiveSignedFamily e ε hε f h v j = b.repr v.val (e ⟨j.val, 0⟩) := by
  exact b.fixedEquivSignedFamily_apply_pos e ε hε f h v j

/-- The inverse positive-coordinate map has zero negative coordinates. -/
theorem fixedEquivPositiveSignedFamily_symm (t : {j // (∏ i, ε j i) = 1} → ℤ) :
    (b.fixedEquivPositiveSignedFamily e ε hε f h).symm t =
      (b.fixedEquivSignedFamily e ε hε f h).symm (t, 0) := by
  rfl

/-- An integral positive-cycle basis of the actual fixed submodule. -/
noncomputable def fixedBasisSignedFamily :
    Module.Basis {j // (∏ i, ε j i) = 1} ℤ f.fixedSubmodule :=
  Module.Basis.ofEquivFun (b.fixedEquivPositiveSignedFamily e ε hε f h)

/-- Coordinates in the integral fixed basis are the original initial coefficients. -/
@[simp]
theorem fixedBasisSignedFamily_repr (v : f.fixedSubmodule)
    (j : {j // (∏ i, ε j i) = 1}) :
    (b.fixedBasisSignedFamily e ε hε f h).repr v j = b.repr v.val (e ⟨j.val, 0⟩) := by
  simp [fixedBasisSignedFamily]

/-- The positive coordinate equivalence is the coordinate map of the integral fixed basis. -/
@[simp]
theorem fixedBasisSignedFamily_equivFun :
    (b.fixedBasisSignedFamily e ε hε f h).equivFun =
      b.fixedEquivPositiveSignedFamily e ε hε f h := by
  simp [fixedBasisSignedFamily]

include hε h in
/-- A negative-cycle initial coefficient of an integral fixed vector is zero. -/
theorem fixedSignedFamily_repr_neg (v : f.fixedSubmodule)
    (j : {j // (∏ i, ε j i) = -1}) :
    b.repr v.val (e ⟨j.val, 0⟩) = 0 := by
  let := intTwoTorsionUnique
  rw [← b.fixedEquivSignedFamily_apply_neg e ε hε f h v j]
  exact congrArg Subtype.val (Subsingleton.elim _ 0)

/-- The integral fixed basis vector has the prescribed prefix coefficients on positive cycles. -/
theorem fixedBasisSignedFamily_repr_pos [DecidableEq {j // (∏ i, ε j i) = 1}]
    (j k : {j // (∏ i, ε j i) = 1}) (i : Fin (n k.val + 1)) :
    b.repr (b.fixedBasisSignedFamily e ε hε f h j).val (e ⟨k.val, i⟩) =
      Fin.partialProd (Fin.init (ε k.val)) i * (if j = k then 1 else 0) := by
  simp only [fixedBasisSignedFamily, Module.Basis.coe_ofEquivFun,
    fixedEquivPositiveSignedFamily_symm]
  by_cases hj : j = k <;> simp [hj]

/-- Every coefficient on a negative cycle of an integral fixed basis vector vanishes. -/
theorem fixedBasisSignedFamily_repr_neg
    (j : {j // (∏ i, ε j i) = 1}) (k : {j // (∏ i, ε j i) = -1})
    (i : Fin (n k.val + 1)) :
    b.repr (b.fixedBasisSignedFamily e ε hε f h j).val (e ⟨k.val, i⟩) = 0 := by
  classical
  simp only [fixedBasisSignedFamily, Module.Basis.coe_ofEquivFun,
    fixedEquivPositiveSignedFamily_symm]
  simp

/-- Each integral fixed basis vector is the signed prefix sum along its positive cycle. -/
theorem fixedBasisSignedFamily_apply (j : {j // (∏ i, ε j i) = 1}) :
    (b.fixedBasisSignedFamily e ε hε f h j).val =
      ∑ i, Fin.partialProd (Fin.init (ε j.val)) i • b (e ⟨j.val, i⟩) := by
  classical
  let := Fintype.ofFinite J
  simp [fixedBasisSignedFamily, Module.Basis.coe_ofEquivFun,
    fixedEquivPositiveSignedFamily_symm, fixedEquivSignedFamily_symm_apply, Pi.single_apply]

variable (A : Type*) [CommRing A]

omit [Finite J] in
include h in
private theorem baseChange_signedFamily (j : J) (i : Fin (n j + 1)) :
    (f.baseChange A) ((b.baseChange A) (e ⟨j, i⟩)) =
      (ε j i : A) • (b.baseChange A) (e ⟨j, finRotate (n j + 1) i⟩) := by
  simp [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul, h,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul']

/-- Signed coordinates of the actual scalar-extended endomorphism retain negative
`2`-torsion over an arbitrary commutative ring. -/
noncomputable def fixedEquivSignedFamilyBaseChange :
    (f.baseChange A).fixedSubmodule ≃ₗ[A]
      ({j // (∏ i, ε j i) = 1} → A) ×
        ({j // (∏ i, ε j i) = -1} → Submodule.torsionBy A A 2) :=
  (b.baseChange A).fixedEquivSignedFamily e ε hε (f.baseChange A)
    (b.baseChange_signedFamily e ε f h A)

/-- In signed coordinates the natural fixed-submodule comparison is precisely `u ↦ (u, 0)`. -/
theorem fixedEquivSignedFamilyBaseChange_comparison
    (x : A ⊗[ℤ] f.fixedSubmodule) :
    b.fixedEquivSignedFamilyBaseChange e ε hε f h A (f.fixedSubmoduleBaseChange A x) =
      (((b.fixedBasisSignedFamily e ε hε f h).baseChange A).equivFun x, 0) := by
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
    apply Prod.ext
    · funext j
      simp [fixedEquivSignedFamilyBaseChange, Module.Basis.baseChange_repr_tmul]
    · funext j
      apply Subtype.ext
      simp [fixedEquivSignedFamilyBaseChange, Module.Basis.baseChange_repr_tmul,
        b.fixedSignedFamily_repr_neg e ε hε f h v j]
  | add x y hx hy =>
    simp only [map_add, hx, hy, Prod.mk_add_mk, add_zero]

/-- The coordinate identity as an equality of linear maps for the actual tensor comparison. -/
theorem fixedEquivSignedFamilyBaseChange_comp :
    (b.fixedEquivSignedFamilyBaseChange e ε hε f h A).toLinearMap ∘ₗ
        f.fixedSubmoduleBaseChange A =
      (LinearMap.inl A _ _) ∘ₗ
        ((b.fixedBasisSignedFamily e ε hε f h).baseChange A).equivFun.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact b.fixedEquivSignedFamilyBaseChange_comparison e ε hε f h A x

/-- Projection onto the positive coordinates splits the natural scalar-extension map. -/
noncomputable def fixedSubmoduleBaseChangeRetraction :
    (f.baseChange A).fixedSubmodule →ₗ[A] A ⊗[ℤ] f.fixedSubmodule :=
  ((b.fixedBasisSignedFamily e ε hε f h).baseChange A).equivFun.symm.toLinearMap ∘ₗ
    (LinearMap.fst A _ _) ∘ₗ (b.fixedEquivSignedFamilyBaseChange e ε hε f h A).toLinearMap

/-- The retraction is a left inverse of the actual fixed-submodule comparison. -/
theorem fixedSubmoduleBaseChangeRetraction_leftInverse :
    Function.LeftInverse (b.fixedSubmoduleBaseChangeRetraction e ε hε f h A)
      (f.fixedSubmoduleBaseChange A) := by
  intro x
  change ((b.fixedBasisSignedFamily e ε hε f h).baseChange A).equivFun.symm
    (b.fixedEquivSignedFamilyBaseChange e ε hε f h A
      (f.fixedSubmoduleBaseChange A x)).1 = x
  rw [b.fixedEquivSignedFamilyBaseChange_comparison]
  exact ((b.fixedBasisSignedFamily e ε hε f h).baseChange A).equivFun.symm_apply_apply x

include b e ε hε h in
/-- Scalar extension embeds the integral fixed module of a signed basis-cycle family. -/
theorem fixedSubmoduleBaseChange_injective :
    Function.Injective (f.fixedSubmoduleBaseChange A) :=
  (b.fixedSubmoduleBaseChangeRetraction_leftInverse e ε hε f h A).injective

include b e hε h in
/-- The natural comparison is surjective exactly when there are no negative cycles or
the coefficient ring has zero `2`-torsion. -/
theorem fixedSubmoduleBaseChange_surjective_iff :
    Function.Surjective (f.fixedSubmoduleBaseChange A) ↔
      IsEmpty {j // (∏ i, ε j i) = -1} ∨ Submodule.torsionBy A A 2 = ⊥ := by
  classical
  let Φ := b.fixedEquivSignedFamilyBaseChange e ε hε f h A
  let Ψ := ((b.fixedBasisSignedFamily e ε hε f h).baseChange A).equivFun
  have hcomp (x : A ⊗[ℤ] f.fixedSubmodule) :
      Φ (f.fixedSubmoduleBaseChange A x) = (Ψ x, 0) :=
    b.fixedEquivSignedFamilyBaseChange_comparison e ε hε f h A x
  constructor
  · intro hsurj
    by_cases hn : IsEmpty {j // (∏ i, ε j i) = -1}
    · exact Or.inl hn
    · right
      have hne : Nonempty {j // (∏ i, ε j i) = -1} :=
        not_isEmpty_iff.mp hn
      obtain ⟨j⟩ := hne
      apply le_antisymm _ bot_le
      intro a ha
      obtain ⟨x, hx⟩ := hsurj (Φ.symm (0, fun _ ↦ ⟨a, ha⟩))
      have heq : Φ (f.fixedSubmoduleBaseChange A x) = (0, fun _ ↦ ⟨a, ha⟩) := by
        rw [hx, Φ.apply_symm_apply]
      rw [hcomp] at heq
      have ha0 : (0 : A) = a := congrArg (fun z ↦ ((z.2 j : Submodule.torsionBy A A 2) : A)) heq
      exact ha0.symm
  · intro hsurj v
    have hz : (Φ v).2 = 0 := by
      funext j
      rcases hsurj with hn | hzero
      · let := hn
        exact isEmptyElim j
      · apply Subtype.ext
        exact hzero.le ((Φ v).2 j).property
    refine ⟨Ψ.symm (Φ v).1, Φ.injective ?_⟩
    rw [hcomp, Ψ.apply_symm_apply]
    exact Prod.ext rfl hz.symm

/-- When the negative-cycle obstruction vanishes, the natural comparison is an equivalence. -/
noncomputable def fixedSubmoduleBaseChangeEquiv
    (hA : IsEmpty {j // (∏ i, ε j i) = -1} ∨ Submodule.torsionBy A A 2 = ⊥) :
    A ⊗[ℤ] f.fixedSubmodule ≃ₗ[A] (f.baseChange A).fixedSubmodule :=
  LinearEquiv.ofBijective (f.fixedSubmoduleBaseChange A)
    ⟨b.fixedSubmoduleBaseChange_injective e ε hε f h A,
      (b.fixedSubmoduleBaseChange_surjective_iff e ε hε f h A).mpr hA⟩

/-- The equivalence uses the actual scalar-extended inclusion on each vector. -/
@[simp]
theorem fixedSubmoduleBaseChangeEquiv_apply
    (hA : IsEmpty {j // (∏ i, ε j i) = -1} ∨ Submodule.torsionBy A A 2 = ⊥)
    (x : A ⊗[ℤ] f.fixedSubmodule) :
    b.fixedSubmoduleBaseChangeEquiv e ε hε f h A hA x = f.fixedSubmoduleBaseChange A x := by
  rfl

end Module.Basis
