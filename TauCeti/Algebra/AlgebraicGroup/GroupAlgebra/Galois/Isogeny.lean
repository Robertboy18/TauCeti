/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Map
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
import TauCeti.Algebra.MonoidAlgebra.FaithfullyFlat
import TauCeti.Algebra.MonoidAlgebra.Finite
import TauCeti.RingTheory.Flat.Descent
import TauCeti.RingTheory.TensorProduct.Descent
import Mathlib.RingTheory.Finiteness.Descent

/-!
# Isogenies of Galois-descended group algebras

For an equivariant map of character groups, the descended coordinate map is finite exactly
when the character cokernel is finite, and faithfully flat exactly when the character map
is injective. Together these characterize central isogenies without finite-generation,
torsion-freeness, or characteristic assumptions on the character groups or base field.

The splitting isomorphisms identify the scalar extension of the descended map with the
split group-algebra map. Faithfully flat descent then transfers the split criteria.
-/

public section

open scoped TensorProduct

open TauCeti.GaloisDescent

universe u

private theorem property_tensorProduct_map
    {P : ∀ {A B : Type u} [CommRing A] [CommRing B], (A →+* B) → Prop}
    (hP : RingHom.IsStableUnderBaseChange P)
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)
    (hf : P f.toRingHom) :
    P (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom := by
  let : Algebra A B := f.toAlgebra
  let : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let : Algebra B (S ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  let : Algebra A (S ⊗[R] B) := ((Algebra.TensorProduct.includeRight :
    B →ₐ[R] S ⊗[R] B).comp f).toAlgebra
  let : Algebra (S ⊗[R] A) (S ⊗[R] B) :=
    (Algebra.TensorProduct.map (AlgHom.id R S) f).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algHom f
  have : IsScalarTower A B (S ⊗[R] B) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A (S ⊗[R] A) (S ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower S (S ⊗[R] A) (S ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq fun s ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower R (S ⊗[R] A) (S ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower R A (S ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : Algebra.IsPushout A B (S ⊗[R] A) (S ⊗[R] B) :=
    (Algebra.IsPushout.comp_iff R A S (S ⊗[R] A)).mp inferInstance
  exact hP A B (S ⊗[R] A) (S ⊗[R] B) hf

namespace Representation.IntertwiningMap

variable {k L M N : Type u} [Field k] [Field L] [Algebra k L]
variable [FiniteDimensional k L] [IsGalois k L] [AddCommGroup M] [AddCommGroup N]
variable {rho : Representation ℤ (L ≃ₐ[k] L) M}
variable {tau : Representation ℤ (L ≃ₐ[k] L) N}

private theorem property_groupAlgebraInvariantsAlgHom_iff
    {P : ∀ {A B : Type u} [CommRing A] [CommRing B], (A →+* B) → Prop}
    (hiso : RingHom.RespectsIso P) (hbase : RingHom.IsStableUnderBaseChange P)
    (hdesc : RingHom.CodescendsAlong P RingHom.FaithfullyFlat)
    (f : Representation.IntertwiningMap rho tau) :
    P f.groupAlgebraInvariantsAlgHom.toRingHom ↔
      P (MonoidAlgebra.mapDomainRingHom L
        f.toLinearMap.toAddMonoidHom.toMultiplicative) := by
  let g := Algebra.TensorProduct.map (AlgHom.id k L) f.groupAlgebraInvariantsAlgHom
  let s := MonoidAlgebra.mapDomainRingHom L f.toLinearMap.toAddMonoidHom.toMultiplicative
  let eM := (groupAlgebraInvariantsBaseChangeBialgEquiv rho).toAlgEquiv.toRingEquiv
  let eN := (groupAlgebraInvariantsBaseChangeBialgEquiv tau).toAlgEquiv.toRingEquiv
  have hcomm : eN.toRingHom.comp g.toRingHom = s.comp eM.toRingHom := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a x =>
        simp [eN, eM, g, s, MonoidAlgebra.mapDomainBialgHom,
          MonoidAlgebra.mapDomainAlgHom]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hg : P g.toRingHom ↔ P s := by
    have h₁ := hiso.cancel_right_isIso (CommRingCat.ofHom g.toRingHom)
      eN.toCommRingCatIso.hom
    have h₂ := hiso.cancel_left_isIso eM.toCommRingCatIso.hom (CommRingCat.ofHom s)
    exact h₁.symm.trans (hcomm ▸ h₂)
  exact (show P f.groupAlgebraInvariantsAlgHom.toRingHom ↔ P g.toRingHom from
    ⟨property_tensorProduct_map hbase _, hdesc.of_tensorProduct_map _⟩).trans hg

/-- The descended coordinate map is finite exactly when the character cokernel is finite. -/
theorem groupAlgebraInvariantsAlgHom_finite_iff
    (f : Representation.IntertwiningMap rho tau) :
    f.groupAlgebraInvariantsAlgHom.Finite ↔
      Finite (Multiplicative N ⧸ f.toLinearMap.toAddMonoidHom.toMultiplicative.range) := by
  exact (property_groupAlgebraInvariantsAlgHom_iff RingHom.finite_respectsIso
    RingHom.finite_isStableUnderBaseChange RingHom.Finite.codescendsAlong_faithfullyFlat f).trans
      (TauCeti.MonoidAlgebra.mapDomainRingHom_finite_iff_finite_quotient L _)

/-- The descended coordinate map is faithfully flat exactly when the character map is injective. -/
theorem groupAlgebraInvariantsAlgHom_faithfullyFlat_iff
    (f : Representation.IntertwiningMap rho tau) :
    f.groupAlgebraInvariantsAlgHom.toRingHom.FaithfullyFlat ↔ Function.Injective f := by
  exact (property_groupAlgebraInvariantsAlgHom_iff RingHom.FaithfullyFlat.respectsIso
    RingHom.FaithfullyFlat.isStableUnderBaseChange
    RingHom.FaithfullyFlat.codescendsAlong_faithfullyFlat f).trans
      (TauCeti.MonoidAlgebra.faithfullyFlat_mapDomainRingHom_iff L _)

private theorem groupAlgebraInvariants_isCocomm
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    Coalgebra.IsCocomm k (groupAlgebraInvariants rho) := by
  let B : Type u := groupAlgebraInvariants rho
  let A := MonoidAlgebra L (Multiplicative M)
  have hswap (t : B ⊗[k] B) :
      (groupAlgebraInvariantsTensorEquiv rho (_root_.TensorProduct.comm k B B t) : A ⊗[L] A) =
        _root_.TensorProduct.comm L A A (groupAlgebraInvariantsTensorEquiv rho t) := by
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp [A, B]
    | add x y hx hy => simp only [map_add, AddMemClass.coe_add, hx, hy]
  constructor
  apply LinearMap.ext
  intro x
  apply (groupAlgebraInvariantsTensorEquiv rho).injective
  apply Subtype.val_injective
  change (groupAlgebraInvariantsTensorEquiv rho
    (_root_.TensorProduct.comm k B B (Coalgebra.comul x)) : A ⊗[L] A) = _
  rw [hswap]
  dsimp only [A, B]
  simp only [groupAlgebraInvariantsTensorEquiv_comul, groupAlgebraInvariantsComul_apply,
    Coalgebra.comm_comul]

/-- Central isogenies in finite Galois descent correspond to injective character maps with
finite cokernel. The kernel may be nonreduced in positive characteristic. -/
theorem isCentralIsogeny_groupAlgebraInvariantsBialgHom_iff
    (f : Representation.IntertwiningMap rho tau) :
    TauCeti.CommHopfAlgCat.IsCentralIsogeny
        (CommHopfAlgCat.ofHom f.groupAlgebraInvariantsBialgHom) ↔
      Function.Injective f ∧
        Finite (Multiplicative N ⧸ f.toLinearMap.toAddMonoidHom.toMultiplicative.range) := by
  rw [TauCeti.CommHopfAlgCat.isCentralIsogeny_iff]
  rw [CommHopfAlgCat.hom_ofHom, groupAlgebraInvariantsBialgHom_toAlgHom]
  rw [groupAlgebraInvariantsAlgHom_finite_iff, groupAlgebraInvariantsAlgHom_faithfullyFlat_iff]
  refine ⟨fun ⟨hfin, hinj, _⟩ ↦ ⟨hinj, hfin⟩, fun ⟨hinj, hfin⟩ ↦ ⟨hfin, hinj, ?_⟩⟩
  exact (TauCeti.HopfIdeal.isCentral_bot_iff_isCocomm.mpr
    (groupAlgebraInvariants_isCocomm tau)).mono bot_le

end Representation.IntertwiningMap
