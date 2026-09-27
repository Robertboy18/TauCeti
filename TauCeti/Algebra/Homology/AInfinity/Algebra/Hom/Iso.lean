/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Cohomology

/-!
# Isomorphisms of A-infinity algebras

A morphism of `A∞` algebras is an *isomorphism* when it has a two-sided inverse `A∞` morphism.
This happens exactly when its linear part `f₁` is bijective.  Indeed the bar map of an `A∞`
morphism is a coalgebra morphism of reduced tensor coalgebras whose arity-one component is `f₁`,
so it is bijective as soon as `f₁` is (see
`TauCeti.ReducedTensorWords.IsCoalgHom.bijective_of_letter_comp_comp_ofLetter_bijective`), and
its inverse is again a degree-zero coalgebra morphism intertwining the bar differentials.  The
inverse `A∞` morphism `TauCeti.AInfinityHom.inverse` is that inverse bar map; its linear part is
the inverse of `f₁`.

Every isomorphism is a quasi-isomorphism.  Between minimal algebras the converse holds, see
`TauCeti.Algebra.Homology.AInfinity.Algebra.Minimal`: a quasi-isomorphism between minimal
algebras is an `A∞` isomorphism.  This is one ingredient of the uniqueness clause of Kadeishvili's
theorem, which additionally needs the existence of such a quasi-isomorphism between two minimal
models; that existence is not proved here.

## Main definitions

* `TauCeti.AInfinityHom.inverse`: the inverse of an `A∞` morphism with bijective linear part.
* `TauCeti.AInfinityHom.IsIso`: an `A∞` morphism with a two-sided inverse.

## Main results

* `TauCeti.AInfinityHom.inverse_comp` and `TauCeti.AInfinityHom.comp_inverse`: the inverse is a
  two-sided inverse, and `TauCeti.AInfinityHom.linearPart_inverse`: its linear part is the inverse
  linear equivalence.
* `TauCeti.AInfinityHom.isIso_iff_linearPart_bijective`: an `A∞` morphism is an isomorphism exactly
  when its linear part is bijective.
* `TauCeti.AInfinityHom.IsIso.isQuasiIso`: an isomorphism is a quasi-isomorphism.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.3 and 3.4.
* K. Lefèvre-Hasegawa, *Sur les A∞-catégories*, Chapter 1.
-/

public section

namespace TauCeti

universe uR uA uB uC

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

namespace AInfinityHom

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-! ### The inverse of a morphism with bijective linear part -/

/-- The bar map of an `A∞` morphism with bijective linear part is bijective. -/
theorem barMap_bijective_of_linearPart_bijective (f : AInfinityHom AA BB)
    (hf : Function.Bijective f.linearPart) : Function.Bijective f.barMap :=
  f.isCoalgHom_barMap.bijective_of_letter_comp_comp_ofLetter_bijective
    (by rwa [letter_comp_barMap_comp_ofLetter])

/-- The bar map of an `A∞` morphism with bijective linear part, as a linear equivalence of reduced
bar constructions. -/
noncomputable def barEquiv (f : AInfinityHom AA BB) (hf : Function.Bijective f.linearPart) :
    ReducedTensorWords R A ≃ₗ[R] ReducedTensorWords R B :=
  LinearEquiv.ofBijective f.barMap (f.barMap_bijective_of_linearPart_bijective hf)

@[simp]
theorem barEquiv_apply (f : AInfinityHom AA BB) (hf : Function.Bijective f.linearPart)
    (z : ReducedTensorWords R A) : f.barEquiv hf z = f.barMap z := (rfl)

theorem coe_barEquiv (f : AInfinityHom AA BB) (hf : Function.Bijective f.linearPart) :
    (f.barEquiv hf).toLinearMap = f.barMap :=
  LinearMap.ext (f.barEquiv_apply hf)

/-- The inverse of an `A∞` morphism with bijective linear part: its bar map is the inverse of the
bar map, which is again a degree-zero coalgebra morphism intertwining the bar differentials. -/
noncomputable def inverse (f : AInfinityHom AA BB) (hf : Function.Bijective f.linearPart) :
    AInfinityHom BB AA where
  barMap := (f.barEquiv hf).symm.toLinearMap
  isCoalgHom_barMap := by
    have h : ReducedTensorWords.IsCoalgHom R (f.barEquiv hf).toLinearMap := by
      rw [coe_barEquiv]
      exact f.isCoalgHom_barMap
    exact h.linearEquiv_symm
  isHomogeneous_barMap := by
    have h : ReducedTensorWords.IsCoalgHom R (f.barEquiv hf).toLinearMap := by
      rw [coe_barEquiv]
      exact f.isCoalgHom_barMap
    refine h.isHomogeneous_linearEquiv_symm ?_
    rw [coe_barEquiv]
    exact f.isHomogeneous_barMap
  barDifferential_comp_barMap := by
    refine LinearMap.ext fun w ↦ (f.barEquiv hf).injective ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, barEquiv_apply, ← barDifferential_barMap, ← barEquiv_apply f hf,
      LinearEquiv.apply_symm_apply]

@[simp]
theorem barMap_inverse (f : AInfinityHom AA BB) (hf : Function.Bijective f.linearPart) :
    (f.inverse hf).barMap = (f.barEquiv hf).symm.toLinearMap := (rfl)

@[simp]
theorem barEquiv_symm_barMap (f : AInfinityHom AA BB) (hf : Function.Bijective f.linearPart)
    (z : ReducedTensorWords R A) : (f.barEquiv hf).symm (f.barMap z) = z := by
  rw [← barEquiv_apply f hf, LinearEquiv.symm_apply_apply]

@[simp]
theorem barMap_barEquiv_symm (f : AInfinityHom AA BB) (hf : Function.Bijective f.linearPart)
    (w : ReducedTensorWords R B) : f.barMap ((f.barEquiv hf).symm w) = w := by
  rw [← barEquiv_apply f hf, LinearEquiv.apply_symm_apply]

/-- The inverse is a left inverse. -/
@[simp]
theorem inverse_comp (f : AInfinityHom AA BB) (hf : Function.Bijective f.linearPart) :
    (f.inverse hf).comp f = AInfinityHom.id AA :=
  barMap_injective <| by
    rw [barMap_comp, barMap_id, barMap_inverse]
    exact LinearMap.ext (f.barEquiv_symm_barMap hf)

/-- The inverse is a right inverse. -/
@[simp]
theorem comp_inverse (f : AInfinityHom AA BB) (hf : Function.Bijective f.linearPart) :
    f.comp (f.inverse hf) = AInfinityHom.id BB :=
  barMap_injective <| by
    rw [barMap_comp, barMap_id, barMap_inverse]
    exact LinearMap.ext (f.barMap_barEquiv_symm hf)

/-- The linear part of the inverse is the inverse of the linear part. -/
@[simp]
theorem linearPart_inverse (f : AInfinityHom AA BB) (hf : Function.Bijective f.linearPart) :
    (f.inverse hf).linearPart = (LinearEquiv.ofBijective f.linearPart hf).symm.toLinearMap := by
  have h := congrArg linearPart (f.inverse_comp hf)
  rw [linearPart_comp, linearPart_id] at h
  refine LinearMap.ext fun b ↦ ?_
  obtain ⟨a, rfl⟩ := hf.2 b
  rw [LinearEquiv.coe_coe, LinearEquiv.ofBijective_symm_apply_apply, ← LinearMap.comp_apply, h,
    LinearMap.id_apply]

/-- The linear part of the inverse is bijective. -/
theorem linearPart_inverse_bijective (f : AInfinityHom AA BB)
    (hf : Function.Bijective f.linearPart) : Function.Bijective (f.inverse hf).linearPart := by
  rw [linearPart_inverse]
  exact (LinearEquiv.ofBijective f.linearPart hf).symm.bijective

/-! ### Isomorphisms -/

/-- An `A∞` morphism is an **isomorphism** when it has a two-sided inverse `A∞` morphism. -/
def IsIso (f : AInfinityHom AA BB) : Prop :=
  ∃ g : AInfinityHom BB AA, g.comp f = AInfinityHom.id AA ∧ f.comp g = AInfinityHom.id BB

/-- The identity `A∞` morphism is an isomorphism. -/
@[simp]
theorem isIso_id (AA : AInfinityAlgebra R A) : (AInfinityHom.id AA).IsIso :=
  ⟨AInfinityHom.id AA, comp_id _, comp_id _⟩

/-- Isomorphisms of `A∞` algebras are closed under composition. -/
theorem IsIso.comp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB} (hg : g.IsIso)
    (hf : f.IsIso) : (g.comp f).IsIso := by
  obtain ⟨g', hg₁, hg₂⟩ := hg
  obtain ⟨f', hf₁, hf₂⟩ := hf
  refine ⟨f'.comp g', ?_, ?_⟩
  · rw [comp_assoc, ← comp_assoc g', hg₁, id_comp, hf₁]
  · rw [comp_assoc, ← comp_assoc f, hf₂, id_comp, hg₂]

/-- An `A∞` morphism with bijective linear part is an isomorphism. -/
theorem isIso_of_linearPart_bijective (f : AInfinityHom AA BB)
    (hf : Function.Bijective f.linearPart) : f.IsIso :=
  ⟨f.inverse hf, f.inverse_comp hf, f.comp_inverse hf⟩

/-- The inverse of an `A∞` morphism with bijective linear part is an isomorphism. -/
theorem isIso_inverse (f : AInfinityHom AA BB) (hf : Function.Bijective f.linearPart) :
    (f.inverse hf).IsIso :=
  ⟨f, f.comp_inverse hf, f.inverse_comp hf⟩

/-- The linear part of an isomorphism is bijective. -/
theorem IsIso.linearPart_bijective {f : AInfinityHom AA BB} (h : f.IsIso) :
    Function.Bijective f.linearPart := by
  obtain ⟨g, hg₁, hg₂⟩ := h
  refine Function.bijective_iff_has_inverse.2 ⟨g.linearPart, fun a ↦ ?_, fun b ↦ ?_⟩
  · rw [← LinearMap.comp_apply, ← linearPart_comp, hg₁, linearPart_id, LinearMap.id_apply]
  · rw [← LinearMap.comp_apply, ← linearPart_comp, hg₂, linearPart_id, LinearMap.id_apply]

/-- An `A∞` morphism is an isomorphism exactly when its linear part is bijective. -/
theorem isIso_iff_linearPart_bijective (f : AInfinityHom AA BB) :
    f.IsIso ↔ Function.Bijective f.linearPart :=
  ⟨IsIso.linearPart_bijective, f.isIso_of_linearPart_bijective⟩

/-- An isomorphism of `A∞` algebras is a quasi-isomorphism. -/
theorem IsIso.isQuasiIso {f : AInfinityHom AA BB} (h : f.IsIso) : f.IsQuasiIso := by
  obtain ⟨g, hg₁, hg₂⟩ := h
  rw [isQuasiIso_def]
  refine Function.bijective_iff_has_inverse.2 ⟨g.cohomologyMap, fun x ↦ ?_, fun y ↦ ?_⟩
  · rw [← NonUnitalAlgHom.comp_apply, ← cohomologyMap_comp, hg₁, cohomologyMap_id,
      NonUnitalAlgHom.coe_id, id_eq]
  · rw [← NonUnitalAlgHom.comp_apply, ← cohomologyMap_comp, hg₂, cohomologyMap_id,
      NonUnitalAlgHom.coe_id, id_eq]

end AInfinityHom

end TauCeti
