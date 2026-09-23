/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars

/-!
# Invariance of `K₀(proj R)`, `G₀(mod R)` and the Cartan map under ring isomorphisms

A ring isomorphism `e : R ≃+* S` induces, by restriction of scalars, an equivalence of module
categories `ModuleCat S ≌ ModuleCat R`. It preserves and reflects finite generation and
projectivity, and it is exact, so it restricts to exact equivalences between the finitely
generated modules and between the finitely generated projective modules over the two rings. On
Grothendieck groups this gives isomorphisms

```text
K₀(proj S) ≃ K₀(proj R),   G₀(mod S) ≃ G₀(mod R),
```

both sending the class of a module to the class of the same module with scalars restricted along
`e`, and the square they form with the two Cartan maps commutes. In particular the Cartan map of
`R` is an isomorphism if and only if that of `S` is.

For an algebra isomorphism `e : A ≃ₐ[k] B` the statements apply to `e.toRingEquiv`, so
`K₀(proj A)`, `G₀(mod A)` and the Cartan map are invariants of the isomorphism class of the
algebra `A`.

## Main definitions

* `TauCeti.finiteModulesEquivalenceOfRingEquiv` and
  `TauCeti.finiteProjectiveModulesEquivalenceOfRingEquiv`: restriction of scalars along a ring
  isomorphism, as equivalences between the finitely generated, respectively finitely generated
  projective, modules over the two rings.
* `TauCeti.finiteModulesK0EquivOfRingEquiv` and
  `TauCeti.finiteProjectiveModulesK0EquivOfRingEquiv`: the induced isomorphisms
  `G₀(mod S) ≃+ G₀(mod R)` and `K₀(proj S) ≃+ K₀(proj R)`.

## Main results

* `TauCeti.isFG_inverseImage_restrictScalars` and
  `TauCeti.finiteProjectiveModules_inverseImage_restrictScalars`: restriction of scalars along a
  ring isomorphism pulls the two object properties back to each other.
* `TauCeti.isConflationExact_restrictScalars_of_ringEquiv`: restriction of scalars along a ring
  isomorphism is conflation-exact for the canonical exact structures.
* `TauCeti.cartanMap_comp_finiteProjectiveModulesK0EquivOfRingEquiv` and
  `TauCeti.cartanMap_finiteProjectiveModulesK0EquivOfRingEquiv`: the Cartan maps of `R` and `S`
  commute with the two induced isomorphisms.
* `TauCeti.cartanMap_bijective_iff`: the Cartan map of `R` is bijective if and only if the Cartan
  map of `S` is.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 2,
  for the invariance of `K₀` of a ring under ring isomorphisms and Morita equivalences.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.ObjectProperty

universe u

variable {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S)

/-! ### Restriction of scalars on the two object properties -/

/-- Restriction of scalars along a ring isomorphism pulls the finitely generated `R`-modules
back to the finitely generated `S`-modules. -/
theorem isFG_inverseImage_restrictScalars :
    (ModuleCat.isFG.{u} R).inverseImage (ModuleCat.restrictScalars e.toRingHom) =
      ModuleCat.isFG.{u} S :=
  funext fun M ↦ propext (ModuleCat.isFG_restrictScalars_iff e.toRingHom e.surjective M)

/-- Restriction of scalars along a ring isomorphism pulls the finitely generated projective
`R`-modules back to the finitely generated projective `S`-modules. -/
theorem finiteProjectiveModules_inverseImage_restrictScalars :
    (finiteProjectiveModules R).inverseImage (ModuleCat.restrictScalars e.toRingHom) =
      finiteProjectiveModules S := by
  funext M
  rw [prop_inverseImage_iff, finiteProjectiveModules_iff, finiteProjectiveModules_iff,
    ModuleCat.finite_restrictScalars_iff e.toRingHom e.surjective,
    ModuleCat.projective_restrictScalars_iff e]

/-- Restriction of scalars along a ring isomorphism is conflation-exact for the canonical exact
structures of the two module categories. -/
theorem isConflationExact_restrictScalars_of_ringEquiv :
    (ExactStructure.abelian (ModuleCat.{u} S)).IsConflationExact
      (ExactStructure.abelian (ModuleCat.{u} R)) (ModuleCat.restrictScalars e.toRingHom) :=
  ExactStructure.isConflationExact_abelian _

/-! ### The equivalences of module subcategories

The two pullback equalities above are transported along
`ModuleCat.restrictScalarsEquivalenceOfRingEquiv_functor` before being passed to
`CategoryTheory.Equivalence.congrFullSubcategory`: the additivity instance of the restricted
equivalence is found by instance search only when the hypothesis is stated syntactically for the
functor of `ModuleCat.restrictScalarsEquivalenceOfRingEquiv e`. -/

/-- **Restriction of scalars on finitely generated modules.** A ring isomorphism `e : R ≃+* S`
induces an equivalence from the finitely generated `S`-modules to the finitely generated
`R`-modules, sending a module to the same module with scalars restricted along `e`. -/
noncomputable def finiteModulesEquivalenceOfRingEquiv : FGModuleCat.{u} S ≌ FGModuleCat.{u} R :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).congrFullSubcategory
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv_functor e ▸
      isFG_inverseImage_restrictScalars e)

/-- **Restriction of scalars on finitely generated projective modules.** A ring isomorphism
`e : R ≃+* S` induces an equivalence from the finitely generated projective `S`-modules to the
finitely generated projective `R`-modules, sending a module to the same module with scalars
restricted along `e`. -/
noncomputable def finiteProjectiveModulesEquivalenceOfRingEquiv :
    (finiteProjectiveModules S).FullSubcategory ≌ (finiteProjectiveModules R).FullSubcategory :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).congrFullSubcategory
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv_functor e ▸
      finiteProjectiveModules_inverseImage_restrictScalars e)

instance : (finiteModulesEquivalenceOfRingEquiv e).functor.Additive := by
  unfold finiteModulesEquivalenceOfRingEquiv
  infer_instance

instance : (finiteProjectiveModulesEquivalenceOfRingEquiv e).functor.Additive := by
  unfold finiteProjectiveModulesEquivalenceOfRingEquiv
  infer_instance

@[simp]
theorem finiteModulesEquivalenceOfRingEquiv_functor_obj_obj (M : FGModuleCat.{u} S) :
    ((finiteModulesEquivalenceOfRingEquiv e).functor.obj M).obj =
      (ModuleCat.restrictScalars e.toRingHom).obj M.obj :=
  (rfl)

@[simp]
theorem finiteModulesEquivalenceOfRingEquiv_inverse_obj_obj (M : FGModuleCat.{u} R) :
    ((finiteModulesEquivalenceOfRingEquiv e).inverse.obj M).obj =
      (ModuleCat.restrictScalars e.symm.toRingHom).obj M.obj :=
  (rfl)

@[simp]
theorem finiteProjectiveModulesEquivalenceOfRingEquiv_functor_obj_obj
    (M : (finiteProjectiveModules S).FullSubcategory) :
    ((finiteProjectiveModulesEquivalenceOfRingEquiv e).functor.obj M).obj =
      (ModuleCat.restrictScalars e.toRingHom).obj M.obj :=
  (rfl)

@[simp]
theorem finiteProjectiveModulesEquivalenceOfRingEquiv_inverse_obj_obj
    (M : (finiteProjectiveModules R).FullSubcategory) :
    ((finiteProjectiveModulesEquivalenceOfRingEquiv e).inverse.obj M).obj =
      (ModuleCat.restrictScalars e.symm.toRingHom).obj M.obj :=
  (rfl)

/-- The equivalence of finitely generated module categories induced by a ring isomorphism is
conflation-exact. -/
theorem isConflationExact_finiteModulesEquivalenceOfRingEquiv_functor :
    (finiteModulesExactStructure S).IsConflationExact (finiteModulesExactStructure R)
      (finiteModulesEquivalenceOfRingEquiv e).functor :=
  isConflationExact_finiteModules_congrFullSubcategory_functor _
    (isConflationExact_restrictScalars_of_ringEquiv e) _

/-- The inverse of the equivalence of finitely generated module categories induced by a ring
isomorphism is conflation-exact. -/
theorem isConflationExact_finiteModulesEquivalenceOfRingEquiv_inverse :
    (finiteModulesExactStructure R).IsConflationExact (finiteModulesExactStructure S)
      (finiteModulesEquivalenceOfRingEquiv e).inverse :=
  isConflationExact_finiteModules_congrFullSubcategory_inverse _
    (isConflationExact_restrictScalars_of_ringEquiv e.symm) _

/-- The equivalence of finitely generated projective module categories induced by a ring
isomorphism is conflation-exact. -/
theorem isConflationExact_finiteProjectiveModulesEquivalenceOfRingEquiv_functor :
    (finiteProjectiveModulesExactStructure S).IsConflationExact
      (finiteProjectiveModulesExactStructure R)
      (finiteProjectiveModulesEquivalenceOfRingEquiv e).functor :=
  isConflationExact_finiteProjectiveModules_congrFullSubcategory_functor _
    (isConflationExact_restrictScalars_of_ringEquiv e) _

/-- The inverse of the equivalence of finitely generated projective module categories induced by
a ring isomorphism is conflation-exact. -/
theorem isConflationExact_finiteProjectiveModulesEquivalenceOfRingEquiv_inverse :
    (finiteProjectiveModulesExactStructure R).IsConflationExact
      (finiteProjectiveModulesExactStructure S)
      (finiteProjectiveModulesEquivalenceOfRingEquiv e).inverse :=
  isConflationExact_finiteProjectiveModules_congrFullSubcategory_inverse _
    (isConflationExact_restrictScalars_of_ringEquiv e.symm) _

/-! ### The induced isomorphisms of Grothendieck groups -/

/-- **Invariance of `G₀(mod R)` under ring isomorphisms.** A ring isomorphism `e : R ≃+* S`
induces `G₀(mod S) ≃+ G₀(mod R)`, sending the class of a finitely generated `S`-module to the
class of the same module with scalars restricted along `e`. -/
noncomputable def finiteModulesK0EquivOfRingEquiv :
    ExactK0.{u} (finiteModulesExactStructure S) ≃+ ExactK0.{u} (finiteModulesExactStructure R) :=
  ExactK0.mapEquiv (finiteModulesEquivalenceOfRingEquiv e)
    (isConflationExact_finiteModulesEquivalenceOfRingEquiv_functor e)
    (isConflationExact_finiteModulesEquivalenceOfRingEquiv_inverse e)

/-- **Invariance of `K₀(proj R)` under ring isomorphisms.** A ring isomorphism `e : R ≃+* S`
induces `K₀(proj S) ≃+ K₀(proj R)`, sending the class of a finitely generated projective
`S`-module to the class of the same module with scalars restricted along `e`. -/
noncomputable def finiteProjectiveModulesK0EquivOfRingEquiv :
    ExactK0.{u} (finiteProjectiveModulesExactStructure S) ≃+
      ExactK0.{u} (finiteProjectiveModulesExactStructure R) :=
  ExactK0.mapEquiv (finiteProjectiveModulesEquivalenceOfRingEquiv e)
    (isConflationExact_finiteProjectiveModulesEquivalenceOfRingEquiv_functor e)
    (isConflationExact_finiteProjectiveModulesEquivalenceOfRingEquiv_inverse e)

@[simp]
theorem finiteModulesK0EquivOfRingEquiv_of (M : FGModuleCat.{u} S) :
    finiteModulesK0EquivOfRingEquiv e (ExactK0.of M) =
      ExactK0.of ((finiteModulesEquivalenceOfRingEquiv e).functor.obj M) :=
  ExactK0.mapEquiv_of.{u, u} _ _ _ M

@[simp]
theorem finiteModulesK0EquivOfRingEquiv_symm_of (M : FGModuleCat.{u} R) :
    (finiteModulesK0EquivOfRingEquiv e).symm (ExactK0.of M) =
      ExactK0.of ((finiteModulesEquivalenceOfRingEquiv e).inverse.obj M) :=
  ExactK0.mapEquiv_symm_of.{u, u} _ _ _ M

@[simp]
theorem finiteProjectiveModulesK0EquivOfRingEquiv_of
    (M : (finiteProjectiveModules S).FullSubcategory) :
    finiteProjectiveModulesK0EquivOfRingEquiv e (ExactK0.of.{u} M) =
      ExactK0.of.{u} ((finiteProjectiveModulesEquivalenceOfRingEquiv e).functor.obj M) :=
  ExactK0.mapEquiv_of.{u, u} _ _ _ M

@[simp]
theorem finiteProjectiveModulesK0EquivOfRingEquiv_symm_of
    (M : (finiteProjectiveModules R).FullSubcategory) :
    (finiteProjectiveModulesK0EquivOfRingEquiv e).symm (ExactK0.of.{u} M) =
      ExactK0.of.{u} ((finiteProjectiveModulesEquivalenceOfRingEquiv e).inverse.obj M) :=
  ExactK0.mapEquiv_symm_of.{u, u} _ _ _ M

/-! ### Compatibility with the Cartan map -/

/-- **Naturality of the Cartan map in the ring.** The Cartan maps of two isomorphic rings are
intertwined by the induced isomorphisms of Grothendieck groups. -/
theorem cartanMap_comp_finiteProjectiveModulesK0EquivOfRingEquiv :
    (cartanMap R).comp (finiteProjectiveModulesK0EquivOfRingEquiv e).toAddMonoidHom =
      (finiteModulesK0EquivOfRingEquiv e).toAddMonoidHom.comp (cartanMap S) := by
  apply ExactK0.hom_ext
  rintro ⟨M, hM⟩
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    finiteProjectiveModulesK0EquivOfRingEquiv_of, cartanMap_of S hM,
    finiteModulesK0EquivOfRingEquiv_of]
  rw [cartanMap_of R
    ((finiteProjectiveModulesEquivalenceOfRingEquiv e).functor.obj ⟨M, hM⟩).property]
  exact congrArg ExactK0.of (ObjectProperty.FullSubcategory.ext (by simp))

@[simp]
theorem cartanMap_finiteProjectiveModulesK0EquivOfRingEquiv
    (x : ExactK0.{u} (finiteProjectiveModulesExactStructure S)) :
    cartanMap R (finiteProjectiveModulesK0EquivOfRingEquiv e x) =
      finiteModulesK0EquivOfRingEquiv e (cartanMap S x) :=
  DFunLike.congr_fun (cartanMap_comp_finiteProjectiveModulesK0EquivOfRingEquiv e) x

include e in
/-- **The resolution-theorem hypothesis is invariant under ring isomorphisms**: the Cartan map of
`R` is bijective if and only if the Cartan map of `S` is. -/
theorem cartanMap_bijective_iff :
    Function.Bijective (cartanMap R) ↔ Function.Bijective (cartanMap S) := by
  have hR : ⇑(cartanMap R) =
      ⇑(finiteModulesK0EquivOfRingEquiv e) ∘ ⇑(cartanMap S) ∘
        ⇑(finiteProjectiveModulesK0EquivOfRingEquiv e).symm := by
    ext x
    simp only [Function.comp_apply, ← cartanMap_finiteProjectiveModulesK0EquivOfRingEquiv,
      AddEquiv.apply_symm_apply]
  have hS : ⇑(cartanMap S) =
      ⇑(finiteModulesK0EquivOfRingEquiv e).symm ∘ ⇑(cartanMap R) ∘
        ⇑(finiteProjectiveModulesK0EquivOfRingEquiv e) := by
    ext x
    simp only [Function.comp_apply, cartanMap_finiteProjectiveModulesK0EquivOfRingEquiv,
      AddEquiv.symm_apply_apply]
  constructor
  · intro h
    rw [hS]
    exact (finiteModulesK0EquivOfRingEquiv e).symm.bijective.comp
      (h.comp (finiteProjectiveModulesK0EquivOfRingEquiv e).bijective)
  · intro h
    rw [hR]
    exact (finiteModulesK0EquivOfRingEquiv e).bijective.comp
      (h.comp (finiteProjectiveModulesK0EquivOfRingEquiv e).symm.bijective)

end TauCeti
