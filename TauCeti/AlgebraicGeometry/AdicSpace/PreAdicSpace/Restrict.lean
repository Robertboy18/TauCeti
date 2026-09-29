/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Instances
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Hom

/-!
# Restriction of pre-adic spaces to open subspaces

For a pre-adic space `X` and an open embedding `f : U ⟶ X` of topological spaces, the
restriction `X.restrict h` is the pre-adic space on `U` whose presheaf is the restriction of
the presheaf of `X`. Its stalk at `x` is the stalk of `X` at `f x`, and its valuation at `x` is
the valuation of `X` at `f x`, transported along this identification. The canonical morphism
`X.ofRestrict h : X.restrict h ⟶ X` is a morphism of pre-adic spaces.

Restrictions are the local pieces from which pre-adic spaces are assembled: a pre-adic space
is an object of `𝒱^pre` with an open cover whose members, with the restricted structure, are
isomorphic in `𝒱^pre` to affinoid pre-adic spaces. To recognise such isomorphisms we show that
the forgetful functor to presheafed spaces reflects isomorphisms: a morphism of pre-adic spaces
whose underlying morphism of presheafed spaces is an isomorphism is itself an isomorphism,
because compatibility with the stalk valuations passes to the inverse. In particular the
restriction of `X` to the whole space is isomorphic to `X`.

## Main definitions

* `TauCeti.PreAdicSpace.restrict`: the restriction of a pre-adic space along an open embedding.
* `TauCeti.PreAdicSpace.ofRestrict`: the canonical morphism from the restriction.
* `TauCeti.PreAdicSpace.restrictStalkIso`: the stalk of the restriction at `x` is the stalk of
  `X` at `f x`.
* `TauCeti.PreAdicSpace.isIso_of_isIso_toHom`: the forgetful functor to presheafed spaces
  reflects isomorphisms.
* `TauCeti.PreAdicSpace.restrictTopIso`: the restriction to the whole space is isomorphic to
  `X`.

The design follows `AlgebraicGeometry.LocallyRingedSpace.restrict`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.1.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti

universe u

namespace ValuationSpectrum

variable {P Q : PresheafedSpace CommRingCat.{u}}

/-- A family of valuations on the stalks of a presheafed space of rings is compatible with the
identification of the stalks at two equal points. -/
theorem comap_eqToHom_stalk (v : ∀ p : P, Spv (P.presheaf.stalk p)) {p q : P} (h : p = q)
    (e : P.presheaf.stalk p = P.presheaf.stalk q) :
    comap (eqToHom e).hom (v q) = v p := by
  subst h
  simp only [eqToHom_refl, CommRingCat.hom_id, comap_id, id_eq]

/-- If two families of stalk valuations are compatible along an isomorphism of presheafed
spaces of rings, they are compatible along its inverse. -/
theorem comap_stalkMap_inv (α : P ⟶ Q) [IsIso α]
    {v : ∀ p : P, Spv (P.presheaf.stalk p)} {w : ∀ q : Q, Spv (Q.presheaf.stalk q)}
    (hα : ∀ p, w (α.base p) = comap (α.stalkMap p).hom (v p)) (q : Q) :
    v ((inv α).base q) = comap ((inv α).stalkMap q).hom (w q) := by
  have hq : α.base ((inv α).base q) = q :=
    congrArg (fun φ : Q ⟶ Q => φ.base q) (IsIso.inv_hom_id α)
  have key : α.stalkMap ((inv α).base q) ≫ (inv α).stalkMap q = eqToHom (by rw [hq]) := by
    rw [← PresheafedSpace.stalkMap.comp,
      PresheafedSpace.stalkMap.congr_hom _ _ (IsIso.inv_hom_id α), PresheafedSpace.stalkMap.id]
    -- The two `eqToHom`s relate stalks at points which are definitionally equal.
    exact Category.comp_id _
  refine comap_injective (ConcreteCategory.bijective_of_isIso (α.stalkMap ((inv α).base q))).2 ?_
  rw [← hα, comap_hom_comap_hom, key, comap_eqToHom_stalk w hq]

/-- Pulling a valuation on a stalk of `P` back along the stalk map of `P.ofRestrict h` and then
along the stalk identification of the restriction returns the valuation. -/
theorem comap_stalkMap_ofRestrict_comap_restrictStalkIso {U : TopCat.{u}}
    {f : U ⟶ (P : TopCat.{u})} (h : IsOpenEmbedding f) (x : U)
    (v : Spv (P.presheaf.stalk (f x))) :
    comap ((P.ofRestrict h).stalkMap x).hom (comap (P.restrictStalkIso h x).hom.hom v) = v := by
  rw [comap_hom_comap_hom, ← PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict]
  -- The point `x` of `U` is a point of the restriction only up to unfolding, so the
  -- cancellation and the identity law are applied as terms rather than rewritten.
  exact (congrArg (fun φ => comap (CommRingCat.Hom.hom φ) v) (Iso.inv_hom_id _)).trans
    (congrFun comap_id v)

end ValuationSpectrum

namespace PreAdicSpace

section ReflectsIsomorphisms

variable {X Y : PreAdicSpace.{u}}

/-- The forgetful functor to presheafed spaces reflects isomorphisms: the inverse of the
underlying morphism of presheafed spaces is compatible with the stalk valuations. -/
instance : forgetToPresheafedSpace.{u}.ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    -- Instance search does not see the objects `forgetToPresheafedSpace.obj X` in the type of
    -- `hf` as the objects `X.toPresheafedSpace` of the morphisms below, nor does it unfold the
    -- abbreviation `toRingPresheafedSpaceHom`; both instances are therefore restated.
    have : IsIso (X := X.toPresheafedSpace) (Y := Y.toPresheafedSpace)
      (forgetToPresheafedSpace.map f) := hf
    have : IsIso (toRingPresheafedSpaceHom (forgetToPresheafedSpace.map f)) :=
      Functor.map_isIso _ _
    -- Generalising over the inverse lets the functoriality equation `map_inv` be used without
    -- rewriting under the dependent stalk types.
    have key : ∀ β : Y.toRingPresheafedSpace ⟶ X.toRingPresheafedSpace,
        β = CategoryTheory.inv (toRingPresheafedSpaceHom (forgetToPresheafedSpace.map f)) →
        ∀ y, X.stalkValuation (β.base y) =
          ValuationSpectrum.comap (β.stalkMap y).hom (Y.stalkValuation y) := by
      rintro β rfl y
      exact ValuationSpectrum.comap_stalkMap_inv
        (toRingPresheafedSpaceHom (forgetToPresheafedSpace.map f)) (v := X.stalkValuation)
        (w := Y.stalkValuation) f.stalkValuation_eq y
    exact ⟨⟨{ toHom := CategoryTheory.inv (forgetToPresheafedSpace.map f)
              stalkValuation_eq := key _ (CategoryTheory.Functor.map_inv _ _) },
      Hom.ext' (IsIso.hom_inv_id (forgetToPresheafedSpace.map f)),
      Hom.ext' (IsIso.inv_hom_id (forgetToPresheafedSpace.map f))⟩⟩

/-- A morphism of pre-adic spaces is an isomorphism as soon as its underlying morphism of
presheafed spaces of complete separated topological rings is one. -/
theorem isIso_of_isIso_toHom (f : X ⟶ Y)
    [hf : IsIso (X := X.toPresheafedSpace) (Y := Y.toPresheafedSpace) f.toHom] : IsIso f :=
  haveI : IsIso (forgetToPresheafedSpace.map f) := hf
  isIso_of_reflects_iso f forgetToPresheafedSpace

end ReflectsIsomorphisms

section Restrict

variable {U : TopCat.{u}} (X : PreAdicSpace.{u}) {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f)

-- The restriction is exposed, as the category structure is: a point of `X.restrict h` must
-- unfold to a point of `U` for statements about the restriction to typecheck.
@[expose] public section RestrictDef

/-- The restriction of a pre-adic space along an open embedding `f : U ⟶ X`. The presheaf is
the restriction of the presheaf of `X`; the stalk at `x` is identified with the stalk of `X` at
`f x`, and the valuation at `x` is the valuation of `X` at `f x` transported along this
identification. -/
noncomputable def restrict : PreAdicSpace.{u} where
  toPresheafedSpace := X.toPresheafedSpace.restrict h
  isLocalRing x :=
    @RingEquiv.isLocalRing _ _ _ (X.isLocalRing (f x)) _
      (X.toRingPresheafedSpace.restrictStalkIso h x).symm.commRingCatIsoToRingEquiv
  valuation x :=
    -- Mathlib's stalk identification is typed at the ring level, where `f x` is not
    -- syntactically a point of `X`, so the local-ring instances are passed explicitly.
    letI i : IsLocalRing (X.toRingPresheafedSpace.presheaf.stalk (f x)) := X.isLocalRing (f x)
    letI i' := @RingEquiv.isLocalRing _ _ _ i _
      (X.toRingPresheafedSpace.restrictStalkIso h x).symm.commRingCatIsoToRingEquiv
    ValuationSpectrum.comap
      (@IsLocalRing.ResidueField.map _ _ _ i' _ i
        (X.toRingPresheafedSpace.restrictStalkIso h x).hom.hom inferInstance)
      (X.valuation (f x))

end RestrictDef

@[simp]
theorem restrict_toPresheafedSpace :
    (X.restrict h).toPresheafedSpace = X.toPresheafedSpace.restrict h := by
  rfl

/-- The presheaf of rings of the restriction is the restriction of the presheaf of rings. -/
theorem toRingPresheafedSpace_restrict :
    (X.restrict h).toRingPresheafedSpace = X.toRingPresheafedSpace.restrict h := by
  rfl

/-- The stalk of the restriction at `x` is the stalk of `X` at `f x`. -/
noncomputable def restrictStalkIso (x : X.restrict h) :
    (X.restrict h).toRingPresheafedSpace.presheaf.stalk x ≅
      X.toRingPresheafedSpace.presheaf.stalk (f x) :=
  X.toRingPresheafedSpace.restrictStalkIso h x

/-- The stalk identification is Mathlib's, for the underlying presheafed spaces of rings. -/
theorem restrictStalkIso_def (x : X.restrict h) :
    X.restrictStalkIso h x = X.toRingPresheafedSpace.restrictStalkIso h x := by
  rfl

/-- The valuation of the restriction at `x` is the valuation of `X` at `f x`, pulled back along
the residue-field map of the stalk identification. -/
theorem valuation_restrict (x : X.restrict h) :
    (X.restrict h).valuation x =
      ValuationSpectrum.comap (IsLocalRing.ResidueField.map (X.restrictStalkIso h x).hom.hom)
        (X.valuation (f x)) := by
  rfl

/-- The stalk valuation of the restriction at `x` is the stalk valuation of `X` at `f x`,
pulled back along the stalk identification. -/
theorem stalkValuation_restrict (x : X.restrict h) :
    (X.restrict h).stalkValuation x =
      ValuationSpectrum.comap (X.restrictStalkIso h x).hom.hom (X.stalkValuation (f x)) := by
  rw [stalkValuation_def, stalkValuation_def, valuation_restrict,
    ← Function.comp_apply (f := ValuationSpectrum.comap _), ← ValuationSpectrum.comap_comp,
    IsLocalRing.ResidueField.map_comp_residue, ValuationSpectrum.comap_comp, Function.comp_apply]

-- The canonical morphism is exposed so that its base map unfolds to `f`.
@[expose] public section OfRestrictDef

/-- The canonical morphism from the restriction of a pre-adic space along an open embedding. -/
noncomputable def ofRestrict : X.restrict h ⟶ X where
  toHom := X.toPresheafedSpace.ofRestrict h
  stalkValuation_eq x := by
    -- Stated for a point of the restriction, where the rewrites below typecheck; the field's
    -- point ranges over the presheafed space of rings and is definitionally the same.
    have key : ∀ y : X.restrict h, X.stalkValuation (f y) =
        ValuationSpectrum.comap ((X.toRingPresheafedSpace.ofRestrict h).stalkMap y).hom
          ((X.restrict h).stalkValuation y) := by
      intro y
      rw [stalkValuation_restrict, restrictStalkIso_def]
      exact (ValuationSpectrum.comap_stalkMap_ofRestrict_comap_restrictStalkIso h y _).symm
    exact key x

end OfRestrictDef

@[simp]
theorem ofRestrict_toHom : (X.ofRestrict h).toHom = X.toPresheafedSpace.ofRestrict h := by
  rfl

theorem ofRestrict_base : (X.ofRestrict h).base = f := by
  rfl

/-- The stalk map of `X.ofRestrict h` is the inverse of the stalk identification. -/
theorem stalkMap_ofRestrict (x : X.restrict h) :
    (X.ofRestrict h).stalkMap x = (X.restrictStalkIso h x).inv := by
  rw [Hom.stalkMap_def, restrictStalkIso_def]
  exact (PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict X.toRingPresheafedSpace h x).symm

/-- The restriction of a pre-adic space to the whole space is isomorphic to the space. -/
noncomputable def restrictTopIso : X.restrict (Opens.isOpenEmbedding ⊤) ≅ X :=
  haveI : IsIso (X := (X.restrict (Opens.isOpenEmbedding ⊤)).toPresheafedSpace)
      (Y := X.toPresheafedSpace) (X.ofRestrict (Opens.isOpenEmbedding ⊤)).toHom :=
    (PresheafedSpace.restrictTopIso X.toPresheafedSpace).isIso_hom
  haveI := isIso_of_isIso_toHom (X.ofRestrict (Opens.isOpenEmbedding ⊤))
  asIso (X.ofRestrict (Opens.isOpenEmbedding ⊤))

@[simp]
theorem restrictTopIso_hom : X.restrictTopIso.hom = X.ofRestrict (Opens.isOpenEmbedding ⊤) := by
  rfl

end Restrict

end PreAdicSpace

end TauCeti

end
