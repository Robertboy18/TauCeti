/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import TauCeti.CategoryTheory.Sites.TopologicalBasis
public import TauCeti.CategoryTheory.Thin

/-!
# Presheaves adapted to a basis

A presheaf `F` on a topological space `X` is *adapted* to a set `B` of opens if, for every open
`V`, the restriction maps `F(V) ⟶ F(U)` to the members `U ∈ B` with `U ≤ V` exhibit `F(V)` as the
limit of the `F(U)`. In the language of Kan extensions, `F` is the pointwise right Kan extension
of its restriction to `B` along the inclusion of `B` into the opens of `X`. This is the sense in
which the structure presheaf of an adic spectrum, defined on rational opens and extended to all
opens by limits, is determined by its values on the rational opens.

When `B` is a basis of the topology, an adapted presheaf is a sheaf exactly when its restriction
to `B` is a sheaf for the topology restricted to `B`; this is what makes sheaf conditions checkable
on a basis for presheaves defined by such limits. Only the direction from `B` to `X` uses
adaptedness; the other direction holds for every sheaf.

## Main definitions

* `TopCat.Presheaf.IsAdapted`: `F` is adapted to `B`.

## Main results

* `TopCat.Presheaf.isSheaf_of_isAdapted_of_isSheaf_restrictedTopology`: an adapted presheaf whose
  restriction to `B` is a sheaf for the restricted topology is a sheaf.
* `TopCat.Presheaf.IsSheaf.isSheaf_restrictedTopology`: the restriction of a sheaf to a basis is a
  sheaf for the restricted topology.
* `TopCat.Presheaf.isSheaf_iff_of_isAdapted`: for a presheaf adapted to a basis, the two sheaf
  conditions are equivalent.
* `TopCat.Presheaf.IsAdapted.mono`: a presheaf adapted to `B` is adapted to every `B' ⊇ B`. This
  is how adaptedness to the rational opens of an adic spectrum yields adaptedness to its open
  affinoid subspaces.
* `TopCat.Presheaf.IsAdapted.of_iso`, `TopCat.Presheaf.IsAdapted.pushforward_of_iso`:
  adaptedness is invariant under isomorphism of presheaves and under homeomorphism, for the family
  of opens whose preimages lie in `B`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Remark and Definition 8.9.
* M. Artin, A. Grothendieck, J.-L. Verdier, *Théorie des topos et cohomologie étale des schémas*
  (SGA 4), Tome 1, Exposé III, 2.2, for the passage from a sheaf on the basis to a sheaf on the
  space, which is Mathlib's `CategoryTheory.RanIsSheafOfIsCocontinuous.isLimitMultifork`.
-/

public section

universe w v u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C] {X : TopCat.{w}} (F : X.Presheaf C) (B : Set (Opens X))

/-- A presheaf `F` on `X` is adapted to a set `B` of opens if, at every open `V`, the restriction
maps to the members of `B` contained in `V` make `F.obj (op V)` the limit of `F` over them: `F`
is the pointwise right Kan extension of its restriction to `B`. -/
@[expose] def IsAdapted : Prop :=
  Nonempty (Functor.RightExtension.mk F
    (𝟙 ((inducedFunctor (Subtype.val : B → Opens X)).op ⋙ F))).IsPointwiseRightKanExtension

/-! ### Enlarging the family -/

section Mono

variable {F} {B} {B' : Set (Opens X)}

/-- A member of `B ⊆ B'` as a member of `B'`. -/
private def memOfSubset (hBB' : B ⊆ B')
    (b : InducedCategory (Opens X) (Subtype.val : B → Opens X)) :
    InducedCategory (Opens X) (Subtype.val : B' → Opens X) :=
  ⟨b.1, hBB' b.2⟩

/-- For `B ⊆ B'`, the functor from the members of `B` below an open `Y` to the members of `B'`
below `Y`, reading a member of `B` as a member of `B'`. -/
private def structuredArrowOfSubset (hBB' : B ⊆ B') (Y : (Opens X)ᵒᵖ) :
    StructuredArrow Y (inducedFunctor (Subtype.val : B → Opens X)).op ⥤
      StructuredArrow Y (inducedFunctor (Subtype.val : B' → Opens X)).op where
  obj g := StructuredArrow.mk (Y := op (memOfSubset hBB' g.right.unop)) g.hom
  map φ := StructuredArrow.homMk
    (InducedCategory.homMk (X := memOfSubset hBB' _) (Y := memOfSubset hBB' _)
      φ.right.unop.hom).op (Subsingleton.elim _ _)

/-- Reading a member of `B` below `Y` as a member of `B'` does not change the leg of the
Kan-extension cone of `F` at it: both are the restriction map of `F` from `Y`. -/
private theorem coneAt_π_app_structuredArrowOfSubset_obj (hBB' : B ⊆ B') {Y : (Opens X)ᵒᵖ}
    (g : StructuredArrow Y (inducedFunctor (Subtype.val : B → Opens X)).op) :
    ((Functor.RightExtension.mk F
      (𝟙 ((inducedFunctor (Subtype.val : B' → Opens X)).op ⋙ F))).coneAt Y).π.app
        ((structuredArrowOfSubset hBB' Y).obj g) =
      ((Functor.RightExtension.mk F
        (𝟙 ((inducedFunctor (Subtype.val : B → Opens X)).op ⋙ F))).coneAt Y).π.app g :=
  rfl

/-- A cone over the members of `B' ⊇ B` below `Y` restricts to a cone over the members of `B`. -/
@[simps]
private def coneOfSubset (hBB' : B ⊆ B') {Y : (Opens X)ᵒᵖ}
    (s : Cone (StructuredArrow.proj Y (inducedFunctor (Subtype.val : B' → Opens X)).op ⋙
      (inducedFunctor (Subtype.val : B' → Opens X)).op ⋙ F)) :
    Cone (StructuredArrow.proj Y (inducedFunctor (Subtype.val : B → Opens X)).op ⋙
      (inducedFunctor (Subtype.val : B → Opens X)).op ⋙ F) where
  pt := s.pt
  π :=
    { app := fun g ↦ s.π.app ((structuredArrowOfSubset hBB' Y).obj g)
      -- the restriction map of `F` along a morphism of members of `B`, and along the same
      -- morphism read in `B'`, are the same morphism of `F`, so this is naturality of `s`
      naturality := fun _ _ φ ↦
        (Category.id_comp _).trans (s.w ((structuredArrowOfSubset hBB' Y).map φ)).symm }

/-- **Adaptedness passes to a larger family.** If `F` is adapted to `B` and `B ⊆ B'`, then `F`
is adapted to `B'`: a compatible family on the members of `B'` below `V` is determined by its
restriction to the members of `B`, and a compatible family on the members of `B` below `V`
extends to the members `U' ∈ B'` below `V` through the limit description of `F(U')`. -/
theorem IsAdapted.mono (hBB' : B ⊆ B') (hF : F.IsAdapted B) : F.IsAdapted B' := by
  obtain ⟨h⟩ := hF
  refine ⟨fun Y ↦ IsLimit.mk (fun s ↦ (h Y).lift (coneOfSubset hBB' s)) (fun s g ↦ ?_)
    (fun s m hm ↦ ?_)⟩
  · -- the leg at `U' ∈ B'` is determined by its restrictions to the members `U ∈ B` below `U'`
    refine (h ((inducedFunctor (Subtype.val : B' → Opens X)).op.obj g.right)).hom_ext'
      fun U φ ↦ ?_
    -- both sides are the leg of `s` at `U`, read as a member of `B'` below `Y`
    have h₁ := (h Y).fac (coneOfSubset hBB' s) (StructuredArrow.mk (g.hom ≫ φ))
    -- the restriction along `φ`, read as a morphism of members of `B'` below `Y`; the type
    -- ascription records that its image under the diagram is `F.map φ`, which holds by definition
    have h₂ : s.π.app g ≫ F.map φ =
        s.π.app ((structuredArrowOfSubset hBB' Y).obj (StructuredArrow.mk (g.hom ≫ φ))) :=
      s.w (StructuredArrow.homMk
        (InducedCategory.homMk (X := memOfSubset hBB' U.unop) (Y := g.right.unop) φ.unop).op
          (Subsingleton.elim _ _) :
        g ⟶ (structuredArrowOfSubset hBB' Y).obj (StructuredArrow.mk (g.hom ≫ φ)))
    simp only [Functor.RightExtension.coneAt_π_app, Functor.RightExtension.mk_left,
      Functor.RightExtension.mk_hom, NatTrans.id_app, Functor.comp_obj, Category.comp_id,
      StructuredArrow.mk_right, StructuredArrow.mk_hom_eq_self, Functor.map_comp,
      coneOfSubset_π_app] at h₁ ⊢
    exact (Category.assoc _ _ _).trans (h₁.trans h₂.symm)
  · -- a morphism into `F(Y)` is determined by its restrictions to the members of `B` below `Y`
    refine (h Y).uniq (coneOfSubset hBB' s) m fun g ↦ ?_
    rw [coneOfSubset_π_app, ← coneAt_π_app_structuredArrowOfSubset_obj hBB' g]
    exact hm _

end Mono

/-! ### Transport along isomorphisms -/

section OfIso

variable {F} {B}

/-- **Adaptedness is invariant under isomorphism of presheaves.** -/
theorem IsAdapted.of_iso {G : X.Presheaf C} (e : F ≅ G) (hF : F.IsAdapted B) : G.IsAdapted B := by
  obtain ⟨h⟩ := hF
  refine ⟨fun Y ↦ IsLimit.equivOfNatIsoOfIso
    (Functor.isoWhiskerLeft (StructuredArrow.proj Y (inducedFunctor (Subtype.val : B → Opens X)).op)
      (Functor.isoWhiskerLeft (inducedFunctor (Subtype.val : B → Opens X)).op e))
    ((Functor.RightExtension.mk F (𝟙 _)).coneAt Y) ((Functor.RightExtension.mk G (𝟙 _)).coneAt Y)
    (Cone.ext (e.app Y) fun g ↦ ?_) (h Y)⟩
  simp

end OfIso

section Pushforward

variable {F} {Y : TopCat.{w}} (f : X ≅ Y)

/-- A member of the preimage of `B` under a homeomorphism as a member of `B`. -/
private def memMapIso
    (b : InducedCategory (Opens Y) (Subtype.val : (Opens.map f.hom).obj ⁻¹' B → Opens Y)) :
    InducedCategory (Opens X) (Subtype.val : B → Opens X) :=
  ⟨(Opens.map f.hom).obj b.1, b.2⟩

/-- For a homeomorphism `f : X ≅ Y`, the functor from the members of the preimage of `B` below an
open `V` of `Y` to the members of `B` below `f⁻¹(V)`, taking preimages. -/
private def structuredArrowMapIso (V : (Opens Y)ᵒᵖ) :
    StructuredArrow V
        (inducedFunctor (Subtype.val : (Opens.map f.hom).obj ⁻¹' B → Opens Y)).op ⥤
      StructuredArrow ((Opens.map f.hom).op.obj V)
        (inducedFunctor (Subtype.val : B → Opens X)).op where
  obj g := StructuredArrow.mk (Y := op (memMapIso B f g.right.unop))
    ((Opens.map f.hom).op.map g.hom)
  map φ := StructuredArrow.homMk
    (InducedCategory.homMk (X := memMapIso B f _) (Y := memMapIso B f _)
      ((Opens.map f.hom).map φ.right.unop.hom)).op (Subsingleton.elim _ _)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- `Opens.map f.hom` and `Opens.map f.inv` are the two directions of the order isomorphism
`Homeomorph.opensCongr` of the homeomorphism `f`, stated in the form met in the index
categories. -/
private theorem map_inv_map_hom_obj (U : Opens X) :
    (Opens.map f.hom).obj ((Opens.map f.inv).obj U) = U :=
  (TopCat.homeoOfIso f).opensCongr.symm_apply_apply U

private theorem map_hom_map_inv_obj (U : Opens Y) :
    (Opens.map f.inv).obj ((Opens.map f.hom).obj U) = U :=
  (TopCat.homeoOfIso f).opensCongr.apply_symm_apply U

private instance (V : (Opens Y)ᵒᵖ) : (structuredArrowMapIso B f V).Full where
  map_surjective {g₁ g₂} ψ :=
    ⟨StructuredArrow.homMk (InducedCategory.homMk (X := g₂.right.unop) (Y := g₁.right.unop)
      -- `Opens.map f.hom` is the functor of the equivalence `Opens.mapMapIso f`, hence full
      (leOfHom ((Opens.mapMapIso f).functor.preimage ψ.right.unop.hom)).hom).op
        (Subsingleton.elim _ _), Subsingleton.elim _ _⟩

private instance (V : (Opens Y)ᵒᵖ) : (structuredArrowMapIso B f V).EssSurj where
  mem_essImage k := by
    -- the member `f(U)` of the preimage of `B`, for `U = k.right` a member of `B` below `f⁻¹(V)`
    have hle : (Opens.map f.inv).obj k.right.unop.1 ≤ V.unop := by
      have h := leOfHom ((Opens.map f.inv).map (homOfLE (leOfHom k.hom.unop)))
      simpa only [Functor.op_obj, unop_op, inducedFunctor_obj, map_hom_map_inv_obj] using h
    have hmem : (Opens.map f.inv).obj k.right.unop.1 ∈ (Opens.map f.hom).obj ⁻¹' B := by
      rw [Set.mem_preimage, map_inv_map_hom_obj]
      exact k.right.unop.2
    let b : InducedCategory (Opens Y) (Subtype.val : (Opens.map f.hom).obj ⁻¹' B → Opens Y) :=
      ⟨(Opens.map f.inv).obj k.right.unop.1, hmem⟩
    refine ⟨StructuredArrow.mk (Y := op b) (homOfLE hle).op,
      ⟨StructuredArrow.isoMk (eqToIso ?_) (Subsingleton.elim _ _)⟩⟩
    exact congrArg op (Subtype.ext (map_inv_map_hom_obj f k.right.unop.1))

private instance (V : (Opens Y)ᵒᵖ) : (structuredArrowMapIso B f V).IsEquivalence where

variable {B} in
/-- **Adaptedness is invariant under homeomorphism.** If `F` is adapted to `B` and `f : X ≅ Y` is
an isomorphism of topological spaces, the pushforward `f_* F` is adapted to the opens of `Y` whose
preimages lie in `B`. -/
theorem IsAdapted.pushforward_of_iso (hF : F.IsAdapted B) :
    (f.hom _* F).IsAdapted ((Opens.map f.hom).obj ⁻¹' B) := by
  obtain ⟨h⟩ := hF
  refine ⟨fun V ↦ ?_⟩
  -- the cone at `V` of `f_* F` is the cone at `f⁻¹(V)` of `F`, reindexed along the equivalence
  -- of the two categories of members
  have := (h ((Opens.map f.hom).op.obj V)).whiskerEquivalence
    (structuredArrowMapIso B f V).asEquivalence
  -- the legs agree by definition: the leg of the reindexed cone at `g` is `F.map` of the
  -- preimage of `g.hom`, which is the leg of the cone of `f_* F` at `g`
  exact IsLimit.ofIsoLimit this (Cone.ext (Iso.refl _) fun g ↦ (Category.id_comp _).symm)

end Pushforward

/-! ### The sheaf condition on a basis -/

/-- **The sheaf condition on a basis `B` suffices for an adapted presheaf.** If `F` is adapted to
the basis `B` and its restriction to `B` is a sheaf for the topology restricted to `B`, then `F` is
a sheaf. A sieve on a member of `B` covers for the restricted topology exactly when its image
covers in `X` (`Functor.mem_restrictedTopology_iff`), so the hypothesis involves only covers of
members of `B` by members of `B`. The inclusion of a basis is cocontinuous for the restricted
topology, and a pointwise right Kan extension of a sheaf along a cocontinuous functor is a sheaf
(SGA 4 III 2.2). -/
theorem isSheaf_of_isAdapted_of_isSheaf_restrictedTopology (hB : Opens.IsBasis B)
    (hF : F.IsAdapted B)
    (h : CategoryTheory.Presheaf.IsSheaf
      ((inducedFunctor (Subtype.val : B → Opens X)).restrictedTopology
        (Opens.grothendieckTopology X))
      ((inducedFunctor (Subtype.val : B → Opens X)).op ⋙ F)) :
    F.IsSheaf :=
  -- a basis is cover-dense, so its inclusion is cocontinuous for the restricted topology
  have := TauCeti.TopologicalSpace.Opens.coverDense_inducedFunctor_subtypeVal hB
  (Presheaf.isSheaf_iff_multifork _ _).mpr fun _ S ↦
    ⟨RanIsSheafOfIsCocontinuous.isLimitMultifork h hF.some S⟩

/-- The restriction of a sheaf to a basis `B` is a sheaf for the restricted topology on `B`. -/
theorem IsSheaf.isSheaf_restrictedTopology {B : Set (Opens X)} (hB : Opens.IsBasis B)
    {F : X.Presheaf C} (hF : F.IsSheaf) :
    CategoryTheory.Presheaf.IsSheaf
      ((inducedFunctor (Subtype.val : B → Opens X)).restrictedTopology
        (Opens.grothendieckTopology X))
      ((inducedFunctor (Subtype.val : B → Opens X)).op ⋙ F) :=
  -- a basis is cover-dense, hence a dense subsite for the restricted topology, hence continuous
  have := TauCeti.TopologicalSpace.Opens.coverDense_inducedFunctor_subtypeVal hB
  Functor.op_comp_isSheaf_of_isSheaf _ _ _ F hF

/-- **A presheaf adapted to a basis is a sheaf exactly when it is a sheaf on the basis**, for the
topology restricted to the basis. -/
theorem isSheaf_iff_of_isAdapted (hB : Opens.IsBasis B) (hF : F.IsAdapted B) :
    F.IsSheaf ↔ CategoryTheory.Presheaf.IsSheaf
      ((inducedFunctor (Subtype.val : B → Opens X)).restrictedTopology
        (Opens.grothendieckTopology X))
      ((inducedFunctor (Subtype.val : B → Opens X)).op ⋙ F) :=
  ⟨fun h ↦ h.isSheaf_restrictedTopology hB,
    isSheaf_of_isAdapted_of_isSheaf_restrictedTopology F B hB hF⟩

end TopCat.Presheaf

end
