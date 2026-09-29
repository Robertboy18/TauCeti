/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Free
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.FreeYoneda
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.MonoidalClosed

/-!
# Sections of the internal Hom of presheaves of modules

Let `R` be a presheaf of commutative rings on a small category `C`, and let `M` and `N` be
presheaves of `R`-modules. The internal Hom `𝓗om(M, N)` of presheaves of modules is only
characterized by the tensor--Hom adjunction (it is produced by the adjoint functor theorem in
`TauCeti.PresheafOfModules.monoidalClosed`). This file computes its sections: a section of
`𝓗om(M, N)` over `U` is a morphism of presheaves of modules `M|_U ⟶ N|_U` on the slice over `U`,
where restriction to the slice is `PresheafOfModulesOfCommRing.pushforward₀ (Over.forget U) R`.

The computation rests on a restriction--extension correspondence, valid over any category:
morphisms `M ⊗ freeYoneda R U ⟶ N` out of the tensor product with the free presheaf of modules
`TauCeti.PresheafOfModules.freeYoneda R U` on the presheaf represented by `U` are the same as
morphisms of restrictions `M|_U ⟶ N|_U`. A morphism `ψ` out of the tensor product restricts to the
map sending a section `m` over `g : V ⟶ U` to `ψ (m ⊗ g)`; conversely a morphism of restrictions
`φ` extends to the map sending a pure tensor `m ⊗ g` to the value of the component of `φ` at `g` on
`m`. Combined with Mathlib's `PresheafOfModules.freeYonedaEquiv`, this identifies the sections of
the internal Hom with morphisms of restrictions, compatibly with restriction along morphisms of `C`
and naturally in both arguments. This is the sectionwise description of the internal Hom which
restriction and stalk comparisons of internal Homs of sheaves of modules rest on.

## Main declarations

* `TauCeti.PresheafOfModules.tensorFreeYonedaHomEquiv`: the restriction--extension
  correspondence `(M ⊗ freeYoneda R U ⟶ N) ≃ (M|_U ⟶ N|_U)`, with the characteristic
  formulas `TauCeti.PresheafOfModules.restrictOfTensorFreeYoneda_app_apply` and
  `TauCeti.PresheafOfModules.tensorFreeYonedaOfRestrict_app_tmul_freeMk` and naturality in both
  arguments;
* `TauCeti.PresheafOfModules.ihomObjEquiv`: the sections of `𝓗om(M, N)` over `U` are the
  morphisms `M|_U ⟶ N|_U`, characterized by `TauCeti.PresheafOfModules.ihomObjEquiv_apply_app`
  (a section acts by evaluation of its restrictions), compatible with restriction along
  morphisms of `C` by `TauCeti.PresheafOfModules.ihomObjEquiv_map_app`, and natural in the target
  and in the source by `TauCeti.PresheafOfModules.ihomObjEquiv_ihom_map_app` and
  `TauCeti.PresheafOfModules.ihomObjEquiv_pre_app_app`.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter II, Exercise 1.15, for the
  sectionwise description of sheaf Hom which this file establishes for the categorical internal
  Hom of presheaves of modules.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Opposite

universe v u

noncomputable section

namespace TauCeti

namespace PresheafOfModules

open _root_.PresheafOfModules PresheafOfModulesOfCommRing

section RestrictionExtension

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{v}}
variable (U : C) (M N : PresheafOfModulesOfCommRing.{v} R)

/-- The morphism of restrictions to the slice over `U` induced by a morphism out of the tensor
product with the free presheaf represented by `U`: over `g : V ⟶ U`, it tensors a section with
the basis element indexed by `g`. -/
def restrictOfTensorFreeYoneda (ψ : M ⊗ freeYoneda R U ⟶ N) :
    (pushforward₀ (Over.forget U) R).obj M ⟶ (pushforward₀ (Over.forget U) R).obj N :=
  homMk (fun X ↦ ModuleCat.ofHom ((ψ.app' (op X.unop.left)).hom ∘ₗ
      (TensorProduct.mk (R.obj (op X.unop.left)) (M.obj (op X.unop.left))
        ((freeYoneda R U).obj (op X.unop.left))).flip (ModuleCat.freeMk X.unop.hom)))
    (fun {X Y} f ↦ by
      refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op X.unop.left)) ↦ ?_)
      have h := PresheafOfModulesOfCommRing.naturality_apply ψ f.unop.left.op
        (m ⊗ₜ (ModuleCat.freeMk X.unop.hom : (freeYoneda R U).obj (op X.unop.left)))
      have h' : (M.map f.unop.left.op m : M.obj (op Y.unop.left)) ⊗ₜ[R.obj (op Y.unop.left)]
          ((freeYoneda R U).map f.unop.left.op (ModuleCat.freeMk X.unop.hom) :
            (freeYoneda R U).obj (op Y.unop.left)) =
          (M.map f.unop.left.op m : M.obj (op Y.unop.left)) ⊗ₜ[R.obj (op Y.unop.left)]
            (ModuleCat.freeMk Y.unop.hom : (freeYoneda R U).obj (op Y.unop.left)) := by
        rw [freeObj_yoneda_map_freeMk, Quiver.Hom.unop_op, Over.w]
        rfl
      exact (congrArg (ConcreteCategory.hom (ψ.app' (op Y.unop.left))) h').symm.trans h)

/-- The component at `g : V ⟶ U` of the morphism of restrictions induced by `ψ` sends a section
`m` over `V` to `ψ (m ⊗ g)`.

This is not a simp lemma: the component is a morphism of modules over the ring of the slice
presheaf `(Over.forget U).op ⋙ R` at `Over.mk g`, and simp rewrites that ring to `R.obj (op V)`
inside the implicit arguments of the coercion, so the left-hand side has no simp normal form. -/
theorem restrictOfTensorFreeYoneda_app_apply (ψ : M ⊗ freeYoneda R U ⟶ N) {V : C} (g : V ⟶ U)
    (m : M.obj (op V)) :
    (restrictOfTensorFreeYoneda U M N ψ).app' (op (Over.mk g)) m =
      ψ.app' (op V) (m ⊗ₜ ModuleCat.freeMk g) := by
  -- Expose the component as a composite of linear maps; both sides then agree definitionally,
  -- but the unifier does not find this reduction on its own.
  change (ψ.app' (op V)).hom ((TensorProduct.mk (R.obj (op V)) (M.obj (op V))
    ((freeYoneda R U).obj (op V))).flip (ModuleCat.freeMk g) m) = _
  rfl

/-- The component at `g : V ⟶ U` of a morphism of restrictions to the slice over `U`, as a
linear map over the ring of sections over `V`. -/
private def componentLinearMap
    (φ : (pushforward₀ (Over.forget U) R).obj M ⟶ (pushforward₀ (Over.forget U) R).obj N)
    {V : C} (g : V ⟶ U) : M.obj (op V) →ₗ[R.obj (op V)] N.obj (op V) where
  toFun m := φ.app' (op (Over.mk g)) m
  map_add' m m' := map_add (φ.app' (op (Over.mk g))).hom m m'
  map_smul' r m := map_smul (φ.app' (op (Over.mk g))).hom r m

/-- The morphism out of the tensor product with the free presheaf represented by `U` induced by
a morphism of restrictions to the slice over `U`: a pure tensor of a section over `V` with the
basis element indexed by `g : V ⟶ U` is sent to the value of the component at `g`. -/
def tensorFreeYonedaOfRestrict
    (φ : (pushforward₀ (Over.forget U) R).obj M ⟶ (pushforward₀ (Over.forget U) R).obj N) :
    M ⊗ freeYoneda R U ⟶ N :=
  homMk (fun V ↦ ModuleCat.ofHom (TensorProduct.lift
      (ModuleCat.freeDesc (M := ModuleCat.of (R.obj V) (M.obj V →ₗ[R.obj V] N.obj V))
        (↾fun g : V.unop ⟶ U ↦ componentLinearMap U M N φ g)).hom.flip))
    (fun {V W} f ↦ by
      -- On the pure tensor `m ⊗ g`, both sides are the component of `φ` at `f.unop ≫ g` applied
      -- to the restriction of `m`, respectively the restriction of the component at `g` applied
      -- to `m`; `h` is the naturality of `φ` along `f.unop`, viewed as a morphism of the slice.
      refine ModuleCat.tensor_free_hom_ext fun m g ↦ ?_
      have h := PresheafOfModulesOfCommRing.naturality_apply φ (Over.homMk f.unop :
        Over.mk (f.unop ≫ g) ⟶ Over.mk g).op m
      have e₁ : (ModuleCat.freeDesc (M := ModuleCat.of (R.obj W) (M.obj W →ₗ[R.obj W] N.obj W))
          (↾fun g : W.unop ⟶ U ↦ componentLinearMap U M N φ g)).hom
            ((freeYoneda R U).map f (ModuleCat.freeMk g) : (freeYoneda R U).obj W) =
          componentLinearMap U M N φ (f.unop ≫ g) :=
        (congrArg (fun x : (freeYoneda R U).obj W ↦ (ModuleCat.freeDesc
          (M := ModuleCat.of (R.obj W) (M.obj W →ₗ[R.obj W] N.obj W))
          (↾fun g : W.unop ⟶ U ↦ componentLinearMap U M N φ g)).hom x)
          (freeObj_yoneda_map_freeMk f g)).trans (ModuleCat.freeDesc_apply _ _)
      have e₂ : (ModuleCat.freeDesc (M := ModuleCat.of (R.obj V) (M.obj V →ₗ[R.obj V] N.obj V))
          (↾fun g : V.unop ⟶ U ↦ componentLinearMap U M N φ g)).hom (ModuleCat.freeMk g) =
          componentLinearMap U M N φ g :=
        ModuleCat.freeDesc_apply _ _
      exact (congrArg (fun L ↦ L (M.map f m)) e₁).trans
        (h.trans (congrArg (N.map f) (congrArg (fun L ↦ L m) e₂).symm)))

/-- The morphism out of the tensor product induced by a morphism of restrictions `φ` sends the
pure tensor of a section `m` over `V` with the basis element indexed by `g : V ⟶ U` to the value
of the component of `φ` at `g` on `m`. -/
@[simp]
theorem tensorFreeYonedaOfRestrict_app_tmul_freeMk
    (φ : (pushforward₀ (Over.forget U) R).obj M ⟶ (pushforward₀ (Over.forget U) R).obj N)
    {V : C} (m : M.obj (op V)) (g : V ⟶ U) :
    (tensorFreeYonedaOfRestrict U M N φ).app' (op V) (m ⊗ₜ ModuleCat.freeMk g) =
      φ.app' (op (Over.mk g)) m :=
  congrArg (fun L : M.obj (op V) →ₗ[R.obj (op V)] N.obj (op V) ↦ L m)
    (ModuleCat.freeDesc_apply (M := ModuleCat.of (R.obj (op V))
      (M.obj (op V) →ₗ[R.obj (op V)] N.obj (op V)))
      (↾fun g : V ⟶ U ↦ componentLinearMap U M N φ g) g)

/-- Restricting to the slice over `U` and tensoring with the free presheaf represented by `U`
are inverse: morphisms `M ⊗ freeYoneda R U ⟶ N` correspond to morphisms of restrictions
`M|_U ⟶ N|_U`. -/
def tensorFreeYonedaHomEquiv :
    (M ⊗ freeYoneda R U ⟶ N) ≃
      ((pushforward₀ (Over.forget U) R).obj M ⟶ (pushforward₀ (Over.forget U) R).obj N) where
  toFun := restrictOfTensorFreeYoneda U M N
  invFun := tensorFreeYonedaOfRestrict U M N
  left_inv ψ := by
    refine hom_ext fun ⟨V⟩ ↦ ModuleCat.tensor_free_hom_ext fun m g ↦ ?_
    exact (tensorFreeYonedaOfRestrict_app_tmul_freeMk U M N _ m g).trans
      (restrictOfTensorFreeYoneda_app_apply U M N ψ g m)
  right_inv φ := by
    refine hom_ext fun X ↦ ?_
    obtain ⟨⟨V, ⟨⟨⟩⟩, g⟩⟩ := X
    refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op V)) ↦ ?_)
    exact (restrictOfTensorFreeYoneda_app_apply U M N _ g m).trans
      (tensorFreeYonedaOfRestrict_app_tmul_freeMk U M N φ m g)

/-- The forward direction of the restriction--extension correspondence is
`TauCeti.PresheafOfModules.restrictOfTensorFreeYoneda`. -/
@[simp]
theorem tensorFreeYonedaHomEquiv_apply (ψ : M ⊗ freeYoneda R U ⟶ N) :
    tensorFreeYonedaHomEquiv U M N ψ = restrictOfTensorFreeYoneda U M N ψ := by
  rfl

/-- The inverse direction of the restriction--extension correspondence is
`TauCeti.PresheafOfModules.tensorFreeYonedaOfRestrict`. -/
@[simp]
theorem tensorFreeYonedaHomEquiv_symm_apply
    (φ : (pushforward₀ (Over.forget U) R).obj M ⟶ (pushforward₀ (Over.forget U) R).obj N) :
    (tensorFreeYonedaHomEquiv U M N).symm φ = tensorFreeYonedaOfRestrict U M N φ := by
  rfl

/-- The restriction--extension correspondence is natural in the target. -/
theorem tensorFreeYonedaHomEquiv_comp {N' : PresheafOfModulesOfCommRing.{v} R}
    (ψ : M ⊗ freeYoneda R U ⟶ N) (α : N ⟶ N') :
    tensorFreeYonedaHomEquiv U M N' (ψ ≫ α) =
      tensorFreeYonedaHomEquiv U M N ψ ≫ (pushforward₀ (Over.forget U) R).map α := by
  refine hom_ext fun X ↦ ?_
  obtain ⟨⟨V, ⟨⟨⟩⟩, g⟩⟩ := X
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op V)) ↦ ?_)
  -- The pushforward of `α` has the components of `α`, by definition of `pushforward₀`.
  have hα (y : N.obj (op V)) :
      ((pushforward₀ (Over.forget U) R).map α).app' (op (Over.mk g)) y = α.app' (op V) y := rfl
  rw [tensorFreeYonedaHomEquiv_apply, tensorFreeYonedaHomEquiv_apply]
  -- The left-hand side is `(ψ ≫ α) (m ⊗ g) = α (ψ (m ⊗ g))`.
  refine (restrictOfTensorFreeYoneda_app_apply U M N' (ψ ≫ α) g m).trans ?_
  refine (congrArg (fun φ ↦ φ (m ⊗ₜ ModuleCat.freeMk g)) (comp_app ψ α (op V))).trans ?_
  refine (ModuleCat.comp_apply _ _ _).trans ?_
  -- The right-hand side is the pushforward of `α` applied to the component of the restriction of
  -- `ψ` at `g`, which is `α (ψ (m ⊗ g))` as well.
  refine (congrArg (fun y ↦ α.app' (op V) y)
    (restrictOfTensorFreeYoneda_app_apply U M N ψ g m)).symm.trans ?_
  refine (hα _).symm.trans ?_
  exact ((congrArg (fun φ ↦ φ m) (comp_app (restrictOfTensorFreeYoneda U M N ψ)
    ((pushforward₀ (Over.forget U) R).map α) (op (Over.mk g)))).trans
    (ModuleCat.comp_apply _ _ _)).symm

/-- The restriction--extension correspondence is natural in the source. -/
theorem tensorFreeYonedaHomEquiv_whiskerRight_comp {M' : PresheafOfModulesOfCommRing.{v} R}
    (β : M' ⟶ M) (ψ : M ⊗ freeYoneda R U ⟶ N) :
    tensorFreeYonedaHomEquiv U M' N (β ▷ freeYoneda R U ≫ ψ) =
      (pushforward₀ (Over.forget U) R).map β ≫ tensorFreeYonedaHomEquiv U M N ψ := by
  refine hom_ext fun X ↦ ?_
  obtain ⟨⟨V, ⟨⟨⟩⟩, g⟩⟩ := X
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M'.obj (op V)) ↦ ?_)
  -- The pushforward of `β` has the components of `β`, by definition of `pushforward₀`.
  have hβ (y : M'.obj (op V)) :
      ((pushforward₀ (Over.forget U) R).map β).app' (op (Over.mk g)) y = β.app' (op V) y := rfl
  rw [tensorFreeYonedaHomEquiv_apply, tensorFreeYonedaHomEquiv_apply]
  -- The left-hand side is `(β ▷ _ ≫ ψ) (m ⊗ g) = ψ (β m ⊗ g)`.
  refine (restrictOfTensorFreeYoneda_app_apply U M' N _ g m).trans ?_
  refine (congrArg (fun φ ↦ φ (m ⊗ₜ ModuleCat.freeMk g))
    (comp_app (β ▷ freeYoneda R U) ψ (op V))).trans ?_
  refine (ModuleCat.comp_apply _ _ _).trans ?_
  refine (congrArg (fun φ : (M' ⊗ freeYoneda R U).obj (op V) ⟶ (M ⊗ freeYoneda R U).obj (op V) ↦
    ψ.app' (op V) (φ (m ⊗ₜ ModuleCat.freeMk g)))
    (PresheafOfModulesOfCommRing.whiskerRight_app β (freeYoneda R U) (op V))).trans ?_
  refine (congrArg (fun y ↦ ψ.app' (op V) y)
    (ModuleCat.MonoidalCategory.whiskerRight_apply _ _ m (ModuleCat.freeMk g))).trans ?_
  -- The right-hand side is the component of the restriction of `ψ` at `g` applied to the
  -- pushforward of `β` applied to `m`, which is `ψ (β m ⊗ g)` as well.
  refine (restrictOfTensorFreeYoneda_app_apply U M N ψ g (β.app' (op V) m)).symm.trans ?_
  refine (congrArg (fun y ↦ (restrictOfTensorFreeYoneda U M N ψ).app' (op (Over.mk g)) y)
    (hβ m)).symm.trans ?_
  exact ((congrArg (fun φ ↦ φ m) (comp_app ((pushforward₀ (Over.forget U) R).map β)
    (restrictOfTensorFreeYoneda U M N ψ) (op (Over.mk g)))).trans
    (ModuleCat.comp_apply _ _ _)).symm

end RestrictionExtension

section Sections

variable {C : Type u} [SmallCategory C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
variable (U : C) (M N : PresheafOfModulesOfCommRing.{u} R)

/-- The sections over `U` of the internal Hom `𝓗om(M, N)` are the morphisms of presheaves of
modules `M|_U ⟶ N|_U` on the slice over `U`: a section corresponds to a morphism out of the free
presheaf represented by `U`, hence, by the tensor--Hom adjunction, to a morphism out of
`M ⊗ freeYoneda R U`, and these are the morphisms of restrictions. -/
def ihomObjEquiv :
    ((ihom M).obj N).obj (op U) ≃
      ((pushforward₀ (Over.forget U) R).obj M ⟶ (pushforward₀ (Over.forget U) R).obj N) :=
  freeYonedaEquiv.symm.trans
    ((((ihom.adjunction M).homEquiv (freeYoneda R U) N).symm).trans
      (tensorFreeYonedaHomEquiv U M N))

/-- The morphism of restrictions corresponding to a section of `𝓗om(M, N)` is obtained by
uncurrying the corresponding morphism out of the free presheaf represented by `U` and
restricting. -/
theorem ihomObjEquiv_apply (s : ((ihom M).obj N).obj (op U)) :
    ihomObjEquiv U M N s =
      restrictOfTensorFreeYoneda U M N (uncurry (freeYonedaEquiv.symm s)) :=
  (Equiv.trans_apply _ _ _).trans ((Equiv.trans_apply _ _ _).trans
    ((congrArg (tensorFreeYonedaHomEquiv U M N) (homEquiv_symm_apply_eq _)).trans
      (tensorFreeYonedaHomEquiv_apply U M N _)))

/-- The section of `𝓗om(M, N)` corresponding to a morphism of restrictions is obtained by
extending it to the tensor product with the free presheaf represented by `U` and currying. -/
theorem ihomObjEquiv_symm_apply
    (φ : (pushforward₀ (Over.forget U) R).obj M ⟶ (pushforward₀ (Over.forget U) R).obj N) :
    (ihomObjEquiv U M N).symm φ = freeYonedaEquiv (curry (tensorFreeYonedaOfRestrict U M N φ)) :=
  (Equiv.symm_trans_apply _ _ _).trans ((Equiv.symm_symm_apply _ _).trans
    (congrArg freeYonedaEquiv ((Equiv.symm_trans_apply _ _ _).trans
      ((Equiv.symm_symm_apply _ _).trans ((homEquiv_apply_eq _).trans
        (congrArg (fun f ↦ curry f) (tensorFreeYonedaHomEquiv_symm_apply U M N φ)))))))

/-- The morphism of restrictions corresponding to a section `s` of `𝓗om(M, N)` over `U` acts at
`g : V ⟶ U` by evaluating the restriction of `s` along `g`.

This is not a simp lemma, for the same reason as
`TauCeti.PresheafOfModules.restrictOfTensorFreeYoneda_app_apply`: simp rewrites the base ring of
the component inside the implicit arguments of the coercion. -/
theorem ihomObjEquiv_apply_app (s : ((ihom M).obj N).obj (op U)) {V : C} (g : V ⟶ U)
    (m : M.obj (op V)) :
    (ihomObjEquiv U M N s).app' (op (Over.mk g)) m =
      ((ihom.ev M).app N).app' (op V)
        (TensorProduct.tmul (R.obj (op V)) (N := PresheafOfModulesOfCommRing.obj ((ihom M).obj N)
          (op V)) m (((ihom M).obj N).map g.op s)) := by
  rw [ihomObjEquiv_apply, restrictOfTensorFreeYoneda_app_apply]
  exact congrArg (fun x : PresheafOfModulesOfCommRing.obj ((ihom M).obj N) (op V) ↦
    ((ihom.ev M).app N).app' (op V) (TensorProduct.tmul (R.obj (op V)) m x))
    (freeYonedaEquiv_symm_app_freeMk (P := (ihom M).obj N) s g)

/-- Restricting a section of `𝓗om(M, N)` along `g : V ⟶ U` restricts the corresponding morphism
of restrictions to the slice over `V`. -/
theorem ihomObjEquiv_map_app (s : ((ihom M).obj N).obj (op U)) {V : C} (g : V ⟶ U) {W : C}
    (h : W ⟶ V) (m : M.obj (op W)) :
    (ihomObjEquiv V M N (((ihom M).obj N).map g.op s)).app' (op (Over.mk h)) m =
      (ihomObjEquiv U M N s).app' (op (Over.mk (h ≫ g))) m := by
  refine (ihomObjEquiv_apply_app V M N _ h m).trans ?_
  rw [ihomObjEquiv_apply_app]
  exact congrArg (fun x : PresheafOfModulesOfCommRing.obj ((ihom M).obj N) (op W) ↦
    ((ihom.ev M).app N).app' (op W) (TensorProduct.tmul (R.obj (op W)) m x))
    (map_comp_apply ((ihom M).obj N) g.op h.op s).symm

/-- The sections equivalence is natural in the target: applying `𝓗om(M, α)` to a section
corresponds to postcomposing the morphism of restrictions with the restriction of `α`. -/
theorem ihomObjEquiv_ihom_map_app {N' : PresheafOfModulesOfCommRing.{u} R} (α : N ⟶ N')
    (s : ((ihom M).obj N).obj (op U)) :
    ihomObjEquiv U M N' (((ihom M).map α).app (op U) s) =
      ihomObjEquiv U M N s ≫ (pushforward₀ (Over.forget U) R).map α := by
  rw [ihomObjEquiv_apply, ihomObjEquiv_apply, ← tensorFreeYonedaHomEquiv_apply,
    ← tensorFreeYonedaHomEquiv_apply, ← tensorFreeYonedaHomEquiv_comp]
  exact congrArg (tensorFreeYonedaHomEquiv U M N')
    ((congrArg (fun f ↦ uncurry f) (freeYonedaEquiv_symm_comp s ((ihom M).map α)).symm).trans
      (uncurry_natural_right _ _))

/-- The sections equivalence is natural in the source: applying `𝓗om(β, N)` to a section
corresponds to precomposing the morphism of restrictions with the restriction of `β`. -/
theorem ihomObjEquiv_pre_app_app {M' : PresheafOfModulesOfCommRing.{u} R} (β : M' ⟶ M)
    (s : ((ihom M).obj N).obj (op U)) :
    ihomObjEquiv U M' N (((pre β).app N).app (op U) s) =
      (pushforward₀ (Over.forget U) R).map β ≫ ihomObjEquiv U M N s := by
  rw [ihomObjEquiv_apply, ihomObjEquiv_apply, ← tensorFreeYonedaHomEquiv_apply,
    ← tensorFreeYonedaHomEquiv_apply, ← tensorFreeYonedaHomEquiv_whiskerRight_comp]
  exact congrArg (tensorFreeYonedaHomEquiv U M' N)
    ((congrArg (fun f ↦ uncurry f) (freeYonedaEquiv_symm_comp s ((pre β).app N)).symm).trans
      (uncurry_pre_app _ _ _))

end Sections

end PresheafOfModules

end TauCeti

end
