/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.MonoidalClosed

/-!
# Sections of the internal Hom of presheaves of modules

Let `R` be a presheaf of commutative rings on a small category `C`, and let `M` and `N` be
presheaves of `R`-modules. The internal Hom `𝓗om(M, N)` of presheaves of modules is only
characterized by the tensor--Hom adjunction (it is produced by the adjoint functor theorem in
`TauCeti.PresheafOfModules.monoidalClosed`). This file computes its sections: a section of
`𝓗om(M, N)` over `U` is a morphism of presheaves of modules `M|_U ⟶ N|_U` on the slice over `U`,
where restriction to the slice is `PresheafOfModulesOfCommRing.pushforward₀ (Over.forget U) R`.

The computation rests on a restriction--extension correspondence: morphisms
`M ⊗ (free on `yoneda U`) ⟶ N` are the same as morphisms of restrictions `M|_U ⟶ N|_U`. A
morphism `ψ` out of the tensor product restricts to the map sending a section `m` over `g : V ⟶ U`
to `ψ (m ⊗ g)`; conversely a morphism of restrictions `φ` extends to the map sending a pure tensor
`m ⊗ g` to the value of the component of `φ` at `g` on `m`. Combined with Mathlib's
`PresheafOfModules.freeYonedaEquiv`, this identifies the sections of the internal Hom with
morphisms of restrictions, compatibly with restriction along morphisms of `C`. This is the
sectionwise description of the internal Hom which restriction and stalk comparisons of internal
Homs of sheaves of modules rest on.

## Main declarations

* `TauCeti.PresheafOfModules.tensorFreeYonedaHomEquiv`: the restriction--extension
  correspondence `(M ⊗ free (yoneda U) ⟶ N) ≃ (M|_U ⟶ N|_U)`, with the characteristic
  formulas `TauCeti.PresheafOfModules.restrictOfTensorFreeYoneda_app_apply` and
  `TauCeti.PresheafOfModules.tensorFreeYonedaOfRestrict_app_tmul_freeMk` and naturality in both
  arguments;
* `TauCeti.PresheafOfModules.ihomObjEquiv`: the sections of `𝓗om(M, N)` over `U` are the
  morphisms `M|_U ⟶ N|_U`, characterized by `TauCeti.PresheafOfModules.ihomObjEquiv_apply_app`
  (a section acts by evaluation of its restrictions) and compatible with restriction along
  morphisms of `C` by `TauCeti.PresheafOfModules.ihomObjEquiv_map_app`.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter II, Exercise 1.15, for the
  sectionwise description of sheaf Hom which this file establishes for the categorical internal
  Hom of presheaves of modules.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Opposite

universe v u

noncomputable section

namespace ModuleCat.MonoidalCategory

variable {S : Type u} [CommRing S] {M₁ M₂ : ModuleCat.{u} S} {X : Type u}

/-- Two morphisms out of the tensor product of a module with a free module agree once they agree
on pure tensors with basis elements. -/
theorem tensor_free_hom_ext {f g : M₁ ⊗ (ModuleCat.free S).obj X ⟶ M₂}
    (h : ∀ (m : M₁) (x : X), f (m ⊗ₜ ModuleCat.freeMk x) = g (m ⊗ₜ ModuleCat.freeMk x)) :
    f = g := by
  refine tensor_ext fun m s ↦ ?_
  have := ModuleCat.free_hom_ext
    (f := ModuleCat.ofHom (f.hom ∘ₗ TensorProduct.mk S M₁ ((ModuleCat.free S).obj X) m))
    (g := ModuleCat.ofHom (g.hom ∘ₗ TensorProduct.mk S M₁ ((ModuleCat.free S).obj X) m))
    (fun x ↦ h m x)
  exact ConcreteCategory.congr_hom this s

end ModuleCat.MonoidalCategory

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

/-- The free presheaf of modules on the presheaf of sets represented by `U` restricts the basis
element indexed by `g : X.unop ⟶ U` along `f : X ⟶ Y` to the basis element indexed by
`f.unop ≫ g`. -/
@[simp]
theorem freeObj_yoneda_map_freeMk {U : C} {X Y : Cᵒᵖ} (f : X ⟶ Y) (g : X.unop ⟶ U) :
    (freeObj (R := R) (yoneda.obj U)).map f (ModuleCat.freeMk g) =
      ModuleCat.freeMk (f.unop ≫ g) := by
  rw [freeObj_map]
  exact ModuleCat.freeDesc_apply _ _

variable {P : PresheafOfModules.{v} R}

/-- The morphism out of the free presheaf of modules on the presheaf of sets represented by `U`
corresponding to a section `x` over `U` sends the basis element indexed by `g : V ⟶ U` to the
restriction of `x` along `g`. -/
@[simp]
theorem freeYonedaEquiv_symm_app_freeMk {U V : C} (x : P.obj (op U)) (g : V ⟶ U) :
    (freeYonedaEquiv.symm x).app (op V) (ModuleCat.freeMk g) = P.map g.op x := by
  have h : freeYonedaEquiv.symm x = freeObjDesc (yonedaEquiv.symm x) := rfl
  rw [h, freeObjDesc_app]
  exact (ModuleCat.freeDesc_apply _ _).trans
    (yonedaEquiv_symm_app_apply (F := P.presheaf ⋙ forget _) x (op V) g)

end PresheafOfModules

namespace PresheafOfModulesOfCommRing

variable {C : Type u} [SmallCategory C] (R : Cᵒᵖ ⥤ CommRingCat.{u})

/-- The free presheaf of modules on the presheaf of sets represented by `U`, over a presheaf of
commutative rings. -/
abbrev freeYoneda (U : C) : PresheafOfModulesOfCommRing.{u} R :=
  PresheafOfModules.freeObj (yoneda.obj U)

variable {R}

/-- The restriction map of a tensor product of presheaves of modules acts on pure tensors
factorwise. This restates `PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul` for the
tensor product written with the monoidal notation. -/
@[simp]
theorem tensor_map_tmul {M N : PresheafOfModulesOfCommRing.{u} R} {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (m : M.obj X) (n : N.obj X) :
    (M ⊗ N).map f (m ⊗ₜ n) = M.map f m ⊗ₜ N.map f n :=
  rfl

end PresheafOfModulesOfCommRing

namespace TauCeti

namespace PresheafOfModules

open _root_.PresheafOfModules PresheafOfModulesOfCommRing

variable {C : Type u} [SmallCategory C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
variable (U : C) (M N : PresheafOfModulesOfCommRing.{u} R)

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

@[simp]
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
      refine ModuleCat.MonoidalCategory.tensor_free_hom_ext fun m g ↦ ?_
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
are inverse: morphisms `M ⊗ (free on `yoneda U`) ⟶ N` correspond to morphisms of restrictions
`M|_U ⟶ N|_U`. -/
def tensorFreeYonedaHomEquiv :
    (M ⊗ freeYoneda R U ⟶ N) ≃
      ((pushforward₀ (Over.forget U) R).obj M ⟶ (pushforward₀ (Over.forget U) R).obj N) where
  toFun := restrictOfTensorFreeYoneda U M N
  invFun := tensorFreeYonedaOfRestrict U M N
  left_inv ψ := by
    refine hom_ext fun V ↦ ModuleCat.MonoidalCategory.tensor_free_hom_ext fun m g ↦ ?_
    exact tensorFreeYonedaOfRestrict_app_tmul_freeMk U M N _ m g
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
theorem tensorFreeYonedaHomEquiv_comp {N' : PresheafOfModulesOfCommRing.{u} R}
    (ψ : M ⊗ freeYoneda R U ⟶ N) (α : N ⟶ N') :
    tensorFreeYonedaHomEquiv U M N' (ψ ≫ α) =
      tensorFreeYonedaHomEquiv U M N ψ ≫ (pushforward₀ (Over.forget U) R).map α := by
  refine hom_ext fun X ↦ ?_
  obtain ⟨⟨V, ⟨⟨⟩⟩, g⟩⟩ := X
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op V)) ↦ ?_)
  exact restrictOfTensorFreeYoneda_app_apply U M N' _ g m

/-- The restriction--extension correspondence is natural in the source. -/
theorem tensorFreeYonedaHomEquiv_whiskerRight_comp {M' : PresheafOfModulesOfCommRing.{u} R}
    (β : M' ⟶ M) (ψ : M ⊗ freeYoneda R U ⟶ N) :
    tensorFreeYonedaHomEquiv U M' N (β ▷ freeYoneda R U ≫ ψ) =
      (pushforward₀ (Over.forget U) R).map β ≫ tensorFreeYonedaHomEquiv U M N ψ := by
  refine hom_ext fun X ↦ ?_
  obtain ⟨⟨V, ⟨⟨⟩⟩, g⟩⟩ := X
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M'.obj (op V)) ↦ ?_)
  exact restrictOfTensorFreeYoneda_app_apply U M' N _ g m

/-- The sections over `U` of the internal Hom `𝓗om(M, N)` are the morphisms of presheaves of
modules `M|_U ⟶ N|_U` on the slice over `U`: a section corresponds to a morphism out of the free
presheaf represented by `U`, hence, by the tensor--Hom adjunction, to a morphism out of
`M ⊗ (free on yoneda U)`, and these are the morphisms of restrictions. -/
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
      restrictOfTensorFreeYoneda U M N (uncurry (freeYonedaEquiv.symm s)) := by
  rfl

/-- The section of `𝓗om(M, N)` corresponding to a morphism of restrictions is obtained by
extending it to the tensor product with the free presheaf represented by `U` and currying. -/
theorem ihomObjEquiv_symm_apply
    (φ : (pushforward₀ (Over.forget U) R).obj M ⟶ (pushforward₀ (Over.forget U) R).obj N) :
    (ihomObjEquiv U M N).symm φ = freeYonedaEquiv (curry (tensorFreeYonedaOfRestrict U M N φ)) := by
  rfl

/-- The morphism of restrictions corresponding to a section `s` of `𝓗om(M, N)` over `U` acts at
`g : V ⟶ U` by evaluating the restriction of `s` along `g`. -/
@[simp]
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

end PresheafOfModules

end TauCeti

end
