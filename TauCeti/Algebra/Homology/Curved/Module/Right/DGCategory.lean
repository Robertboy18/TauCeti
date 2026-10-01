/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.HomComplex
public import TauCeti.Algebra.Homology.DG.Module.Right.Composition
public import TauCeti.CategoryTheory.DG.HomComplexData
public import TauCeti.CategoryTheory.DG.HomotopyCategory

/-!
# The differential graded category of curved differential graded right modules

The right modules over a curved differential graded algebra `(A, d, w)` form a differential
graded category.  The Hom complex from `M` to `N` is `TauCeti.curvedDGRightModuleHomComplex`,
whose degree-`p` cochains are the right-module maps raising internal degree by `p`, with the
graded commutator `f ↦ dN ∘ f - (-1) ^ p f ∘ dM` as differential; composition of homogeneous
cochains is composition of the underlying maps.  Individual curved modules have no cohomology,
but the Hom differential squares to zero because source and target have the *same* curvature,
and the graded Leibniz rule for composition holds verbatim.  This file bundles curved right
modules as `TauCeti.CurvedDGRightModuleCat`, installs the differential graded structure through
the explicit Hom-complex data of `TauCeti/CategoryTheory/DG/HomComplexData.lean`, and identifies
its calculus with the cochain calculus: the differential is the graded commutator with the
module differentials, the identity is the identity cochain, and composition in Mathlib's enriched
factor order is composition of cochains twisted by the Koszul sign `(-1) ^ (p * q)`.

The generic constructions on a differential graded category then supply the two categories
attached to curved modules.  The closed degree-zero morphisms `TauCeti.dgCycles` are the
right-module maps commuting with the differentials, and the degree-zero boundaries
`TauCeti.dgBoundaries` are the maps `dN ∘ k + k ∘ dM` for an **odd homotopy** `k`, a right-module
map of degree `-1`; there is no Koszul sign because the algebra acts on the other side.  The
**curved homotopy category** is `TauCeti.DGHomotopyCategory R (CurvedDGRightModuleCat h)`: it has
the curved modules as objects and homotopy classes of closed degree-zero morphisms as morphisms,
two closed morphisms being identified exactly when their difference is the boundary of an odd
homotopy.  Its weak equivalences are *not* quasi-isomorphisms; a curved module has no homology.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat`: bundled curved differential graded right modules.
* `TauCeti.CurvedDGRightModuleCat.homComplexData`: the Hom complexes, composition, and identities
  of curved differential graded right modules as explicit Hom-complex data.
* `TauCeti.CurvedDGRightModuleCat.instDGCategory`: the differential graded category of curved
  differential graded right modules.
* `TauCeti.CurvedDGRightModuleCat.dgHomLinearEquivCochains`: the explicit identification of
  homogeneous morphisms with right-module cochains.

## Main results

* `TauCeti.dgRightModuleCochains.curvedDifferential_comp`: the graded Leibniz rule for
  composition of cochains between curved modules.
* `TauCeti.CurvedDGRightModuleCat.dgDifferential_eq`, `TauCeti.CurvedDGRightModuleCat.dgId_eq`
  and `TauCeti.CurvedDGRightModuleCat.dgComp_eq`: the differential graded calculus of the
  category is the cochain calculus, with the Koszul sign in composition.
* `TauCeti.CurvedDGRightModuleCat.mem_dgCycles_iff`: the closed degree-zero morphisms are the
  maps commuting with the module differentials.
* `TauCeti.CurvedDGRightModuleCat.mem_dgBoundaries_iff`: the degree-zero boundaries are the
  boundaries `dN ∘ k + k ∘ dM` of odd homotopies.
* `TauCeti.CurvedDGRightModuleCat.homOf_eq_iff_exists_homotopy`: two closed morphisms agree in the
  curved homotopy category exactly when they are homotopic through an odd homotopy.

## Implementation notes

As for `TauCeti.DGRightModuleCat`, the enrichment fixes the universe of the ground ring while the
Hom complexes live in the universe of the modules, so the differential graded structure lives on
`CurvedDGRightModuleCat.{u, u, u} h`: ground ring, algebra, and modules share one universe.  The
bundled structure itself is stated in three universes.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Section 3.1, for curved DG modules and their homotopy category.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 6.2.
  His curvature is the negative of the right-module curvature used here.
* B. Keller, *Deriving DG categories*, Sections 1 and 2, for the differential graded category of
  modules.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti

section Bundled

universe uR uA uM

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}

/-- A bundled curved differential graded right module over the curved differential graded
algebra `h`. -/
structure CurvedDGRightModuleCat (h : IsCurvedDGAlgebra 𝒜 d w) where
  /-- The underlying module. -/
  carrier : Type uM
  [addCommGroup : AddCommGroup carrier]
  [moduleBase : Module R carrier]
  [moduleOp : Module Aᵐᵒᵖ carrier]
  [scalarTower : IsScalarTower R Aᵐᵒᵖ carrier]
  /-- The internal grading of the module. -/
  grading : ℤ → Submodule R carrier
  [decomposition : DirectSum.Decomposition grading]
  [gradedSMul : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece grading]
  /-- The module differential. -/
  differential : carrier →ₗ[R] carrier
  /-- The differential and action satisfy the curved DG right-module laws. -/
  isCurvedDGRightModule : IsCurvedDGRightModule h grading differential

namespace CurvedDGRightModuleCat

attribute [instance] addCommGroup moduleBase moduleOp scalarTower decomposition gradedSMul

variable {h : IsCurvedDGAlgebra 𝒜 d w}

instance : CoeSort (CurvedDGRightModuleCat.{uR, uA, uM} h) (Type uM) := ⟨carrier⟩

/-- Bundle a curved differential graded right module with its existing structures. -/
abbrev of {M : Type uM} [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]
    [IsScalarTower R Aᵐᵒᵖ M] {ℳ : ℤ → Submodule R M}
    [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
    {dM : M →ₗ[R] M} (hM : IsCurvedDGRightModule h ℳ dM) : CurvedDGRightModuleCat h where
  carrier := M
  grading := ℳ
  differential := dM
  isCurvedDGRightModule := hM

end CurvedDGRightModuleCat

end Bundled

universe u

variable {R : Type u} {A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

/-! ### The Leibniz rule for composition -/

namespace dgRightModuleCochains

variable {M N P : Type u}
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
  [AddCommGroup P] [Module R P] [Module Aᵐᵒᵖ P] [IsScalarTower R Aᵐᵒᵖ P]
  {ℳ : ℤ → Submodule R M}
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
    [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}
  {ℳN : ℤ → Submodule R N}
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳN]
    [DirectSum.Decomposition ℳN] {dN : N →ₗ[R] N}
  {ℳP : ℤ → Submodule R P}
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳP]
    [DirectSum.Decomposition ℳP] {dP : P →ₗ[R] P}
  {hM : IsCurvedDGRightModule h ℳ dM} {hN : IsCurvedDGRightModule h ℳN dN}
  {hP : IsCurvedDGRightModule h ℳP dP}

/-- The curved Hom differential satisfies the graded Leibniz rule for composition of cochains,
with the sign carried by the degree of the outer factor. -/
theorem curvedDifferential_comp {p q : ℤ}
    (g : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳN) (ℳN := ℳP) p)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) q) :
    curvedDifferential (hM := hM) (hN := hP) (p + q) (comp g f rfl) =
      comp (curvedDifferential (hM := hN) (hN := hP) p g) f (by omega) +
        p.negOnePow • comp g (curvedDifferential (hM := hM) (hN := hN) q f) (by omega) := by
  ext x
  simp only [curvedDifferential_apply, comp_apply, map_sub, Submodule.coe_add,
    LinearMap.add_apply, Submodule.coe_smul_of_tower, LinearMap.smul_apply]
  have hmap (z : N) : g.1 (q.negOnePow • z) = q.negOnePow • g.1 z := by
    rw [Units.smul_def, map_zsmul, ← Units.smul_def]
  rw [hmap, Int.negOnePow_add, smul_sub, smul_smul]
  abel

/-- The identity cochain of a curved module is closed. -/
@[simp]
theorem curvedDifferential_id (hM : IsCurvedDGRightModule h ℳ dM) :
    curvedDifferential (hM := hM) (hN := hM) 0 (id (R := R) (A := A) (ℳ := ℳ)) = 0 := by
  ext x
  simp only [curvedDifferential_apply, id_apply, Int.negOnePow_zero, one_smul, sub_self,
    Submodule.coe_zero, LinearMap.zero_apply]

end dgRightModuleCochains

namespace CurvedDGRightModuleCat

/-! ### The explicit Hom-complex data -/

/-- The explicit Hom-complex data of the differential graded category of curved right modules
over `h`: the Hom complex from `M` to `N` is `TauCeti.curvedDGRightModuleHomComplex`, composition
of homogeneous cochains is composition of the underlying maps, in Keller's order, and the
identity is the identity cochain. -/
noncomputable def homComplexData : DGCategoryData R (CurvedDGRightModuleCat.{u, u, u} h) :=
  DGCategoryData.ofKeller
    (fun M N => curvedDGRightModuleHomComplex M.isCurvedDGRightModule N.isCurvedDGRightModule)
    (fun {_ _ _} _ _ _ hqp => LinearMap.mk₂ R (fun g f => dgRightModuleCochains.comp g f hqp)
      (fun _ _ _ => dgRightModuleCochains.add_comp _ _ _ hqp)
      (fun _ _ _ => dgRightModuleCochains.smul_comp _ _ _ hqp)
      (fun _ _ _ => dgRightModuleCochains.comp_add _ _ _ hqp)
      (fun _ _ _ => dgRightModuleCochains.comp_smul _ _ _ hqp))
    (fun M => dgRightModuleCochains.id (R := R) (A := A) (ℳ := M.grading))
    (fun {_ _ _ _ _ _} hqp g f => by
      subst hqp
      rw [curvedDGRightModuleHomComplex_d_apply, curvedDGRightModuleHomComplex_d_apply,
        curvedDGRightModuleHomComplex_d_apply]
      exact dgRightModuleCochains.curvedDifferential_comp g f)
    (fun {_ _ _ _ _ _ _ _ _ _} hrq hqp _ k g f => by
      subst hrq hqp
      exact dgRightModuleCochains.comp_assoc k g f _)
    (fun g => dgRightModuleCochains.comp_id g)
    (fun f => dgRightModuleCochains.id_comp f)

variable (M N P : CurvedDGRightModuleCat.{u, u, u} h)

/-- The Hom complex of the explicit data is the curved Hom complex of the two modules. -/
@[simp]
theorem homComplexData_hom :
    (homComplexData (h := h)).hom M N =
      curvedDGRightModuleHomComplex M.isCurvedDGRightModule N.isCurvedDGRightModule :=
  (rfl)

/-! ### The differential graded category -/

/-- The differential graded category of curved differential graded right modules over `h`. -/
noncomputable instance instDGCategory : DGCategory R (CurvedDGRightModuleCat.{u, u, u} h) :=
  (homComplexData (h := h)).toDGCategory

/-- The Hom complex of the differential graded category of curved right modules is the curved
Hom complex of the two modules. -/
@[simp↓]
theorem dgHomComplex_eq :
    dgHomComplex R M N =
      curvedDGRightModuleHomComplex M.isCurvedDGRightModule N.isCurvedDGRightModule :=
  (rfl)

/-- Homogeneous morphisms of the differential graded category, identified with right-module
cochains through the equality of their Hom complexes. -/
noncomputable def dgHomLinearEquivCochains (n : ℤ) :
    DGHom R n M N ≃ₗ[R]
      dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := N.grading) n :=
  (eqToIso (congrArg (fun K : CochainComplex (ModuleCat R) ℤ => K.X n)
    (dgHomComplex_eq M N))).toLinearEquiv

/-- The identification with cochains acts by transport along the equality of the degree-`n`
terms of the Hom complexes. -/
theorem dgHomLinearEquivCochains_apply (n : ℤ) (f : DGHom R n M N) :
    dgHomLinearEquivCochains M N n f =
      (eqToHom (congrArg (fun K : CochainComplex (ModuleCat R) ℤ => K.X n)
        (dgHomComplex_eq M N))).hom f :=
  Iso.toLinearEquiv_apply _ _

/-- Transported composition in the explicit Hom-complex data is composition of cochains in
reversed order, with the Koszul sign converting Keller's factor order into Mathlib's. -/
@[simp]
theorem homComplexData_comp {p q n : ℤ} (hpq : p + q = n)
    (f : DGHom R p M N) (g : DGHom R q N P) :
    dgHomLinearEquivCochains M P n ((homComplexData (h := h)).comp p q n hpq f g) =
      (p * q).negOnePow • dgRightModuleCochains.comp
        (dgHomLinearEquivCochains N P q g) (dgHomLinearEquivCochains M N p f) (by omega) := by
  simp only [dgHomLinearEquivCochains_apply]
  unfold homComplexData
  generalize_proofs (config := { maxDepth := 0, abstract := false })
  erw [DGCategoryData.ofKeller_comp]
  · exact congrArg (fun c : (curvedDGRightModuleHomComplex M.isCurvedDGRightModule
        P.isCurvedDGRightModule).X n => (p * q).negOnePow • c)
      (LinearMap.mk₂_apply R _ g f)
  all_goals assumption

/-- The transported identity of the explicit data is the identity cochain. -/
@[simp]
theorem homComplexData_id :
    dgHomLinearEquivCochains M M 0 ((homComplexData (h := h)).id M) =
      dgRightModuleCochains.id (R := R) (A := A) (ℳ := M.grading) := by
  simp only [dgHomLinearEquivCochains_apply]
  unfold homComplexData
  generalize_proofs (config := { maxDepth := 0, abstract := false })
  erw [DGCategoryData.ofKeller_id]
  · erw [eqToHom_refl]
    exact ModuleCat.id_apply _ _
  all_goals assumption

/-- The transported differential of the explicit data is the graded commutator with the module
differentials. -/
@[simp]
theorem homComplexData_d_apply (n : ℤ) (f : DGHom R n M N) :
    dgHomLinearEquivCochains M N (n + 1)
        ((((homComplexData (h := h)).hom M N).d n (n + 1)).hom f) =
      dgRightModuleCochains.curvedDifferential (hM := M.isCurvedDGRightModule)
        (hN := N.isCurvedDGRightModule) n (dgHomLinearEquivCochains M N n f) :=
  curvedDGRightModuleHomComplex_d_apply M.isCurvedDGRightModule N.isCurvedDGRightModule n
    (dgHomLinearEquivCochains M N n f)

/-- The differential of the differential graded category of curved right modules is the graded
commutator with the module differentials, after transport to cochains. -/
@[simp↓]
theorem dgDifferential_eq (n : ℤ) (f : DGHom R n M N) :
    dgHomLinearEquivCochains M N (n + 1) (dgDifferential R n f) =
      dgRightModuleCochains.curvedDifferential (hM := M.isCurvedDGRightModule)
        (hN := N.isCurvedDGRightModule) n (dgHomLinearEquivCochains M N n f) :=
  (congrArg (dgHomLinearEquivCochains M N (n + 1))
    (DGCategoryData.dgDifferential_toDGCategory (homComplexData (h := h)) n f)).trans
      (homComplexData_d_apply M N n f)

/-- The identity of the differential graded category of curved right modules transports to the
identity cochain. -/
@[simp↓]
theorem dgId_eq :
    dgHomLinearEquivCochains M M 0 (dgId R M) =
      dgRightModuleCochains.id (R := R) (A := A) (ℳ := M.grading) :=
  (congrArg (dgHomLinearEquivCochains M M 0)
    (DGCategoryData.dgId_toDGCategory (homComplexData (h := h)) M)).trans (homComplexData_id M)

/-- Composition in the differential graded category of curved right modules is composition of
cochains, carrying the Koszul sign which converts Mathlib's enriched factor order into
composition of the underlying maps, after transport to cochains. -/
@[simp↓]
theorem dgComp_eq {p q n : ℤ} (f : DGHom R p M N) (g : DGHom R q N P) (hpq : p + q = n) :
    dgHomLinearEquivCochains M P n (dgComp R f g hpq) =
      (p * q).negOnePow • dgRightModuleCochains.comp
        (dgHomLinearEquivCochains N P q g) (dgHomLinearEquivCochains M N p f) (by omega) :=
  (congrArg (dgHomLinearEquivCochains M P n)
    (DGCategoryData.dgComp_toDGCategory (homComplexData (h := h)) f g hpq)).trans
      (homComplexData_comp M N P hpq f g)

/-! ### Closed degree-zero morphisms, odd homotopies, and the curved homotopy category -/

/-- A degree-zero morphism of the differential graded category of curved right modules is closed
exactly when its underlying map commutes with the module differentials. -/
theorem mem_dgCycles_iff (f : DGHom R 0 M N) :
    f ∈ dgCycles R M N ↔
      ∀ x : M, N.differential ((dgHomLinearEquivCochains M N 0 f).1 x) =
        (dgHomLinearEquivCochains M N 0 f).1 (M.differential x) := by
  rw [mem_dgCycles, ← (dgHomLinearEquivCochains M N (0 + 1)).map_eq_zero_iff, dgDifferential_eq,
    dgRightModuleCochains.curvedDifferential_zero_eq_zero_iff]

/-- A degree-zero morphism of the differential graded category of curved right modules is a
boundary exactly when its underlying map is the boundary `dN ∘ k + k ∘ dM` of an **odd
homotopy** `k`, a right-module map lowering the internal degree by one. -/
theorem mem_dgBoundaries_iff (f : DGHom R 0 M N) :
    f ∈ dgBoundaries R M N ↔
      ∃ k : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := N.grading) (-1),
        ∀ x : M, (dgHomLinearEquivCochains M N 0 f).1 x =
          N.differential (k.1 x) + k.1 (M.differential x) := by
  rw [mem_dgBoundaries]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨dgHomLinearEquivCochains M N (-1) k, fun x => ?_⟩
    have hk := congrArg (fun c : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading)
      (ℳN := N.grading) (-1 + 1) => (c.1 : M →ₗ[Aᵐᵒᵖ] N) x) (dgDifferential_eq M N (-1) k)
    rw [dgRightModuleCochains.curvedDifferential_neg_one_apply] at hk
    exact hk
  · rintro ⟨k, hk⟩
    refine ⟨(dgHomLinearEquivCochains M N (-1)).symm k, ?_⟩
    apply (dgHomLinearEquivCochains M N 0).injective
    refine Subtype.ext (LinearMap.ext fun x => ?_)
    have hd := congrArg (fun c : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading)
      (ℳN := N.grading) (-1 + 1) => (c.1 : M →ₗ[Aᵐᵒᵖ] N) x)
      (dgDifferential_eq M N (-1) ((dgHomLinearEquivCochains M N (-1)).symm k))
    rw [LinearEquiv.apply_symm_apply, dgRightModuleCochains.curvedDifferential_neg_one_apply]
      at hd
    rw [hk x]
    exact hd

/-- **The curved homotopy category.** Two closed degree-zero morphisms of curved right modules
represent the same morphism of the homotopy category `TauCeti.DGHomotopyCategory` exactly when
they are homotopic: their difference is the boundary `dN ∘ k + k ∘ dM` of an odd homotopy `k`. -/
theorem homOf_eq_iff_exists_homotopy {f g : DGHom R 0 M N}
    (hf : f ∈ dgCycles R M N) (hg : g ∈ dgCycles R M N) :
    DGHomotopyCategory.homOf R f hf = DGHomotopyCategory.homOf R g hg ↔
      ∃ k : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := N.grading) (-1),
        ∀ x : M, (dgHomLinearEquivCochains M N 0 f).1 x -
            (dgHomLinearEquivCochains M N 0 g).1 x =
          N.differential (k.1 x) + k.1 (M.differential x) := by
  rw [DGHomotopyCategory.homOf_eq_iff, mem_dgBoundaries_iff]
  simp only [map_sub, Submodule.coe_sub, LinearMap.sub_apply]

end CurvedDGRightModuleCat

end TauCeti
