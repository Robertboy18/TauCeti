/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.DegreeZero
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.TateTheorem

/-!
# Tate's theorem for a finite normal layer

Let `V ◁ U` be a finite normal layer of a formation with coefficient module `A`, and let
`u ∈ H²(U/V, A^V)`. Tate's theorem says that if, for every subgroup `H` of `U/V`,

* `H¹(H, A^V) = 0`,
* `H²(H, A^V)` has exactly `#H` elements,
* the restriction of `u` to `H` generates `H²(H, A^V)`,

then cup product with `u` is an isomorphism `Ĥʳ(U/V, ℤ) ≃ Ĥʳ⁺²(U/V, A^V)` in every integer degree
`r` (`TauCeti.ClassFieldTheory.tateTheorem`). The three hypotheses are separate explicit
arguments, quantified over the finite quotient system `H ↦ subgroupLayer H` of the layer, and
the underlying homomorphism of the isomorphism is the cup-product map `cupClass`
(`tateTheorem_toAddMonoidHom`). For a class formation the hypotheses hold for the fundamental
class, which gives the Tate isomorphisms `ClassFormation.tateIso` of Artin–Tate's Main Theorem.

The generic content is `TauCeti.TateCohomology.cup_bijective_of_cupTrivialInt_bijective`. This
file connects it to the finite-layer language: Tate cohomology of the layer of a subgroup `H`
is Tate cohomology of `H` with coefficients in the restricted module
(`NormalLayer.subgroupLayerTateIso`), and the hypotheses at `H = ⊤` give the degree-zero
bijection on the whole Galois group.

## Main definitions

* `TauCeti.ClassFieldTheory.NormalLayer.subgroupLayerTateIso`: Tate cohomology of the layer of a
  subgroup, as Tate cohomology of that subgroup.
* `TauCeti.ClassFieldTheory.tateTheorem`: Tate's theorem for a finite normal layer, as an additive
  equivalence.
* `TauCeti.ClassFieldTheory.ClassFormation.tateIso`: Tate's theorem for a class formation, applied
  to the fundamental class.

## Main statements

* `TauCeti.ClassFieldTheory.cupClass_bijective`: cup product with `u` is bijective in every degree,
  with the generation hypothesis on the whole Galois group only.
* `TauCeti.ClassFieldTheory.tateTheorem_toAddMonoidHom`,
  `TauCeti.ClassFieldTheory.ClassFormation.tateIso_toAddMonoidHom`: the isomorphisms are the
  cup-product maps.

## References

* J. Tate, *The higher dimensional cohomology groups of class field theory*, Ann. of Math. 56
  (1952), 294–297.
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV §4, Theorem 1.
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory Rep

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace NormalLayer

variable (L : NormalLayer G) (F : Formation G) (H : Subgroup L.Gal)

/-- The identification of the coefficient module of the layer of `H` with the coefficient module
of `L` intertwines the action of the Galois group of the layer of `H` with the action of `H` on
the restricted module. This is the compatible pair along which `subgroupLayerTateIso` transports
Tate cohomology. -/
theorem isIntertwiningMap_repIso_subgroupLayer :
    ((L.subgroupLayer H).rep F).ρ.IsIntertwiningMap
      ((Rep.res H.subtype (L.rep F)).ρ.comp
        (L.subgroupGalEquiv H : (L.subgroupLayer H).Gal →* H))
      (Representation.equivOfIso ((L.subgroupRestriction H).repIso F)).toLinearEquiv := by
  -- The action of `H` on the restricted module, read through `subgroupGalEquiv`, is the action
  -- along `galHom`, since `galHom` is the inclusion of `H` after `subgroupGalEquiv`.
  have hσ : (Rep.res H.subtype (L.rep F)).ρ.comp
        (L.subgroupGalEquiv H : (L.subgroupLayer H).Gal →* H) =
      (Rep.res (L.subgroupRestriction H).galHom (L.rep F)).ρ := by
    rw [galHom_subgroupRestriction]
    exact MonoidHom.comp_assoc _ _ _
  rw [hσ]
  exact ⟨fun g x ↦ Rep.hom_comm_apply ((L.subgroupRestriction H).repIso F).hom g x⟩

variable [Fintype H]

/-- **Tate cohomology of the layer of `H` is Tate cohomology of `H`** with coefficients in the
restriction of the coefficient module of `L`. -/
def subgroupLayerTateIso (r : ℤ) :
    (L.subgroupLayer H).TateH F r ≅ tateCohomology (Rep.res H.subtype (L.rep F)) r :=
  TauCeti.TateCohomology.mapIso (e := L.subgroupGalEquiv H)
    (e' := (Representation.equivOfIso ((L.subgroupRestriction H).repIso F)).toLinearEquiv)
    (L.isIntertwiningMap_repIso_subgroupLayer F H) r

/-- The comparison `subgroupLayerTateIso` is the Tate map attached to the compatible pair
`isIntertwiningMap_repIso_subgroupLayer`. -/
theorem subgroupLayerTateIso_hom (r : ℤ) :
    (L.subgroupLayerTateIso F H r).hom =
      TauCeti.TateCohomology.map (L.isIntertwiningMap_repIso_subgroupLayer F H) r := by
  rw [subgroupLayerTateIso, TauCeti.TateCohomology.mapIso_hom]

omit [Fintype H] in
/-- Restriction to the layer of the whole Galois group is injective on cohomology: corestriction
splits it, the relative degree being `1`. -/
theorem cohomologyRes_subgroupRestriction_top_injective (n : ℕ) :
    Function.Injective ((L.subgroupRestriction ⊤).cohomologyRes F n) := by
  intro x y hxy
  have h := congrArg ((L.subgroupRestriction ⊤).cohomologyCor F n) hxy
  simpa [LayerRestriction.cohomologyCor_cohomologyRes_apply,
    relativeDegree_subgroupRestriction] using h

/-- If the restriction of `u` to the layer of the whole Galois group generates the cohomology of
that layer, then `u` generates the cohomology of `L`. -/
theorem exists_zsmul_eq_of_cohomologyRes_subgroupRestriction_top {n : ℕ} (u : L.H F n)
    (hgen : ∀ x : (L.subgroupLayer ⊤).H F n,
      ∃ m : ℤ, x = m • (L.subgroupRestriction ⊤).cohomologyRes F n u)
    (y : L.H F n) : ∃ m : ℤ, m • u = y := by
  obtain ⟨m, hm⟩ := hgen ((L.subgroupRestriction ⊤).cohomologyRes F n y)
  exact ⟨m, L.cohomologyRes_subgroupRestriction_top_injective F n (by rw [map_zsmul, hm])⟩

end NormalLayer

section TateTheorem

variable (F : Formation G) (L : NormalLayer G) (u : L.H F 2)

/-- Cup product with a class `u` generating `H²(U/V, A^V)` is bijective from `Ĥʳ(U/V, ℤ)` to
`Ĥʳ⁺²(U/V, A^V)` in every integer degree `r`, provided `H¹(H, A^V) = 0` and `H²(H, A^V)` has
exactly `#H` elements for every subgroup `H` of `U/V`. This is Tate's theorem with the generation
hypothesis stated on the whole Galois group only; its restricted forms on subgroups follow. -/
theorem cupClass_bijective
    (h1 : ∀ H : Subgroup L.Gal, Subsingleton ((L.subgroupLayer H).H F 1))
    (hcard : ∀ H : Subgroup L.Gal, Nat.card ((L.subgroupLayer H).H F 2) = Nat.card H)
    (hgen : ∀ y : L.H F 2, ∃ m : ℤ, m • u = y)
    (r : ℤ) : Function.Bijective (cupClass F L u r) := by
  -- The order hypothesis at `H = ⊤` says that `H²(U/V, A^V)` has order `[U : V]`.
  have hcardG : Nat.card (L.H F 2) = L.degree := by
    rw [← congrArg (fun X : NormalLayer G ↦ Nat.card (X.H F 2)) L.subgroupLayer_top, hcard ⊤,
      Subgroup.card_top, L.degree_eq_natCard_gal]
  -- The degree-zero bijection on the whole Galois group.
  have h0 : Function.Bijective
      (TauCeti.TateCohomology.cupTrivialInt (L.rep F) ((L.tateHIsoH F 2).inv u)) := by
    rw [← cupClass_degree_zero_eq_cupTrivialInt]
    exact cupClass_degree_zero_bijective F L u hgen hcardG
  -- The generic theorem, with the hypotheses on subgroups read through `subgroupLayerTateIso`.
  have hbij := TauCeti.TateCohomology.cup_bijective_of_cupTrivialInt_bijective (L.rep F)
    ((L.tateHIsoH F 2).inv u) h0
    (fun _ _ H _ _ ↦
      haveI := h1 H
      (ModuleCat.isZero_of_subsingleton _).of_iso
        ((L.subgroupLayerTateIso F H 1).symm ≪≫ (L.subgroupLayer H).tateHIsoH F 1))
    (fun _ _ H _ _ ↦
      (Nat.card_congr ((L.subgroupLayerTateIso F H 2).symm ≪≫
        (L.subgroupLayer H).tateHIsoH F 2).toLinearEquiv.toEquiv).trans (hcard H))
    r (r + 2) rfl
  have heq : ⇑(cupClass F L u r) =
      ⇑((tateCohomologyFunctor (r + 2)).map (λ_ (L.rep F)).hom) ∘
        fun x : L.TrivialTateH r ↦ TauCeti.TateCohomology.cup (Rep.trivial ℤ L.Gal ℤ) (L.rep F)
          r 2 (r + 2) rfl x ((L.tateHIsoH F 2).inv u) :=
    funext fun x ↦ cupClass_apply F L u r x
  rw [heq]
  exact (ConcreteCategory.bijective_of_isIso _).comp hbij

/-- **Tate's theorem** (J. Tate, *The higher dimensional cohomology groups of class field theory*,
Ann. of Math. 56 (1952); Artin–Tate, Chapter XIV §4), with its hypotheses stated one by one over
the finite quotient system `H ↦ L.subgroupLayer H`:

* `h1`: `H¹(H, A^V) = 0` for every subgroup `H ≤ U/V`;
* `hcard`: `H²(H, A^V)` has exactly `#H` elements;
* `hgen`: the restriction of `u` to the layer of `H` generates that layer's `H²`.

Then cup product with `u` is an isomorphism `Ĥʳ(U/V, ℤ) ≃ Ĥʳ⁺²(U/V, A^V)` in every integer
degree `r`; its underlying homomorphism is `cupClass F L u r` (`tateTheorem_toAddMonoidHom`). -/
def tateTheorem
    (h1 : ∀ H : Subgroup L.Gal, Subsingleton ((L.subgroupLayer H).H F 1))
    (hcard : ∀ H : Subgroup L.Gal, Nat.card ((L.subgroupLayer H).H F 2) = Nat.card H)
    (hgen : ∀ (H : Subgroup L.Gal) (x : (L.subgroupLayer H).H F 2),
      ∃ m : ℤ, x = m • (L.subgroupRestriction H).cohomologyRes F 2 u)
    (r : ℤ) : L.TrivialTateH r ≃+ L.TateH F (r + 2) :=
  AddEquiv.ofBijective (cupClass F L u r) (cupClass_bijective F L u h1 hcard
    (L.exists_zsmul_eq_of_cohomologyRes_subgroupRestriction_top F u (hgen ⊤)) r)

/-- The isomorphism of Tate's theorem acts by cup product with `u`. -/
@[simp]
theorem tateTheorem_apply
    (h1 : ∀ H : Subgroup L.Gal, Subsingleton ((L.subgroupLayer H).H F 1))
    (hcard : ∀ H : Subgroup L.Gal, Nat.card ((L.subgroupLayer H).H F 2) = Nat.card H)
    (hgen : ∀ (H : Subgroup L.Gal) (x : (L.subgroupLayer H).H F 2),
      ∃ m : ℤ, x = m • (L.subgroupRestriction H).cohomologyRes F 2 u)
    (r : ℤ) (x : L.TrivialTateH r) :
    tateTheorem F L u h1 hcard hgen r x = cupClass F L u r x := by
  rw [tateTheorem]
  exact AddEquiv.ofBijective_apply _ _ x

/-- The isomorphism of Tate's theorem **is** cup product with `u`, not an unrelated equivalence
between two groups of the same cardinality. -/
theorem tateTheorem_toAddMonoidHom
    (h1 : ∀ H : Subgroup L.Gal, Subsingleton ((L.subgroupLayer H).H F 1))
    (hcard : ∀ H : Subgroup L.Gal, Nat.card ((L.subgroupLayer H).H F 2) = Nat.card H)
    (hgen : ∀ (H : Subgroup L.Gal) (x : (L.subgroupLayer H).H F 2),
      ∃ m : ℤ, x = m • (L.subgroupRestriction H).cohomologyRes F 2 u)
    (r : ℤ) :
    (tateTheorem F L u h1 hcard hgen r).toAddMonoidHom = cupClass F L u r :=
  AddMonoidHom.ext (tateTheorem_apply F L u h1 hcard hgen r)

end TateTheorem

namespace ClassFormation

variable {F : Formation G}

/-- **Tate's theorem for a class formation**, in every integer degree: the generic theorem applied
to the fundamental class, with the three hypotheses discharged by the three individually named
consequences of the axioms. This is Artin–Tate's Main Theorem (Chapter XIV §4, Theorem 1). -/
def tateIso (cf : ClassFormation F) (L : NormalLayer G) (r : ℤ) :
    L.TrivialTateH r ≃+ L.TateH F (r + 2) :=
  tateTheorem F L (cf.fundamentalClass L) (cf.h1_subgroupLayer L) (cf.card_H2_subgroupLayer L)
    (cf.fundamentalClass_restrict_generates L) r

/-- The Tate isomorphism of a class formation acts by cup product with the fundamental class. -/
@[simp]
theorem tateIso_apply (cf : ClassFormation F) (L : NormalLayer G) (r : ℤ)
    (x : L.TrivialTateH r) :
    cf.tateIso L r x = cf.cupFundamentalClass L r x := by
  rw [tateIso, tateTheorem_apply, cupFundamentalClass_apply]

/-- The Tate isomorphism of a class formation is the cup-product map with the fundamental class,
not an unrelated equivalence between groups of the same cardinality. -/
theorem tateIso_toAddMonoidHom (cf : ClassFormation F) (L : NormalLayer G) (r : ℤ) :
    (cf.tateIso L r).toAddMonoidHom = cf.cupFundamentalClass L r :=
  AddMonoidHom.ext (cf.tateIso_apply L r)

end ClassFormation

end TauCeti.ClassFieldTheory
