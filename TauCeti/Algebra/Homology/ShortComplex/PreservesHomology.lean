/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Homology classes under a functor preserving homology

For a functor `F` preserving the left homology of a short complex `S`, Mathlib identifies the
cycles and the homology of `S.map F` with the images under `F` of those of `S`, by
`ShortComplex.mapCyclesIso` and `ShortComplex.mapHomologyIso`, and records how the first of them
interacts with the inclusion of the cycles (`ShortComplex.mapCyclesIso_hom_iCycles`). This file
records the companion statement for the class map: under the two identifications, the class map
`homologyπ` of `S.map F` is the image under `F` of the class map of `S`
(`ShortComplex.homologyπ_comp_mapHomologyIso_hom`).

This is what makes a homology class computed after applying `F` recognisable as the image of a
class before applying it, for instance when a connecting map is constructed in an abelian category
after forgetting structure from a non-abelian one.

The same identifications are then restated for a homological complex `K` and a functor `F`
preserving homology: `HomologicalComplex.mapCyclesIso` and `HomologicalComplex.mapHomologyIso`
identify the cycles and the homology of `(F.mapHomologicalComplex c).obj K` in degree `n` with
the images under `F` of those of `K`. They are the short complex statements at `K.sc n`, which is
what the degree-`n` cycles and homology of a homological complex are by definition, but stated
against `K.iCycles n` and `K.homologyπ n`, the names a consumer of homological complexes works
with.
-/

public section

namespace CategoryTheory.ShortComplex

variable {C D : Type*} [Category C] [Category D] [Limits.HasZeroMorphisms C]
  [Limits.HasZeroMorphisms D] (S : ShortComplex C) (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- The inverse cycles identification carries the inclusion of cycles in the mapped complex to
the image of the original inclusion. -/
@[reassoc (attr := simp)]
theorem mapCyclesIso_inv_comp_iCycles [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (S.mapCyclesIso F).inv ≫ (S.map F).iCycles = F.map S.iCycles := by
  rw [Iso.inv_comp_eq, mapCyclesIso_hom_iCycles]

/-- **The class map commutes with a functor preserving homology.** Under the identifications
`mapCyclesIso` and `mapHomologyIso`, the class map of `S.map F` is the image under `F` of the
class map of `S`. -/
@[reassoc (attr := simp)]
theorem homologyπ_comp_mapHomologyIso_hom [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  -- Both identifications are computed from the left homology data `h` of `S`. The objects of
  -- `h.map F` are those of `h` under `F` only after unfolding, so rewriting with
  -- `LeftHomologyData.mapHomologyIso_eq` produces goals that are not type-correct at reducible
  -- transparency; the squares are therefore pasted as terms.
  let h := S.leftHomologyData
  exact (congrArg ((S.map F).homologyπ ≫ ·)
      (congrArg Iso.hom (LeftHomologyData.mapHomologyIso_eq h F))).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ F.map h.homologyIso.inv) (h.map F).homologyπ_comp_homologyIso_hom).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg ((h.map F).cyclesIso.hom ≫ ·) ((F.map_comp _ _).symm.trans
      ((congrArg F.map h.π_comp_homologyIso_inv).trans (F.map_comp _ _)))).trans <|
    (Category.assoc _ _ _).symm.trans <|
    congrArg (· ≫ F.map S.homologyπ)
      (congrArg Iso.hom (LeftHomologyData.mapCyclesIso_eq h F)).symm

end CategoryTheory.ShortComplex

namespace HomologicalComplex

open CategoryTheory

variable {C D : Type*} [Category C] [Category D] [Limits.HasZeroMorphisms C]
  [Limits.HasZeroMorphisms D] {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C c)
  (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesHomology] (n : ι) [K.HasHomology n]
  [((F.mapHomologicalComplex c).obj K).HasHomology n]

/-- For a functor `F` preserving homology, the cycles in degree `n` of the image of `K` under `F`
are the image under `F` of the cycles of `K`. -/
noncomputable def mapCyclesIso :
    ((F.mapHomologicalComplex c).obj K).cycles n ≅ F.obj (K.cycles n) :=
  (K.sc n).mapCyclesIso F

/-- For a functor `F` preserving homology, the homology in degree `n` of the image of `K` under
`F` is the image under `F` of the homology of `K`. -/
noncomputable def mapHomologyIso :
    ((F.mapHomologicalComplex c).obj K).homology n ≅ F.obj (K.homology n) :=
  (K.sc n).mapHomologyIso F

/-- `mapCyclesIso` carries the inclusion of the cycles of the image of `K` to the image of the
inclusion of the cycles of `K`. -/
@[reassoc (attr := simp)]
theorem mapCyclesIso_hom_iCycles :
    (K.mapCyclesIso F n).hom ≫ F.map (K.iCycles n) =
      ((F.mapHomologicalComplex c).obj K).iCycles n :=
  (K.sc n).mapCyclesIso_hom_iCycles F

/-- Under `mapCyclesIso` and `mapHomologyIso`, the class map of the image of `K` is the image
under `F` of the class map of `K`. -/
@[reassoc (attr := simp)]
theorem homologyπ_comp_mapHomologyIso_hom :
    ((F.mapHomologicalComplex c).obj K).homologyπ n ≫ (K.mapHomologyIso F n).hom =
      (K.mapCyclesIso F n).hom ≫ F.map (K.homologyπ n) :=
  (K.sc n).homologyπ_comp_mapHomologyIso_hom F

end HomologicalComplex
