/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Differential
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Tangent
public import TauCeti.Algebra.Lie.E7.Minuscule.Generated.Serre
public import TauCeti.Algebra.Lie.E7.Minuscule.Generated.StandardComodule

/-!
# Simple-coroot differentials in the generated E₇ group

The simple coroots in fundamental-weight coordinates define actual cocharacters through the
weight torus of the generated group. Their differentials at the unit tangent vector are the
brackets of the normalized opposite root vectors, over every commutative ring.

The calculation uses character–cocharacter pairings in the 56-dimensional minuscule
representation and the injective tangent inclusion. Consequently the Serre comparison sends
its Cartan generators to these coroot differentials. The tangent image of the weight torus is
their linear span and is therefore contained in the image of the Serre comparison.
No assertion of torus maximality or of surjectivity of the Serre comparison is needed.

## Main declarations

* `generatedCorootCocharacter`: the cocharacter defined by a fundamental-weight coordinate.
* `generatedCorootCocharacter_eq_namedCoroot`: its identification with the named simple coroot.
* `generatedTangentMatrixLieHom_corootDifferential`: its matrix of weight–coroot pairings.
* `generatedCartanVector_eq_corootDifferential`: the normalized opposite-root bracket.
* `generatedSerreLift_serreH_eq_corootDifferential`: the Cartan-generator value of the comparison.
* `range_derivationCompLieHom_generatedWeightTorusCoordinateMap_eq_span`: the toral tangent image.
* `range_derivationCompLieHom_generatedWeightTorusCoordinateMap_le_range_generatedSerreLift`:
  containment of that image in the Serre image.
-/

public section

namespace TauCeti.E7Minuscule

noncomputable section

variable (R : Type*) [CommRing R]

/-- The simple cocharacter obtained by evaluating a fundamental-weight coordinate at `i`
and then including the weight torus in the generated group. -/
def generatedCorootCocharacter (i : Fin 7) :
    generatedCoordinateHopfAlgebra R →ₐc[R] LaurentPolynomial R :=
  (generatedWeightTorusCoordinateMap R).hom.cocharacter
    (Finsupp.applyAddHom i).toMultiplicative

/-- The cocharacter is the named simple coroot of the simply connected E₇ root datum,
with the existing simple-root numbering. -/
theorem generatedCorootCocharacter_eq_namedCoroot (ht : DynkinType.E7.Valid) (i : Fin 7) :
    generatedCorootCocharacter R i =
      (generatedWeightTorusCoordinateMap R).hom.cocharacter
        (SplitTorus.cocharEquiv.symm
          ((DynkinType.E7.simplyConnectedRootDatum ht).coroot
            (DynkinType.E7.simpleIndex ht i))) := by
  rw [generatedCorootCocharacter]
  congr 1
  apply SplitTorus.cocharEquiv.injective
  erw [Equiv.apply_symm_apply, DynkinType.coroot_simpleIndex]
  change SplitTorus.cocharEquiv (Finsupp.applyAddHom i).toMultiplicative =
    (Pi.single i 1 : Fin 7 → ℤ)
  ext j
  simp [SplitTorus.cocharEquiv_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]

/-- The differential of the `i`-th coroot has diagonal entries given by pairing the
minuscule weights with the named simple coroot. The tangent vector of `𝔾ₘ` is normalized to one. -/
theorem generatedTangentMatrixLieHom_corootDifferential
    (ht : DynkinType.E7.Valid) (i : Fin 7) :
    generatedTangentMatrixLieHom R
        (derivationComp (generatedCorootCocharacter R i)
          (MultiplicativeGroup.tangentLinearEquiv.symm (1 : R))) =
      Matrix.diagonal fun a ↦
        ((DynkinType.E7.simplyConnectedRootDatum ht).coroot'
          (DynkinType.E7.simpleIndex ht i) (DynkinType.e7MinusculeWeight a) : R) := by
  have hπ : (generatedWeightTorusCoordinateMap R).hom.comp (generatedCoordinateMap R).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) DynkinType.e7MinusculeWeight := by
    rw [← _root_.CommHopfAlgCat.hom_comp,
      generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  rw [generatedTangentMatrixLieHom_apply, generatedCorootCocharacter,
    GeneralLinear.tangentMatrix_derivationComp_cocharacter_of_weightTorus _ _ _ hπ]
  congr 1
  ext a
  erw [DynkinType.coroot'_simpleIndex_apply DynkinType.E7 ht i]
  simp

/-- The bracket of the opposite normalized root vectors is the differential of the
corresponding actual coroot cocharacter, with no characteristic assumption. -/
theorem generatedCartanVector_eq_corootDifferential (i : Fin 7) :
    generatedCartanVector R i =
      derivationComp (generatedCorootCocharacter R i)
        (MultiplicativeGroup.tangentLinearEquiv.symm (1 : R)) := by
  apply generatedTangentMatrixLieHom_injective R
  rw [generatedTangentMatrixLieHom_generatedCartanVector,
    generatedTangentMatrixLieHom_corootDifferential R DynkinType.valid_E7]
  ext a b
  simp only [Matrix.map_apply, cartanMatrix_apply, Matrix.diagonal_apply]
  split_ifs
  · erw [DynkinType.coroot'_simpleIndex_apply DynkinType.E7 DynkinType.valid_E7 i]
  · simp

/-- The Serre comparison sends each Cartan generator to the actual simple-coroot differential. -/
theorem generatedSerreLift_serreH_eq_corootDifferential (i : Fin 7) :
    generatedSerreLift R (serreH R (CartanMatrix.E 7) i) =
      derivationComp (generatedCorootCocharacter R i)
        (MultiplicativeGroup.tangentLinearEquiv.symm (1 : R)) := by
  rw [generatedSerreLift_serreH, generatedCartanVector_eq_corootDifferential]

/-- The tangent image of the generated weight torus is the span of the normalized
Cartan vectors. No injectivity of the torus differential is assumed. -/
theorem range_derivationCompLieHom_generatedWeightTorusCoordinateMap_eq_span :
    LinearMap.range
        (derivationCompLieHom (B := R) (generatedWeightTorusCoordinateMap R).hom).toLinearMap =
      Submodule.span R (Set.range (generatedCartanVector R)) := by
  rw [SplitTorus.range_derivationCompLieHom]
  congr 1
  congr 1
  funext i
  rw [generatedCartanVector_eq_corootDifferential, generatedCorootCocharacter,
    derivationCompLieHom_apply]

/-- Every tangent vector in the weight-torus image is in the image of the Serre comparison. -/
theorem range_derivationCompLieHom_generatedWeightTorusCoordinateMap_le_range_generatedSerreLift :
    LinearMap.range
        (derivationCompLieHom (B := R) (generatedWeightTorusCoordinateMap R).hom).toLinearMap ≤
      LinearMap.range (generatedSerreLift R).toLinearMap := by
  rw [range_derivationCompLieHom_generatedWeightTorusCoordinateMap_eq_span, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨serreH R (CartanMatrix.E 7) i, generatedSerreLift_serreH R i⟩

end

end TauCeti.E7Minuscule
