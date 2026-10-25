/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Carrier

/-!
# Torus characters of the type-E7 minuscule carrier in its named root datum

`TauCeti.E7Minuscule.groupScheme` is the full-weight Chevalley carrier obtained from the
56-dimensional minuscule representation of the type-`E₇` Serre presentation. Its fourteen
numbered simple root subgroups and rank-seven split weight torus are explicit. The carrier's
conjugation equation initially describes the root character as
`DynkinType.E7.rootGeneratorWeight DynkinType.valid_E7`, hence as a Cartan-matrix row.

This file rewrites that equation against the uniform simply connected root datum used by
downstream consumers. The identities
`DynkinType.rootGeneratorWeight_inl_eq_root_simpleIndex` and
`DynkinType.rootGeneratorWeight_inr_eq_neg_root_simpleIndex` identify the character of the
`i`-th raising subgroup with

```text
(E7.simplyConnectedRootDatum ht).root (E7.simpleIndex ht i)
```

and the lowering character with its negative. The results below substitute those identities into
the carrier's scheme-level conjugation equation. They therefore certify that the explicit
minuscule carrier and `DynkinType.simplyConnectedRootDatum` use the same Bourbaki numbering and
the same character lattice.

This file does not assert reductivity, maximality of the weight torus, existence of all root
subgroups, or an identification of the carrier with an independently defined algebraic group. It
packages only the named simple-root pinning equations already justified by the construction.

## Main results

* `TauCeti.E7Minuscule.weightTorus_conj_rootSubgroup_root_simpleIndex`: conjugation by the
  weight torus on a positive simple root subgroup is governed by the corresponding root of the
  uniform simply connected `E₇` datum.
* `TauCeti.E7Minuscule.weightTorus_conj_rootSubgroup_neg_root_simpleIndex`: the analogous
  equation for a negative simple root.
* `TauCeti.E7Minuscule.weightTorusPoints_conj_rootSubgroupPoints_root_simpleIndex` and
  `TauCeti.E7Minuscule.weightTorusPoints_conj_rootSubgroupPoints_neg_root_simpleIndex`: the same
  two equations on matrix-valued points, which is the form a consumer working with a group of
  points rather than with scheme morphisms uses.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Sections 4.4 and 7.1.
* J. E. Humphreys, *Linear Algebraic Groups*, Sections 26--27.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI.

The interface follows `TauCeti/Algebra/Lie/E6/Minuscule/RootDatum.lean`, added in
[TauCetiProject/TauCeti#5278](https://github.com/TauCetiProject/TauCeti/pull/5278). The
rank-seven equations specialize the generic `DynkinType` identities once, so the carrier
and its generated subgroup share the same public root and coroot coordinates.

This advances the "Pinnings" and "Root subgroup maps" targets of Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. Milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md` consumes it: the type-`E₇` carrier must be traceable from
`ValidLieTypeIndex.dynkinType` to `DynkinType.simplyConnectedRootDatum`, with its numbered root
subgroups governed by characters of that datum.
-/

public section

universe v

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.E7Minuscule

open DynkinType

/-! ## Root-datum coordinates on the rank-seven lattices -/

/-- The named simple coroot is the corresponding coordinate vector. -/
theorem coroot_simpleIndex (ht : E7.Valid) (i : Fin 7) :
    ((E7.simplyConnectedRootDatum ht).coroot (E7.simpleIndex ht i) : Fin 7 → ℤ) =
      Pi.single i 1 := by
  -- Use the generic formula's index type so both occurrences of `Pi.single`
  -- have matching dependent types; `E7.rank` is definitionally seven.
  change (E7.simplyConnectedRootDatum ht).coroot (E7.simpleIndex ht i) =
    (Pi.single i 1 : Fin E7.rank → ℤ)
  exact E7.coroot_simpleIndex ht i

/-- A named simple coroot evaluates a weight at its numbered coordinate. -/
theorem coroot'_simpleIndex_apply (ht : E7.Valid) (i : Fin 7) (mu : Fin 7 → ℤ) :
    (E7.simplyConnectedRootDatum ht).coroot' (E7.simpleIndex ht i) mu = mu i := by
  simpa only [rank_E7] using E7.coroot'_simpleIndex_apply ht i mu

/-- The raising-generator weight is the named positive simple root. -/
theorem rootGeneratorWeight_inl_eq_root_simpleIndex (ht : E7.Valid) (i : Fin 7) :
    (E7.rootGeneratorWeight valid_E7 (.inl i) : Fin 7 → ℤ) =
      (E7.simplyConnectedRootDatum ht).root (E7.simpleIndex ht i) := by
  simpa only [rank_E7] using E7.rootGeneratorWeight_inl_eq_root_simpleIndex ht i

/-- The lowering-generator weight is the negative named simple root. -/
theorem rootGeneratorWeight_inr_eq_neg_root_simpleIndex (ht : E7.Valid) (i : Fin 7) :
    (E7.rootGeneratorWeight valid_E7 (.inr i) : Fin 7 → ℤ) =
      -(E7.simplyConnectedRootDatum ht).root (E7.simpleIndex ht i) := by
  simpa only [rank_E7] using E7.rootGeneratorWeight_inr_eq_neg_root_simpleIndex ht i

/-- A raising-generator weight has the coordinates of the corresponding Cartan row. -/
theorem rootGeneratorWeight_inl (i j : Fin 7) :
    E7.rootGeneratorWeight valid_E7 (.inl i) j = CartanMatrix.E 7 i j := by
  simpa only [rank_E7, cartanMatrix_E7] using E7.rootGeneratorWeight_inl valid_E7 i j

/-- A lowering-generator weight has the negative coordinates of the corresponding Cartan row. -/
theorem rootGeneratorWeight_inr (i j : Fin 7) :
    E7.rootGeneratorWeight valid_E7 (.inr i) j = -CartanMatrix.E 7 i j := by
  simpa only [rank_E7, cartanMatrix_E7] using E7.rootGeneratorWeight_inr valid_E7 i j

/-! ## Torus conjugation equations against the named simple roots -/

/-- **The torus conjugation equation at a named positive simple root.** A point `s` of the split
weight torus conjugates the raising-subgroup element of parameter `u` at node `i` to the same
subgroup with parameter `αᵢ(s)u`, where `αᵢ` is the corresponding root of the uniform simply
connected type-`E₇` datum. -/
theorem weightTorus_conj_rootSubgroup_root_simpleIndex (ht : E7.Valid) (i : Fin 7)
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin 7)).X)
    (u : A) :
    (s ≫ weightTorus.hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup (.inl i)).hom.hom) *
        (s ≫ weightTorus.hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter
                (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
                ((E7.simplyConnectedRootDatum ht).root
                  (E7.simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup (.inl i)).hom.hom := by
  rw [← rootGeneratorWeight_inl_eq_root_simpleIndex ht]
  exact weightTorus_conj_rootSubgroup (.inl i) A s u

/-- **The torus conjugation equation at a named negative simple root.** A point `s` of the split
weight torus conjugates the lowering-subgroup element of parameter `u` at node `i` to the same
subgroup with parameter `(-αᵢ)(s)u`. -/
theorem weightTorus_conj_rootSubgroup_neg_root_simpleIndex (ht : E7.Valid) (i : Fin 7)
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin 7)).X)
    (u : A) :
    (s ≫ weightTorus.hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup (.inr i)).hom.hom) *
        (s ≫ weightTorus.hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter
                (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
                (-(E7.simplyConnectedRootDatum ht).root
                  (E7.simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup (.inr i)).hom.hom := by
  rw [← rootGeneratorWeight_inr_eq_neg_root_simpleIndex ht]
  exact weightTorus_conj_rootSubgroup (.inr i) A s u

/-! ## Torus conjugation equations on matrix-valued points -/

/-- **The pinning equation at a named positive simple root, on matrix-valued points.** A point `s`
of the split weight torus conjugates the raising-subgroup element of parameter `u` at node `i` to
the same subgroup with parameter `αᵢ(s)u`, where `αᵢ` is the corresponding root of the uniform
simply connected type-`E₇` datum. -/
theorem weightTorusPoints_conj_rootSubgroupPoints_root_simpleIndex (ht : E7.Valid) (i : Fin 7)
    (A : Type v) [CommRing A] (s : Fin 7 → Aˣ) (u : Multiplicative A) :
    weightTorusPoints A s * rootSubgroupPoints (.inl i) A u * (weightTorusPoints A s)⁻¹ =
      rootSubgroupPoints (.inl i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
              ((E7.simplyConnectedRootDatum ht).root (E7.simpleIndex ht i)) : A) *
            Multiplicative.toAdd u)) := by
  rw [← rootGeneratorWeight_inl_eq_root_simpleIndex ht]
  exact weightTorusPoints_conj_rootSubgroupPoints (.inl i) A s u

/-- **The pinning equation at a named negative simple root, on matrix-valued points.** A point `s`
of the split weight torus conjugates the lowering-subgroup element of parameter `u` at node `i` to
the same subgroup with parameter `(-αᵢ)(s)u`. -/
theorem weightTorusPoints_conj_rootSubgroupPoints_neg_root_simpleIndex (ht : E7.Valid) (i : Fin 7)
    (A : Type v) [CommRing A] (s : Fin 7 → Aˣ) (u : Multiplicative A) :
    weightTorusPoints A s * rootSubgroupPoints (.inr i) A u * (weightTorusPoints A s)⁻¹ =
      rootSubgroupPoints (.inr i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
              (-(E7.simplyConnectedRootDatum ht).root (E7.simpleIndex ht i)) : A) *
            Multiplicative.toAdd u)) := by
  rw [← rootGeneratorWeight_inr_eq_neg_root_simpleIndex ht]
  exact weightTorusPoints_conj_rootSubgroupPoints (.inr i) A s u

end TauCeti.E7Minuscule
