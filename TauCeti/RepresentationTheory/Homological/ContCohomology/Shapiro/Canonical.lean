/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ContinuousCohomologyIso
public import TauCeti.RepresentationTheory.Homological.ContCohomology.HomologySequence
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Exact

/-!
# The canonical Shapiro map in every degree

For a compact group `G`, a subgroup `U` and a discrete `U`-module `A`, the coinduced module
`Coind_U^G A` of `TauCeti.DiscreteCoind` comes with the compatible pair consisting of the inclusion
`U ↪ G` and the counit `Coind_U^G A → A`, evaluation at `1`. Mathlib's functoriality of continuous
cohomology in compatible pairs turns it into a map in every degree,

```text
Hⁿ(G, Coind_U^G A) ⟶ Hⁿ(U, A),
```

the **canonical Shapiro map** `TauCeti.ContinuousCohomology.shapiroMap`. It is restriction to `U`
followed by the coefficient map of the counit, and Shapiro's lemma is the statement that it is
bijective. This file defines the map on the canonical carrier and proves two things about it:

* in degrees `0`, `1` and `2` it is carried by the comparison isomorphisms of the explicit
  low-degree model to the explicit Shapiro maps `TauCeti.ContCohomology.explicitShapiro0`,
  `explicitShapiroMap1` and `explicitShapiroMap2`, so it is bijective there for a closed subgroup
  of a profinite group;
* it commutes with the connecting maps of the long exact sequence: for a short exact sequence of
  discrete `U`-modules and its coinduction to `G`, the square of Shapiro maps and connecting maps
  commutes in every degree.

Shapiro's lemma in every degree follows from these two statements by induction on the degree, given
the acyclicity of `Coind_1^G A` in every positive degree: the connecting maps of
`0 → A → Coind_1^U A → Q → 0` and of its coinduction to `G` are then bijective, transitivity of
coinduction identifies `Coind_U^G (Coind_1^U A)` with `Coind_1^G A`, and the commuting square
carries bijectivity of the Shapiro map in degree `n` to bijectivity in degree `n + 1`. That
induction is not carried out here.

## Main definitions

* `TauCeti.ContinuousCohomology.shapiroMap`: the canonical Shapiro map
  `Hⁿ(G, Coind_U^G A) ⟶ Hⁿ(U, A)` in `TopModuleCat ℤ`.

## Main results

* `TauCeti.ContinuousCohomology.shapiroMap_eq_res_comp_coeffMap`: the Shapiro map is restriction
  followed by the coefficient map of the counit.
* `TauCeti.ContinuousCohomology.explicitH0Iso_shapiroMap`,
  `TauCeti.ContinuousCohomology.explicitH1AddEquivContinuousCohomology_shapiroMap`,
  `TauCeti.ContinuousCohomology.explicitH2AddEquivContinuousCohomology_shapiroMap`: agreement with
  the explicit Shapiro maps in degrees `0`, `1` and `2` under the comparison isomorphisms.
* `TauCeti.ContinuousCohomology.bijective_shapiroMap_zero`,
  `TauCeti.ContinuousCohomology.bijective_shapiroMap_one`,
  `TauCeti.ContinuousCohomology.bijective_shapiroMap_two`: Shapiro's lemma on the canonical carrier
  in degrees `0`, `1` and `2`, for a closed subgroup of a profinite group.
* `TauCeti.ContCohomology.DiscreteShortExact.delta_shapiroMap`: the Shapiro maps commute with
  the connecting maps.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  (1.6.4), with the footnote on p. 61 recording that NSW write `Ind` for the coinduced module.
* L. Ribes, P. Zalesskii, *Profinite Groups*, Thm. 6.10.5.
-/

public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

open TauCeti.ContCohomology

universe u

section CanonicalMap

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction U A]

/-- **The canonical Shapiro map** `Hⁿ(G, Coind_U^G A) ⟶ Hⁿ(U, A)` in every degree: the map on
continuous cohomology induced by the compatible pair of the inclusion `U ↪ G` and the counit
`Coind_U^G A → A`, evaluation at `1`. Shapiro's lemma says that it is bijective. -/
noncomputable def shapiroMap (n : ℕ) :
    continuousCohomology n (ofDiscreteModule ℤ G (DiscreteCoind G U A)) ⟶
      continuousCohomology n (ofDiscreteModule ℤ U A) :=
  _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype U)
    (ofDiscreteModulePair (ContinuousMonoidHom.subgroupSubtype U : U →* G)
      (DiscreteCoind.eval G U A).toIntLinearMap fun u f => eval_subgroupSubtype_smul G U A u f) n

/-- The canonical Shapiro map is the compatible-pair map of the inclusion and the counit. -/
theorem shapiroMap_def (n : ℕ) :
    shapiroMap U A n = _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype U)
      (ofDiscreteModulePair (ContinuousMonoidHom.subgroupSubtype U : U →* G)
        (DiscreteCoind.eval G U A).toIntLinearMap fun u f => eval_subgroupSubtype_smul G U A u f)
          n := (rfl)

/-- **The Shapiro map is restriction followed by the counit**: restrict from `G` to `U`, then apply
the coefficient map induced by evaluation at `1`. The two sides compose because the restriction of
the canonical object of a discrete `G`-module to `U` is the canonical object of the same module
over `U` (`TauCeti.res_ofDiscreteModule`). -/
theorem shapiroMap_eq_res_comp_coeffMap (n : ℕ) :
    shapiroMap U A n =
      res U (ofDiscreteModule ℤ G (DiscreteCoind G U A)) n ≫
        coeffMap (ofDiscreteModuleMap (DiscreteCoind.eval G U A).toIntLinearMap
          fun u f => DiscreteCoind.eval_smul u f) n := by
  rw [res_def, coeffMap_def]
  -- The composite of the two compatible pairs is the pair of the inclusion and the counit: both
  -- act on a coinduced function by evaluation at `1`.
  refine (map_congr rfl (heq_of_eq (ofDiscreteModulePair_eq_of_hom_apply _ _ _ _
    fun f => ?_)) n).trans
    (_root_.ContinuousCohomology.map_comp (X := ofDiscreteModule ℤ G (DiscreteCoind G U A))
      (ContinuousMonoidHom.subgroupSubtype U) (ContinuousMonoidHom.id U) (𝟙 _)
      (ofDiscreteModuleMap (DiscreteCoind.eval G U A).toIntLinearMap
        fun u f => DiscreteCoind.eval_smul u f) n)
  exact (TopRep.comp_apply ((TopRep.resFunctor (ContinuousMonoidHom.id U : U →* U)).map
    (𝟙 (TopRep.res (ContinuousMonoidHom.subgroupSubtype U : U →* G)
      (ofDiscreteModule ℤ G (DiscreteCoind G U A)))))
    (ofDiscreteModuleMap (DiscreteCoind.eval G U A).toIntLinearMap
      fun u f => DiscreteCoind.eval_smul u f) f).trans
    (ofDiscreteModuleMap_hom_apply (G := U) (DiscreteCoind.eval G U A).toIntLinearMap
      (fun u f => DiscreteCoind.eval_smul u f) f)

/-! ### Degree zero -/

/-- In degree zero the canonical Shapiro map is the explicit one, `H⁰(G, Coind_U^G A) ≃+ H⁰(U, A)`
by evaluation at `1`, under the comparisons with the canonical carrier. -/
theorem explicitH0Iso_shapiroMap (x : H0 G (DiscreteCoind G U A)) :
    shapiroMap U A 0 ((explicitH0IsoContinuousCohomology G (DiscreteCoind G U A)).hom x) =
      (explicitH0IsoContinuousCohomology U A).hom (explicitShapiro0 G U A x) := by
  rw [shapiroMap_def, explicitH0Iso_map]
  exact congrArg _ (Subtype.ext (((coe_explicitMap0 _ _ _ _ _ x).trans
    (DiscreteCoind.eval_apply _)).trans (explicitShapiro0_apply x).symm))

/-- **Shapiro's lemma in degree zero on the canonical carrier**: the canonical Shapiro map
`H⁰(G, Coind_U^G A) ⟶ H⁰(U, A)` is bijective. No closedness of `U` is needed in this degree. -/
theorem bijective_shapiroMap_zero : Function.Bijective (shapiroMap U A 0) := by
  have h : (shapiroMap U A 0 : continuousCohomology 0 (ofDiscreteModule ℤ G (DiscreteCoind G U A)) →
      continuousCohomology 0 (ofDiscreteModule ℤ U A)) =
      (explicitH0IsoContinuousCohomology U A).hom ∘ explicitShapiro0 G U A ∘
        (explicitH0IsoContinuousCohomology G (DiscreteCoind G U A)).inv := by
    funext y
    rw [Function.comp_apply, Function.comp_apply, ← explicitH0Iso_shapiroMap U A
      ((explicitH0IsoContinuousCohomology G (DiscreteCoind G U A)).inv y),
      Iso.inv_hom_id_apply (explicitH0IsoContinuousCohomology G (DiscreteCoind G U A)) y]
  rw [h]
  exact (Function.bijective_iff_has_inverse.2
      ⟨(explicitH0IsoContinuousCohomology U A).inv,
        fun y => Iso.hom_inv_id_apply (explicitH0IsoContinuousCohomology U A) y,
        fun y => Iso.inv_hom_id_apply (explicitH0IsoContinuousCohomology U A) y⟩).comp
    ((explicitShapiro0 G U A).bijective.comp (Function.bijective_iff_has_inverse.2
      ⟨(explicitH0IsoContinuousCohomology G (DiscreteCoind G U A)).hom,
        fun y => Iso.inv_hom_id_apply (explicitH0IsoContinuousCohomology G (DiscreteCoind G U A)) y,
        fun y => Iso.hom_inv_id_apply (explicitH0IsoContinuousCohomology G (DiscreteCoind G U A))
          y⟩))

/-! ### Degrees one and two -/

variable [CompactSpace G] [ContinuousSMul U A]

/-- In degree one the canonical Shapiro map is the explicit forward Shapiro map
`TauCeti.ContCohomology.explicitShapiroMap1` under the comparisons with the canonical carrier. -/
theorem explicitH1AddEquivContinuousCohomology_shapiroMap [CompactSpace U]
    (x : H1 G (DiscreteCoind G U A)) :
    shapiroMap U A 1 (explicitH1AddEquivContinuousCohomology G (DiscreteCoind G U A) x) =
      explicitH1AddEquivContinuousCohomology U A (explicitShapiroMap1 G U A x) := by
  rw [shapiroMap_def]
  exact explicitH1AddEquivContinuousCohomology_map G (DiscreteCoind G U A) U A
    (ContinuousMonoidHom.subgroupSubtype U) (DiscreteCoind.eval G U A)
    (eval_subgroupSubtype_smul G U A) x

/-- In degree two the canonical Shapiro map is the explicit forward Shapiro map
`TauCeti.ContCohomology.explicitShapiroMap2` under the comparisons with the canonical carrier. -/
theorem explicitH2AddEquivContinuousCohomology_shapiroMap [CompactSpace U]
    (x : H2 G (DiscreteCoind G U A)) :
    shapiroMap U A 2 (explicitH2AddEquivContinuousCohomology G (DiscreteCoind G U A) x) =
      explicitH2AddEquivContinuousCohomology U A (explicitShapiroMap2 G U A x) := by
  rw [shapiroMap_def, explicitShapiroMap2_def]
  exact explicitH2AddEquivContinuousCohomology_map G (DiscreteCoind G U A) U A
    (ContinuousMonoidHom.subgroupSubtype U) (DiscreteCoind.eval G U A)
    (eval_subgroupSubtype_smul G U A) x

variable [TotallyDisconnectedSpace G]

/-- **Shapiro's lemma in degree one on the canonical carrier**: for a closed subgroup `U` of a
profinite group `G`, the canonical Shapiro map `H¹(G, Coind_U^G A) ⟶ H¹(U, A)` is bijective. -/
theorem bijective_shapiroMap_one (hU : IsClosed (U : Set G)) :
    Function.Bijective (shapiroMap U A 1) := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  have h : (shapiroMap U A 1 : continuousCohomology 1 (ofDiscreteModule ℤ G (DiscreteCoind G U A)) →
      continuousCohomology 1 (ofDiscreteModule ℤ U A)) =
      explicitH1AddEquivContinuousCohomology U A ∘ explicitShapiroMap1 G U A ∘
        (explicitH1AddEquivContinuousCohomology G (DiscreteCoind G U A)).symm := by
    funext y
    rw [Function.comp_apply, Function.comp_apply,
      ← explicitH1AddEquivContinuousCohomology_shapiroMap, AddEquiv.apply_symm_apply]
  rw [h]
  exact (explicitH1AddEquivContinuousCohomology U A).bijective.comp
    ((bijective_explicitShapiroMap1 G U A hU).comp
      (explicitH1AddEquivContinuousCohomology G (DiscreteCoind G U A)).symm.bijective)

/-- **Shapiro's lemma in degree two on the canonical carrier**: for a closed subgroup `U` of a
profinite group `G`, the canonical Shapiro map `H²(G, Coind_U^G A) ⟶ H²(U, A)` is bijective. -/
theorem bijective_shapiroMap_two (hU : IsClosed (U : Set G)) :
    Function.Bijective (shapiroMap U A 2) := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  have h : (shapiroMap U A 2 : continuousCohomology 2 (ofDiscreteModule ℤ G (DiscreteCoind G U A)) →
      continuousCohomology 2 (ofDiscreteModule ℤ U A)) =
      explicitH2AddEquivContinuousCohomology U A ∘ explicitShapiroMap2 G U A ∘
        (explicitH2AddEquivContinuousCohomology G (DiscreteCoind G U A)).symm := by
    funext y
    rw [Function.comp_apply, Function.comp_apply,
      ← explicitH2AddEquivContinuousCohomology_shapiroMap, AddEquiv.apply_symm_apply]
  rw [h]
  exact (explicitH2AddEquivContinuousCohomology U A).bijective.comp
    ((bijective_explicitShapiroMap2 G U A hU).comp
      (explicitH2AddEquivContinuousCohomology G (DiscreteCoind G U A)).symm.bijective)

/-- **Shapiro's lemma in degrees at most two on the canonical carrier**, in one statement: for a
closed subgroup `U` of a profinite group `G` and `n ≤ 2`, the canonical Shapiro map
`Hⁿ(G, Coind_U^G A) ⟶ Hⁿ(U, A)` is bijective. -/
theorem bijective_shapiroMap_of_le_two (hU : IsClosed (U : Set G)) {n : ℕ} (hn : n ≤ 2) :
    Function.Bijective (shapiroMap U A n) := by
  match n, hn with
  | 0, _ => exact bijective_shapiroMap_zero U A
  | 1, _ => exact bijective_shapiroMap_one U A hU
  | 2, _ => exact bijective_shapiroMap_two U A hU

end CanonicalMap

end TauCeti.ContinuousCohomology

/-! ### Compatibility with the connecting maps -/

namespace TauCeti.ContCohomology.DiscreteShortExact

open TauCeti.ContinuousCohomology

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {U : Subgroup G} [CompactSpace U]
  {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction U A]
  {B : Type u} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction U B]
  [ContinuousSMul U B]
  {C : Type u} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction U C]
  (S : DiscreteShortExact U A B C)

/-- **The Shapiro maps commute with the connecting maps.** For a short exact sequence
`0 → A → B → C → 0` of discrete `U`-modules and its coinduction
`0 → Coind A → Coind B → Coind C → 0` to `G`, the square

```text
Hⁿ(G, Coind_U^G C) ---δ---> Hⁿ⁺¹(G, Coind_U^G A)
       |                            |
   shapiroMap                   shapiroMap
       v                            v
    Hⁿ(U, C) ----------δ--------> Hⁿ⁺¹(U, A)
```

commutes in every degree. This is the naturality of the connecting map in the compatible pair of
the inclusion and the counit; it is the step that carries bijectivity of the Shapiro map from one
degree to the next once the middle terms are acyclic. -/
theorem delta_shapiroMap (hU : IsClosed (U : Set G)) (n : ℕ) :
    (coind U hU S).delta n ≫ shapiroMap U A (n + 1) = shapiroMap U C n ≫ S.delta n := by
  rw [shapiroMap_def, shapiroMap_def]
  exact (coind U hU S).delta_map S (ContinuousMonoidHom.subgroupSubtype U)
    (DiscreteCoind.eval G U A) (DiscreteCoind.eval G U B) (DiscreteCoind.eval G U C)
    (eval_subgroupSubtype_smul G U A) (eval_subgroupSubtype_smul G U B)
    (eval_subgroupSubtype_smul G U C)
    (fun a => by rw [DiscreteCoind.eval_apply, DiscreteCoind.eval_apply, coind_incl_apply])
    (fun b => by rw [DiscreteCoind.eval_apply, DiscreteCoind.eval_apply, coind_proj_apply])
    n

end TauCeti.ContCohomology.DiscreteShortExact
