/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.InternalHom
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Shapiro

/-!
# The evaluation pairing of a coinduced module, through Shapiro's lemma

Let `U` be an open subgroup of finite index of a profinite group `G`, let `A` be a finite discrete
`U`-module and `N` a discrete `G`-module. The dual of the coinduced module `Coind_U^G A` is again
coinduced, `Hom(Coind_U^G A, N) ≅ Coind_U^G Hom(A, N)` through
`TauCeti.DiscreteCoind.toInternalHom`, and Shapiro's lemma identifies the cohomology of both
coinduced modules with that of `U`. Under these identifications the `(1,1)` evaluation pairing
`⟨-, -⟩_G : H¹(G, Hom(Coind_U^G A, N)) × H¹(G, Coind_U^G A) → H²(G, N)` of
`TauCeti/RepresentationTheory/Homological/ContCohomology/Cup/Duality/Basic.lean` is the
corestriction of the evaluation pairing of `U`:

```text
⟨toInternalHom F, x⟩_G = cor_U^G ⟨sh F, sh x⟩_U.
```

The evaluation pairing of `G` on the coinduced modules is the trace of the pointwise evaluation
pairing (`TauCeti.DiscreteCoind.toAddMonoidHom_toInternalHom_apply`), the cup product is natural
in the pairing, and the corestriction of a cup product of `U` is the trace of the cup product of
`G` along the pointwise pairing of the inverse Shapiro images
(`TauCeti.ContCohomology.explicitCor2_explicitCup11`).

This is the identity through which a duality statement for the finite modules of `G` is read on the
open subgroup `U`: a class of `H¹(U, A)` is detected by the pairing of `U` as soon as its inverse
Shapiro image is detected by the pairing of `G`.

## Main statement

* `TauCeti.ContCohomology.explicitDualityPairing11_explicitCoeff1_toInternalHom`: the `(1,1)`
  evaluation pairing of `G` on a coinduced module and its dual is the corestriction of the `(1,1)`
  evaluation pairing of `U` on the Shapiro images.

## References

* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 8
  (1962/63), exposé 252, §9.2.
-/

public section

namespace TauCeti.ContCohomology

universe uG uA uN

variable (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
  (A : Type uA) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction U A] [ContinuousSMul U A] [Finite A]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]

/-- **The evaluation pairing of a coinduced module is the corestriction of the evaluation pairing
of the subgroup.** For an open subgroup `U` of finite index of a profinite group `G`, a finite
discrete `U`-module `A` and a discrete `G`-module `N`, a class `F` of
`H¹(G, Coind_U^G Hom(A, N))`, read in `H¹(G, Hom(Coind_U^G A, N))` through
`TauCeti.DiscreteCoind.toInternalHom`, pairs with a class `x` of `H¹(G, Coind_U^G A)` to the
corestriction of the evaluation pairing of `U` of the Shapiro images of `F` and `x`:
`⟨toInternalHom F, x⟩_G = cor_U^G ⟨sh F, sh x⟩_U`. -/
theorem explicitDualityPairing11_explicitCoeff1_toInternalHom
    (F : H1 G (DiscreteCoind G U (InternalHom U A N))) (x : H1 G (DiscreteCoind G U A)) :
    explicitDualityPairing11 G (DiscreteCoind G U A) N
        (explicitCoeff1 G (DiscreteCoind G U (InternalHom U A N))
          (DiscreteCoind.toInternalHom U A N) continuous_of_discreteTopology F) x =
      explicitCor2 G N U hU
        (explicitDualityPairing11 U A N
          (explicitShapiro1 G U (InternalHom U A N) (U.isClosed_of_isOpen hU) F)
          (explicitShapiro1 G U A (U.isClosed_of_isOpen hU) x)) := by
  rw [explicitDualityPairing11_def, explicitDualityPairing11_def, explicitCor2_explicitCup11,
    AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  -- The pairing `(F, f) ↦ tr (g ↦ F g (f g))` of the coinduced modules, with values in `N`: it is
  -- the evaluation pairing of `G` read through `toInternalHom`, and the trace of the pointwise
  -- evaluation pairing.
  set μ : DiscreteCoind G U (InternalHom U A N) →+ DiscreteCoind G U A →+ N :=
    (DiscreteCoind.pointwisePairing U (InternalHom.evalPairing U)
      (InternalHom.evalPairing_equivariant (G := U))).compr₂
      (DiscreteCoind.trace G U N : DiscreteCoind G U N →+ N) with hμ
  have hequiv : ∀ (g : G) (F' : DiscreteCoind G U (InternalHom U A N)) (f : DiscreteCoind G U A),
      μ (g • F') (g • f) = g • μ F' f := fun g F' f ↦ by
    simp only [hμ, AddMonoidHom.compr₂_apply, DiscreteCoind.pointwisePairing_smul,
      DistribMulActionHom.coe_fn_coe, map_smul]
  have h₁ := explicitCoeff2_explicitCup11 G (DiscreteCoind G U (InternalHom U A N))
    (DiscreteCoind G U A) N (InternalHom G (DiscreteCoind G U A) N) (DiscreteCoind G U A) N μ
    continuous_of_discreteTopology hequiv (InternalHom.evalPairing G) continuous_of_discreteTopology
    (InternalHom.evalPairing_equivariant (G := G)) (DiscreteCoind.toInternalHom U A N)
    (DistribMulActionHom.id G) (DistribMulActionHom.id G) continuous_of_discreteTopology
    continuous_id continuous_id (fun F' f ↦ by
      simp only [hμ, DistribMulActionHom.id_apply, InternalHom.evalPairing_apply,
        DiscreteCoind.toAddMonoidHom_toInternalHom_apply, AddMonoidHom.compr₂_apply,
        DistribMulActionHom.coe_fn_coe]) F x
  have h₂ := explicitCoeff2_explicitCup11 G (DiscreteCoind G U (InternalHom U A N))
    (DiscreteCoind G U A) (DiscreteCoind G U N) (DiscreteCoind G U (InternalHom U A N))
    (DiscreteCoind G U A) N
    (DiscreteCoind.pointwisePairing U (InternalHom.evalPairing U)
      (InternalHom.evalPairing_equivariant (G := U))) continuous_of_discreteTopology
    (fun g f f' ↦ DiscreteCoind.pointwisePairing_smul U (InternalHom.evalPairing U)
      (InternalHom.evalPairing_equivariant (G := U)) g f f') μ continuous_of_discreteTopology hequiv
    (DistribMulActionHom.id G) (DistribMulActionHom.id G) (DiscreteCoind.trace G U N)
    continuous_id continuous_id DiscreteCoind.continuous_trace (fun F' f ↦ by
      simp only [hμ, DistribMulActionHom.id_apply, AddMonoidHom.compr₂_apply,
        DistribMulActionHom.coe_fn_coe]) F x
  simp only [explicitCoeff2_id, explicitCoeff1_id, AddMonoidHom.id_apply] at h₁ h₂
  exact h₁.symm.trans h₂.symm

end TauCeti.ContCohomology
