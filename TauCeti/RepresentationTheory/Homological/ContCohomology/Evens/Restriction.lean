/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Class
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Conjugation

/-!
# The restriction of the index-two Evens norm

Let `U` be an open subgroup of index two in a topological group `G` and let
`α : U →* Multiplicative (ZMod 2)` be a continuous homomorphism, that is a class in `H¹(U, 𝔽₂)`.
The index-two Evens norm `N^{Ev}(α) ∈ H²(G, 𝔽₂)` is the class of the two-point graph cocycle of
`TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Cochain`, and its restriction back
to `U` is the cup product of `α` with its conjugate:
```text
res_U N^{Ev}(α) = α ⌣ (s · α),
```
where `s · α` is the conjugation action of the nontrivial coset, in the choice-free form
`TauCeti.ContCohomology.evensConj1`. This is the first of the four identities characterizing the
index-two norm, in the form Kozlowski's index-two expansion uses.

The identity holds already at the level of cochains. On `U × U` the graph cochain is
`α γ * α (s⁻¹ η s)`, which is the `(1,1)` cup-product cochain of `α` with its conjugate for the
multiplication pairing of `𝔽₂`; passing to classes gives the identity in the explicit `H²(U, 𝔽₂)`.

## Main definitions

* `TauCeti.ContCohomology.evensHomCocycleAmbient`: a continuous homomorphism on `U`, as a
  continuous `1`-cocycle of `U` with the lifted trivial `𝔽₂` coefficients of the ambient group.

## Main results

* `TauCeti.ContCohomology.evensNorm_res`: the restriction of the graph class is the cup product of
  `α` with its conjugate.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), 54–65.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer. Math.
  Soc. **91** (1984), 309–313, Lemma 2.4.
-/

public section

namespace TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

local instance : ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

omit [IsTopologicalGroup G] in
private theorem evensHomCochainAmbient_mem_Z1 (U : OpenSubgroup G)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    (fun h : U.toSubgroup => (trivialF2Equiv G).symm (Multiplicative.toAdd (α h))) ∈
      Z1 U.toSubgroup (trivialF2 G).V := by
  refine mem_Z1_iff.2 ⟨?_, fun g h => ?_⟩
  · exact (continuous_of_discreteTopology : Continuous (trivialF2Equiv G).symm).comp
      (continuous_toAdd.comp hα)
  · apply (trivialF2Equiv G).injective
    simp only [Subgroup.smul_def, TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply, map_add,
      AddEquiv.apply_symm_apply, map_mul, toAdd_mul]
    exact add_comm _ _

/-- A continuous homomorphism `α : U → Multiplicative (ZMod 2)` on an open subgroup, as a
continuous `1`-cocycle of `U` with coefficients in the lifted trivial `𝔽₂` object of the ambient
group `G`. This is the representative of the class of `α` to which restriction, corestriction and
the cup products of the ambient group apply. -/
noncomputable def evensHomCocycleAmbient (U : OpenSubgroup G)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    Z1 U.toSubgroup (trivialF2 G).V :=
  ⟨fun h => (trivialF2Equiv G).symm (Multiplicative.toAdd (α h)),
    evensHomCochainAmbient_mem_Z1 U α hα⟩

omit [IsTopologicalGroup G] in
/-- The underlying cochain of `evensHomCocycleAmbient`. -/
@[simp]
theorem coe_evensHomCocycleAmbient (U : OpenSubgroup G)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    (evensHomCocycleAmbient U α hα : U.toSubgroup → (trivialF2 G).V) =
      fun h => (trivialF2Equiv G).symm (Multiplicative.toAdd (α h)) :=
  (rfl)

/-- **Identity 1 of the index-two Evens norm: `res_U N^{Ev}(α) = α ⌣ (s · α)`.** The restriction to
`U` of the class of the two-point graph cocycle, formed with any `s ∉ U`, is the `(1,1)` cup
product, for the multiplication pairing of `𝔽₂`, of the class of `α` with its conjugate
`TauCeti.ContCohomology.evensConj1`. The right-hand side does not mention `s`. -/
theorem evensNorm_res (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2) {s : G} (hs : s ∉ U)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    explicitRes2 G (trivialF2 G).V U.toSubgroup
        (evensGraphCocycle U s α hU hs hα : H2 G (trivialF2 G).V) =
      explicitCup11 U.toSubgroup (trivialF2 G).V (trivialF2 G).V (trivialF2 G).V
        (trivialF2Pairing G) continuous_of_discreteTopology
        (fun u m n => trivialF2Pairing_smul_smul G (u : G) m n)
        (evensHomCocycleAmbient U α hα : H1 U.toSubgroup (trivialF2 G).V)
        (evensConj1 G (trivialF2 G).V U.toSubgroup hU U.isOpen'
          (evensHomCocycleAmbient U α hα : H1 U.toSubgroup (trivialF2 G).V)) := by
  have := Subgroup.normal_of_index_eq_two hU
  rw [evensConj1_eq_explicitConj1 G (trivialF2 G).V U.toSubgroup hU U.isOpen' hs,
    explicitConj1_apply_eq_smul, smul_mk, explicitCup11_mk, explicitRes2_mk]
  apply congrArg (fun z : Z2 U.toSubgroup (trivialF2 G).V => (z : H2 U.toSubgroup (trivialF2 G).V))
  apply Subtype.ext
  funext ⟨γ, η⟩
  have hconj : s⁻¹ * (η : G) * s ∈ U.toSubgroup :=
    (Subgroup.normal_of_index_eq_two hU).conj_mem' η η.2 s
  simp only [cocyclesMap2_coe, cochainsMap2_apply, ContinuousMonoidHom.coe_subgroupSubtype,
    Subgroup.subtype_apply, AddMonoidHom.id_apply, coe_evensGraphCocycle, cocyclesMap1_coe,
    cochainsMap1_apply, coe_evensHomCocycleAmbient, DistribSMul.toAddMonoidHom_apply,
    MonoidHom.coe_coe, Subgroup.inverseConjugationHom_apply, trivialF2Pairing_apply,
    Subgroup.smul_def, TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply,
    AddEquiv.apply_symm_apply]
  rw [evensGraphCochain_apply_of_mem_of_mem hU hs γ.2 η.2, evensExtend_of_mem γ.2,
    evensExtend_of_mem hconj]

end TauCeti.ContCohomology
