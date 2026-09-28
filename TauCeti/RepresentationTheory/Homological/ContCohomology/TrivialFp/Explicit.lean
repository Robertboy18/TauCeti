/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.H2ZMod
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp
public import TauCeti.Topology.Algebra.ContinuousZModDual

/-!
# The explicit models of `H¹(G, 𝔽_p)` and `H²(G, 𝔽_p)`

The cohomology `cohomFp p G n` with trivial `ZMod p` coefficients is Mathlib's continuous cohomology
of an object of `TopRep (ZMod p) G`, while the explicit low-degree cohomology `H1 G M` and `H2 G M`
of `TauCeti.ContCohomology` is computed from inhomogeneous cochains with values in a discrete
`G`-module, and every rank count of a pro-`p` group is stated for the explicit model. This file
identifies the two in degrees one and two.

The comparison for a discrete smooth representation over any scalars is
`TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete` and its degree-two counterpart. For
`X = trivialFp p G` the carrier is the universe lift of `ZMod p`, and a further change of
coefficients along `trivialFpEquiv p G` lands in `H1 G (ZMod p)` and `H2 G (ZMod p)`, for any
trivial action of `G` on `ZMod p`. In degree one, the class group of a trivial action is the group
of continuous characters, so `H¹(G, 𝔽_p)` is the continuous `𝔽_p`-dual of `G`, as an
`𝔽_p`-vector space.

## Main definitions

* `TauCeti.cohomFpAddEquivH1`, `TauCeti.cohomFpAddEquivH2`: `cohomFp p G 1` and `cohomFp p G 2` are
  the explicit `H1 G (ZMod p)` and `H2 G (ZMod p)` for a trivial action.
* `TauCeti.cohomFpLinearEquivH2`: the degree-two identification is `𝔽_p`-linear.
* `TauCeti.cohomFpLinearEquivContinuousZModDual`: `H¹(G, 𝔽_p)` is the continuous `𝔽_p`-dual of
  `G`, as an `𝔽_p`-vector space; `TauCeti.cohomFpLinearEquivContinuousZModDual_π_apply` computes
  it on the class of a homogeneous one-cocycle.

## References

* J.-P. Serre, *Galois Cohomology*, I §2.
-/
public section

namespace TauCeti

open CategoryTheory TauCeti.ContCohomology _root_.ContinuousCohomology

universe u

attribute [local instance] TopRep.distribMulAction

-- Preferring the ring path keeps a single additive structure on `ZMod p`.
attribute [local instance 2000] Ring.toAddCommGroup

section TrivialFp

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] continuousSMul_trivialFp

variable [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)]
  (htriv : ∀ (g : G) (m : ZMod p), g • m = m)
include htriv

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod p)] in
/-- The universe lift `trivialFpEquiv p G` is compatible with the trivial actions on both sides. -/
private theorem trivialFpEquiv_smul (g : G) (x : (trivialFp p G).V) :
    trivialFpEquiv p G ((ContinuousMulEquiv.refl G) g • x) = g • trivialFpEquiv p G x := by
  rw [smul_trivialFp_V, htriv]

/-- **`H¹(G, 𝔽_p)` is the explicit `H1 G (ZMod p)`**, for any trivial action of `G` on `ZMod p`. -/
noncomputable def cohomFpAddEquivH1 : cohomFp p G 1 ≃+ H1 G (ZMod p) :=
  (trivialFp p G).explicitH1AddEquivContinuousCohomologyOfDiscrete.symm.trans
    (explicitMap1Equiv G (trivialFp p G).V G (ZMod p) (ContinuousMulEquiv.refl G)
      (trivialFpEquiv p G).toAddEquiv continuous_of_discreteTopology continuous_of_discreteTopology
      (trivialFpEquiv_smul p G htriv))

/-- **`H²(G, 𝔽_p)` is the explicit `H2 G (ZMod p)`**, for any trivial action of `G` on `ZMod p`. -/
noncomputable def cohomFpAddEquivH2 [LocallyCompactSpace G] : cohomFp p G 2 ≃+ H2 G (ZMod p) :=
  (trivialFp p G).explicitH2AddEquivContinuousCohomologyOfDiscrete.symm.trans
    (explicitMap2Equiv G (trivialFp p G).V G (ZMod p) (ContinuousMulEquiv.refl G)
      (trivialFpEquiv p G).toAddEquiv continuous_of_discreteTopology continuous_of_discreteTopology
      (trivialFpEquiv_smul p G htriv))

/-- **`H²(G, 𝔽_p)` is the explicit `H2 G (ZMod p)` as an `𝔽_p`-vector space**, for any trivial
action of `G` on `ZMod p`. -/
noncomputable def cohomFpLinearEquivH2 [LocallyCompactSpace G] :
    cohomFp p G 2 ≃ₗ[ZMod p] H2 G (ZMod p) :=
  LinearEquiv.ofBijective ((cohomFpAddEquivH2 p G htriv).toAddMonoidHom.toZModLinearMap p)
    (cohomFpAddEquivH2 p G htriv).bijective

/-- The linear identification of `H²(G, 𝔽_p)` with its explicit model is the additive one. -/
@[simp]
theorem cohomFpLinearEquivH2_apply [LocallyCompactSpace G] (x : cohomFp p G 2) :
    cohomFpLinearEquivH2 p G htriv x = cohomFpAddEquivH2 p G htriv x :=
  (rfl)

omit htriv in
/-- **`H¹(G, 𝔽_p)` is the continuous `𝔽_p`-dual of `G`**, as an `𝔽_p`-vector space: the classes of
continuous `1`-cocycles for the trivial action are the continuous characters `G → 𝔽_p`. -/
noncomputable def cohomFpLinearEquivContinuousZModDual :
    cohomFp p G 1 ≃ₗ[ZMod p] continuousZModDual p G :=
  -- The explicit model `H1 G (ZMod p)` needs an action of `G` on `ZMod p`; the trivial one is
  -- installed for the duration of the construction and does not appear in the statement.
  let _ : DistribMulAction G (ZMod p) := DistribMulAction.compHom (ZMod p) (1 : G →* (ZMod p)ˣ)
  have htriv : ∀ (g : G) (m : ZMod p), g • m = m := fun _ m ↦ one_smul (ZMod p)ˣ m
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd.congr fun x ↦ (htriv x.1 x.2).symm⟩
  let e : cohomFp p G 1 ≃+ continuousZModDual p G :=
    (cohomFpAddEquivH1 p G htriv).trans (H1EquivOfSmulEqSelf htriv)
  LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap p) e.bijective

omit [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)] htriv in
/-- The character attached by `cohomFpLinearEquivContinuousZModDual` to the class of a homogeneous
one-cocycle `z` reads `z` at `(1, g)`. -/
theorem cohomFpLinearEquivContinuousZModDual_π_apply (z : cocycles (trivialFp p G) 1) (g : G) :
    Multiplicative.toAdd
        (Additive.toMul (cohomFpLinearEquivContinuousZModDual p G (π (trivialFp p G) 1 z)) g) =
      trivialFpEquiv p G (((TopRep.homogeneousCochains (trivialFp p G)).iCycles 1 z).val 1 g) := by
  -- The trivial action installed by the construction.
  let _ : DistribMulAction G (ZMod p) := DistribMulAction.compHom (ZMod p) (1 : G →* (ZMod p)ˣ)
  have htriv : ∀ (g : G) (m : ZMod p), g • m = m := fun _ m ↦ one_smul (ZMod p)ˣ m
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd.congr fun x ↦ (htriv x.1 x.2).symm⟩
  have h1 : cohomFpLinearEquivContinuousZModDual p G (π (trivialFp p G) 1 z) =
      H1EquivOfSmulEqSelf htriv (cohomFpAddEquivH1 p G htriv (π (trivialFp p G) 1 z)) := rfl
  -- The cocycle of the carrier corresponding to `z`: it has the same values, and its class maps
  -- to the class of `z`.
  set w := (ofDiscreteModuleCocyclesRestrictScalarsIntIso (trivialFp p G) 1).inv z
  have hz : (ofDiscreteModuleCocyclesRestrictScalarsIntIso (trivialFp p G) 1).hom w = z :=
    Iso.inv_hom_id_apply _ _
  have hval : ((TopRep.homogeneousCochains (trivialFp p G)).iCycles 1 z).val 1 g =
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G (trivialFp p G).V)).iCycles 1 w).val 1
        g := by
    rw [← hz]
    exact iCycles_ofDiscreteModuleCocyclesRestrictScalarsIntIso_hom_apply (trivialFp p G) w 1 g
  have hπ : (ofDiscreteModuleRestrictScalarsIntIso (trivialFp p G) 1).hom
      (π (ofDiscreteModule ℤ G (trivialFp p G).V) 1 w) = π (trivialFp p G) 1 z := by
    rw [← CategoryTheory.comp_apply, π_comp_ofDiscreteModuleRestrictScalarsIntIso_hom,
      CategoryTheory.comp_apply, hz]
    rfl
  have h2 : (trivialFp p G).explicitH1AddEquivContinuousCohomologyOfDiscrete.symm
      (π (trivialFp p G) 1 z) =
      (((cocycleEquiv1 G (trivialFp p G).V).symm w : Z1 G _) : H1 G (trivialFp p G).V) := by
    rw [AddEquiv.symm_apply_eq, TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete_apply,
      explicitH1AddEquivContinuousCohomology_apply, AddEquiv.apply_symm_apply]
    exact hπ.symm
  rw [h1, cohomFpAddEquivH1, AddEquiv.trans_apply, h2, explicitMap1Equiv_apply]
  -- `explicitMap1_mk` and `cocyclesMap1_apply` are applied as terms: `explicitMap1Equiv` states
  -- the continuity of the coefficient map at the equivalence and the lemmas at its coercion to a
  -- homomorphism, which `rw` does not identify.
  refine (congrArg (fun q ↦ Multiplicative.toAdd (Additive.toMul (H1EquivOfSmulEqSelf htriv q) g))
    (explicitMap1_mk _ _ _ _ _ _ _ _ ((cocycleEquiv1 G (trivialFp p G).V).symm w))).trans ?_
  rw [H1EquivOfSmulEqSelf_mk, Z1EquivOfSmulEqSelf_apply, toAdd_ofAdd]
  refine (cocyclesMap1_apply _ _ _ _ _ _ _ _ _ g).trans ?_
  rw [cocycleEquiv1_symm_apply, hval]
  rfl

end TrivialFp

end TauCeti
