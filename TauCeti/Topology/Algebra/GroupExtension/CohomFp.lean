/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.ZMod.TrivialAction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Explicit
public import TauCeti.Topology.Algebra.GroupExtension.Cohomology

/-!
# The class of a profinite extension by `𝔽_p` in `H²(G, 𝔽_p)`

The extension dictionary of `TauCeti/Topology/Algebra/GroupExtension/Cohomology.lean` classifies the
profinite extensions of a topological group `G` by a compact module `M` through the explicit
continuous cohomology group `H²(G, M)` of `TauCeti.ContCohomology`. The cohomology every dimension
count of the pro-`p` theory is stated on is instead Mathlib's `continuousCohomology` of the trivial
`𝔽_p`-representation, `TauCeti.cohomFp p G 2`, and the two are identified by
`TauCeti.cohomFpAddEquivH2` for any trivial action of `G` on `ZMod p`. This file reads the class of
a profinite extension of `G` by the multiplicatively written `𝔽_p`, on which `G` acts trivially,
in `cohomFp p G 2`, so that the extensions by `𝔽_p` and the cup products of classes of
`H¹(G, 𝔽_p)` live in one group. The class vanishes exactly when the extension has a continuous
homomorphic section, and two extensions have the same class exactly when they are continuously
equivalent, which are the two theorems of the dictionary transported along the identification.

## Main declarations

* `TauCeti.cohomFpAddEquivH2Additive`: `cohomFp p G 2` is the explicit `H²(G, Additive 𝔽_p)` of
  the additive type tag of a multiplicatively written `𝔽_p` with trivial action.
* `TauCeti.ProfiniteGroupExtension.cohomFpClass`: **the class in `H²(G, 𝔽_p)` of a profinite
  extension of `G` by `𝔽_p`.**
* `TauCeti.ProfiniteGroupExtension.cohomFpClass_eq_zero_iff`: the class vanishes exactly when the
  extension has a continuous homomorphic section.
* `TauCeti.ProfiniteGroupExtension.exists_equiv_continuous_iff_cohomFpClass_eq`: two extensions are
  continuously equivalent exactly when their classes agree.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Ch. I, §2.
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable (p : ℕ) (G : Type u) [Group G] [MulDistribMulAction G (Multiplicative (ZMod p))]
  (htriv : ∀ (g : G) (m : Multiplicative (ZMod p)), g • m = m)
include htriv

/-- The identification `Additive (Multiplicative (ZMod p)) ≃+ ZMod p` carries a trivial action of
`G` on the source to the trivial action `TauCeti.trivialZModAction` on the target. -/
theorem additiveMultiplicative_smul (g : G) (m : Additive (Multiplicative (ZMod p))) :
    letI := trivialZModAction p G
    AddEquiv.additiveMultiplicative (ZMod p) (g • m) =
      g • AddEquiv.additiveMultiplicative (ZMod p) m := by
  simp only [AddEquiv.additiveMultiplicative_apply, Additive.toMul_smul, htriv]
  -- The action on the right is `TauCeti.trivialZModAction`, whose scalar multiplication is
  -- `g • x = x` by definition.
  rfl

variable [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [hcont : ContinuousSMul G (Multiplicative (ZMod p))]

/-- **`H²(G, 𝔽_p)` is the explicit `H²(G, Additive 𝔽_p)`** of the multiplicatively written
`𝔽_p` with a trivial action of `G`, read additively: the identification `TauCeti.cohomFpAddEquivH2`
with the explicit `H²(G, ZMod p)` for the trivial action, followed by the change of coefficients
along `Additive (Multiplicative (ZMod p)) ≃+ ZMod p`. -/
noncomputable def cohomFpAddEquivH2Additive :
    cohomFp p G 2 ≃+ H2 G (Additive (Multiplicative (ZMod p))) :=
  letI := trivialZModAction p G
  haveI : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  (cohomFpAddEquivH2 p G fun _ _ => rfl).trans
    (explicitMap2Equiv G (Additive (Multiplicative (ZMod p))) G (ZMod p)
      (ContinuousMulEquiv.refl G) (AddEquiv.additiveMultiplicative (ZMod p))
      continuous_of_discreteTopology continuous_of_discreteTopology
      (additiveMultiplicative_smul p G htriv)).symm

/-- The identification `TauCeti.cohomFpAddEquivH2Additive` is `TauCeti.cohomFpAddEquivH2` for the
trivial action `TauCeti.trivialZModAction`, followed by the change of coefficients along
`Additive (Multiplicative (ZMod p)) ≃+ ZMod p`. -/
theorem cohomFpAddEquivH2Additive_apply (x : cohomFp p G 2) :
    letI := trivialZModAction p G
    haveI : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
    cohomFpAddEquivH2Additive p G htriv x =
      (explicitMap2Equiv G (Additive (Multiplicative (ZMod p))) G (ZMod p)
        (ContinuousMulEquiv.refl G) (AddEquiv.additiveMultiplicative (ZMod p))
        continuous_of_discreteTopology continuous_of_discreteTopology
        (additiveMultiplicative_smul p G htriv)).symm (cohomFpAddEquivH2 p G (fun _ _ => rfl) x) :=
  (rfl)

namespace ProfiniteGroupExtension

variable {p G} [NeZero p] [T2Space G] (X Y : ProfiniteGroupExtension G (Multiplicative (ZMod p)))

/-- **The class in `H²(G, 𝔽_p)` of a profinite extension of `G` by `𝔽_p`** with trivial action:
its class in the explicit continuous cohomology,
`TauCeti.ProfiniteGroupExtension.contCohomologyClass`, read in Mathlib's continuous cohomology of
the trivial `𝔽_p`-representation. -/
noncomputable def cohomFpClass : cohomFp p G 2 :=
  (cohomFpAddEquivH2Additive p G htriv).symm X.contCohomologyClass

theorem cohomFpClass_def :
    X.cohomFpClass htriv = (cohomFpAddEquivH2Additive p G htriv).symm X.contCohomologyClass :=
  (rfl)

/-- The class of a profinite extension by `𝔽_p` in `H²(G, 𝔽_p)` is its class in the explicit
continuous cohomology, under the identification `TauCeti.cohomFpAddEquivH2Additive`. -/
@[simp]
theorem cohomFpAddEquivH2Additive_cohomFpClass :
    cohomFpAddEquivH2Additive p G htriv (X.cohomFpClass htriv) = X.contCohomologyClass :=
  (cohomFpAddEquivH2Additive p G htriv).apply_symm_apply _

/-- **A profinite extension by `𝔽_p` has a continuous homomorphic section exactly when its class in
`H²(G, 𝔽_p)` vanishes.** -/
theorem cohomFpClass_eq_zero_iff :
    X.cohomFpClass htriv = 0 ↔ ∃ s : X.toGroupExtension.Splitting, Continuous ⇑s := by
  rw [cohomFpClass_def, map_eq_zero_iff _ (cohomFpAddEquivH2Additive p G htriv).symm.injective,
    contCohomologyClass_def,
    ← X.toGroupExtension.exists_splitting_continuous_iff_contCohomologyClass_eq_zero]

/-- **Two profinite extensions by `𝔽_p` are continuously equivalent exactly when their classes in
`H²(G, 𝔽_p)` agree.** -/
theorem exists_equiv_continuous_iff_cohomFpClass_eq :
    (∃ e : X.toGroupExtension.Equiv Y.toGroupExtension, Continuous ⇑e) ↔
      X.cohomFpClass htriv = Y.cohomFpClass htriv := by
  rw [cohomFpClass_def, cohomFpClass_def,
    (cohomFpAddEquivH2Additive p G htriv).symm.injective.eq_iff,
    exists_equiv_continuous_iff_contCohomologyClass_eq]

end ProfiniteGroupExtension

end TauCeti
