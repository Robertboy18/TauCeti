/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.WeightOne.RiemannForm
public import TauCeti.Geometry.Symplectic.Transport

/-!
# Effective weight-one Hodge structures are complex structures on the realification

An effective weight-one Hodge structure on an integral module `V` and an almost complex structure
on its realification `ℝ ⊗[ℤ] V` are the same datum. One direction is
`TauCeti.AlmostComplexStructure.latticeHodgeStructure`, which takes the `i`-eigenspace of the
complexified `J` as `F¹`. The other restricts the Weil operator to the real points of the lattice
conjugation, which this file identifies with the realification through
`TauCeti.Hodge.realificationRealPointsEquiv`, `x ↦ 1 ⊗ₜ x`. The two constructions are mutually
inverse: the Weil operator of the Hodge structure of `J` is the complexification of `J`, and the
Hodge structure of the Weil operator of an effective `hs` is `hs`, because an effective weight-one
filtration is determined by its single nontrivial step `F¹ = H^{1,0}`, the `i`-eigenspace of the
Weil operator.

Packaged as `TauCeti.Hodge.effectiveWeightOneEquiv`, this is the classical identification of
effective weight-one Hodge structures with complex tori: a lattice `Λ` together with a complex
structure on `Λ_ℝ`. Through `TauCeti.AlmostComplexStructure.isRiemannForm_iff_isPolarization` it
also identifies the forms polarizing an effective weight-one structure with the Riemann forms for
its complex structure, so polarized effective weight-one structures are polarized abelian-variety
data `(Λ, J, E)`.

## Main declarations

* `TauCeti.Hodge.realificationRealPointsEquiv`: the realification of `V` is the real form of its
  abstract complexification, the real points of the lattice conjugation.
* `TauCeti.Hodge.HodgeStructureOn.realificationAlmostComplexStructure`: the Weil operator of an
  odd-weight integral Hodge structure as an almost complex structure on the realification, with
  `TauCeti.Hodge.HodgeStructureOn.latticeComplexification_realificationAlmostComplexStructure`
  recovering the Weil operator as its complexification.
* `TauCeti.Hodge.HodgeStructureOn.latticeHodgeStructure_realificationAlmostComplexStructure` and
  `TauCeti.AlmostComplexStructure.realificationAlmostComplexStructure_latticeHodgeStructure`: the
  two constructions are mutually inverse.
* `TauCeti.Hodge.effectiveWeightOneEquiv`: **effective weight-one Hodge structures on `V`
  correspond to almost complex structures on its realification.**
* `TauCeti.Hodge.HodgeStructureOn.isRiemannForm_realificationAlmostComplexStructure_iff`: the
  polarizing forms of an effective weight-one structure are the Riemann forms of its complex
  structure.

The identification follows Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.1 and
§7.2.2, and Birkenhake–Lange, *Complex Abelian Varieties*, §1.1 and §4.1.
-/

public section

namespace TauCeti.Hodge

open scoped TensorProduct

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

/-! ### The realification as the real form of the abstract complexification -/

/-- The realification of an integral module is the real form of its abstract complexification:
`x ↦ 1 ⊗ₜ x`, composed with the realification comparison, is a real-linear isomorphism onto the
real points of the lattice conjugation. -/
noncomputable def realificationRealPointsEquiv (hℂ : IsBaseChange ℂ ιℂ) :
    Realification V ≃ₗ[ℝ] realPoints (latticeConjugation hℂ).toEquiv.toLinearMap :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict _
      (((realificationComplexEquiv hℂ).restrictScalars ℝ).toLinearMap ∘ₗ
        TensorProduct.mk ℝ ℂ (Realification V) 1) fun x ↦ by simp)
    ⟨fun x y hxy ↦ Module.Flat.tensorProduct_mk_injective ℝ (Realification V) ℂ
        ((realificationComplexEquiv hℂ).injective (congrArg Subtype.val hxy)),
      fun y ↦ by
        have hy : (y : Vℂ) ∈ realPoints (latticeConj hℂ) := by
          simpa only [mem_realPoints, LinearEquiv.coe_coe, latticeConjugation_toEquiv_apply]
            using y.2
        obtain ⟨x, hx⟩ := exists_eq_realificationComplexEquiv_one_tmul hℂ hy
        exact ⟨x, Subtype.ext hx.symm⟩⟩

/-- The real form comparison sends a real vector to its pure tensor in the complexification. -/
@[simp]
theorem coe_realificationRealPointsEquiv_apply (hℂ : IsBaseChange ℂ ιℂ) (x : Realification V) :
    (realificationRealPointsEquiv hℂ x : Vℂ) = realificationComplexEquiv hℂ (1 ⊗ₜ[ℝ] x) :=
  (rfl)

/-- The inverse real form comparison is characterized by the pure tensor of its value. -/
@[simp]
theorem realificationComplexEquiv_one_tmul_realificationRealPointsEquiv_symm
    (hℂ : IsBaseChange ℂ ιℂ) (y : realPoints (latticeConjugation hℂ).toEquiv.toLinearMap) :
    realificationComplexEquiv hℂ (1 ⊗ₜ[ℝ] (realificationRealPointsEquiv hℂ).symm y) = y := by
  rw [← coe_realificationRealPointsEquiv_apply, LinearEquiv.apply_symm_apply]

/-! ### The Weil operator as a complex structure on the realification -/

namespace HodgeStructureOn

variable {n : ℤ} {hℂ : IsBaseChange ℂ ιℂ}

/-- The Weil operator of an odd-weight integral Hodge structure, restricted to the real form and
read on the realification: an almost complex structure on `ℝ ⊗[ℤ] V`. -/
noncomputable def realificationAlmostComplexStructure (hs : HodgeStructure hℂ n) (hn : Odd n) :
    AlmostComplexStructure (Realification V) :=
  (hs.realAlmostComplexStructure hn).transport (realificationRealPointsEquiv hℂ).symm

/-- On real vectors, the complex structure of an odd-weight Hodge structure acts by its Weil
operator. -/
@[simp]
theorem realificationComplexEquiv_one_tmul_realificationAlmostComplexStructure
    (hs : HodgeStructure hℂ n) (hn : Odd n) (x : Realification V) :
    realificationComplexEquiv hℂ (1 ⊗ₜ[ℝ] hs.realificationAlmostComplexStructure hn x) =
      hs.weilOperator (realificationComplexEquiv hℂ (1 ⊗ₜ[ℝ] x)) := by
  rw [realificationAlmostComplexStructure, AlmostComplexStructure.transport_apply,
    LinearEquiv.symm_symm, realificationComplexEquiv_one_tmul_realificationRealPointsEquiv_symm,
    coe_realAlmostComplexStructure_apply, coe_realificationRealPointsEquiv_apply]

/-- **The complexification of the real complex structure is the Weil operator.** Transporting the
complex structure of an odd-weight Hodge structure back to the abstract complexification recovers
the Weil operator, since both are complex-linear and agree on real vectors. -/
@[simp]
theorem latticeComplexification_realificationAlmostComplexStructure
    (hs : HodgeStructure hℂ n) (hn : Odd n) :
    (hs.realificationAlmostComplexStructure hn).latticeComplexification hℂ = hs.weilOperator := by
  ext y
  obtain ⟨u, rfl⟩ := (realificationComplexEquiv hℂ).surjective y
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul z x =>
    rw [← mul_one z, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_smul, map_smul,
      AlmostComplexStructure.latticeComplexification_realificationComplexEquiv_one_tmul,
      realificationComplexEquiv_one_tmul_realificationAlmostComplexStructure]

/-- **The Hodge structure of the complex structure of an effective weight-one Hodge structure is
the structure itself.** An effective weight-one filtration has a single nontrivial step,
`F¹ = H^{1,0}`, and that is the `i`-eigenspace of the Weil operator. -/
theorem latticeHodgeStructure_realificationAlmostComplexStructure (hs : HodgeStructure hℂ 1)
    (heff : hs.IsEffective) :
    (hs.realificationAlmostComplexStructure odd_one).latticeHodgeStructure hℂ = hs := by
  refine HodgeStructureOn.ext (funext fun p ↦ ?_)
  rw [AlmostComplexStructure.latticeHodgeStructure_F,
    latticeComplexification_realificationAlmostComplexStructure]
  split_ifs with hp hpone
  · exact (heff.F_eq_top_of_nonpos hp).symm
  · subst hpone
    rw [hs.eigenspace_weilOperator_I heff, heff.piece_weight_eq_F]
  · exact (heff.F_eq_bot_of_weight_lt (by omega)).symm

/-- **The polarizing forms of an effective weight-one Hodge structure are the Riemann forms for its
complex structure**, when `V` is flat over `ℤ`. -/
theorem isRiemannForm_realificationAlmostComplexStructure_iff [Module.Flat ℤ V]
    (hs : HodgeStructure hℂ 1) (heff : hs.IsEffective) (E : LinearMap.BilinForm ℤ V) :
    (hs.realificationAlmostComplexStructure odd_one).IsRiemannForm E ↔ IsPolarization hℂ hs E := by
  rw [AlmostComplexStructure.isRiemannForm_iff_isPolarization _ hℂ,
    latticeHodgeStructure_realificationAlmostComplexStructure hs heff]

end HodgeStructureOn

end TauCeti.Hodge

namespace TauCeti.AlmostComplexStructure

open scoped TensorProduct

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

/-- **The complex structure of the Hodge structure of `J` is `J`.** The Weil operator of the
weight-one Hodge structure of `J` is the complexification of `J`, which acts on real vectors by
`J`. -/
@[simp]
theorem realificationAlmostComplexStructure_latticeHodgeStructure
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ) :
    (J.latticeHodgeStructure hℂ).realificationAlmostComplexStructure odd_one = J := by
  ext x
  apply (Hodge.realificationRealPointsEquiv hℂ).injective
  apply Subtype.ext
  simp only [Hodge.coe_realificationRealPointsEquiv_apply,
    Hodge.HodgeStructureOn.realificationComplexEquiv_one_tmul_realificationAlmostComplexStructure,
    latticeHodgeStructure_weilOperator, latticeComplexification_realificationComplexEquiv_one_tmul]

end TauCeti.AlmostComplexStructure

namespace TauCeti.Hodge

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

/-! ### The equivalence -/

/-- **Effective weight-one Hodge structures on a lattice are the complex structures on its
realification.** An effective weight-one Hodge structure is sent to the restriction of its Weil
operator to real vectors; a complex structure `J` is sent to the Hodge structure with
`F¹` the `i`-eigenspace of the complexification of `J`. -/
noncomputable def effectiveWeightOneEquiv (hℂ : IsBaseChange ℂ ιℂ) :
    {hs : HodgeStructure hℂ 1 // hs.IsEffective} ≃ AlmostComplexStructure (Realification V) where
  toFun hs := hs.1.realificationAlmostComplexStructure odd_one
  invFun J := ⟨J.latticeHodgeStructure hℂ, J.isEffective_latticeHodgeStructure hℂ⟩
  left_inv hs := Subtype.ext
    (HodgeStructureOn.latticeHodgeStructure_realificationAlmostComplexStructure hs.1 hs.2)
  right_inv J := J.realificationAlmostComplexStructure_latticeHodgeStructure hℂ

@[simp]
theorem effectiveWeightOneEquiv_apply (hℂ : IsBaseChange ℂ ιℂ)
    (hs : {hs : HodgeStructure hℂ 1 // hs.IsEffective}) :
    effectiveWeightOneEquiv hℂ hs = hs.1.realificationAlmostComplexStructure odd_one :=
  (rfl)

@[simp]
theorem coe_effectiveWeightOneEquiv_symm_apply (hℂ : IsBaseChange ℂ ιℂ)
    (J : AlmostComplexStructure (Realification V)) :
    ((effectiveWeightOneEquiv hℂ).symm J : HodgeStructure hℂ 1) = J.latticeHodgeStructure hℂ :=
  (rfl)

end TauCeti.Hodge
