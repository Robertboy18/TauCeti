/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.WeightOne.RiemannForm
public import TauCeti.Geometry.Symplectic.Transport

/-!
# Effective weight-one Hodge structures are complex structures

An effective weight-one Hodge structure on the complexification `ℂ ⊗[ℝ] W` of a real vector space
`W`, for its canonical conjugation, and an almost complex structure on `W` are the same datum. One
direction is `TauCeti.AlmostComplexStructure.hodgeStructure`, which takes the `i`-eigenspace of the
complexified `J` as `F¹`. The other restricts the Weil operator to the real points of the
conjugation, which `TauCeti.Hodge.complexificationRealPointsEquiv`, `w ↦ 1 ⊗ₜ w`, identifies with
`W`. The two constructions are mutually inverse: the Weil operator of the Hodge structure of `J` is
the complexification of `J`, and the Hodge structure of the Weil operator of an effective `hs` is
`hs`, because an effective weight-one filtration is determined by its single nontrivial step
`F¹ = H^{1,0}`, the `i`-eigenspace of the Weil operator.

For an integral module `V` with an abstract complexification the same holds with `W` the
realification `ℝ ⊗[ℤ] V`: the forward direction is
`TauCeti.AlmostComplexStructure.latticeHodgeStructure`, and the real form of the lattice
conjugation is the realification through `TauCeti.Hodge.realificationRealPointsEquiv`. Packaged as
`TauCeti.Hodge.latticeEffectiveWeightOneEquiv`, this is the classical identification of effective
weight-one integral Hodge structures with complex tori: a lattice `Λ` together with a complex
structure on `Λ_ℝ`. Through `TauCeti.AlmostComplexStructure.isRiemannForm_iff_isPolarization` it
also identifies the forms polarizing an effective weight-one structure with the Riemann forms for
its complex structure, so polarized effective weight-one structures are polarized abelian-variety
data `(Λ, J, E)`.

## Main declarations

* `TauCeti.Hodge.HodgeStructureOn.almostComplexStructure`: the Weil operator of an odd-weight Hodge
  structure on a complexification `ℂ ⊗[ℝ] W` as an almost complex structure on `W`, with
  `TauCeti.Hodge.HodgeStructureOn.baseChange_almostComplexStructure` recovering the Weil operator
  as its complexification.
* `TauCeti.Hodge.HodgeStructureOn.hodgeStructure_almostComplexStructure` and
  `TauCeti.AlmostComplexStructure.almostComplexStructure_hodgeStructure`: the two constructions
  are mutually inverse.
* `TauCeti.Hodge.effectiveWeightOneEquiv`: **effective weight-one Hodge structures on `ℂ ⊗[ℝ] W`
  correspond to almost complex structures on `W`.**
* `TauCeti.Hodge.HodgeStructureOn.realificationAlmostComplexStructure`,
  `TauCeti.Hodge.HodgeStructureOn.latticeComplexification_realificationAlmostComplexStructure`,
  `TauCeti.Hodge.HodgeStructureOn.latticeHodgeStructure_realificationAlmostComplexStructure`,
  `TauCeti.AlmostComplexStructure.realificationAlmostComplexStructure_latticeHodgeStructure` and
  `TauCeti.Hodge.latticeEffectiveWeightOneEquiv`: the same for an integral module and its
  realification.
* `TauCeti.Hodge.HodgeStructureOn.isRiemannForm_realificationAlmostComplexStructure_iff`: the
  polarizing forms of an effective weight-one integral structure are the Riemann forms of its
  complex structure.

The identification follows Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.1 and
§7.2.2, and Birkenhake–Lange, *Complex Abelian Varieties*, §1.1 and §4.1.
-/

public section

namespace TauCeti.Hodge

open scoped TensorProduct

universe u v

namespace HodgeStructureOn

/-! ### The Weil operator as a complex structure on a real vector space -/

section Real

variable {W : Type u} [AddCommGroup W] [Module ℝ W] {n : ℤ}

/-- The Weil operator of an odd-weight Hodge structure on the complexification of a real vector
space, restricted to the real form and read on the space itself: an almost complex structure on
`W`. -/
noncomputable def almostComplexStructure
    (hs : HodgeStructureOn (ℂ ⊗[ℝ] W) (complexificationConjugation W) n) (hn : Odd n) :
    AlmostComplexStructure W :=
  (hs.realAlmostComplexStructure hn).transport (complexificationRealPointsEquiv W).symm

/-- The real form comparison intertwines the complex structure on `W` with the complex structure
on the real points. -/
@[simp]
theorem complexificationRealPointsEquiv_almostComplexStructure
    (hs : HodgeStructureOn (ℂ ⊗[ℝ] W) (complexificationConjugation W) n) (hn : Odd n) (w : W) :
    complexificationRealPointsEquiv W (hs.almostComplexStructure hn w) =
      hs.realAlmostComplexStructure hn (complexificationRealPointsEquiv W w) := by
  rw [almostComplexStructure, AlmostComplexStructure.transport_apply, LinearEquiv.symm_symm,
    LinearEquiv.apply_symm_apply]

/-- On real vectors, the complex structure of an odd-weight Hodge structure acts by its Weil
operator. -/
@[simp]
theorem one_tmul_almostComplexStructure
    (hs : HodgeStructureOn (ℂ ⊗[ℝ] W) (complexificationConjugation W) n) (hn : Odd n) (w : W) :
    (1 : ℂ) ⊗ₜ[ℝ] hs.almostComplexStructure hn w = hs.weilOperator (1 ⊗ₜ[ℝ] w) := by
  rw [← coe_complexificationRealPointsEquiv_apply,
    complexificationRealPointsEquiv_almostComplexStructure, coe_realAlmostComplexStructure_apply,
    coe_complexificationRealPointsEquiv_apply]

/-- **The complexification of the complex structure is the Weil operator.** Both are complex-linear
and agree on real vectors. -/
@[simp]
theorem baseChange_almostComplexStructure
    (hs : HodgeStructureOn (ℂ ⊗[ℝ] W) (complexificationConjugation W) n) (hn : Odd n) :
    (hs.almostComplexStructure hn).toLinearMap.baseChange ℂ = hs.weilOperator := by
  refine (TensorProduct.isBaseChange ℝ W ℂ).algHom_ext _ _ fun w ↦ ?_
  rw [TensorProduct.mk_apply, LinearMap.baseChange_tmul, one_tmul_almostComplexStructure]

/-- **The Hodge structure of the complex structure of an effective weight-one Hodge structure is
the structure itself.** An effective weight-one filtration has a single nontrivial step,
`F¹ = H^{1,0}`, and that is the `i`-eigenspace of the Weil operator. -/
theorem hodgeStructure_almostComplexStructure
    (hs : HodgeStructureOn (ℂ ⊗[ℝ] W) (complexificationConjugation W) 1) (heff : hs.IsEffective) :
    (hs.almostComplexStructure odd_one).hodgeStructure = hs := by
  refine HodgeStructureOn.ext (funext fun p ↦ ?_)
  rw [AlmostComplexStructure.hodgeStructure_F, baseChange_almostComplexStructure]
  split_ifs with hp hpone
  · exact (heff.F_eq_top_of_nonpos hp).symm
  · subst hpone
    rw [hs.eigenspace_weilOperator_I heff, heff.piece_weight_eq_F]
  · exact (heff.F_eq_bot_of_weight_lt (by omega)).symm

end Real

/-! ### The Weil operator as a complex structure on the realification -/

section Lattice

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ} {hℂ : IsBaseChange ℂ ιℂ} {n : ℤ}

/-- The Weil operator of an odd-weight integral Hodge structure, restricted to the real form and
read on the realification: an almost complex structure on `ℝ ⊗[ℤ] V`. -/
noncomputable def realificationAlmostComplexStructure (hs : HodgeStructure hℂ n) (hn : Odd n) :
    AlmostComplexStructure (Realification V) :=
  (hs.realAlmostComplexStructure hn).transport (realificationRealPointsEquiv hℂ).symm

/-- The real form comparison intertwines the complex structure on the realification with the
complex structure on the real points. -/
@[simp]
theorem realificationRealPointsEquiv_realificationAlmostComplexStructure
    (hs : HodgeStructure hℂ n) (hn : Odd n) (x : Realification V) :
    realificationRealPointsEquiv hℂ (hs.realificationAlmostComplexStructure hn x) =
      hs.realAlmostComplexStructure hn (realificationRealPointsEquiv hℂ x) := by
  rw [realificationAlmostComplexStructure, AlmostComplexStructure.transport_apply,
    LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]

/-- On real vectors, the complex structure of an odd-weight Hodge structure acts by its Weil
operator. -/
@[simp]
theorem realificationComplexEquiv_one_tmul_realificationAlmostComplexStructure
    (hs : HodgeStructure hℂ n) (hn : Odd n) (x : Realification V) :
    realificationComplexEquiv hℂ (1 ⊗ₜ[ℝ] hs.realificationAlmostComplexStructure hn x) =
      hs.weilOperator (realificationComplexEquiv hℂ (1 ⊗ₜ[ℝ] x)) := by
  rw [← coe_realificationRealPointsEquiv_apply,
    realificationRealPointsEquiv_realificationAlmostComplexStructure,
    coe_realAlmostComplexStructure_apply, coe_realificationRealPointsEquiv_apply]

/-- **The complexification of the real complex structure is the Weil operator.** Transporting the
complex structure of an odd-weight Hodge structure back to the abstract complexification recovers
the Weil operator, since both are complex-linear and agree on the integral vectors. -/
@[simp]
theorem latticeComplexification_realificationAlmostComplexStructure
    (hs : HodgeStructure hℂ n) (hn : Odd n) :
    (hs.realificationAlmostComplexStructure hn).latticeComplexification hℂ = hs.weilOperator := by
  refine hℂ.algHom_ext _ _ fun v ↦ ?_
  rw [← realificationComplexEquiv_one_tmul_realificationMap hℂ v,
    AlmostComplexStructure.latticeComplexification_realificationComplexEquiv_one_tmul,
    realificationComplexEquiv_one_tmul_realificationAlmostComplexStructure]

/-- **The Hodge structure of the complex structure of an effective weight-one integral Hodge
structure is the structure itself.** An effective weight-one filtration has a single nontrivial
step, `F¹ = H^{1,0}`, and that is the `i`-eigenspace of the Weil operator. -/
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

end Lattice

end HodgeStructureOn

end TauCeti.Hodge

namespace TauCeti.AlmostComplexStructure

open scoped TensorProduct

universe u v

/-- **The complex structure of the Hodge structure of `J` is `J`.** The Weil operator of the
weight-one Hodge structure of `J` is the complexification of `J`, which acts on real vectors by
`J`. -/
@[simp]
theorem almostComplexStructure_hodgeStructure {W : Type u} [AddCommGroup W] [Module ℝ W]
    (J : AlmostComplexStructure W) : J.hodgeStructure.almostComplexStructure odd_one = J := by
  ext w
  apply (Hodge.complexificationRealPointsEquiv W).injective
  apply Subtype.ext
  simp only [Hodge.coe_complexificationRealPointsEquiv_apply,
    Hodge.HodgeStructureOn.one_tmul_almostComplexStructure, hodgeStructure_weilOperator,
    LinearMap.baseChange_tmul]

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

/-- **The complex structure of the integral Hodge structure of `J` is `J`.** The Weil operator of
the weight-one Hodge structure of `J` is the transported complexification of `J`, which acts on
real vectors by `J`. -/
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

open scoped TensorProduct

universe u v

/-! ### The equivalences -/

section Real

variable (W : Type u) [AddCommGroup W] [Module ℝ W]

/-- **Effective weight-one Hodge structures on the complexification of a real vector space are the
complex structures on it.** An effective weight-one Hodge structure is sent to the restriction of
its Weil operator to real vectors; a complex structure `J` is sent to the Hodge structure with `F¹`
the `i`-eigenspace of the complexification of `J`. -/
noncomputable def effectiveWeightOneEquiv :
    {hs : HodgeStructureOn (ℂ ⊗[ℝ] W) (complexificationConjugation W) 1 // hs.IsEffective} ≃
      AlmostComplexStructure W where
  toFun hs := hs.1.almostComplexStructure odd_one
  invFun J := ⟨J.hodgeStructure, J.isEffective_hodgeStructure⟩
  left_inv hs := Subtype.ext (HodgeStructureOn.hodgeStructure_almostComplexStructure hs.1 hs.2)
  right_inv J := J.almostComplexStructure_hodgeStructure

/-- The equivalence sends an effective weight-one Hodge structure to its complex structure. -/
@[simp]
theorem effectiveWeightOneEquiv_apply
    (hs : {hs : HodgeStructureOn (ℂ ⊗[ℝ] W) (complexificationConjugation W) 1 // hs.IsEffective}) :
    effectiveWeightOneEquiv W hs = hs.1.almostComplexStructure odd_one :=
  (rfl)

/-- The inverse equivalence sends a complex structure to its weight-one Hodge structure. -/
@[simp]
theorem coe_effectiveWeightOneEquiv_symm_apply (J : AlmostComplexStructure W) :
    ((effectiveWeightOneEquiv W).symm J :
      HodgeStructureOn (ℂ ⊗[ℝ] W) (complexificationConjugation W) 1) = J.hodgeStructure :=
  (rfl)

end Real

section Lattice

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

/-- **Effective weight-one Hodge structures on a lattice are the complex structures on its
realification.** An effective weight-one Hodge structure is sent to the restriction of its Weil
operator to real vectors; a complex structure `J` is sent to the Hodge structure with `F¹` the
`i`-eigenspace of the complexification of `J`. -/
noncomputable def latticeEffectiveWeightOneEquiv (hℂ : IsBaseChange ℂ ιℂ) :
    {hs : HodgeStructure hℂ 1 // hs.IsEffective} ≃ AlmostComplexStructure (Realification V) where
  toFun hs := hs.1.realificationAlmostComplexStructure odd_one
  invFun J := ⟨J.latticeHodgeStructure hℂ, J.isEffective_latticeHodgeStructure hℂ⟩
  left_inv hs := Subtype.ext
    (HodgeStructureOn.latticeHodgeStructure_realificationAlmostComplexStructure hs.1 hs.2)
  right_inv J := J.realificationAlmostComplexStructure_latticeHodgeStructure hℂ

/-- The equivalence sends an effective weight-one integral Hodge structure to its complex
structure on the realification. -/
@[simp]
theorem latticeEffectiveWeightOneEquiv_apply (hℂ : IsBaseChange ℂ ιℂ)
    (hs : {hs : HodgeStructure hℂ 1 // hs.IsEffective}) :
    latticeEffectiveWeightOneEquiv hℂ hs = hs.1.realificationAlmostComplexStructure odd_one :=
  (rfl)

/-- The inverse equivalence sends a complex structure on the realification to its weight-one
integral Hodge structure. -/
@[simp]
theorem coe_latticeEffectiveWeightOneEquiv_symm_apply (hℂ : IsBaseChange ℂ ιℂ)
    (J : AlmostComplexStructure (Realification V)) :
    ((latticeEffectiveWeightOneEquiv hℂ).symm J : HodgeStructure hℂ 1) =
      J.latticeHodgeStructure hℂ :=
  (rfl)

end Lattice

end TauCeti.Hodge
