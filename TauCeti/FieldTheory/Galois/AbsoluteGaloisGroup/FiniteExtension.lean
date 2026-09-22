/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic

/-!
# The absolute Galois group of a finite separable extension as an open subgroup

Let `L/K` be a finite separable extension and `σ : L →ₐ[K] Kˢ` a `K`-embedding of `L` into a
separable closure `Kˢ` of `K`. The automorphisms of `Kˢ` that fix `σ(L)` pointwise form an open
subgroup

```text
galoisSubgroup K L σ ≤ G_K = AbsoluteGaloisGroup K
```

of index `[L : K]`, and it is the absolute Galois group of `L`: through `σ`, the field `Kˢ` is a
separable closure of `L` as well, so a chosen identification `Lˢ ≃ Kˢ` over `L` carries the
automorphisms of `Lˢ` over `L` onto the automorphisms of `Kˢ` over `σ(L)`. This file constructs
that identification and proves that it is an isomorphism of **topological** groups
`G_L ≃ₜ* galoisSubgroup K L σ` for the Krull topologies, which is what continuous cohomology
depends on.

The embedding is genuine data. Without one there is no homomorphism `G_L → G_K` at all, and two
embeddings cut out conjugate subgroups. Restriction, corestriction and the other subgroup-indexed
operations of Galois cohomology along `L/K` are the operations at `galoisSubgroup K L σ`, read
through `galoisSubgroupEquiv K L σ`, and their independence of `σ` is a statement about those
operations rather than about the subgroup. The index formula is what discharges the finite-index
and index-two hypotheses those operations carry.

Only the openness of the subgroup uses finiteness of `L/K`: the identification of separable
closures and the isomorphism of Galois groups make sense for any separable `L/K`, and are stated
here for a finite one because the open subgroup is the object the cohomological operations are
indexed by. Separability of `L/K` is a consequence of the existence of `σ` and is not assumed.

## Main definitions

* `TauCeti.galoisSubgroup K L σ`: the open subgroup of `G_K` fixing `σ(L)` pointwise.
* `TauCeti.separableClosureRingEquiv K L σ`: a chosen ring isomorphism `Lˢ ≃+* Kˢ` extending `σ`.
* `TauCeti.galoisSubgroupEquiv K L σ`: the isomorphism of topological groups
  `G_L ≃ₜ* galoisSubgroup K L σ` obtained by transport along that identification.

## Main results

* `TauCeti.isSepClosure_tower_top`: a separable closure of `K` is a separable closure of every
  intermediate extension.
* `TauCeti.galoisSubgroup_index`: the index of `galoisSubgroup K L σ` in `G_K` is `[L : K]`.
* `TauCeti.galoisSubgroupEquiv_apply_separableClosureRingEquiv`: the isomorphism intertwines the
  actions of `G_L` on `Lˢ` and of `G_K` on `Kˢ` through `separableClosureRingEquiv K L σ`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I §5 for
  restriction and corestriction along a finite extension, and Ch. VI §1 for the absolute Galois
  group at the separable closure.
-/

public section

noncomputable section

namespace TauCeti

open IntermediateField

variable (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K)

/-! ### The identification of separable closures -/

/-- **A separable closure of `K` is a separable closure of every intermediate extension `L`**:
separable closedness is a property of the field alone, and separability over `K` implies
separability over `L`. -/
theorem isSepClosure_tower_top (E : Type*) [Field E] [Algebra K E] [Algebra L E]
    [IsScalarTower K L E] [IsSepClosure K E] : IsSepClosure L E :=
  ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K L E⟩

/-- **A chosen identification `Lˢ ≃+* Kˢ` extending `σ`.** Any two separable closures of `L` are
`L`-isomorphic, and `Kˢ` is one of them through `σ`; the `L`-linearity of the chosen isomorphism is
recorded by `separableClosureRingEquiv_algebraMap`. It is a ring isomorphism rather than an
`L`-algebra isomorphism because the `L`-algebra structure of `Kˢ` is not an instance. -/
def separableClosureRingEquiv : SeparableClosure L ≃+* SeparableClosure K :=
  letI : Algebra L (SeparableClosure K) := σ.toRingHom.toAlgebra
  haveI : IsScalarTower K L (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (σ.commutes x).symm
  haveI : IsSepClosure L (SeparableClosure K) := isSepClosure_tower_top K L _
  (IsSepClosure.equiv L (SeparableClosure L) (SeparableClosure K)).toRingEquiv

/-- The identification of separable closures restricts to `σ` on `L`. -/
@[simp]
theorem separableClosureRingEquiv_algebraMap (x : L) :
    separableClosureRingEquiv K L σ (algebraMap L (SeparableClosure L) x) = σ x :=
  letI : Algebra L (SeparableClosure K) := σ.toRingHom.toAlgebra
  haveI : IsScalarTower K L (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (σ.commutes x).symm
  haveI : IsSepClosure L (SeparableClosure K) := isSepClosure_tower_top K L _
  (IsSepClosure.equiv L (SeparableClosure L) (SeparableClosure K)).commutes x

/-- The inverse identification sends `σ x` back to `x`. -/
@[simp]
theorem separableClosureRingEquiv_symm_apply_algHom (x : L) :
    (separableClosureRingEquiv K L σ).symm (σ x) = algebraMap L (SeparableClosure L) x := by
  rw [← separableClosureRingEquiv_algebraMap K L σ x, RingEquiv.symm_apply_apply]

/-- The identification of separable closures fixes the image of `K`. -/
@[simp]
theorem separableClosureRingEquiv_algebraMap_base (c : K) :
    separableClosureRingEquiv K L σ (algebraMap K (SeparableClosure L) c) =
      algebraMap K (SeparableClosure K) c := by
  rw [IsScalarTower.algebraMap_apply K L (SeparableClosure L), separableClosureRingEquiv_algebraMap,
    σ.commutes]

/-- The inverse identification fixes the image of `K`. -/
@[simp]
theorem separableClosureRingEquiv_symm_algebraMap_base (c : K) :
    (separableClosureRingEquiv K L σ).symm (algebraMap K (SeparableClosure K) c) =
      algebraMap K (SeparableClosure L) c := by
  rw [← separableClosureRingEquiv_algebraMap_base K L σ c, RingEquiv.symm_apply_apply]

/-! ### The open subgroup -/

variable [FiniteDimensional K L]

/-- **The open subgroup of `G_K` cut out by a `K`-embedding of `L` into `Kˢ`**: the automorphisms
of `Kˢ` fixing `σ(L)` pointwise. It is open because `L/K` is finite, and `galoisSubgroupEquiv`
identifies it with the absolute Galois group of `L`. -/
def galoisSubgroup : OpenSubgroup (AbsoluteGaloisGroup K) where
  toSubgroup := σ.fieldRange.fixingSubgroup
  isOpen' :=
    haveI : FiniteDimensional K σ.fieldRange := σ.toLinearMap.finiteDimensional_range
    σ.fieldRange.fixingSubgroup_isOpen

/-- The subgroup underlying `galoisSubgroup K L σ` is the fixing subgroup of the image of `σ`. -/
theorem galoisSubgroup_toSubgroup :
    (galoisSubgroup K L σ).toSubgroup = σ.fieldRange.fixingSubgroup :=
  (rfl)

/-- An automorphism of `Kˢ` lies in `galoisSubgroup K L σ` exactly when it fixes `σ x` for every
`x : L`. -/
@[simp]
theorem mem_galoisSubgroup_iff {g : AbsoluteGaloisGroup K} :
    g ∈ galoisSubgroup K L σ ↔ ∀ x : L, g (σ x) = σ x := by
  rw [← OpenSubgroup.mem_toSubgroup, galoisSubgroup_toSubgroup,
    IntermediateField.mem_fixingSubgroup_iff]
  simp

/-- **The index of `galoisSubgroup K L σ` is the degree `[L : K]`.** -/
theorem galoisSubgroup_index : (galoisSubgroup K L σ).toSubgroup.index = Module.finrank K L := by
  rw [galoisSubgroup_toSubgroup, ← finrank_eq_fixingSubgroup_index]
  exact (AlgEquiv.ofInjectiveField σ).toLinearEquiv.finrank_eq.symm

/-- `galoisSubgroup K L σ` is all of `G_K` exactly when `L/K` is trivial, that is `[L : K] = 1`. -/
theorem galoisSubgroup_eq_top_iff : galoisSubgroup K L σ = ⊤ ↔ Module.finrank K L = 1 := by
  rw [← galoisSubgroup_index, Subgroup.index_eq_one, ← OpenSubgroup.toSubgroup_top,
    OpenSubgroup.toSubgroup_injective.eq_iff]

/-! ### The isomorphism with the absolute Galois group of `L` -/

/-- The underlying group isomorphism of `galoisSubgroupEquiv`: conjugate an automorphism of `Lˢ`
by the identification `separableClosureRingEquiv K L σ`.

It is named so that the structure field and the continuity proofs below refer to one and the same
term rather than to separately built copies identified by definitional unfolding. -/
private def galoisSubgroupMulEquiv :
    AbsoluteGaloisGroup L ≃* ↥(galoisSubgroup K L σ).toSubgroup where
  toFun g :=
    ⟨AlgEquiv.ofRingEquiv (R := K)
      (f := (separableClosureRingEquiv K L σ).symm.trans
        (g.toRingEquiv.trans (separableClosureRingEquiv K L σ)))
      fun c ↦ by
        simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
          separableClosureRingEquiv_symm_algebraMap_base]
        rw [IsScalarTower.algebraMap_apply K L (SeparableClosure L), AlgEquiv.commutes,
          ← IsScalarTower.algebraMap_apply, separableClosureRingEquiv_algebraMap_base], by
        rw [OpenSubgroup.mem_toSubgroup, mem_galoisSubgroup_iff]
        intro x
        simp⟩
  invFun h :=
    AlgEquiv.ofRingEquiv (R := L)
      (f := (separableClosureRingEquiv K L σ).trans
        ((h : AbsoluteGaloisGroup K).toRingEquiv.trans (separableClosureRingEquiv K L σ).symm))
      fun x ↦ by
        have hx := (mem_galoisSubgroup_iff K L σ).mp h.2 x
        simp [hx]
  left_inv g := by ext x; simp
  right_inv h := by ext x; simp
  map_mul' g g' := by ext x; simp

private theorem galoisSubgroupMulEquiv_apply (g : AbsoluteGaloisGroup L) (y : SeparableClosure K) :
    (galoisSubgroupMulEquiv K L σ g : AbsoluteGaloisGroup K) y =
      separableClosureRingEquiv K L σ (g ((separableClosureRingEquiv K L σ).symm y)) :=
  (rfl)

/-- The forward map of `galoisSubgroupMulEquiv` is continuous for the Krull topologies: an
automorphism of `Kˢ` fixing a finite subextension `M = K(t)` of `Kˢ` is the image of every
automorphism of `Lˢ` fixing the finite subextension `L(e⁻¹ t)`, where `e` is the identification of
separable closures. -/
private theorem continuous_galoisSubgroupMulEquiv :
    Continuous (galoisSubgroupMulEquiv K L σ) := by
  refine Continuous.subtype_mk (continuous_of_continuousAt_one
    ((galoisSubgroup K L σ).toSubgroup.subtype.comp (galoisSubgroupMulEquiv K L σ).toMonoidHom)
    (continuousAt_def.mpr fun N hN ↦ ?_)) _
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨M, hM, hMN⟩ := hN
  -- `M` is generated over `K` by a finite set `t`.
  have hfg : Algebra.EssFiniteType K M := inferInstance
  rw [essFiniteType_iff, fg_def] at hfg
  obtain ⟨t, ht, rfl⟩ := hfg
  rw [krullTopology_mem_nhds_one_iff]
  have := (ht.image (separableClosureRingEquiv K L σ).symm).to_subtype
  refine ⟨adjoin L ((separableClosureRingEquiv K L σ).symm '' t),
    finiteDimensional_adjoin fun y _ ↦ Algebra.IsIntegral.isIntegral y, fun g hg ↦ hMN ?_⟩
  -- The image of `g` fixes `t`, hence all of `K(t)`.
  have hfix : ∀ y ∈ t, (galoisSubgroupMulEquiv K L σ g : AbsoluteGaloisGroup K) y = y := by
    intro y hy
    have hgy : g ((separableClosureRingEquiv K L σ).symm y) =
        (separableClosureRingEquiv K L σ).symm y :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg _ (subset_adjoin L _ ⟨y, hy, rfl⟩)
    rw [galoisSubgroupMulEquiv_apply, hgy, RingEquiv.apply_symm_apply]
  refine (le_iff_le (K := adjoin K t)
    (H := fixingSubgroup (AbsoluteGaloisGroup K) t)).mp ?_ fun y ↦ ?_
  · exact adjoin_le_iff.mpr fun y hy ↦ (mem_fixedField_iff
      (H := fixingSubgroup (AbsoluteGaloisGroup K) t) y).mpr fun f hf ↦ hf ⟨y, hy⟩
  · exact hfix y y.2

/-- **The absolute Galois group of `L` is the open subgroup of `G_K` cut out by `σ`**, as
topological groups: conjugation by the identification `separableClosureRingEquiv K L σ` of separable
closures is an isomorphism `G_L ≃ₜ* galoisSubgroup K L σ` for the Krull topologies.

Continuity of the inverse comes for free: `G_L` is compact and the subgroup is Hausdorff. -/
def galoisSubgroupEquiv : AbsoluteGaloisGroup L ≃ₜ* ↥(galoisSubgroup K L σ).toSubgroup where
  __ := galoisSubgroupMulEquiv K L σ
  continuous_toFun := continuous_galoisSubgroupMulEquiv K L σ
  continuous_invFun :=
    (Continuous.homeoOfEquivCompactToT2 (f := (galoisSubgroupMulEquiv K L σ).toEquiv)
      (continuous_galoisSubgroupMulEquiv K L σ)).symm.continuous

/-- `galoisSubgroupEquiv K L σ` conjugates by the identification of separable closures. -/
theorem galoisSubgroupEquiv_apply (g : AbsoluteGaloisGroup L) (y : SeparableClosure K) :
    (galoisSubgroupEquiv K L σ g : AbsoluteGaloisGroup K) y =
      separableClosureRingEquiv K L σ (g ((separableClosureRingEquiv K L σ).symm y)) :=
  galoisSubgroupMulEquiv_apply K L σ g y

/-- **The isomorphism intertwines the Galois actions**: the image of `g : G_L` acts on
`e x ∈ Kˢ` as `g` acts on `x ∈ Lˢ`, where `e = separableClosureRingEquiv K L σ`. -/
@[simp]
theorem galoisSubgroupEquiv_apply_separableClosureRingEquiv (g : AbsoluteGaloisGroup L)
    (x : SeparableClosure L) :
    (galoisSubgroupEquiv K L σ g : AbsoluteGaloisGroup K) (separableClosureRingEquiv K L σ x) =
      separableClosureRingEquiv K L σ (g x) := by
  rw [galoisSubgroupEquiv_apply, RingEquiv.symm_apply_apply]

/-- The inverse of `galoisSubgroupEquiv K L σ` conjugates back by the identification of separable
closures. -/
theorem galoisSubgroupEquiv_symm_apply (h : ↥(galoisSubgroup K L σ).toSubgroup)
    (x : SeparableClosure L) :
    (galoisSubgroupEquiv K L σ).symm h x =
      (separableClosureRingEquiv K L σ).symm
        ((h : AbsoluteGaloisGroup K) (separableClosureRingEquiv K L σ x)) :=
  (rfl)

end TauCeti
