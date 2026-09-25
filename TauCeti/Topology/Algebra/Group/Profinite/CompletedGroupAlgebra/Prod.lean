/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Map

/-!
# The completed group algebra of a product with a finite group

For a finite discrete group `C` and a topological group `Γ`, the completed group algebra of the
product `C × Γ` is the group algebra of `C` over the completed group algebra of `Γ`:

```text
R[[C × Γ]] ≅ R[[Γ]][C].
```

The map `R[[Γ]][C] → R[[C × Γ]]` sends the monomial `x · c` to `x · (c, 1)`, where `x ∈ R[[Γ]]`
is pushed into `R[[C × Γ]]` along the inclusion `γ ↦ (1, γ)` of the second factor and `(c, 1)` is
a group element (`TauCeti.completedGroupAlgebra.monoidAlgebraProdHom`, which is an `R`-algebra
homomorphism because these two kinds of elements commute). At the level `{1} × U` of `R[[C × Γ]]`,
for an open normal subgroup `U` of `Γ`, it reads the coefficient at the class of `(c, γ)` off the
coefficient at the class of `γ` of the level `U` of the coefficient at `c`
(`coeff_proj_monoidAlgebraProdHom`); this makes it injective for every discrete `C` and every
`Γ`. When `C`
is finite, `Γ` is compact with separately continuous multiplication, and the coefficient ring is a
compact Hausdorff topological ring, it is also surjective: its image is a compact, hence closed,
subspace containing the group elements, whose span is dense. The resulting isomorphism is
`TauCeti.completedGroupAlgebra.monoidAlgebraProdEquiv`.

For `R = ℤ_p` and `Γ ≅ ℤ_p` this identifies `ℤ_p[[C × ℤ_p]]` with `ℤ_p[[ℤ_p]][C]`, and through the
power-series coordinate of the Iwasawa algebra with `ℤ_p⟦X⟧[C]`; it is the first step in writing
the completed group algebra of the orientation image `{±1} × (1 + 2^f ℤ₂)` of a dyadic Demushkin
group as a power-series ring over the group ring `ℤ₂[C₂]`, the coefficient ring of Labute's
treatment of the even-rank case with `q = 2`.

## Main definitions

* `TauCeti.completedGroupAlgebra.monoidAlgebraProdHom R C Γ`: the `R`-algebra homomorphism
  `R[[Γ]][C] →ₐ[R] R[[C × Γ]]`.
* `TauCeti.completedGroupAlgebra.monoidAlgebraProdEquiv R C Γ`: the isomorphism
  `R[[Γ]][C] ≃ₐ[R] R[[C × Γ]]` for finite `C`, compact `Γ` and compact Hausdorff `R`.

## Main results

* `TauCeti.completedGroupAlgebra.monoidAlgebraProdHom_single_of`: the monomial `γ · c` goes to the
  group element `(c, γ)`.
* `TauCeti.completedGroupAlgebra.coeff_proj_monoidAlgebraProdHom`: the levelwise description at
  the level `{1} × U`.
* `TauCeti.completedGroupAlgebra.monoidAlgebraProdHom_injective`,
  `TauCeti.completedGroupAlgebra.monoidAlgebraProdHom_surjective`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), Section 4.
-/

public section

namespace TauCeti

open Topology

universe u v w

variable (R : Type u) [CommRing R] (C : Type v) [Group C] [TopologicalSpace C]
  (Γ : Type w) [Group Γ] [TopologicalSpace Γ]

namespace completedGroupAlgebra

/-- The inclusion of the second factor `γ ↦ (1, γ)` is continuous. -/
theorem continuous_inr : Continuous (MonoidHom.inr C Γ) :=
  continuous_const.prodMk continuous_id

variable {C Γ}

/-- The elements of `R[[C × Γ]]` coming from `R[[Γ]]` along `γ ↦ (1, γ)` commute with the group
elements `(c, 1)` of the first factor. -/
theorem commute_map_inr_of_inl (x : completedGroupAlgebra R Γ) (c : C) :
    Commute (map R (MonoidHom.inr C Γ) (continuous_inr C Γ) x)
      (of R (C × Γ) (MonoidHom.inl C Γ c)) := by
  refine ext fun W ↦ ?_
  rw [map_mul, map_mul, proj_map, proj_of]
  refine MonoidAlgebra.mapDomain_commute_single (fun q ↦ ?_) (fun s ↦ Commute.all _ _) _
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
  rw [QuotientGroup.map_mk, MonoidHom.inr_apply, MonoidHom.inl_apply]
  exact Commute.map (by simp [Commute, SemiconjBy] : Commute ((1 : C), γ) (c, (1 : Γ)))
    (QuotientGroup.mk' _)

variable (C Γ)

/-- The `R`-algebra homomorphism `R[[Γ]][C] →ₐ[R] R[[C × Γ]]` sending the monomial `x · c` to the
product of the image of `x` along `γ ↦ (1, γ)` with the group element `(c, 1)`. It sends `γ · c`
to the group element `(c, γ)` (`monoidAlgebraProdHom_single_of`), is injective
(`monoidAlgebraProdHom_injective`), and is an isomorphism for finite `C`
(`monoidAlgebraProdEquiv`). -/
noncomputable def monoidAlgebraProdHom :
    MonoidAlgebra (completedGroupAlgebra R Γ) C →ₐ[R] completedGroupAlgebra R (C × Γ) :=
  MonoidAlgebra.liftNCAlgHom (map R (MonoidHom.inr C Γ) (continuous_inr C Γ))
    ((of R (C × Γ)).comp (MonoidHom.inl C Γ)) (commute_map_inr_of_inl R)

/-- On the monomial `x · c`, the map `R[[Γ]][C] → R[[C × Γ]]` is the image of `x` along
`γ ↦ (1, γ)` times the group element `(c, 1)`. -/
theorem monoidAlgebraProdHom_single (c : C) (x : completedGroupAlgebra R Γ) :
    monoidAlgebraProdHom R C Γ (MonoidAlgebra.single c x) =
      map R (MonoidHom.inr C Γ) (continuous_inr C Γ) x * of R (C × Γ) (c, 1) := by
  simp only [monoidAlgebraProdHom, MonoidAlgebra.coe_liftNCAlgHom, MonoidAlgebra.liftNC_single,
    MonoidHom.comp_apply, MonoidHom.inl_apply, AddMonoidHom.coe_coe]

/-- The monomial `γ · c` goes to the group element `(c, γ)`. -/
@[simp]
theorem monoidAlgebraProdHom_single_of (c : C) (γ : Γ) :
    monoidAlgebraProdHom R C Γ (MonoidAlgebra.single c (of R Γ γ)) = of R (C × Γ) (c, γ) := by
  rw [monoidAlgebraProdHom_single, map_of, MonoidHom.inr_apply, ← map_mul, Prod.mk_mul_mk, one_mul,
    mul_one]

/-- The monomial `x · 1` goes to the image of `x` along `γ ↦ (1, γ)`. -/
@[simp]
theorem monoidAlgebraProdHom_single_one (x : completedGroupAlgebra R Γ) :
    monoidAlgebraProdHom R C Γ (MonoidAlgebra.single 1 x) =
      map R (MonoidHom.inr C Γ) (continuous_inr C Γ) x := by
  rw [monoidAlgebraProdHom_single, ← Prod.one_eq_mk, map_one, mul_one]

variable {C Γ} [DiscreteTopology C]

/-- The level `{1} × U` of `R[[C × Γ]]` reads the level `U` of the coefficients: the coefficient at
the class of `(c, γ)` of the image of `f` is the coefficient at the class of `γ` of the level `U`
of the coefficient of `f` at `c`. -/
theorem coeff_proj_monoidAlgebraProdHom (f : MonoidAlgebra (completedGroupAlgebra R Γ) C)
    (U : OpenNormalSubgroup Γ) (c : C) (γ : Γ) :
    (proj R (C × Γ) ((openNormalSubgroupBot C).prod U) (monoidAlgebraProdHom R C Γ f)).coeff
        ((c, γ) : (C × Γ) ⧸ ((openNormalSubgroupBot C).prod U).toSubgroup) =
      (proj R Γ U (f.coeff c)).coeff (γ : Γ ⧸ U.toSubgroup) := by
  classical
  -- Membership in the level `{1} × U`, and the inclusion of the second factor into it.
  have hmem : ∀ x : C × Γ, x ∈ ((openNormalSubgroupBot C).prod U).toSubgroup ↔
      x.1 = 1 ∧ x.2 ∈ U.toSubgroup := fun x ↦ by
    rw [OpenNormalSubgroup.toSubgroup_prod, Subgroup.mem_prod, openNormalSubgroupBot_toSubgroup,
      Subgroup.mem_bot]
  have hle : U.toSubgroup ≤
      ((openNormalSubgroupBot C).prod U).toSubgroup.comap (MonoidHom.inr C Γ) :=
    fun γ hγ ↦ by rw [Subgroup.mem_comap, hmem]; exact ⟨rfl, hγ⟩
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]
  | single c' x =>
    rw [monoidAlgebraProdHom_single, map_mul, proj_of, MonoidAlgebra.coeff_mul_single_apply,
      mul_one, proj_map_of_le R _ _ U _ hle, MonoidAlgebra.coeff_mapDomain, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, Prod.inv_mk, Prod.mk_mul_mk, inv_one, mul_one,
      MonoidAlgebra.coeff_single]
    by_cases hc : c' = c
    · subst hc
      rw [Finsupp.single_eq_same, mul_inv_cancel, ← MonoidHom.inr_apply (M := C) γ,
        ← QuotientGroup.map_mk _ _ _ hle, Finsupp.mapDomain_apply]
      intro a b hab
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      rw [QuotientGroup.map_mk, QuotientGroup.map_mk, QuotientGroup.eq, MonoidHom.inr_apply,
        MonoidHom.inr_apply, Prod.inv_mk, Prod.mk_mul_mk, hmem] at hab
      exact QuotientGroup.eq.mpr hab.2
    · rw [Finsupp.single_eq_of_ne (Ne.symm hc), map_zero, MonoidAlgebra.coeff_zero,
        Finsupp.zero_apply, Finsupp.mapDomain_of_notMem_range]
      rintro ⟨q, hq⟩
      obtain ⟨δ, rfl⟩ := QuotientGroup.mk_surjective q
      rw [QuotientGroup.map_mk, QuotientGroup.eq, MonoidHom.inr_apply, Prod.inv_mk, Prod.mk_mul_mk,
        hmem, inv_one, one_mul, mul_inv_eq_one] at hq
      exact hc hq.1.symm

/-- The map `R[[Γ]][C] → R[[C × Γ]]` is injective, for every group `C` with the discrete topology
and every topological group `Γ`. -/
theorem monoidAlgebraProdHom_injective : Function.Injective (monoidAlgebraProdHom R C Γ) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦ MonoidAlgebra.coeff_injective
    (Finsupp.ext fun c ↦ ext fun U ↦ MonoidAlgebra.coeff_injective (Finsupp.ext fun q ↦ ?_))
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
  rw [← coeff_proj_monoidAlgebraProdHom, hf]
  simp

section Surjective

variable [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [CompactSpace R]
  [CompactSpace Γ] [SeparatelyContinuousMul Γ] [Finite C]

/-- The map `R[[Γ]][C] → R[[C × Γ]]` is surjective when `C` is finite, `Γ` is compact with
separately continuous multiplication, and the coefficient ring is a compact Hausdorff topological
ring: its range is compact, hence closed, and contains the group elements, whose span is dense. -/
theorem monoidAlgebraProdHom_surjective : Function.Surjective (monoidAlgebraProdHom R C Γ) := by
  classical
  let _ := Fintype.ofFinite C
  -- The map, read on `C → R[[Γ]]`, is a finite sum of continuous maps.
  let Φ : (C → completedGroupAlgebra R Γ) → completedGroupAlgebra R (C × Γ) := fun x ↦
    ∑ c, map R (MonoidHom.inr C Γ) (continuous_inr C Γ) (x c) * of R (C × Γ) (c, 1)
  have hΦ : ∀ x, Φ x = monoidAlgebraProdHom R C Γ
      (MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm x)) := fun x ↦ by
    simp only [Φ, Finsupp.equivFunOnFinite_symm_eq_sum, MonoidAlgebra.ofCoeff_sum,
      MonoidAlgebra.ofCoeff_single, map_sum, monoidAlgebraProdHom_single]
  have hcont : Continuous Φ := continuous_finsetSum _ fun c _ ↦
    ((continuous_map R _ _).comp (continuous_apply c)).mul continuous_const
  have hrange : Set.range (monoidAlgebraProdHom R C Γ) = Set.range Φ := by
    ext y
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨Finsupp.equivFunOnFinite f.coeff, by rw [hΦ]; simp⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, (hΦ x).symm⟩
  have hclosed : IsClosed (Set.range (monoidAlgebraProdHom R C Γ)) := by
    rw [hrange]
    exact (isCompact_range hcont).isClosed
  -- The closed range contains the dense span of the group elements.
  have hspan : (Submodule.span R (Set.range (of R (C × Γ))) : Set (completedGroupAlgebra R (C × Γ)))
      ⊆ Set.range (monoidAlgebraProdHom R C Γ) := by
    have hle : Submodule.span R (Set.range (of R (C × Γ))) ≤
        Subalgebra.toSubmodule (monoidAlgebraProdHom R C Γ).range := by
      rw [Submodule.span_le]
      rintro _ ⟨⟨c, γ⟩, rfl⟩
      exact (Subalgebra.mem_toSubmodule _).mpr ((AlgHom.mem_range _).mpr
        ⟨MonoidAlgebra.single c (of R Γ γ), monoidAlgebraProdHom_single_of R C Γ c γ⟩)
    exact fun y hy ↦ (AlgHom.mem_range _).mp ((Subalgebra.mem_toSubmodule _).mp (hle hy))
  intro y
  have hy : y ∈ closure (Submodule.span R (Set.range (of R (C × Γ))) :
      Set (completedGroupAlgebra R (C × Γ))) := by
    rw [(dense_span_range_of R (C × Γ)).closure_eq]; trivial
  exact closure_minimal hspan hclosed hy

variable (C Γ)

/-- **The completed group algebra of a product with a finite group.** For a finite discrete group
`C`, a compact group `Γ` with separately continuous multiplication and a compact Hausdorff
topological coefficient ring `R`, the group algebra of `C` over `R[[Γ]]` is the completed group
algebra of `C × Γ`: the monomial `γ · c` corresponds to the group element `(c, γ)`. -/
noncomputable def monoidAlgebraProdEquiv :
    MonoidAlgebra (completedGroupAlgebra R Γ) C ≃ₐ[R] completedGroupAlgebra R (C × Γ) :=
  AlgEquiv.ofBijective (monoidAlgebraProdHom R C Γ)
    ⟨monoidAlgebraProdHom_injective R, monoidAlgebraProdHom_surjective R⟩

@[simp]
theorem coe_monoidAlgebraProdEquiv :
    ⇑(monoidAlgebraProdEquiv R C Γ) = monoidAlgebraProdHom R C Γ :=
  (rfl)

/-- The inverse of `monoidAlgebraProdEquiv` sends the group element `(c, γ)` to the monomial
`γ · c`. -/
@[simp]
theorem monoidAlgebraProdEquiv_symm_of (c : C) (γ : Γ) :
    (monoidAlgebraProdEquiv R C Γ).symm (of R (C × Γ) (c, γ)) =
      MonoidAlgebra.single c (of R Γ γ) :=
  (monoidAlgebraProdEquiv R C Γ).symm_apply_eq.mpr (monoidAlgebraProdHom_single_of R C Γ c γ).symm

end Surjective

end completedGroupAlgebra

end TauCeti
