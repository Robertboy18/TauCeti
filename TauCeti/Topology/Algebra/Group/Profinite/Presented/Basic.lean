/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Basic
public import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# Presented profinite groups

The profinite group **presented** by generators `X` and relators `rels ⊆ freeProfiniteGroup X` is
the free profinite group on `X` modulo the *closed* normal closure of `rels`. Closedness is what
keeps the quotient profinite: the algebraic normal closure of a set of relators need not be
closed, and the quotient by a non-closed subgroup is not even Hausdorff.

The presented profinite group is pinned down by its universal property: a map from `X` to a
profinite group `P` under which every relator becomes trivial extends uniquely to a continuous
homomorphism from `presentedProfiniteGroup X rels`. As for the free profinite group, uniqueness
only needs a Hausdorff target, in any universe, while existence needs `P` profinite in the
universe of `X`.

The pro-`p` version, which quotients the free pro-`p` group instead, is
`TauCeti.presentedProP` in `TauCeti.Topology.Algebra.Group.Profinite.Presented.ProP`.

## Main definitions

* `TauCeti.presentedProfiniteGroup X rels`: the presented profinite group.
* `TauCeti.presentedProfiniteGroup.mk`: the canonical continuous projection from the free
  profinite group.
* `TauCeti.presentedProfiniteGroup.of`: the canonical generators.
* `TauCeti.presentedProfiniteGroup.lift`: the continuous homomorphism induced by a map on the
  generators that kills the relators.

## Main results

* `TauCeti.presentedProfiniteGroup.dense_closure_range_of`: the generators generate topologically.
* `TauCeti.presentedProfiniteGroup.hom_ext`: continuous homomorphisms agreeing on the generators
  are equal.
* `TauCeti.presentedProfiniteGroup.existsUnique_lift`: the universal property.
* `TauCeti.presentedProfiniteGroup.lift_surjective`: a topologically generating map lifts to a
  surjection.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 3.3.
-/

public section

namespace TauCeti

universe u v

/-- The profinite group **presented** by generators `X` and relators `rels`: the free profinite
group on `X` modulo the closed normal closure of `rels`. -/
noncomputable abbrev presentedProfiniteGroup (X : Type u) (rels : Set (freeProfiniteGroup X)) :
    Type u :=
  freeProfiniteGroup X ⧸ (Subgroup.normalClosure rels).topologicalClosure

namespace presentedProfiniteGroup

variable {X : Type u} (rels : Set (freeProfiniteGroup X))

/-- The canonical continuous projection from the free profinite group onto the profinite group it
presents. -/
noncomputable def mk : freeProfiniteGroup X →ₜ* presentedProfiniteGroup X rels :=
  ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩

/-- The canonical projection sends an element to its class. -/
@[simp low]
theorem mk_apply (x : freeProfiniteGroup X) : mk rels x = (x : presentedProfiniteGroup X rels) :=
  (rfl)

/-- The canonical projection onto the presented profinite group is surjective. -/
theorem mk_surjective : Function.Surjective (mk rels) :=
  QuotientGroup.mk'_surjective _

/-- The kernel of the canonical projection is the closed normal closure of the relators. -/
theorem ker_mk : (mk rels).toMonoidHom.ker = (Subgroup.normalClosure rels).topologicalClosure :=
  QuotientGroup.ker_mk' _

/-- An element of the free profinite group dies in the presented profinite group exactly when it
lies in the closed normal closure of the relators. -/
theorem mk_eq_one_iff {x : freeProfiniteGroup X} :
    mk rels x = 1 ↔ x ∈ (Subgroup.normalClosure rels).topologicalClosure :=
  QuotientGroup.eq_one_iff x

/-- Every relator dies in the presented profinite group. -/
theorem mk_eq_one_of_mem {r : freeProfiniteGroup X} (hr : r ∈ rels) : mk rels r = 1 :=
  (mk_eq_one_iff rels).mpr <|
    (Subgroup.normalClosure rels).le_topologicalClosure (Subgroup.subset_normalClosure hr)

variable {rels}

/-- The canonical generators of the presented profinite group: the classes of the generators of
the free profinite group. -/
noncomputable def of (x : X) : presentedProfiniteGroup X rels :=
  mk rels (freeProfiniteGroup.of x)

/-- The canonical projection sends a free generator to the corresponding generator of the
presented profinite group. -/
@[simp]
theorem mk_of (x : X) : mk rels (freeProfiniteGroup.of x) = of x :=
  (rfl)

/-- The generators generate the presented profinite group topologically. -/
theorem dense_closure_range_of :
    Dense ((Subgroup.closure (Set.range (of : X → presentedProfiniteGroup X rels)) :
      Subgroup (presentedProfiniteGroup X rels)) : Set (presentedProfiniteGroup X rels)) := by
  have h : Set.range (of : X → presentedProfiniteGroup X rels) =
      mk rels '' Set.range (freeProfiniteGroup.of : X → freeProfiniteGroup X) := by
    rw [← Set.range_comp]
    rfl
  have hmap : Subgroup.closure
      (mk rels '' Set.range (freeProfiniteGroup.of : X → freeProfiniteGroup X)) =
        (Subgroup.closure (Set.range (freeProfiniteGroup.of : X → freeProfiniteGroup X))).map
          (mk rels).toMonoidHom :=
    (MonoidHom.map_closure _ _).symm
  rw [h, hmap, Subgroup.coe_map]
  exact (mk_surjective rels).denseRange.dense_image (map_continuous (mk rels))
    (freeProfiniteGroup.dense_closure_range_of X)

section HomExt

variable {Q : Type v} [Group Q] [TopologicalSpace Q] [T2Space Q]

/-- Two continuous homomorphisms out of a presented profinite group that agree on the generators
are equal. The target need only be a Hausdorff topological space carrying a group structure. -/
@[ext]
theorem hom_ext {φ ψ : presentedProfiniteGroup X rels →ₜ* Q} (h : ∀ x : X, φ (of x) = ψ (of x)) :
    φ = ψ := by
  have hcomp : φ.comp (mk rels) = ψ.comp (mk rels) :=
    freeProfiniteGroup.hom_ext fun x ↦ by simpa using h x
  refine ContinuousMonoidHom.ext fun y ↦ ?_
  obtain ⟨x, rfl⟩ := mk_surjective rels y
  exact DFunLike.congr_fun hcomp x

end HomExt

section Lift

variable {P : Type u} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [TotallyDisconnectedSpace P]

/-- The closed normal closure of the relators lies in the kernel of the free profinite lift of a
map that kills every relator. -/
theorem topologicalClosure_normalClosure_le_ker_lift (f : X → P)
    (h : ∀ r ∈ rels, freeProfiniteGroup.lift f r = 1) :
    (Subgroup.normalClosure rels).topologicalClosure ≤
      (freeProfiniteGroup.lift f).toMonoidHom.ker :=
  Subgroup.topologicalClosure_normalClosure_le_ker (map_continuous (freeProfiniteGroup.lift f)) h

/-- The continuous homomorphism to a profinite group `P` induced by a map `f : X → P` on the
generators under which every relator becomes trivial. -/
noncomputable def lift (f : X → P) (h : ∀ r ∈ rels, freeProfiniteGroup.lift f r = 1) :
    presentedProfiniteGroup X rels →ₜ* P :=
  ⟨QuotientGroup.lift _ (freeProfiniteGroup.lift f).toMonoidHom
      (topologicalClosure_normalClosure_le_ker_lift f h),
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
      (map_continuous (freeProfiniteGroup.lift f))⟩

/-- The induced homomorphism computes on classes as the free profinite lift. -/
@[simp]
theorem lift_mk (f : X → P) (h : ∀ r ∈ rels, freeProfiniteGroup.lift f r = 1)
    (x : freeProfiniteGroup X) : lift f h (mk rels x) = freeProfiniteGroup.lift f x :=
  QuotientGroup.lift_mk' _ (topologicalClosure_normalClosure_le_ker_lift f h) x

/-- The induced homomorphism agrees with `f` on each generator. -/
@[simp]
theorem lift_of (f : X → P) (h : ∀ r ∈ rels, freeProfiniteGroup.lift f r = 1) (x : X) :
    lift f h (of x) = f x := by
  rw [of, lift_mk, freeProfiniteGroup.lift_of]

/-- The induced homomorphism recovers the free profinite lift along the canonical projection. -/
@[simp]
theorem lift_comp_mk (f : X → P) (h : ∀ r ∈ rels, freeProfiniteGroup.lift f r = 1) :
    (lift f h).comp (mk rels) = freeProfiniteGroup.lift f :=
  freeProfiniteGroup.hom_ext fun x ↦ by simp

/-- A continuous homomorphism restricting to `f` on the generators is the induced
homomorphism. -/
theorem lift_unique (f : X → P) (h : ∀ r ∈ rels, freeProfiniteGroup.lift f r = 1)
    (φ : presentedProfiniteGroup X rels →ₜ* P) (hφ : ∀ x : X, φ (of x) = f x) : φ = lift f h :=
  hom_ext fun x ↦ by rw [hφ, lift_of]

/-- **The universal property of the presented profinite group.** A map from `X` to a profinite
group under which every relator becomes trivial extends uniquely to a continuous homomorphism
from `presentedProfiniteGroup X rels`. -/
theorem existsUnique_lift (f : X → P) (h : ∀ r ∈ rels, freeProfiniteGroup.lift f r = 1) :
    ∃! φ : presentedProfiniteGroup X rels →ₜ* P, ∀ x : X, φ (of x) = f x :=
  ⟨lift f h, lift_of f h, fun φ hφ ↦ lift_unique f h φ hφ⟩

/-- The induced homomorphism is natural in the target. -/
@[simp]
theorem comp_lift {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [TotallyDisconnectedSpace Q] (g : P →ₜ* Q) (f : X → P)
    (h : ∀ r ∈ rels, freeProfiniteGroup.lift f r = 1) :
    g.comp (lift f h) = lift (⇑g ∘ f) fun r hr ↦ by
      rw [← freeProfiniteGroup.comp_lift, ContinuousMonoidHom.coe_comp, Function.comp_apply,
        h r hr, map_one] :=
  hom_ext fun x ↦ by simp

/-- A map whose range generates the target topologically induces a surjection. -/
theorem lift_surjective {f : X → P} (h : ∀ r ∈ rels, freeProfiniteGroup.lift f r = 1)
    (hf : Dense ((Subgroup.closure (Set.range f) : Subgroup P) : Set P)) :
    Function.Surjective (lift f h) := by
  have hcomp : ⇑(freeProfiniteGroup.lift f) = lift f h ∘ mk rels :=
    funext fun x ↦ (lift_mk f h x).symm
  exact Function.Surjective.of_comp (hcomp ▸ freeProfiniteGroup.lift_surjective hf)

end Lift

end presentedProfiniteGroup

end TauCeti
