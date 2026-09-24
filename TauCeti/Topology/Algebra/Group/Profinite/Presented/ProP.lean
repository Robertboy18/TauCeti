/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
public import TauCeti.Topology.Algebra.Group.Profinite.Rank
public import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# Presented pro-`p` groups

The pro-`p` group **presented** by generators `X` and relators `rels ⊆ freeProP p X` is the free
pro-`p` group on `X` modulo the *closed* normal closure of `rels`. Closedness is what keeps the
quotient profinite: the algebraic normal closure of a set of relators need not be closed, and the
quotient by a non-closed subgroup is not even Hausdorff.

The presented pro-`p` group is pro-`p`, and it is pinned down by its universal property: a map
from `X` to a pro-`p` group `P` under which every relator becomes trivial extends uniquely to a
continuous homomorphism from `presentedProP p X rels`. As for the free pro-`p` group, uniqueness
only needs a Hausdorff target, in any universe, while existence needs `P` profinite pro-`p` in
the universe of `X`. With no relators the presented group is the free pro-`p` group.

Every Hausdorff group that is a continuous image of `freeProP p X` is presented on `X`, with the
kernel as its set of relators (`presentedProP.equivOfSurjective`). Consequently a topologically
finitely generated pro-`p` group `G` has a presentation on any finite type with at least
`topologicalGeneratorRankNat G` elements; a presentation on exactly that many generators is what
is called a **minimal presentation** of `G`.

## Main definitions

* `TauCeti.presentedProP p X rels`: the presented pro-`p` group.
* `TauCeti.presentedProP.mk`: the canonical continuous projection from the free pro-`p` group.
* `TauCeti.presentedProP.of`: the canonical generators.
* `TauCeti.presentedProP.lift`: the continuous homomorphism induced by a map on the generators
  that kills the relators.
* `TauCeti.presentedProP.equivFreeProP`: with no relators, the presented group is free.
* `TauCeti.presentedProP.equivOfSurjective`: a continuous image of `freeProP p X` is presented on
  `X` by the kernel.

## Main results

* `TauCeti.isProP_presentedProP`: a presented pro-`p` group is pro-`p`.
* `TauCeti.presentedProP.dense_closure_range_of`: the generators generate topologically.
* `TauCeti.presentedProP.hom_ext`: continuous homomorphisms agreeing on the generators are equal.
* `TauCeti.presentedProP.existsUnique_lift`: the universal property.
* `TauCeti.presentedProP.lift_surjective`: a topologically generating map lifts to a surjection.
* `TauCeti.isTopologicallyFinitelyGenerated_presentedProP`: a group presented on a finite type is
  topologically finitely generated.
* `TauCeti.IsProP.exists_surjective_freeProP`: a topologically finitely generated pro-`p` group is
  a continuous image of the free pro-`p` group on any finite type with at least
  `topologicalGeneratorRankNat` elements.
* `TauCeti.IsProP.exists_continuousMulEquiv_presentedProP`: hence it has a presentation on any
  such type.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 3.3 and 7.8.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, Section III.9.
-/

public section

namespace TauCeti

universe u v

/-- The pro-`p` group **presented** by generators `X` and relators `rels`: the free pro-`p` group
on `X` modulo the closed normal closure of `rels`. -/
noncomputable abbrev presentedProP (p : ℕ) (X : Type u) (rels : Set (freeProP p X)) : Type u :=
  freeProP p X ⧸ (Subgroup.normalClosure rels).topologicalClosure

/-- A presented pro-`p` group is pro-`p`. -/
theorem isProP_presentedProP (p : ℕ) (X : Type u) (rels : Set (freeProP p X)) :
    IsProP p (presentedProP p X rels) :=
  (isProP_freeProP p X).quotient _

namespace presentedProP

variable {p : ℕ} {X : Type u} (rels : Set (freeProP p X))

/-- The canonical continuous projection from the free pro-`p` group onto the pro-`p` group it
presents. -/
noncomputable def mk : freeProP p X →ₜ* presentedProP p X rels :=
  ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩

/-- The canonical projection sends an element to its class. Not a simp lemma: `mk rels x` is the
simp normal form of a class, so that `lift_mk` and its relatives fire. -/
theorem mk_apply (x : freeProP p X) : mk rels x = (x : presentedProP p X rels) :=
  (rfl)

/-- The canonical projection onto the presented pro-`p` group is surjective. -/
theorem mk_surjective : Function.Surjective (mk rels) :=
  QuotientGroup.mk'_surjective _

/-- The kernel of the canonical projection is the closed normal closure of the relators. -/
theorem ker_mk : (mk rels).toMonoidHom.ker = (Subgroup.normalClosure rels).topologicalClosure :=
  QuotientGroup.ker_mk' _

/-- An element of the free pro-`p` group dies in the presented pro-`p` group exactly when it lies
in the closed normal closure of the relators. -/
theorem mk_eq_one_iff {x : freeProP p X} :
    mk rels x = 1 ↔ x ∈ (Subgroup.normalClosure rels).topologicalClosure :=
  QuotientGroup.eq_one_iff x

/-- Every relator dies in the presented pro-`p` group. -/
theorem mk_eq_one_of_mem {r : freeProP p X} (hr : r ∈ rels) : mk rels r = 1 :=
  (mk_eq_one_iff rels).mpr <|
    (Subgroup.normalClosure rels).le_topologicalClosure (Subgroup.subset_normalClosure hr)

variable {rels}

/-- The canonical generators of the presented pro-`p` group: the classes of the generators of the
free pro-`p` group. -/
noncomputable def of (x : X) : presentedProP p X rels :=
  mk rels (freeProP.of x)

/-- The canonical projection sends a free generator to the corresponding generator of the
presented pro-`p` group. -/
@[simp]
theorem mk_of (x : X) : mk rels (freeProP.of x) = of x :=
  (rfl)

/-- The generators generate the presented pro-`p` group topologically. -/
theorem dense_closure_range_of :
    Dense ((Subgroup.closure (Set.range (of : X → presentedProP p X rels)) :
      Subgroup (presentedProP p X rels)) : Set (presentedProP p X rels)) := by
  -- The generators are the image of the free profinite generators under the continuous
  -- surjection `freeProfiniteGroup X → freeProP p X → presentedProP p X rels`.
  let q : freeProfiniteGroup X →ₜ* presentedProP p X rels :=
    (mk rels).comp (freeProP.fromFreeProfiniteGroup p X)
  have hq : Function.Surjective q :=
    (mk_surjective rels).comp freeProP.fromFreeProfiniteGroup_surjective
  have h : Set.range (of : X → presentedProP p X rels) =
      q '' Set.range (freeProfiniteGroup.of : X → freeProfiniteGroup X) := by
    rw [← Set.range_comp]
    congr 1
    funext x
    simp only [q, Function.comp_apply, ContinuousMonoidHom.coe_comp,
      freeProP.fromFreeProfiniteGroup_of, mk_of]
  have hmap : Subgroup.closure (q '' Set.range (freeProfiniteGroup.of : X → freeProfiniteGroup X)) =
      (Subgroup.closure (Set.range (freeProfiniteGroup.of : X → freeProfiniteGroup X))).map
        q.toMonoidHom :=
    (MonoidHom.map_closure _ _).symm
  rw [h, hmap, Subgroup.coe_map]
  exact hq.denseRange.dense_image (map_continuous q) (freeProfiniteGroup.dense_closure_range_of X)

/-- A pro-`p` group presented on a finite type is topologically finitely generated. -/
theorem _root_.TauCeti.isTopologicallyFinitelyGenerated_presentedProP [Finite X] :
    IsTopologicallyFinitelyGenerated (presentedProP p X rels) :=
  (Set.finite_range (of : X → presentedProP p X rels)).isTopologicallyFinitelyGenerated <|
    SetLike.coe_injective <| by
      rw [Subgroup.topologicalClosure_coe, dense_closure_range_of.closure_eq, Subgroup.coe_top]

section HomExt

variable {Q : Type v} [Group Q] [TopologicalSpace Q] [T2Space Q]

/-- Two continuous homomorphisms out of a presented pro-`p` group that agree on the generators
are equal. The target need only be a Hausdorff topological space carrying a group structure. -/
@[ext]
theorem hom_ext {φ ψ : presentedProP p X rels →ₜ* Q} (h : ∀ x : X, φ (of x) = ψ (of x)) :
    φ = ψ := by
  have hcomp : φ.comp (mk rels) = ψ.comp (mk rels) :=
    freeProP.hom_ext fun x ↦ by simpa using h x
  refine ContinuousMonoidHom.ext fun y ↦ ?_
  obtain ⟨x, rfl⟩ := mk_surjective rels y
  exact DFunLike.congr_fun hcomp x

end HomExt

section Lift

variable {P : Type u} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [TotallyDisconnectedSpace P]

/-- The closed normal closure of the relators lies in the kernel of the free pro-`p` lift of a
map that kills every relator. -/
theorem topologicalClosure_normalClosure_le_ker_lift (hP : IsProP p P) (f : X → P)
    (h : ∀ r ∈ rels, freeProP.lift hP f r = 1) :
    (Subgroup.normalClosure rels).topologicalClosure ≤ (freeProP.lift hP f).toMonoidHom.ker :=
  Subgroup.topologicalClosure_normalClosure_le_ker (map_continuous (freeProP.lift hP f)) h

/-- The continuous homomorphism to a pro-`p` group `P` induced by a map `f : X → P` on the
generators under which every relator becomes trivial. -/
noncomputable def lift (hP : IsProP p P) (f : X → P) (h : ∀ r ∈ rels, freeProP.lift hP f r = 1) :
    presentedProP p X rels →ₜ* P :=
  ⟨QuotientGroup.lift _ (freeProP.lift hP f).toMonoidHom
      (topologicalClosure_normalClosure_le_ker_lift hP f h),
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (map_continuous (freeProP.lift hP f))⟩

/-- The induced homomorphism computes on classes as the free pro-`p` lift. -/
@[simp]
theorem lift_mk (hP : IsProP p P) (f : X → P) (h : ∀ r ∈ rels, freeProP.lift hP f r = 1)
    (x : freeProP p X) : lift hP f h (mk rels x) = freeProP.lift hP f x :=
  QuotientGroup.lift_mk' _ (topologicalClosure_normalClosure_le_ker_lift hP f h) x

/-- The induced homomorphism agrees with `f` on each generator. -/
@[simp]
theorem lift_of (hP : IsProP p P) (f : X → P) (h : ∀ r ∈ rels, freeProP.lift hP f r = 1)
    (x : X) : lift hP f h (of x) = f x := by
  rw [of, lift_mk, freeProP.lift_of]

/-- The induced homomorphism recovers the free pro-`p` lift along the canonical projection. -/
@[simp]
theorem lift_comp_mk (hP : IsProP p P) (f : X → P) (h : ∀ r ∈ rels, freeProP.lift hP f r = 1) :
    (lift hP f h).comp (mk rels) = freeProP.lift hP f :=
  freeProP.hom_ext fun x ↦ by simp

/-- A continuous homomorphism restricting to `f` on the generators is the induced
homomorphism. -/
theorem lift_unique (hP : IsProP p P) (f : X → P) (h : ∀ r ∈ rels, freeProP.lift hP f r = 1)
    (φ : presentedProP p X rels →ₜ* P) (hφ : ∀ x : X, φ (of x) = f x) : φ = lift hP f h :=
  hom_ext fun x ↦ by rw [hφ, lift_of]

/-- **The universal property of the presented pro-`p` group.** A map from `X` to a profinite
pro-`p` group under which every relator becomes trivial extends uniquely to a continuous
homomorphism from `presentedProP p X rels`. -/
theorem existsUnique_lift (hP : IsProP p P) (f : X → P)
    (h : ∀ r ∈ rels, freeProP.lift hP f r = 1) :
    ∃! φ : presentedProP p X rels →ₜ* P, ∀ x : X, φ (of x) = f x :=
  ⟨lift hP f h, lift_of hP f h, fun φ hφ ↦ lift_unique hP f h φ hφ⟩

/-- The induced homomorphism is natural in the target. -/
@[simp]
theorem comp_lift {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [TotallyDisconnectedSpace Q] (hP : IsProP p P) (hQ : IsProP p Q)
    (g : P →ₜ* Q) (f : X → P) (h : ∀ r ∈ rels, freeProP.lift hP f r = 1) :
    g.comp (lift hP f h) = lift hQ (⇑g ∘ f) fun r hr ↦ by
      rw [← freeProP.comp_lift hP hQ, ContinuousMonoidHom.coe_comp, Function.comp_apply, h r hr,
        map_one] :=
  hom_ext fun x ↦ by simp

/-- A map whose range generates the target topologically induces a surjection. -/
theorem lift_surjective (hP : IsProP p P) {f : X → P} (h : ∀ r ∈ rels, freeProP.lift hP f r = 1)
    (hf : Dense ((Subgroup.closure (Set.range f) : Subgroup P) : Set P)) :
    Function.Surjective (lift hP f h) := by
  have hcomp : ⇑(freeProP.lift hP f) = lift hP f h ∘ mk rels :=
    funext fun x ↦ (lift_mk hP f h x).symm
  exact Function.Surjective.of_comp (hcomp ▸ freeProP.lift_surjective hP hf)

end Lift

/-! ## The empty set of relators -/

section Empty

/-- With no relators, the presented pro-`p` group is the free pro-`p` group: the canonical
projection is a topological isomorphism. -/
noncomputable def equivFreeProP : presentedProP p X (∅ : Set (freeProP p X)) ≃ₜ* freeProP p X where
  toFun := lift (isProP_freeProP p X) freeProP.of fun _ hr ↦ hr.elim
  invFun := mk ∅
  left_inv y := by
    have h : (mk ∅).comp (lift (isProP_freeProP p X) freeProP.of fun _ hr ↦ hr.elim) =
        ContinuousMonoidHom.id (presentedProP p X ∅) :=
      hom_ext fun x ↦ by simp
    exact DFunLike.congr_fun h y
  right_inv y := by
    have h : (lift (isProP_freeProP p X) freeProP.of fun _ hr ↦ hr.elim).comp (mk ∅) =
        ContinuousMonoidHom.id (freeProP p X) :=
      freeProP.hom_ext fun x ↦ by simp
    exact DFunLike.congr_fun h y
  map_mul' := map_mul _
  continuous_toFun := map_continuous _
  continuous_invFun := map_continuous _

/-- The inverse of the isomorphism with the free pro-`p` group is the canonical projection. -/
@[simp]
theorem equivFreeProP_symm_apply (x : freeProP p X) :
    equivFreeProP.symm x = mk (∅ : Set (freeProP p X)) x :=
  (rfl)

/-- The isomorphism with the free pro-`p` group sends the class of an element to that element. -/
@[simp]
theorem equivFreeProP_mk (x : freeProP p X) :
    equivFreeProP (mk (∅ : Set (freeProP p X)) x) = x := by
  rw [← equivFreeProP_symm_apply, ContinuousMulEquiv.apply_symm_apply]

/-- The isomorphism with the free pro-`p` group matches the generators. -/
@[simp]
theorem equivFreeProP_of (x : X) :
    equivFreeProP (of (rels := (∅ : Set (freeProP p X))) x) = freeProP.of x := by
  rw [← mk_of, equivFreeProP_mk]

end Empty

/-! ## Continuous images of free pro-`p` groups are presented -/

section OfSurjective

variable {G : Type v} [Group G] [TopologicalSpace G] [T2Space G]

/-- The algebraic isomorphism underlying `equivOfSurjective`: the kernel of a continuous
homomorphism to a Hausdorff group is closed and normal, so it is its own closed normal closure,
and the first isomorphism theorem applies. -/
private noncomputable def mulEquivOfSurjective (φ : freeProP p X →ₜ* G)
    (hφ : Function.Surjective φ) :
    presentedProP p X ((φ : freeProP p X →* G).ker : Set (freeProP p X)) ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq (Subgroup.topologicalClosure_normalClosure_eq_self _
    (isClosed_singleton.preimage (map_continuous φ)))).trans
    (QuotientGroup.quotientKerEquivOfSurjective (φ : freeProP p X →* G) hφ)

private theorem mulEquivOfSurjective_mk (φ : freeProP p X →ₜ* G) (hφ : Function.Surjective φ)
    (x : freeProP p X) : mulEquivOfSurjective φ hφ (mk _ x) = φ x := by
  rw [mulEquivOfSurjective, mk_apply, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  unfold QuotientGroup.quotientKerEquivOfSurjective
  rw [QuotientGroup.quotientKerEquivOfRightInverse_apply]
  rfl

/-- A Hausdorff group that is a continuous image of the free pro-`p` group on `X` is presented on
`X`, with the kernel as its set of relators. -/
noncomputable def equivOfSurjective (φ : freeProP p X →ₜ* G) (hφ : Function.Surjective φ) :
    presentedProP p X ((φ : freeProP p X →* G).ker : Set (freeProP p X)) ≃ₜ* G :=
  have hcont : Continuous (mulEquivOfSurjective φ hφ) :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr <|
      (funext (mulEquivOfSurjective_mk φ hφ) :
        ⇑(mulEquivOfSurjective φ hφ) ∘ QuotientGroup.mk = ⇑φ) ▸ map_continuous φ
  ContinuousMulEquiv.mk (mulEquivOfSurjective φ hφ) hcont
    (hcont.continuous_symm_of_equiv_compact_to_t2 (f := (mulEquivOfSurjective φ hφ).toEquiv))

/-- The presentation isomorphism of a continuous image sends the class of an element to its
image. -/
@[simp]
theorem equivOfSurjective_mk (φ : freeProP p X →ₜ* G) (hφ : Function.Surjective φ)
    (x : freeProP p X) : equivOfSurjective φ hφ (mk _ x) = φ x :=
  mulEquivOfSurjective_mk φ hφ x

/-- The presentation isomorphism of a continuous image matches the generators. -/
@[simp]
theorem equivOfSurjective_of (φ : freeProP p X →ₜ* G) (hφ : Function.Surjective φ) (x : X) :
    equivOfSurjective φ hφ (of x) = φ (freeProP.of x) := by
  rw [← mk_of, equivOfSurjective_mk]

end OfSurjective

end presentedProP

/-! ## Presentations of topologically finitely generated pro-`p` groups -/

section Existence

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- A topologically finitely generated pro-`p` group is a continuous image of the free pro-`p`
group on any finite type with at least `topologicalGeneratorRankNat G` elements. -/
theorem IsProP.exists_surjective_freeProP (hG : IsProP p G) (h : IsTopologicallyFinitelyGenerated G)
    (X : Type u) [Finite X] (hX : topologicalGeneratorRankNat G h ≤ Nat.card X) :
    ∃ φ : freeProP p X →ₜ* G, Function.Surjective φ := by
  classical
  obtain ⟨s, hs, hgen⟩ := exists_finset_card_eq_topologicalGeneratorRankNat h
  have _ : Fintype X := Fintype.ofFinite X
  obtain ⟨e⟩ : Nonempty (s ↪ X) :=
    Function.Embedding.nonempty_of_card_le (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_eq_finsetCard, hs]
      exact hX)
  -- Send the image of `s` under `e` back to `s`, and everything else to `1`.
  let f : X → G := Function.extend e Subtype.val fun _ ↦ 1
  refine ⟨freeProP.lift hG f, freeProP.lift_surjective hG ?_⟩
  have hsub : (s : Set G) ⊆ Set.range f := fun a ha ↦
    ⟨e ⟨a, ha⟩, by simp [f, e.injective.extend_apply]⟩
  refine Dense.mono (SetLike.coe_subset_coe.mpr (Subgroup.closure_mono hsub)) ?_
  rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, hgen, Subgroup.coe_top]

/-- **Every topologically finitely generated pro-`p` group has a presentation** on any finite type
with at least `topologicalGeneratorRankNat G` elements, in particular on a type with exactly
`topologicalGeneratorRankNat G` elements, which is what a *minimal presentation* means. -/
theorem IsProP.exists_continuousMulEquiv_presentedProP (hG : IsProP p G)
    (h : IsTopologicallyFinitelyGenerated G) (X : Type u) [Finite X]
    (hX : topologicalGeneratorRankNat G h ≤ Nat.card X) :
    ∃ rels : Set (freeProP p X), Nonempty (presentedProP p X rels ≃ₜ* G) := by
  obtain ⟨φ, hφ⟩ := hG.exists_surjective_freeProP h X hX
  exact ⟨_, ⟨presentedProP.equivOfSurjective φ hφ⟩⟩

end Existence

end TauCeti
