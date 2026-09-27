/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CompactDiscrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.Topology.Algebra.Group.Profinite.Basic
public import TauCeti.Topology.Separation.Profinite

/-!
# The cohomology of a closed subgroup as a colimit over the open subgroups containing it

Let `G` be a profinite group, `X` a smooth discrete representation of `G` (a discrete module with
continuous action), and `H ≤ G` a closed subgroup. Then `H` is the intersection of the open
subgroups `V` containing it, and the continuous cohomology of `H` is the filtered colimit of the
cohomology of those `V`:

```text
Hⁿ(H, X) = colim_{H ≤ V open} Hⁿ(V, X).
```

This file proves that description elementwise, in every degree, on Mathlib's canonical carrier
`continuousCohomology n`:

* **surjectivity**: every class of `Hⁿ(H, X)` is the restriction of a class of `Hⁿ(V, X)` for some
  open `V ⊇ H`;
* **injectivity**: a class of `Hⁿ(G, X)` restricting to zero on `H` restricts to zero on some open
  `V ⊇ H`. Applied with an open subgroup in place of `G`, this says that two classes of `Hⁿ(V, X)`
  with the same restriction to `H` agree after restriction to some open `V' ⊆ V` containing `H`.

Both statements are proved on the homogeneous cochains `C(G, C(G, …, X))` of the coinduced
resolution, where the point is that everything is locally constant. A cochain of `H` extends to a
cochain of `G`: an invariant cochain is determined by its value at `1`, and a continuous map from
the closed subspace `H` of the profinite space `G` into a discrete space extends continuously to
`G`. A cochain of `G` vanishing on `H` vanishes on an open neighbourhood of `H`, since a locally
constant map on a compact set takes finitely many values, and an open neighbourhood of a closed
subgroup contains an open subgroup containing it. Smoothness of `X` enters exactly once, to make
the orbit maps `g ↦ g • v` of the resolution continuous, which is what a cochain determined by its
value at `1` needs in order to exist.

## Main results

* `TauCeti.ContinuousCohomology.resolutionMap_subgroupSubtype_eq_zero_iff`,
  `TauCeti.ContinuousCohomology.exists_openSubgroup_le_resolutionMap_subgroupSubtype_eq_zero`:
  on the coinduced resolution, restriction to a subgroup vanishes exactly when the cochain vanishes
  on tuples from the subgroup, and vanishing on a closed subgroup spreads to an open subgroup.
* `TauCeti.ContinuousCohomology.resolutionMap_subgroupSubtype_surjective`,
  `TauCeti.ContinuousCohomology.exists_mem_invariants_resolutionMap_subgroupSubtype_eq`: on the
  coinduced resolution, restriction to a closed subgroup is surjective, also on invariant elements.
* `TauCeti.ContinuousCohomology.exists_openSubgroup_le_res_eq_zero`: a class restricting to zero
  on a closed subgroup restricts to zero on an open subgroup containing it.
* `TauCeti.ContinuousCohomology.exists_openSubgroup_le_resLe_eq`: every class of a closed subgroup
  is restricted from an open subgroup containing it.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §2.2, Proposition 8.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.1).
* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Section 6.5.
-/

public section

open CategoryTheory TopRep Topology

namespace TauCeti

universe u v

variable {k : Type u} {G : Type v} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

namespace ContinuousCohomology

open _root_.ContinuousCohomology

variable (X : TopRep k G)

/-! ### Restriction on the coinduced resolution

The restriction of a homogeneous cochain to a subgroup `S` is, on the coinduced resolution,
`ContinuousCohomology.resolutionMap` along the inclusion of `S` with the identity of the
coefficients: it reads the iterated map `C(G, C(G, …, X))` on tuples from `S`. -/

/-- Restricting the coinduced resolution to a subgroup `S` and then to a subgroup `H ≤ S` is
restricting it to `H`. -/
private theorem resolutionMap_subgroupInclusion_resolutionMap_subgroupSubtype {H S : Subgroup G}
    (h : H ≤ S) : ∀ (n : ℕ) (F : (TopRep.resolutionX X n).V),
    (resolutionMap (ContinuousMonoidHom.subgroupInclusion h)
        (𝟙 (TopRep.res (H.subtype : H →* G) X)) n).hom
        ((resolutionMap (ContinuousMonoidHom.subgroupSubtype S)
          (𝟙 (TopRep.res (S.subtype : S →* G) X)) n).hom F) =
      (resolutionMap (ContinuousMonoidHom.subgroupSubtype H)
        (𝟙 (TopRep.res (H.subtype : H →* G) X)) n).hom F
  | 0, _ => rfl
  | n + 1, F => ContinuousMap.ext fun x ↦
    -- in degree `n + 1` the restrictions evaluate at `x` to the restrictions of `F x`, so both
    -- sides are, by definition, the degree-`n` statement at `F x`
    resolutionMap_subgroupInclusion_resolutionMap_subgroupSubtype h n
      ((F : C(G, (TopRep.resolutionX X n).V)) x)

/-! ### Vanishing on a subset

`ResolutionVanishesOn X T n F` says that the iterated map `F : C(G, C(G, …, X))` of degree `n`
vanishes on all `n`-tuples of points of `T`. For a subgroup `S` it is the vanishing of the
restriction of `F` to `S`. -/

/-- An element `F` of the `n`-th term `C(G, C(G, …, X))` of the coinduced resolution **vanishes on
`T`** when it is zero on every `n`-tuple of points of `T`. -/
def ResolutionVanishesOn (T : Set G) : (n : ℕ) → (TopRep.resolutionX X n).V → Prop
  | 0, v => v = 0
  | n + 1, F => ∀ g ∈ T, ResolutionVanishesOn T n ((F : C(G, (TopRep.resolutionX X n).V)) g)

@[simp]
theorem resolutionVanishesOn_zero (T : Set G) (v : (TopRep.resolutionX X 0).V) :
    ResolutionVanishesOn X T 0 v ↔ v = 0 :=
  Iff.rfl

@[simp]
theorem resolutionVanishesOn_succ (T : Set G) (n : ℕ) (F : (TopRep.resolutionX X (n + 1)).V) :
    ResolutionVanishesOn X T (n + 1) F ↔
      ∀ g ∈ T, ResolutionVanishesOn X T n ((F : C(G, (TopRep.resolutionX X n).V)) g) :=
  Iff.rfl

variable {X}

/-- Vanishing on a set implies vanishing on every subset. -/
theorem ResolutionVanishesOn.mono {T T' : Set G} (h : T' ⊆ T) :
    ∀ (n : ℕ) {F : (TopRep.resolutionX X n).V},
      ResolutionVanishesOn X T n F → ResolutionVanishesOn X T' n F
  | 0, _, hF => hF
  | n + 1, _, hF => fun g hg ↦ (hF g (h hg)).mono h n

/-- The restriction of an element of the coinduced resolution to a subgroup `S` is zero exactly
when the element vanishes on `S`. -/
theorem resolutionMap_subgroupSubtype_eq_zero_iff (S : Subgroup G) :
    ∀ (n : ℕ) (F : (TopRep.resolutionX X n).V),
      (resolutionMap (ContinuousMonoidHom.subgroupSubtype S)
          (𝟙 (TopRep.res (S.subtype : S →* G) X)) n).hom F = 0 ↔
        ResolutionVanishesOn X S n F
  | 0, F => Iff.rfl
  | n + 1, F => by
    rw [resolutionVanishesOn_succ, ContinuousMap.ext_iff]
    -- at a point `s : S` the restriction is, by definition, the restriction of `F s`, so both
    -- sides are the degree-`n` statement at the values of `F` on `S`
    exact ⟨fun h g hg ↦ (resolutionMap_subgroupSubtype_eq_zero_iff S n _).1 (h ⟨g, hg⟩),
      fun h s ↦ (resolutionMap_subgroupSubtype_eq_zero_iff S n _).2 (h s s.2)⟩

variable [CompactSpace G] [DiscreteTopology X.V]

/-- **Vanishing on a compact set spreads to an open neighbourhood.** An element of the coinduced
resolution of a discrete representation of a compact group that vanishes on a compact set `T`
vanishes on an open set containing `T`: on `T` it takes finitely many values, each of which
vanishes on `T` in one degree less. -/
theorem ResolutionVanishesOn.exists_isOpen {T : Set G} (hT : IsCompact T) (n : ℕ) :
    ∀ {F : (TopRep.resolutionX X n).V}, ResolutionVanishesOn X T n F →
      ∃ W : Set G, IsOpen W ∧ T ⊆ W ∧ ResolutionVanishesOn X W n F := by
  induction n with
  | zero => exact fun hF ↦ ⟨Set.univ, isOpen_univ, Set.subset_univ _, hF⟩
  | succ n ih =>
    intro F hF
    set F' : C(G, (TopRep.resolutionX X n).V) := F
    have : Finite (F' '' T) := ((hT.image F'.continuous).finite_of_discrete).to_subtype
    -- each of the finitely many values of `F'` on `T` vanishes on an open set containing `T`
    choose W hWopen hTW hW using fun v : F' '' T ↦
      ih (F := v) (by obtain ⟨g, hg, hgv⟩ := v.2; exact hgv ▸ hF g hg)
    refine ⟨F' ⁻¹' (F' '' T) ∩ ⋂ v, W v, ((isOpen_discrete _).preimage F'.continuous).inter
      (isOpen_iInter_of_finite fun v ↦ hWopen v),
      Set.subset_inter (Set.subset_preimage_image _ _) (Set.subset_iInter fun v ↦ hTW v),
      fun g hg ↦ ?_⟩
    exact (hW ⟨F' g, hg.1⟩).mono (Set.inter_subset_right.trans (Set.iInter_subset _ _)) n

variable [TotallyDisconnectedSpace G]

/-- **Vanishing on a closed subgroup spreads to an open subgroup.** An element of the coinduced
resolution of a discrete representation of a profinite group whose restriction to a closed
subgroup `H` vanishes has vanishing restriction to some open subgroup containing `H`. -/
theorem exists_openSubgroup_le_resolutionMap_subgroupSubtype_eq_zero {H : Subgroup G}
    (hH : IsClosed (H : Set G)) {n : ℕ} {F : (TopRep.resolutionX X n).V}
    (hF : (resolutionMap (ContinuousMonoidHom.subgroupSubtype H)
      (𝟙 (TopRep.res (H.subtype : H →* G) X)) n).hom F = 0) :
    ∃ V : OpenSubgroup G, H ≤ V ∧ (resolutionMap (ContinuousMonoidHom.subgroupSubtype
      (V : Subgroup G)) (𝟙 (TopRep.res ((V : Subgroup G).subtype : V →* G) X)) n).hom F = 0 := by
  obtain ⟨W, hWopen, hHW, hW⟩ :=
    ((resolutionMap_subgroupSubtype_eq_zero_iff H n F).1 hF).exists_isOpen hH.isCompact n
  obtain ⟨V, hHV, hVW⟩ := H.exists_openSubgroup_le_subset_of_isClosed hH hWopen hHW
  exact ⟨V, hHV, (resolutionMap_subgroupSubtype_eq_zero_iff (V : Subgroup G) n F).2
    (hW.mono hVW n)⟩

/-! ### Extension from a closed subgroup -/

variable (X) in
/-- **Restriction of the coinduced resolution to a closed subgroup is surjective.** Over a
profinite group, every element of the coinduced resolution of the restriction of a discrete
representation to a closed subgroup `H` is the restriction of an element of the resolution of
`G`: a continuous map from the closed subspace `H` into a discrete space extends to `G`. -/
theorem resolutionMap_subgroupSubtype_surjective {H : Subgroup G} (hH : IsClosed (H : Set G))
    (n : ℕ) :
    Function.Surjective (resolutionMap (ContinuousMonoidHom.subgroupSubtype H)
      (𝟙 (TopRep.res (H.subtype : H →* G) X)) n).hom := by
  induction n with
  | zero => exact fun w ↦ ⟨w, rfl⟩
  | succ n ih =>
    intro w
    have : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
    set w' : C(H, (TopRep.resolutionX (TopRep.res (H.subtype : H →* G) X) n).V) := w
    -- lift the values of `w` through the surjection in degree `n`, then extend to `G`
    obtain ⟨W, hW⟩ := ContinuousMap.exists_extension_of_discrete hH.isClosedEmbedding_subtypeVal
      (⟨fun s ↦ Function.surjInv ih (w' s),
        (continuous_of_discreteTopology (f := Function.surjInv ih)).comp w'.continuous⟩ :
        C(H, (TopRep.resolutionX X n).V))
    refine ⟨W, ContinuousMap.ext fun s ↦ ?_⟩
    have hWs : W (s : G) = Function.surjInv ih (w' s) := congr($(hW) s)
    -- the left-hand side is, by definition, the restriction of `W s`
    exact (congrArg (resolutionMap (ContinuousMonoidHom.subgroupSubtype H)
      (𝟙 (TopRep.res (H.subtype : H →* G) X)) n).hom hWs).trans (Function.surjInv_eq ih (w' s))

section Invariants

attribute [local instance] TopRep.distribMulAction

omit [DiscreteTopology X.V] in
/-- **An invariant cochain of a closed subgroup extends to an invariant cochain of the group.**
Over a profinite group and for a smooth discrete representation `X`, every `H`-invariant element
`w` of the coinduced resolution of the restriction of `X` to a closed subgroup `H` is the
restriction of a `G`-invariant element of the resolution of `X`: an invariant element is
determined by its value at `1` as `g ↦ g • v`, and that value extends to `G` by
`resolutionMap_subgroupSubtype_surjective`. -/
theorem exists_mem_invariants_resolutionMap_subgroupSubtype_eq (hX : IsSmoothDiscrete k X)
    {H : Subgroup G} (hH : IsClosed (H : Set G)) (n : ℕ)
    {w : (TopRep.resolutionX (TopRep.res (H.subtype : H →* G) X) (n + 1)).V}
    (hw : w ∈ (TopRep.resolutionX (TopRep.res (H.subtype : H →* G) X) (n + 1)).ρ.invariants) :
    ∃ W ∈ (TopRep.resolutionX X (n + 1)).ρ.invariants,
      (resolutionMap (ContinuousMonoidHom.subgroupSubtype H)
        (𝟙 (TopRep.res (H.subtype : H →* G) X)) (n + 1)).hom W = w := by
  have := hX.discreteTopology
  set w' : C(H, (TopRep.resolutionX (TopRep.res (H.subtype : H →* G) X) n).V) := w
  obtain ⟨u, hu⟩ : ∃ u : (TopRep.resolutionX X n).V,
      (resolutionMap (ContinuousMonoidHom.subgroupSubtype H)
        (𝟙 (TopRep.res (H.subtype : H →* G) X)) n).hom u = w' 1 :=
    resolutionMap_subgroupSubtype_surjective X hH n (w' 1)
  -- the orbit map of `u` is continuous because the resolution is smooth
  have hcont : Continuous fun g : G ↦ (TopRep.resolutionX X n).ρ g u := by
    have : ContinuousSMul G (TopRep.resolutionX X n).V := (hX.resolutionX n).continuousSMul
    have h : Continuous fun g : G ↦ g • u := continuous_id.smul continuous_const
    simpa only [TopRep.distribMulAction_smul] using h
  -- the invariant element with value `u` at `1`
  let W : C(G, (TopRep.resolutionX X n).V) := ⟨fun g ↦ (TopRep.resolutionX X n).ρ g u, hcont⟩
  refine ⟨W, fun g ↦ ContinuousMap.ext fun x ↦ ?_, ContinuousMap.ext fun s ↦ ?_⟩
  · -- invariance: `ρ g (ρ (g⁻¹ * x) u) = ρ x u`
    simp only [ContRepresentation.coind₁_apply_apply, W, ContinuousMap.coe_mk,
      ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left]
  · -- the left-hand side is, by definition, the restriction of `W s = ρ s u`; restriction is
    -- equivariant, and `w` is invariant with value `w' 1` at `1`
    have h₁ := TopRep.hom_comm_apply (resolutionMap (ContinuousMonoidHom.subgroupSubtype H)
      (𝟙 (TopRep.res (H.subtype : H →* G) X)) n) s u
    have h₂ := congr($(hw s) s)
    simp only [ContRepresentation.coind₁_apply_apply, inv_mul_cancel] at h₂
    exact (h₁.trans (by rw [hu])).trans h₂

end Invariants

/-! ### The colimit description -/

omit [DiscreteTopology X.V]

variable {n : ℕ}

/-- **A class restricting to zero on a closed subgroup restricts to zero on an open subgroup
containing it.** For a profinite group `G`, a smooth discrete representation `X` and a closed
subgroup `H`, a class of `Hⁿ(G, X)` whose restriction to `H` vanishes has vanishing restriction
to some open subgroup `V ⊇ H`. This is the injectivity half of the description of `Hⁿ(H, X)` as
the filtered colimit of the `Hⁿ(V, X)` over the open subgroups `V ⊇ H`; applied to an open
subgroup in place of `G`, it says that two classes of `Hⁿ(V, X)` with the same restriction to `H`
agree after restriction to some open subgroup between `H` and `V`. -/
theorem exists_openSubgroup_le_res_eq_zero (hX : IsSmoothDiscrete k X) {H : Subgroup G}
    (hH : IsClosed (H : Set G)) {x : continuousCohomology n X} (hx : (res H X n).hom x = 0) :
    ∃ V : OpenSubgroup G, H ≤ V ∧ (res (V : Subgroup G) X n).hom x = 0 := by
  have := hX.discreteTopology
  set K := TopRep.homogeneousCochains X
  set KH := TopRep.homogeneousCochains (TopRep.res (H.subtype : H →* G) X)
  set φH := cochainsMap (ContinuousMonoidHom.subgroupSubtype H)
    (𝟙 (TopRep.res (H.subtype : H →* G) X))
  obtain ⟨z, rfl⟩ := K.homologyπ_surjective n x
  obtain ⟨m, hm⟩ : ∃ m, (ComplexShape.up ℕ).prev n = m := ⟨_, rfl⟩
  -- the restricted cocycle is a boundary `d w`
  have hz : KH.homologyπ n (HomologicalComplex.cyclesMap φH n z) = 0 := by
    have h := ConcreteCategory.congr_hom (π_map (ContinuousMonoidHom.subgroupSubtype H)
      (𝟙 (TopRep.res (H.subtype : H →* G) X)) n) z
    simp only [ConcreteCategory.comp_apply] at h
    rw [res_def] at hx
    exact h.symm.trans hx
  obtain ⟨w, hw⟩ := (KH.homologyπ_eq_zero_iff n hm).1 hz
  -- extend the primitive `w` to an invariant cochain `W` of `G`
  obtain ⟨W, hWinv, hW⟩ :=
    exists_mem_invariants_resolutionMap_subgroupSubtype_eq hX hH m w.2
  let Wc : K.X m := ⟨W, hWinv⟩
  have hWc : φH.f m Wc = w := Subtype.ext hW
  -- `F = z - d W` restricts to zero on `H`
  set F : K.X n := K.iCycles n z - K.d m n Wc with hFdef
  have hF : φH.f n F = 0 := by
    have h₁ := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φH n) z
    have h₂ := ConcreteCategory.congr_hom (φH.comm m n) Wc
    simp only [ConcreteCategory.comp_apply] at h₁ h₂
    rw [hFdef, map_sub, sub_eq_zero]
    refine (h₁.symm.trans (congrArg (KH.iCycles n).hom hw.symm)).trans ?_
    rw [← hWc]
    exact (KH.iCycles_toCycles_apply m _).trans h₂
  have hF' : (resolutionMap (ContinuousMonoidHom.subgroupSubtype H)
      (𝟙 (TopRep.res (H.subtype : H →* G) X)) (n + 1)).hom F.1 = 0 :=
    congrArg Subtype.val hF
  -- so it restricts to zero on some open subgroup `V ⊇ H`
  obtain ⟨V, hHV, hV⟩ := exists_openSubgroup_le_resolutionMap_subgroupSubtype_eq_zero (X := X) hH
    (n := n + 1) (F := F.1) hF'
  set KV := TopRep.homogeneousCochains (TopRep.res ((V : Subgroup G).subtype : V →* G) X)
  set φV := cochainsMap (ContinuousMonoidHom.subgroupSubtype (V : Subgroup G))
    (𝟙 (TopRep.res ((V : Subgroup G).subtype : V →* G) X))
  have hFV : φV.f n F = 0 := Subtype.ext hV
  refine ⟨V, hHV, ?_⟩
  -- on `V` the restricted cocycle is the boundary of the restriction of `W`
  have h := ConcreteCategory.congr_hom (π_map (ContinuousMonoidHom.subgroupSubtype
    (V : Subgroup G)) (𝟙 (TopRep.res ((V : Subgroup G).subtype : V →* G) X)) n) z
  have h₁ := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φV n) z
  have h₂ := ConcreteCategory.congr_hom (φV.comm m n) Wc
  simp only [ConcreteCategory.comp_apply] at h h₁ h₂
  rw [res_def]
  refine h.trans ((KV.homologyπ_eq_zero_iff n hm).2 ⟨φV.f m Wc, KV.iCycles_injective n ?_⟩)
  refine ((KV.iCycles_toCycles_apply m _).trans h₂).trans (Eq.trans ?_ h₁.symm)
  calc φV.f n (K.d m n Wc) = φV.f n (F + K.d m n Wc) := by rw [map_add, hFV, zero_add]
    _ = φV.f n (K.iCycles n z) := by rw [hFdef, sub_add_cancel]

/-- **Every class of a closed subgroup is restricted from an open subgroup containing it.** For a
profinite group `G`, a smooth discrete representation `X` and a closed subgroup `H`, every class
of `Hⁿ(H, X)` is the restriction of a class of `Hⁿ(V, X)` for some open subgroup `V ⊇ H`. This is
the surjectivity half of the description of `Hⁿ(H, X)` as the filtered colimit of the `Hⁿ(V, X)`
over the open subgroups `V ⊇ H`. -/
theorem exists_openSubgroup_le_resLe_eq (hX : IsSmoothDiscrete k X) {H : Subgroup G}
    (hH : IsClosed (H : Set G))
    (y : continuousCohomology n (TopRep.res (H.subtype : H →* G) X)) :
    ∃ (V : OpenSubgroup G) (hHV : H ≤ V)
      (x : continuousCohomology n (TopRep.res ((V : Subgroup G).subtype : V →* G) X)),
        (resLe hHV X n).hom x = y := by
  have := hX.discreteTopology
  set K := TopRep.homogeneousCochains X
  set KH := TopRep.homogeneousCochains (TopRep.res (H.subtype : H →* G) X)
  set φH := cochainsMap (ContinuousMonoidHom.subgroupSubtype H)
    (𝟙 (TopRep.res (H.subtype : H →* G) X))
  obtain ⟨z, rfl⟩ := KH.homologyπ_surjective n y
  -- extend the cocycle `z` to an invariant cochain `C` of `G`
  obtain ⟨C, hCinv, hC⟩ :=
    exists_mem_invariants_resolutionMap_subgroupSubtype_eq hX hH n (KH.iCycles n z).2
  let Cc : K.X n := ⟨C, hCinv⟩
  have hCc : φH.f n Cc = KH.iCycles n z := Subtype.ext hC
  -- the differential of `C` restricts to zero on `H`, hence on some open subgroup `V ⊇ H`
  have h₀ := ConcreteCategory.congr_hom (φH.comm n (n + 1)) Cc
  simp only [ConcreteCategory.comp_apply] at h₀
  have hD₀ : φH.f (n + 1) (K.d n (n + 1) Cc) = 0 := by
    rw [← h₀, hCc]
    exact KH.d_iCycles_apply (n + 1) z
  have hD : (resolutionMap (ContinuousMonoidHom.subgroupSubtype H)
      (𝟙 (TopRep.res (H.subtype : H →* G) X)) (n + 1 + 1)).hom (K.d n (n + 1) Cc).1 = 0 :=
    congrArg Subtype.val hD₀
  obtain ⟨V, hHV, hV⟩ := exists_openSubgroup_le_resolutionMap_subgroupSubtype_eq_zero (X := X) hH
    (n := n + 1 + 1) (F := (K.d n (n + 1) Cc).1) hD
  set KV := TopRep.homogeneousCochains (TopRep.res ((V : Subgroup G).subtype : V →* G) X)
  set φV := cochainsMap (ContinuousMonoidHom.subgroupSubtype (V : Subgroup G))
    (𝟙 (TopRep.res ((V : Subgroup G).subtype : V →* G) X))
  set φHV := cochainsMap (X := TopRep.res ((V : Subgroup G).subtype : V →* G) X)
    (ContinuousMonoidHom.subgroupInclusion hHV) (𝟙 (TopRep.res (H.subtype : H →* G) X))
  -- the restriction of `C` to `V` is a cocycle of `V`
  have hdV : (KV.d n (n + 1)).hom (φV.f n Cc) = 0 := by
    have h := ConcreteCategory.congr_hom (φV.comm n (n + 1)) Cc
    simp only [ConcreteCategory.comp_apply] at h
    exact h.trans (Subtype.ext hV)
  let zV : KV.cycles n := KV.cyclesMkOfEq (φV.f n Cc) (n + 1) (CochainComplex.next ℕ n) hdV
  refine ⟨V, hHV, KV.homologyπ n zV, ?_⟩
  -- its class restricts to the class of `z`, since the underlying cochains agree
  have h := ConcreteCategory.congr_hom
    (π_map (X := TopRep.res ((V : Subgroup G).subtype : V →* G) X)
      (ContinuousMonoidHom.subgroupInclusion hHV) (𝟙 (TopRep.res (H.subtype : H →* G) X)) n) zV
  have h₁ := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φHV n) zV
  simp only [ConcreteCategory.comp_apply] at h h₁
  rw [resLe_def]
  refine h.trans (congrArg (KH.homologyπ n).hom (KH.iCycles_injective n ?_))
  refine (h₁.trans (congrArg (φHV.f n).hom
    (KV.iCycles_cyclesMkOfEq (φV.f n Cc) (n + 1) (CochainComplex.next ℕ n) hdV))).trans ?_
  rw [← hCc]
  exact Subtype.ext
    (resolutionMap_subgroupInclusion_resolutionMap_subgroupSubtype X hHV (n + 1) C)

end ContinuousCohomology

end TauCeti
