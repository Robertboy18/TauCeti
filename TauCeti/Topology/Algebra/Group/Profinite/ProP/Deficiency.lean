/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Explicit
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.EulerCharacteristic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.RelationRank

/-!
# The deficiency of a pro-`p` group

Let `G` be a topologically finitely generated pro-`p` group with generator rank `d(G)` and
relation rank `r(G) = dim_{𝔽_p} H²(G, 𝔽_p)`. Its **deficiency** is the integer
`def(G) = d(G) - r(G)`. The deficiency bounds every finite presentation of `G`: for a presentation
`G ≅ ⟨X ∣ rels⟩` of `G` by a free pro-`p` group `F` on a finite type `X` and finitely many
relators `rels`,

```text
#X - #rels ≤ def(G)   in ℤ,
```

with equality exactly when `rels` is a minimal set of normal generators of the relation subgroup.
So the deficiency bounds `#X - #rels` over the finite presentations of `G`, and a presentation whose
relators form a minimal set of normal generators realizes the bound.

The inequality is the count of the five-term exact sequence

```text
0 → H¹(G, 𝔽_p) → H¹(F, 𝔽_p) → H¹(R, 𝔽_p)^F → H²(G, 𝔽_p) → H²(F, 𝔽_p) = 0
```

of the presentation `1 → R → F → G → 1`, in which `H¹(F, 𝔽_p)` has dimension `#X`, `H¹(G, 𝔽_p)`
has dimension `d(G)`, and `H¹(R, 𝔽_p)^F` is the `𝔽_p`-dual of `R ⧸ Rᵖ[R, F]`, of dimension the least
number `d(R ⧸ Rᵖ[R, F])` of generators of `R` as a closed normal subgroup of `F`. Exactness gives
the identity

```text
#X + r(G) = d(G) + d(R ⧸ Rᵖ[R, F]),
```

for every presentation, minimal or not, and `d(R ⧸ Rᵖ[R, F]) ≤ #rels` since the relators generate
`R` normally. For a minimal presentation, `#X = d(G)` and the identity is the count
`r(G) = d(R ⧸ Rᵖ[R, F])` of `TauCeti.presentedProP.finrank_H2`.

The identity is proved first for the explicit model `H2 G (ZMod p)` of the cohomology, with the
trivial action of `G` on `𝔽_p` carried as an instance together with the hypothesis that it is
trivial, as in `TauCeti.Topology.Algebra.Group.Profinite.ProP.RelationRank`; the deficiency and the
inequality are then stated for `cohomFp p G 2`, the canonical carrier of every dimension count.

## Main definitions

* `TauCeti.deficiency`: the deficiency `def(G) = d(G) - dim_{𝔽_p} H²(G, 𝔽_p)`, in `ℤ`.

## Main results

* `TauCeti.card_add_finrank_H2_of_isClosed`: for `G ≅ F ⧸ R` with `F` free pro-`p` on a finite
  type `X` and `R` closed normal with `R ⧸ Rᵖ[R, F]` topologically finitely generated,
  `#X + dim H²(G, 𝔽_p) = d(G) + d(R ⧸ Rᵖ[R, F])`.
* `TauCeti.presentedProP.card_add_finrank_H2`, `TauCeti.presentedProP.card_add_finrank_cohomFp_two`:
  the same identity for a presentation `⟨X ∣ rels⟩ ≅ G`, on the explicit and on the canonical
  carrier.
* `TauCeti.presentedProP.finite_H2_of_finite`,
  `TauCeti.presentedProP.module_finite_cohomFp_two_of_finite`: `H²(G, 𝔽_p)` is finite for a group
  with a finite presentation.
* `TauCeti.presentedProP.card_sub_card_le_deficiency`: `#X - #rels ≤ def(G)`, and
  `TauCeti.presentedProP.card_sub_card_eq_deficiency_iff`: equality holds exactly when the
  number of relators is the least number of normal generators of the relation subgroup.
* `TauCeti.deficiency_congr`: the deficiency is an isomorphism invariant.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.9.4) and
  (3.9.5).
* J.-P. Serre, *Galois Cohomology*, Chapter I, §4.3.
-/

public section

namespace TauCeti

open ContCohomology Subgroup

universe u v w

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the trivial
-- action installed below is the one the explicit `H²(G, 𝔽_p)` is stated against.
attribute [local instance 2000] Ring.toAddCommGroup

variable {p : ℕ} [Fact p.Prime]

section Quotient

variable {X : Type u} [Finite X] [DistribMulAction (freeProP p X) (ZMod p)]
  [ContinuousSMul (freeProP p X) (ZMod p)] {R : Subgroup (freeProP p X)} [R.Normal]
  (hRc : IsClosed (R : Set (freeProP p X)))
  (htrivF : ∀ (g : freeProP p X) (m : ZMod p), g • m = m)
include hRc htrivF

/-- **The five-term count for a quotient of a free pro-`p` group of finite rank.** Let `F` be the
free pro-`p` group on a finite type `X`, acting trivially on `𝔽_p`, and let `R` be a closed normal
subgroup with `R ⧸ Rᵖ[R, F]` topologically finitely generated. Then
`|H²(F ⧸ R, 𝔽_p ^ R)| · p ^ #X = p ^ (d(F ⧸ R) + d(R ⧸ Rᵖ[R, F]))`: the five-term sequence of
`1 → R → F → F ⧸ R → 1` has `|H¹(F, 𝔽_p)| = p ^ #X`, `|H¹(F ⧸ R, 𝔽_p ^ R)| = p ^ d(F ⧸ R)`,
`|H¹(R, 𝔽_p)^F| = p ^ d(R ⧸ Rᵖ[R, F])` and `H²(F, 𝔽_p) = 0`. -/
theorem natCard_H2_quotient_mul_pow_card_of_isClosed
    (h : IsTopologicallyFinitelyGenerated (R ⧸ (pLowerCentralStep p R).subgroupOf R)) :
    Nat.card (H2 (freeProP p X ⧸ R) (FixedPoints.addSubgroup R (ZMod p))) * p ^ Nat.card X =
      p ^ (topologicalGeneratorRankNat (freeProP p X ⧸ R)
        ((isTopologicallyFinitelyGenerated_freeProP p X).quotient R) +
        topologicalGeneratorRankNat (R ⧸ (pLowerCentralStep p R).subgroupOf R) h) := by
  -- Closedness of `R` supplies the profinite instances on `F ⧸ R`.
  have := hRc
  have := freeProP.subsingleton_H2_zmod (p := p) (X := X)
  have hF : Nat.card (H1 (freeProP p X) (ZMod p)) = p ^ Nat.card X := by
    rw [(isProP_freeProP p X).natCard_H1_of_natCard_eq
      (isTopologicallyFinitelyGenerated_freeProP p X) (Nat.card_zmod p) htrivF,
      topologicalGeneratorRankNat_freeProP]
  have hA : Nat.card (FixedPoints.addSubgroup R (ZMod p)) = p := by
    rw [fixedPoints_addSubgroup_eq_top_of_smul_eq (ZMod p) R htrivF, AddSubgroup.card_top,
      Nat.card_zmod]
  have hQtriv : ∀ (g : freeProP p X ⧸ R) (m : FixedPoints.addSubgroup R (ZMod p)), g • m = m :=
    fun g m ↦ by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
      rw [coe_quotient_smul_fixedPoints_addSubgroup]
      exact Subtype.ext ((coe_smul_fixedPoints_addSubgroup x m).trans (htrivF x m))
  have hQ := ((isProP_freeProP p X).quotient R).natCard_H1_of_natCard_eq
    ((isTopologicallyFinitelyGenerated_freeProP p X).quotient R) hA hQtriv
  have hC := natCard_H1ConjInvariants hRc htrivF h
  have key := natCard_H1_mul_natCard_H2_quotient_of_subsingleton (freeProP p X) (ZMod p) R hRc
  rw [hF, hQ, hC, ← pow_add] at key
  rw [mul_comm, key]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)]
  (e : freeProP p X ⧸ R ≃ₜ* G) (htriv : ∀ (g : G) (m : ZMod p), g • m = m)
  (hfg : IsTopologicallyFinitelyGenerated G)
include e htriv hfg

/-- **The five-term count for a group presented by a free pro-`p` group of finite rank.** Let `F`
be the free pro-`p` group on a finite type `X`, let `R` be a closed normal subgroup with
`R ⧸ Rᵖ[R, F]` topologically finitely generated, and let `G ≅ F ⧸ R` act trivially on `𝔽_p`, as
does `F`. Then `|H²(G, 𝔽_p)| · p ^ #X = p ^ (d(G) + d(R ⧸ Rᵖ[R, F]))`. -/
theorem natCard_H2_mul_pow_card_of_isClosed
    (h : IsTopologicallyFinitelyGenerated (R ⧸ (pLowerCentralStep p R).subgroupOf R)) :
    Nat.card (H2 G (ZMod p)) * p ^ Nat.card X =
      p ^ (topologicalGeneratorRankNat G hfg +
        topologicalGeneratorRankNat (R ⧸ (pLowerCentralStep p R).subgroupOf R) h) := by
  have := hRc
  rw [← Nat.card_congr (h2QuotientEquiv e htrivF htriv).toEquiv,
    natCard_H2_quotient_mul_pow_card_of_isClosed hRc htrivF h, topologicalGeneratorRankNat_congr e]

/-- **`H²(G, 𝔽_p)` is finite for a finitely presented group.** Let `F` be the free pro-`p` group
on a finite type `X`, let `R` be a closed normal subgroup with `R ⧸ Rᵖ[R, F]` topologically finitely
generated, and let `G ≅ F ⧸ R` act trivially on `𝔽_p`, as does `F`. Then `H²(G, 𝔽_p)` is
finite. -/
theorem finite_H2_of_isClosed
    (h : IsTopologicallyFinitelyGenerated (R ⧸ (pLowerCentralStep p R).subgroupOf R)) :
    Finite (H2 G (ZMod p)) := by
  refine Nat.finite_of_card_ne_zero fun h0 ↦ ?_
  have := natCard_H2_mul_pow_card_of_isClosed hRc htrivF e htriv hfg h
  rw [h0, zero_mul] at this
  exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero this.symm

/-- **The generator, relation and normal-generator counts of a presentation.** Let `F` be the free
pro-`p` group on a finite type `X`, let `R` be a closed normal subgroup with `R ⧸ Rᵖ[R, F]`
topologically finitely generated, and let `G ≅ F ⧸ R` act trivially on `𝔽_p`, as does `F`. Then

```text
#X + dim H²(G, 𝔽_p) = d(G) + d(R ⧸ Rᵖ[R, F]),
```

where `d(R ⧸ Rᵖ[R, F])` is the least number of generators of `R` as a closed normal subgroup of
`F`. No minimality of the presentation is assumed. -/
theorem card_add_finrank_H2_of_isClosed
    (h : IsTopologicallyFinitelyGenerated (R ⧸ (pLowerCentralStep p R).subgroupOf R)) :
    Nat.card X + Module.finrank (ZMod p) (H2 G (ZMod p)) =
      topologicalGeneratorRankNat G hfg +
        topologicalGeneratorRankNat (R ⧸ (pLowerCentralStep p R).subgroupOf R) h := by
  have := finite_H2_of_isClosed hRc htrivF e htriv hfg h
  have key := natCard_H2_mul_pow_card_of_isClosed hRc htrivF e htriv hfg h
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, ← pow_add] at key
  have := Nat.pow_right_injective (Fact.out : p.Prime).two_le key
  omega

end Quotient

namespace presentedProP

section Relators

variable {X : Type u} {rels : Set (freeProP p X)}

omit [Fact p.Prime] in
/-- The relators, as a finite subset of their closed normal closure. -/
private theorem exists_finset_image_val_eq (hrels : rels.Finite) :
    ∃ s : Finset (normalClosure rels).topologicalClosure, s.card = Nat.card rels ∧
      Subtype.val '' (s : Set (normalClosure rels).topologicalClosure) = rels := by
  classical
  have hsub : ∀ x ∈ hrels.toFinset, x ∈ (normalClosure rels).topologicalClosure := fun x hx ↦
    le_topologicalClosure _ (subset_normalClosure (hrels.mem_toFinset.1 hx))
  have := hrels.fintype
  refine ⟨hrels.toFinset.subtype _, ?_, ?_⟩
  · rw [Finset.card_subtype, Finset.filter_true_of_mem hsub, hrels.card_toFinset,
      Nat.card_eq_fintype_card]
  · rw [← Function.Embedding.coe_subtype, ← Finset.coe_map, Finset.subtype_map_of_mem hsub,
      hrels.coe_toFinset]

/-- **A finite relator set normally generates its relation subgroup finitely.** For a finite set of
relators `rels`, with closed normal closure `R` in the free pro-`p` group `F`, the quotient
`R ⧸ Rᵖ[R, F]` is topologically finitely generated. -/
theorem isTopologicallyFinitelyGenerated_quotient_pLowerCentralStep_of_finite
    (hrels : rels.Finite) :
    IsTopologicallyFinitelyGenerated ((normalClosure rels).topologicalClosure ⧸
      (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
        (normalClosure rels).topologicalClosure) := by
  obtain ⟨s, -, hs⟩ := exists_finset_image_val_eq hrels
  exact ((isProP_freeProP p X).isTopologicallyFinitelyGenerated_quotient_pLowerCentralStep_iff
    Fact.out (isClosed_topologicalClosure _)).2 ⟨s, by rw [hs]⟩

/-- **The relators bound the least number of normal generators.** For a finite set of relators
`rels` with closed normal closure `R` in the free pro-`p` group `F`, the topological generator rank
of `R ⧸ Rᵖ[R, F]`, which is the least number of generators of `R` as a closed normal subgroup, is
at most the number of relators. -/
theorem topologicalGeneratorRankNat_quotient_pLowerCentralStep_le_card (hrels : rels.Finite) :
    topologicalGeneratorRankNat ((normalClosure rels).topologicalClosure ⧸
      (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
        (normalClosure rels).topologicalClosure)
      (isTopologicallyFinitelyGenerated_quotient_pLowerCentralStep_of_finite hrels) ≤
      Nat.card rels := by
  obtain ⟨s, hcard, hs⟩ := exists_finset_image_val_eq hrels
  exact ((isProP_freeProP p X).topologicalGeneratorRankNat_quotient_pLowerCentralStep_le_iff
    Fact.out (isClosed_topologicalClosure _) _ _).2 ⟨s, hcard.le, by rw [hs]⟩

end Relators

section Count

variable {X : Type u} [Finite X] {rels : Set (freeProP p X)} {G : Type v} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod p)]
  [ContinuousSMul G (ZMod p)] (e : presentedProP p X rels ≃ₜ* G)
  (htriv : ∀ (g : G) (m : ZMod p), g • m = m)
include e htriv

/-- **The generator, relation and normal-generator counts of a presentation.** Let `G ≅ ⟨X ∣ rels⟩`
be a presentation, on a finite type `X`, of a group acting trivially on `𝔽_p`, and let `R` be the
closed normal closure of the relators, with `R ⧸ Rᵖ[R, F]` topologically finitely generated. Then

```text
#X + dim H²(G, 𝔽_p) = d(G) + d(R ⧸ Rᵖ[R, F]),
```

where `d(R ⧸ Rᵖ[R, F])` is the least number of generators of `R` as a closed normal subgroup of
`F`. The presentation need not be minimal. -/
theorem card_add_finrank_H2 (hfg : IsTopologicallyFinitelyGenerated G)
    (h : IsTopologicallyFinitelyGenerated ((normalClosure rels).topologicalClosure ⧸
      (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
        (normalClosure rels).topologicalClosure)) :
    Nat.card X + Module.finrank (ZMod p) (H2 G (ZMod p)) =
      topologicalGeneratorRankNat G hfg +
        topologicalGeneratorRankNat ((normalClosure rels).topologicalClosure ⧸
          (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
            (normalClosure rels).topologicalClosure) h := by
  -- The count needs an action of `F` on `𝔽_p`; the trivial one is installed.
  let : DistribMulAction (freeProP p X) (ZMod p) :=
    DistribMulAction.compHom (ZMod p) (1 : freeProP p X →* (ZMod p)ˣ)
  have htrivF : ∀ (g : freeProP p X) (m : ZMod p), g • m = m := fun _ m ↦ one_smul (ZMod p)ˣ m
  have : ContinuousSMul (freeProP p X) (ZMod p) :=
    ⟨continuous_snd.congr fun x ↦ (htrivF x.1 x.2).symm⟩
  exact card_add_finrank_H2_of_isClosed (isClosed_topologicalClosure _) htrivF e htriv hfg h

/-- **`H²(G, 𝔽_p)` is finite for a finitely presented pro-`p` group.** Let `G ≅ ⟨X ∣ rels⟩` be a
presentation, on a finite type `X` with finitely many relators, of a group acting trivially on
`𝔽_p`. Then `H²(G, 𝔽_p)` is finite. -/
theorem finite_H2_of_finite (hrels : rels.Finite) : Finite (H2 G (ZMod p)) := by
  -- The count needs an action of `F` on `𝔽_p`; the trivial one is installed.
  let : DistribMulAction (freeProP p X) (ZMod p) :=
    DistribMulAction.compHom (ZMod p) (1 : freeProP p X →* (ZMod p)ˣ)
  have htrivF : ∀ (g : freeProP p X) (m : ZMod p), g • m = m := fun _ m ↦ one_smul (ZMod p)ˣ m
  have : ContinuousSMul (freeProP p X) (ZMod p) :=
    ⟨continuous_snd.congr fun x ↦ (htrivF x.1 x.2).symm⟩
  exact finite_H2_of_isClosed (isClosed_topologicalClosure _) htrivF e htriv
    ((isTopologicallyFinitelyGenerated_congr e).1 isTopologicallyFinitelyGenerated)
    (isTopologicallyFinitelyGenerated_quotient_pLowerCentralStep_of_finite hrels)

end Count

end presentedProP

section Deficiency

variable (p) (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The deficiency** `def(G) = d(G) - r(G)` of a topologically finitely generated topological
group, in `ℤ`: the topological generator rank minus the relation rank `dim_{𝔽_p} H²(G, 𝔽_p)`. The
subtraction is in `ℤ`, so no natural-number truncation occurs; for a pro-`p` group with a finite
presentation `⟨X ∣ rels⟩` it is the largest value of `#X - #rels`
(`TauCeti.presentedProP.card_sub_card_le_deficiency`). -/
noncomputable def deficiency (hfg : IsTopologicallyFinitelyGenerated G) : ℤ :=
  (topologicalGeneratorRankNat G hfg : ℤ) - Module.finrank (ZMod p) (cohomFp p G 2)

/-- The deficiency is the generator rank minus the relation rank. -/
theorem deficiency_def (hfg : IsTopologicallyFinitelyGenerated G) :
    deficiency p G hfg =
      (topologicalGeneratorRankNat G hfg : ℤ) - Module.finrank (ZMod p) (cohomFp p G 2) :=
  (rfl)

/-- **`d(G) = def(G) + r(G)`**: the generator rank is the deficiency plus the relation rank. -/
theorem deficiency_add_finrank_cohomFp_two (hfg : IsTopologicallyFinitelyGenerated G) :
    deficiency p G hfg + Module.finrank (ZMod p) (cohomFp p G 2) =
      topologicalGeneratorRankNat G hfg := by
  rw [deficiency_def, sub_add_cancel]

variable {G} in
/-- **The deficiency is an isomorphism invariant.** -/
theorem deficiency_congr [LocallyCompactSpace G] {H : Type w} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] (e : G ≃ₜ* H)
    (hG : IsTopologicallyFinitelyGenerated G) (hH : IsTopologicallyFinitelyGenerated H) :
    deficiency p G hG = deficiency p H hH := by
  rw [deficiency_def, deficiency_def, topologicalGeneratorRankNat_congr e,
    finrank_cohomFp_two_congr p e]

end Deficiency

namespace presentedProP

variable {X : Type u} [Finite X] {rels : Set (freeProP p X)} {G : Type v} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  (e : presentedProP p X rels ≃ₜ* G)
include e

/-- **The generator, relation and normal-generator counts of a presentation**, on the canonical
carrier. Let `G ≅ ⟨X ∣ rels⟩` be a presentation on a finite type `X`, and let `R` be the closed
normal closure of the relators, with `R ⧸ Rᵖ[R, F]` topologically finitely generated. Then

```text
#X + dim H²(G, 𝔽_p) = d(G) + d(R ⧸ Rᵖ[R, F]),
```

where `d(R ⧸ Rᵖ[R, F])` is the least number of generators of `R` as a closed normal subgroup of
`F`. The presentation need not be minimal. -/
theorem card_add_finrank_cohomFp_two (hfg : IsTopologicallyFinitelyGenerated G)
    (h : IsTopologicallyFinitelyGenerated ((normalClosure rels).topologicalClosure ⧸
      (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
        (normalClosure rels).topologicalClosure)) :
    Nat.card X + Module.finrank (ZMod p) (cohomFp p G 2) =
      topologicalGeneratorRankNat G hfg +
        topologicalGeneratorRankNat ((normalClosure rels).topologicalClosure ⧸
          (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
            (normalClosure rels).topologicalClosure) h := by
  -- The explicit `H²(G, 𝔽_p)` needs an action of `G` on `𝔽_p`; the trivial one is installed.
  let : DistribMulAction G (ZMod p) := DistribMulAction.compHom (ZMod p) (1 : G →* (ZMod p)ˣ)
  have htriv : ∀ (g : G) (m : ZMod p), g • m = m := fun _ m ↦ one_smul (ZMod p)ˣ m
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd.congr fun x ↦ (htriv x.1 x.2).symm⟩
  rw [(cohomFpLinearEquivH2 p G htriv).finrank_eq]
  exact card_add_finrank_H2 e htriv hfg h

/-- **`H²(G, 𝔽_p)` is finite-dimensional for a finitely presented pro-`p` group**, so that the
relation rank `r(G) = dim_{𝔽_p} H²(G, 𝔽_p)` is a natural number. -/
theorem module_finite_cohomFp_two_of_finite (hrels : rels.Finite) :
    Module.Finite (ZMod p) (cohomFp p G 2) := by
  -- The explicit `H²(G, 𝔽_p)` needs an action of `G` on `𝔽_p`; the trivial one is installed.
  let : DistribMulAction G (ZMod p) := DistribMulAction.compHom (ZMod p) (1 : G →* (ZMod p)ˣ)
  have htriv : ∀ (g : G) (m : ZMod p), g • m = m := fun _ m ↦ one_smul (ZMod p)ˣ m
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd.congr fun x ↦ (htriv x.1 x.2).symm⟩
  have := finite_H2_of_finite e htriv hrels
  exact Module.Finite.equiv (cohomFpLinearEquivH2 p G htriv).symm

/-- **The deficiency inequality.** For a presentation `G ≅ ⟨X ∣ rels⟩` of a pro-`p` group on a
finite type `X` with finitely many relators, `#X - #rels ≤ def(G)` in `ℤ`: a presentation with
`#X` generators needs at least `#X - def(G)` relators. -/
theorem card_sub_card_le_deficiency (hrels : rels.Finite)
    (hfg : IsTopologicallyFinitelyGenerated G) :
    (Nat.card X : ℤ) - Nat.card rels ≤ deficiency p G hfg := by
  have h1 := card_add_finrank_cohomFp_two e hfg
    (isTopologicallyFinitelyGenerated_quotient_pLowerCentralStep_of_finite hrels)
  have h2 := topologicalGeneratorRankNat_quotient_pLowerCentralStep_le_card hrels
  rw [deficiency_def]
  omega

/-- **Equality in the deficiency inequality.** For a presentation `G ≅ ⟨X ∣ rels⟩` of a pro-`p`
group on a finite type `X` with finitely many relators, `#X - #rels = def(G)` exactly when the
number of relators is the least number of generators of the relation subgroup `R` as a closed
normal subgroup, that is `d(R ⧸ Rᵖ[R, F])`. So a presentation whose relators form a minimal set of
normal generators realizes the deficiency. -/
theorem card_sub_card_eq_deficiency_iff (hrels : rels.Finite)
    (hfg : IsTopologicallyFinitelyGenerated G) :
    (Nat.card X : ℤ) - Nat.card rels = deficiency p G hfg ↔
      Nat.card rels = topologicalGeneratorRankNat ((normalClosure rels).topologicalClosure ⧸
        (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
          (normalClosure rels).topologicalClosure)
        (isTopologicallyFinitelyGenerated_quotient_pLowerCentralStep_of_finite hrels) := by
  have h1 := card_add_finrank_cohomFp_two e hfg
    (isTopologicallyFinitelyGenerated_quotient_pLowerCentralStep_of_finite hrels)
  rw [deficiency_def]
  omega

end presentedProP

end TauCeti
