/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Rank
public import TauCeti.Topology.Algebra.Group.Profinite.Presentation

/-!
# Minimal presentations of pro-`p` groups

A continuous surjection `f : G ↠ H` of pro-`p` groups, with `G` topologically finitely generated,
cannot raise the topological generator rank. This file identifies when the rank is preserved: the
Frattini quotients form a surjection `G ⧸ Φ(G) ↠ H ⧸ Φ(H)` of `𝔽_p`-vector spaces whose kernel is
`(ker f) Φ(G) ⧸ Φ(G)`, so, counting orders through Burnside's basis theorem, `d(H) = d(G)` holds
exactly when `ker f ≤ Φ(G)`. The quantitative form is that `(ker f) Φ(G)` has index `p ^ d(H)` in
`G`.

Applied to the quotient map from a free pro-`p` group of finite rank onto a presented pro-`p`
group, this characterizes **minimal presentations**: a presentation `G ≅ ⟨X ∣ rels⟩` with `X`
finite is minimal, meaning `Nat.card X = d(G)`, exactly when every relator lies in the Frattini
subgroup `Φ(F) = closure (Fᵖ [F, F])` of the free pro-`p` group `F` on `X`. Every topologically
finitely generated pro-`p` group has such a presentation, on any finite type of cardinality `d(G)`.
This is the condition `R ≤ Φ(F)` on the relation subgroup under which the relation rank of `G` is
read off from the presentation, and it is the normalization a Demushkin relator satisfies.

## Main results

* `TauCeti.IsProP.index_proPFrattini_sup_ker`: along a continuous surjection `f : G ↠ H` onto a
  topologically finitely generated pro-`p` group, `Φ(G) ⊔ ker f` has index `p ^ d(H)`.
* `TauCeti.IsProP.topologicalGeneratorRankNat_eq_iff_ker_le_proPFrattini`: for a continuous
  surjection `f : G ↠ H` of pro-`p` groups with `G` topologically finitely generated,
  `d(H) = d(G)` exactly when `ker f ≤ Φ(G)`.
* `TauCeti.presentedProP.topologicalGeneratorRankNat_eq_card_iff`: a pro-`p` group presented on a
  finite type `X` has rank `Nat.card X` exactly when the relators lie in the Frattini subgroup of
  the free pro-`p` group on `X`.
* `TauCeti.presentedProP.subset_proPFrattini_iff_card_eq`: a presentation of `G` on a finite type
  `X` has its relators in the Frattini subgroup exactly when `Nat.card X = d(G)`.
* `TauCeti.IsProP.exists_subset_proPFrattini_continuousMulEquiv_presentedProP`: every
  topologically finitely generated pro-`p` group has a minimal presentation on any finite type of
  cardinality `d(G)`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8 and Section 7.8.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, Section III.9.
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), Section 1.
-/

public section

namespace TauCeti

universe u v

variable {p : ℕ} [hp : Fact p.Prime]

section Surjective

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [TotallyDisconnectedSpace H]

namespace IsProP

/-- Along a continuous surjection `f : G ↠ H` from a compact group onto a topologically finitely
generated profinite pro-`p` group, the subgroup `Φ(G) ⊔ ker f`, the preimage of the Frattini
subgroup of `H`, has index `p ^ d(H)` in `G`. -/
theorem index_proPFrattini_sup_ker (hH : IsProP p H) (hfg : IsTopologicallyFinitelyGenerated H)
    (f : G →* H) (hf : Continuous f) (hsurj : Function.Surjective f) :
    (proPFrattini p G ⊔ f.ker).index = p ^ topologicalGeneratorRankNat H hfg := by
  rw [← comap_proPFrattini_eq_of_surjective hp.out f hf hsurj,
    Subgroup.index_comap_of_surjective _ hsurj, Subgroup.index_eq_card,
    hH.natCard_quotient_proPFrattini hfg]

variable [TotallyDisconnectedSpace G]

/-- **Rank preservation along a surjection.** For a continuous surjection `f : G ↠ H` of profinite
pro-`p` groups with `G` topologically finitely generated, the topological generator rank of `H`
equals that of `G` exactly when the kernel of `f` lies in the Frattini subgroup of `G`. The
inequality `d(H) ≤ d(G)` is `TauCeti.topologicalGeneratorRankNat_le_of_surjective`. -/
theorem topologicalGeneratorRankNat_eq_iff_ker_le_proPFrattini (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) (f : G →* H) (hf : Continuous f)
    (hsurj : Function.Surjective f) :
    topologicalGeneratorRankNat H (hfg.of_surjective hf hsurj) =
        topologicalGeneratorRankNat G hfg ↔
      f.ker ≤ proPFrattini p G := by
  -- Both `Φ(G)` and `Φ(G) ⊔ ker f` have index a power of `p`, and the exponents are the two ranks.
  have hidx := index_proPFrattini_sup_ker (hG.of_surjective f hf hsurj)
    (hfg.of_surjective hf hsurj) f hf hsurj
  have hΦ : (proPFrattini p G).index = p ^ topologicalGeneratorRankNat G hfg := by
    rw [Subgroup.index_eq_card, hG.natCard_quotient_proPFrattini hfg]
  constructor
  · intro heq
    -- Equal ranks force the relative index of `Φ(G)` in `Φ(G) ⊔ ker f` to be `1`.
    have hmul := Subgroup.relIndex_mul_index
      (le_sup_left : proPFrattini p G ≤ proPFrattini p G ⊔ f.ker)
    rw [hidx, hΦ, heq] at hmul
    have hone : (proPFrattini p G).relIndex (proPFrattini p G ⊔ f.ker) = 1 :=
      Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos _) (by rw [hmul, one_mul])
    exact le_sup_right.trans (Subgroup.relIndex_eq_one.mp hone)
  · intro hle
    rw [sup_eq_left.mpr hle, hΦ] at hidx
    exact (Nat.pow_right_injective hp.out.two_le hidx).symm

end IsProP

end Surjective

namespace presentedProP

variable {X : Type u} (rels : Set (freeProP p X))

omit hp in
/-- The kernel of the quotient map onto a presented pro-`p` group is the closed normal closure of
the relators. -/
theorem ker_mk :
    (mk p rels : freeProP p X →* presentedProP p X rels).ker =
      (Subgroup.normalClosure rels).topologicalClosure :=
  Subgroup.ext fun r ↦ MonoidHom.mem_ker.trans (mk_eq_one_iff r)

variable [Finite X]

/-- **Minimal presentations.** A pro-`p` group presented on a finite type `X` has topological
generator rank `Nat.card X` exactly when every relator lies in the Frattini subgroup of the free
pro-`p` group on `X`. -/
theorem topologicalGeneratorRankNat_eq_card_iff :
    topologicalGeneratorRankNat (presentedProP p X rels) isTopologicallyFinitelyGenerated =
        Nat.card X ↔
      rels ⊆ proPFrattini p (freeProP p X) := by
  rw [← topologicalGeneratorRankNat_freeProP p (isTopologicallyFinitelyGenerated_freeProP p X),
    (isProP_freeProP p X).topologicalGeneratorRankNat_eq_iff_ker_le_proPFrattini
      (isTopologicallyFinitelyGenerated_freeProP p X) (mk p rels : freeProP p X →* _)
      (map_continuous (mk p rels)) (mk_surjective p rels),
    ker_mk, Subgroup.topologicalClosure_normalClosure_le_iff isClosed_proPFrattini]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A presentation `G ≅ ⟨X ∣ rels⟩` of a topologically finitely generated group on a finite type
`X` has all its relators in the Frattini subgroup of the free pro-`p` group on `X` exactly when it
is minimal, that is when `Nat.card X` is the topological generator rank of `G`. -/
theorem subset_proPFrattini_iff_card_eq (e : presentedProP p X rels ≃ₜ* G)
    (h : IsTopologicallyFinitelyGenerated G) :
    rels ⊆ proPFrattini p (freeProP p X) ↔ Nat.card X = topologicalGeneratorRankNat G h := by
  rw [← topologicalGeneratorRankNat_eq_card_iff, topologicalGeneratorRankNat_congr e, eq_comm]

end presentedProP

/-- **Existence of minimal presentations.** A topologically finitely generated pro-`p` group has a
presentation on any finite type of cardinality its topological generator rank, with all relators in
the Frattini subgroup of the free pro-`p` group. -/
theorem IsProP.exists_subset_proPFrattini_continuousMulEquiv_presentedProP {G : Type u} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : IsProP p G) (h : IsTopologicallyFinitelyGenerated G) (X : Type u) [Finite X]
    (hX : Nat.card X = topologicalGeneratorRankNat G h) :
    ∃ rels : Set (freeProP p X), rels ⊆ proPFrattini p (freeProP p X) ∧
      Nonempty (presentedProP p X rels ≃ₜ* G) := by
  obtain ⟨rels, ⟨e⟩⟩ := hG.exists_continuousMulEquiv_presentedProP h X hX.ge
  exact ⟨rels, (presentedProP.subset_proPFrattini_iff_card_eq rels e h).mpr hX, ⟨e⟩⟩

end TauCeti
