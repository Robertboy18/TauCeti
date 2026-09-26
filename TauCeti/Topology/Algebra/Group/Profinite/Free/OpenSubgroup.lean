/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Cohomology
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Serre
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.EulerCharacteristic

/-!
# Pro-`p` Nielsen–Schreier for open subgroups

An open subgroup `U` of index `m` in a free pro-`p` group `F` of finite rank `n ≥ 1` is free pro-`p`
of rank `1 + m * (n - 1)`.

The route is cohomological. The vanishing of `H²(F, M)` on finite discrete `p`-primary modules
passes to `U` through Shapiro's lemma (`TauCeti.ContCohomology.subsingleton_H2_of_isOpen`), which
makes `U` projective and hence, by Serre's theorem
`TauCeti.IsProP.nonempty_continuousMulEquiv_freeProP_of_isProjective`, free pro-`p` of rank
`d(U)`. The rank is computed by the two-term Euler formula
`TauCeti.IsProP.topologicalGeneratorRankNat_add_index`: `d(U) + m = 1 + m * n`, so
`d(U) = 1 + m * (n - 1)` once `n ≥ 1`. The Schreier bound
`TauCeti.topologicalGeneratorRankNat_le_of_openSubgroup` is therefore an equality for free
pro-`p` groups.

Closed subgroups that are not open are free pro-`p` of possibly infinite rank; that statement needs
free pro-`p` groups on a pointed profinite space and is not made here.

## Main results

* `TauCeti.freeProP.topologicalGeneratorRankNat_add_index`: `d(U) + [F : U] = 1 + [F : U] * n`.
* `TauCeti.freeProP.topologicalGeneratorRankNat_openSubgroup`: `d(U) = 1 + [F : U] * (n - 1)` for
  `n ≥ 1`.
* `TauCeti.freeProP.isProjective_openSubgroup`: an open subgroup of a free pro-`p` group is
  projective.
* `TauCeti.freeProP.nonempty_continuousMulEquiv_openSubgroup` and
  `TauCeti.freeProP.nonempty_continuousMulEquiv_openSubgroup_fin`: **pro-`p` Nielsen–Schreier for
  open subgroups**, `U ≅ freeProP p (Fin (1 + [F : U] * (n - 1)))`.

## References

* H. Koch, *Galois Theory of `p`-Extensions*, Example 6.3.
* J.-P. Serre, *Galois Cohomology*, Ch. I, §4.2.
* L. Ribes and P. Zalesskii, *Profinite Groups*, Thm. 3.6.2, for the transversal proof.
-/

public section

namespace TauCeti

open ContCohomology

universe u v w

namespace freeProP

variable {p : ℕ} [hp : Fact p.Prime] {X : Type u} [Finite X]

/-- **The Nielsen–Schreier rank formula for open subgroups, additive form.** For an open subgroup
`U` of the free pro-`p` group on a finite type `X`, `d(U) + [F : U] = 1 + [F : U] * #X`. -/
theorem topologicalGeneratorRankNat_add_index (U : OpenSubgroup (freeProP p X)) :
    topologicalGeneratorRankNat U.toSubgroup
        ((isTopologicallyFinitelyGenerated_freeProP p X).of_openSubgroup U) + U.toSubgroup.index =
      1 + U.toSubgroup.index * Nat.card X := by
  have h := (isProP_freeProP p X).topologicalGeneratorRankNat_add_index
    (isTopologicallyFinitelyGenerated_freeProP p X)
    (fun A _ _ _ _ _ _ hA _ ↦ subsingleton_H2_of_isPPrimaryTorsion
      (isPPrimaryTorsion_of_natCard_eq_pow (hA.trans (pow_one p).symm))) U
  rwa [topologicalGeneratorRankNat_freeProP] at h

/-- **The Nielsen–Schreier rank formula for open subgroups.** For an open subgroup `U` of index
`m` in the free pro-`p` group on a nonempty finite type `X` of cardinality `n`,
`d(U) = 1 + m * (n - 1)`. -/
theorem topologicalGeneratorRankNat_openSubgroup [Nonempty X] (U : OpenSubgroup (freeProP p X)) :
    topologicalGeneratorRankNat U.toSubgroup
        ((isTopologicallyFinitelyGenerated_freeProP p X).of_openSubgroup U) =
      1 + U.toSubgroup.index * (Nat.card X - 1) := by
  have h := topologicalGeneratorRankNat_add_index U
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.card_pos (α := X)).ne'
  rw [hn, Nat.succ_sub_one]
  rw [hn, Nat.succ_eq_add_one, mul_add, mul_one] at h
  omega

omit [Finite X] in
/-- **An open subgroup of a free pro-`p` group is projective.** The vanishing of `H²` on finite
discrete `p`-primary modules passes from the free group to `U` through Shapiro's lemma, and
solves the finite embedding problems of `U` with `p`-group kernel. -/
theorem isProjective_openSubgroup (U : OpenSubgroup (freeProP p X)) :
    IsProjective.{u, v, w} p U.toSubgroup := by
  have : CompactSpace U.toSubgroup := isCompact_iff_compactSpace.mp U.isClosed.isCompact
  refine isProjective_of_hasPGroupSolutions
    (hasElementaryAbelianSolutions_of_subsingleton_continuousCohomology_two ?_).hasPGroupSolutions
  intro M _ _ _ _ _ _ hM
  have : Subsingleton (H2 U.toSubgroup M) :=
    subsingleton_H2_of_isOpen U.isOpen
      (fun M _ _ _ _ _ _ hM ↦ subsingleton_H2_of_isPPrimaryTorsion hM) M
      (isPPrimaryTorsion_iff.2 fun m ↦ ⟨1, by rw [pow_one]; exact hM m⟩)
  exact (explicitH2AddEquivContinuousCohomology U.toSubgroup M).toEquiv.symm.subsingleton

/-- **Pro-`p` Nielsen–Schreier for open subgroups.** An open subgroup `U` of the free pro-`p` group
on a finite type `X` is free pro-`p`: it is topologically isomorphic to the free pro-`p` group on
any finite type of cardinality `d(U)`. -/
theorem nonempty_continuousMulEquiv_openSubgroup (U : OpenSubgroup (freeProP p X)) (Y : Type u)
    [Finite Y] (hY : Nat.card Y = topologicalGeneratorRankNat U.toSubgroup
      ((isTopologicallyFinitelyGenerated_freeProP p X).of_openSubgroup U)) :
    Nonempty (U.toSubgroup ≃ₜ* freeProP p Y) :=
  have : CompactSpace U.toSubgroup := isCompact_iff_compactSpace.mp U.isClosed.isCompact
  IsProP.nonempty_continuousMulEquiv_freeProP_of_isProjective ((isProP_freeProP p X).subgroup _)
    _ (isProjective_openSubgroup U) Y hY

/-- **Pro-`p` Nielsen–Schreier for open subgroups, with the index-rank formula.** An open subgroup
`U` of index `m` in the free pro-`p` group of rank `n ≥ 1` is free pro-`p` of rank
`1 + m * (n - 1)`. -/
theorem nonempty_continuousMulEquiv_openSubgroup_fin {n : ℕ} (hn : n ≠ 0)
    (U : OpenSubgroup (freeProP p (Fin n))) :
    Nonempty (U.toSubgroup ≃ₜ* freeProP p (Fin (1 + U.toSubgroup.index * (n - 1)))) :=
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 (Nat.pos_of_ne_zero hn)
  nonempty_continuousMulEquiv_openSubgroup U _ (by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin, topologicalGeneratorRankNat_openSubgroup,
      Nat.card_eq_fintype_card, Fintype.card_fin])

end freeProP

end TauCeti
