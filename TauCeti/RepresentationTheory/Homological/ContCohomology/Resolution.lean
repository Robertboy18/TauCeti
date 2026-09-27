/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Pointwise formulas for the coinduced resolution

Mathlib computes the continuous cohomology of a topological representation `X` from the coinduced
resolution `TopRep.resolutionX X n`, the iterated function space `C(G, C(G, …, C(G, X)))`, whose
differential `TopRep.d` is defined recursively by `d (n + 1) F x = F - d n (F x)`. This file
records the pointwise formulas that the recursion gives for the action and for the differential on
a successor level, and their consequence that evaluation at any point `x : G` contracts the
resolution: `d n (F x) + (d (n + 1) F) x = F`, summed over finitely many points. Evaluation at a
point is not `G`-equivariant, so the contraction does not descend to the invariants, which are the
homogeneous cochains; it is nevertheless what drives the acyclicity of coinduced modules, and a sum
of such contractions over suitably chosen points can descend.

## Main results

* `TopRep.resolutionX_succ_ρ_apply_apply` and `TopRep.hom_d_succ_apply_apply`: the action and
  the differential on a successor level of the resolution, at a point.
* `TopRep.d_sum_apply_add_sum_d_apply`: evaluation at finitely many points, summed, contracts the
  coinduced resolution up to the number of points.
-/

public section

namespace TopRep

variable {k G : Type*} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (X : TopRep k G)

/-- The action on a successor level of the coinduced resolution, at a point:
`(g • F) x = g • F (g⁻¹ * x)`. -/
@[simp]
theorem resolutionX_succ_ρ_apply_apply (n : ℕ) (g : G) (F : (resolutionX X (n + 1)).V) (x : G) :
    ((resolutionX X (n + 1)).ρ g F) x = (resolutionX X n).ρ g (F (g⁻¹ * x)) :=
  ContRepresentation.coind₁_apply_apply (resolutionX X n).ρ g F x

/-- The successor differential of the coinduced resolution, at a point:
`(d (n + 1) F) x = F - d n (F x)`. -/
@[simp]
theorem hom_d_succ_apply_apply (n : ℕ) (F : (resolutionX X (n + 1)).V) (x : G) :
    ((d X (n + 1)).hom F) x = F - (d X n).hom (F x) :=
  (rfl)

/-- **Summed evaluations contract the coinduced resolution up to a multiple.** For an element
`F : C(G, Xₘ)` of the degree `m + 1` term of the coinduced resolution and finitely many points
`σ i` of `G`, `dₘ (∑ᵢ F (σ i)) + ∑ᵢ (dₘ₊₁ F) (σ i) = |ι| • F`. Each summand is the identity
`dₘ (F x) + (dₘ₊₁ F) x = F` saying that evaluation at a point contracts the resolution. -/
theorem d_sum_apply_add_sum_d_apply {ι : Type*} [Fintype ι] (σ : ι → G) (m : ℕ)
    (F : (resolutionX X (m + 1)).V) :
    (d X m).hom (∑ i, (F : C(G, (resolutionX X m).V)) (σ i)) +
      ∑ i, ((d X (m + 1)).hom F : C(G, (resolutionX X (m + 1)).V)) (σ i) =
        Fintype.card ι • F := by
  rw [map_sum, ← Finset.sum_add_distrib]
  simp [hom_d_succ, ContIntertwiningMap.sub_apply]

end TopRep
