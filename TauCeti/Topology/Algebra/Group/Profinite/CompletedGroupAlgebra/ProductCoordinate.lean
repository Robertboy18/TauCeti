/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import TauCeti.Algebra.MonoidAlgebra.PowerSeries
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.PowerSeries
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Prod

/-!
# The power-series coordinate of `ℤ_p[[C × Γ]]`, and the dyadic coordinate

For a finite discrete group `C` and an infinite procyclic pro-`p` group `Γ` with topological
generator `γ`, so that `Γ ≅ ℤ_p`, the completed group algebra `ℤ_p[[C × Γ]]` is the power-series
ring over the group ring `ℤ_p[C]`:

```text
ℤ_p[C]⟦X⟧ ≃ₐ[ℤ_p] ℤ_p[[C × Γ]],   X ↦ (1, γ) - 1,   c ↦ (c, 1).
```

This is `TauCeti.completedGroupAlgebra.prodPowerSeriesCoordinate`, the composite of three
isomorphisms: `ℤ_p[C]⟦X⟧ ≅ ℤ_p⟦X⟧[C]` (`TauCeti.MonoidAlgebra.powerSeriesAlgEquiv`, `C` finite),
the power-series coordinate `ℤ_p⟦X⟧ ≅ ℤ_p[[Γ]]` of the Iwasawa algebra applied to the
coefficients (`TauCeti.completedGroupAlgebra.powerSeriesCoordinate`), and
`ℤ_p[[Γ]][C] ≅ ℤ_p[[C × Γ]]` (`TauCeti.completedGroupAlgebra.monoidAlgebraProdEquiv`). As for
the procyclic coordinate, it depends on the generator `γ`.

The case `p = 2`, `C = C₂ = Multiplicative (ZMod 2)` and `Γ = ℤ₂` is the **dyadic coordinate**
`TauCeti.completedGroupAlgebra.dyadicCoordinate`: for a group `Γ` with a topological isomorphism
`e : Γ ≃ₜ* C₂ × ℤ₂`, it identifies `ℤ₂[[Γ]]` with `ℤ₂[C₂]⟦X⟧`, sending `X` to `γ - 1` for the
generator `γ = e.symm (1, 1)` of the `ℤ₂`-factor and the group element `σ` of `C₂` to
`e.symm (σ, 1)`. This is the shape `Γ ≅ C₂ × ℤ₂` of the image `{±1} × (1 + 2^f ℤ₂)` of the
canonical character of an even-rank Demushkin group with `q = 2`, over which Labute's argument for
that case runs (Labute, §4, p. 122), and `ℤ₂[C₂]` is its coefficient ring. Here
`Multiplicative (ZMod 2)` is a genuine cyclic group of order two, not `ZMod 2` read as a
multiplicative monoid, whose monoid algebra would be a different ring.

## Main definitions

* `TauCeti.completedGroupAlgebra.prodPowerSeriesCoordinate C hΓ hγ`: the isomorphism
  `ℤ_p[C]⟦X⟧ ≃ₐ[ℤ_p] ℤ_p[[C × Γ]]`, with `prodPowerSeriesCoordinate_X` and
  `prodPowerSeriesCoordinate_C_single` as its values on `X` and on the group ring.
* `TauCeti.completedGroupAlgebra.dyadicCoordinate e`: the isomorphism
  `ℤ₂[C₂]⟦X⟧ ≃ₐ[ℤ₂] ℤ₂[[Γ]]` for `e : Γ ≃ₜ* C₂ × ℤ₂`, with `dyadicCoordinate_X` and
  `dyadicCoordinate_C_single`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), Section 4.
-/

public section

open PowerSeries

namespace TauCeti.completedGroupAlgebra

section ProdPowerSeries

variable {p : ℕ} [Fact p.Prime] (C : Type*) [Group C] [TopologicalSpace C] [DiscreteTopology C]
  [Finite C] {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [IsMulCommutative Γ] [TotallyDisconnectedSpace Γ] [Infinite Γ] (hΓ : IsProP p Γ) {γ : Γ}
  (hγ : (Subgroup.closure ({γ} : Set Γ)).topologicalClosure = ⊤)

/-- **The power-series coordinate of `ℤ_p[[C × Γ]]`.** For a finite discrete group `C` and a
topological generator `γ` of the infinite commutative pro-`p` group `Γ` (so that `Γ ≅ ℤ_p`), the
completed group algebra of `C × Γ` is the power-series ring over the group ring `ℤ_p[C]`, with
`X ↦ (1, γ) - 1` and the group element `c` going to `(c, 1)`. The coordinate depends on `γ`. -/
noncomputable def prodPowerSeriesCoordinate :
    PowerSeries (MonoidAlgebra ℤ_[p] C) ≃ₐ[ℤ_[p]] completedGroupAlgebra ℤ_[p] (C × Γ) :=
  (MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p] C).symm.trans
    ((MonoidAlgebra.mapAlgEquiv ℤ_[p] C (powerSeriesCoordinate hΓ hγ)).trans
      (monoidAlgebraProdEquiv ℤ_[p] C Γ))

/-- The coordinate sends `X` to `(1, γ) - 1`. -/
@[simp]
theorem prodPowerSeriesCoordinate_X :
    prodPowerSeriesCoordinate C hΓ hγ PowerSeries.X = of ℤ_[p] (C × Γ) (1, γ) - 1 := by
  simp [prodPowerSeriesCoordinate]

/-- The coordinate sends `1 + X` to the group element `(1, γ)`. -/
@[simp]
theorem prodPowerSeriesCoordinate_one_add_X :
    prodPowerSeriesCoordinate C hΓ hγ (1 + PowerSeries.X) = of ℤ_[p] (C × Γ) (1, γ) := by
  rw [map_add, map_one, prodPowerSeriesCoordinate_X, add_sub_cancel]

/-- The coordinate sends the constant `a · c` of the group ring to `a` times the group element
`(c, 1)`. -/
@[simp]
theorem prodPowerSeriesCoordinate_C_single (c : C) (a : ℤ_[p]) :
    prodPowerSeriesCoordinate C hΓ hγ (PowerSeries.C (MonoidAlgebra.single c a)) =
      algebraMap ℤ_[p] (completedGroupAlgebra ℤ_[p] (C × Γ)) a * of ℤ_[p] (C × Γ) (c, 1) := by
  simp [prodPowerSeriesCoordinate, monoidAlgebraProdHom_single]

/-- The coordinate sends the group element `c` of the group ring to the group element `(c, 1)`. -/
theorem prodPowerSeriesCoordinate_C_single_one (c : C) :
    prodPowerSeriesCoordinate C hΓ hγ (PowerSeries.C (MonoidAlgebra.single c 1)) =
      of ℤ_[p] (C × Γ) (c, 1) := by
  rw [prodPowerSeriesCoordinate_C_single, map_one, one_mul]

/-- The inverse coordinate sends the group element `(c, 1)` to the group element `c` of the
group ring. -/
@[simp]
theorem prodPowerSeriesCoordinate_symm_of_inl (c : C) :
    (prodPowerSeriesCoordinate C hΓ hγ).symm (of ℤ_[p] (C × Γ) (c, 1)) =
      PowerSeries.C (MonoidAlgebra.single c 1) :=
  (prodPowerSeriesCoordinate C hΓ hγ).symm_apply_eq.mpr
    (prodPowerSeriesCoordinate_C_single_one C hΓ hγ c).symm

/-- The inverse coordinate sends the group element `(1, γ)` to `1 + X`. -/
@[simp]
theorem prodPowerSeriesCoordinate_symm_of_inr :
    (prodPowerSeriesCoordinate C hΓ hγ).symm (of ℤ_[p] (C × Γ) (1, γ)) = 1 + PowerSeries.X :=
  (prodPowerSeriesCoordinate C hΓ hγ).symm_apply_eq.mpr
    (prodPowerSeriesCoordinate_one_add_X C hΓ hγ).symm

end ProdPowerSeries

section Dyadic

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
  (e : Γ ≃ₜ* Multiplicative (ZMod 2) × Multiplicative ℤ_[2])

/-- **The dyadic coordinate.** For a group `Γ ≅ C₂ × ℤ₂`, with `C₂ = Multiplicative (ZMod 2)`,
the completed group algebra `ℤ₂[[Γ]]` is the power-series ring over the group ring `ℤ₂[C₂]`,
with `X ↦ γ - 1` for the topological generator `γ = e.symm (1, 1)` of the `ℤ₂`-factor and the
group element `σ` of `C₂` going to `e.symm (σ, 1)`. This is the coefficient ring of Labute's
treatment of the even-rank Demushkin groups with `q = 2` whose canonical character has image
`{±1} × (1 + 2^f ℤ₂)`. -/
noncomputable def dyadicCoordinate :
    PowerSeries (MonoidAlgebra ℤ_[2] (Multiplicative (ZMod 2))) ≃ₐ[ℤ_[2]]
      completedGroupAlgebra ℤ_[2] Γ :=
  (prodPowerSeriesCoordinate (Multiplicative (ZMod 2)) (isProP_multiplicative_padicInt 2)
    (topologicallyGenerates_ofAdd_one_padicInt 2)).trans (domCongr ℤ_[2] e.symm)

/-- The dyadic coordinate sends `X` to `γ - 1`, for the generator `γ = e.symm (1, 1)` of the
`ℤ₂`-factor. -/
@[simp]
theorem dyadicCoordinate_X :
    dyadicCoordinate e PowerSeries.X = of ℤ_[2] Γ (e.symm (1, Multiplicative.ofAdd 1)) - 1 := by
  rw [dyadicCoordinate, AlgEquiv.trans_apply, prodPowerSeriesCoordinate_X, map_sub,
    map_one (domCongr ℤ_[2] e.symm), domCongr_of]

/-- The dyadic coordinate sends the constant `a · σ` of the group ring `ℤ₂[C₂]` to `a` times the
group element `e.symm (σ, 1)`. -/
@[simp]
theorem dyadicCoordinate_C_single (σ : Multiplicative (ZMod 2)) (a : ℤ_[2]) :
    dyadicCoordinate e (PowerSeries.C (MonoidAlgebra.single σ a)) =
      algebraMap ℤ_[2] (completedGroupAlgebra ℤ_[2] Γ) a * of ℤ_[2] Γ (e.symm (σ, 1)) := by
  rw [dyadicCoordinate, AlgEquiv.trans_apply, prodPowerSeriesCoordinate_C_single, map_mul,
    AlgEquiv.commutes, domCongr_of]

end Dyadic

end TauCeti.completedGroupAlgebra
