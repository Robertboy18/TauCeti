/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Continuity of power-series substitution for the product topology

Mathlib substitutes a power series `b` with nilpotent constant coefficient into a power series
`f` through `PowerSeries.subst b f`, and proves that this is continuous for the product topology
on power series over *discrete* coefficient rings (`MvPowerSeries.continuous_subst`). Here the
coefficient rings carry an arbitrary topology, as `ℤ_p` does with its `p`-adic topology: each
coefficient of `f.subst b` is a finite sum `∑ d < N, f_d • coeff e (b ^ d)`, because the powers
`b ^ d` have order at least `d` once `d` is large, so it depends continuously on `f`.

The substitution `X ↦ (1 + X) ^ u - 1`, for a binomial series `(1 + X) ^ u`, is recorded as a
legitimate substitution: it is the change of variable relating the power-series coordinates of a
completed group algebra attached to two topological generators.

## Main results

* `PowerSeries.WithPiTopology.continuous_subst`,
  `PowerSeries.WithPiTopology.continuous_substAlgHom`: substitution is continuous for the product
  topologies.
* `PowerSeries.hasSubst_binomialSeries_sub_one`: `(1 + X) ^ u - 1` can be substituted.
-/

public section

namespace PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The binomial series `(1 + X) ^ u - 1` has constant coefficient zero, so power series can be
substituted into it. -/
theorem hasSubst_binomialSeries_sub_one [BinomialRing R] (u : R) :
    HasSubst (binomialSeries S u - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp)

namespace WithPiTopology

open Filter Topology

variable [TopologicalSpace R] [TopologicalSpace S] [ContinuousAdd S] [ContinuousSMul R S]

/-- **Substitution of power series is continuous** for the product topologies on `R⟦X⟧` and
`S⟦X⟧`, with arbitrary topologies on the coefficient rings. -/
theorem continuous_subst {b : S⟦X⟧} (hb : HasSubst b) :
    Continuous (subst b : R⟦X⟧ → S⟦X⟧) := by
  refine continuous_iff_continuousAt.mpr fun f ↦
    (tendsto_iff_coeff_tendsto _ _ _ _).mpr fun e ↦ ?_
  -- Beyond some exponent `N`, the powers of `b` have no coefficient of degree `≤ e`.
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hb.eventually_coeff_pow_eq_zero e)
  have key : ∀ g : R⟦X⟧,
      coeff e (g.subst b) = ∑ d ∈ Finset.range N, coeff d g • coeff e (b ^ d) := by
    intro g
    rw [coeff_subst' hb]
    refine finsum_eq_finsetSum_of_support_subset _ fun d hd ↦ ?_
    by_contra hdN
    rw [Finset.coe_range, Set.mem_Iio, not_lt] at hdN
    exact hd (by simp [hN d hdN e le_rfl])
  simp_rw [key]
  exact (continuous_finsetSum _ fun d _ ↦ (continuous_coeff R d).smul continuous_const).continuousAt

/-- Substitution of power series, as an algebra homomorphism, is continuous for the product
topologies. -/
theorem continuous_substAlgHom {b : S⟦X⟧} (hb : HasSubst b) :
    Continuous (substAlgHom (R := R) hb) := by
  rw [coe_substAlgHom]
  exact continuous_subst hb

end WithPiTopology

end PowerSeries
