/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Padic.Basic
public import TauCeti.RingTheory.PowerSeries.Evaluation
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Power series over the `p`-adic integers: evaluation and division by `X - c`

A power series `ψ ∈ ℤ_[p]⟦X⟧` can be evaluated at a `p`-adic integer `c` exactly when `p ∣ c`:
these are the topologically nilpotent elements of `ℤ_[p]`, at which Mathlib's evaluation
`PowerSeries.aeval` is defined, and `ψ ↦ ψ(c)` is then a continuous `ℤ_[p]`-algebra
homomorphism `ℤ_[p]⟦X⟧ →ₐ[ℤ_[p]] ℤ_[p]` given by the convergent sum of the monomials
(`PowerSeries.hasSum_aeval`). For such `c`, a power series is divisible by `X - c` exactly when
it vanishes at `c`: this is the special case of Weierstrass division that produces the basis
corrections in Labute's classification of Demushkin groups.

The evaluation machinery needs `ℤ_[p]` to be linearly topologized, which is recorded here as an
instance: the norm topology is the `(p)`-adic topology
(`TauCeti.Huber.PadicInt.isAdic_maximalIdeal`), whose neighbourhood basis of zero consists of the
ideals `(p ^ n)`.

## Main results

* `PadicInt.instIsLinearTopology`: `ℤ_[p]` is linearly topologized.
* `PadicInt.isTopologicallyNilpotent_iff_dvd`: the topologically nilpotent elements of `ℤ_[p]`,
  the points at which power series can be evaluated, are the multiples of `p`.
* `PadicInt.X_sub_C_dvd_iff_aeval_eq_zero`: for `p ∣ c`, `(X - C c) ∣ ψ ↔ ψ(c) = 0`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), §4, p. 122.
-/

public section

open IsLocalRing

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- The norm topology of `ℤ_[p]` is linear: the ideals `(p ^ n)` are a neighbourhood basis of
zero. -/
instance instIsLinearTopology : IsLinearTopology ℤ_[p] ℤ_[p] :=
  TauCeti.Huber.PadicInt.isAdic_maximalIdeal.isLinearTopology

/-- A `p`-adic integer is topologically nilpotent, so that power series can be evaluated at it,
exactly when it is divisible by `p`. -/
theorem isTopologicallyNilpotent_iff_dvd {c : ℤ_[p]} :
    IsTopologicallyNilpotent c ↔ (p : ℤ_[p]) ∣ c := by
  rw [TauCeti.Huber.PadicInt.isAdic_maximalIdeal.isTopologicallyNilpotent_iff_mem_radical,
    (maximalIdeal.isMaximal ℤ_[p]).isPrime.radical, maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

/-- **Division by `X - c` over `ℤ_[p]`.** For a `p`-adic integer `c` divisible by `p`, a power
series over `ℤ_[p]` is divisible by `X - C c` exactly when its value at `c` is zero. -/
theorem X_sub_C_dvd_iff_aeval_eq_zero {c : ℤ_[p]} (hc : (p : ℤ_[p]) ∣ c) (f : PowerSeries ℤ_[p]) :
    (PowerSeries.X - PowerSeries.C c) ∣ f ↔
      PowerSeries.aeval (isTopologicallyNilpotent_iff_dvd.mpr hc) f = 0 :=
  PowerSeries.X_sub_C_dvd_iff_aeval_eq_zero
    (by rwa [maximalIdeal_eq_span_p, Ideal.mem_span_singleton]) _ f

end PadicInt
