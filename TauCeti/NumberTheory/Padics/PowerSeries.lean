/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Padic.Basic
public import TauCeti.RingTheory.PowerSeries.Evaluation

/-!
# Power series over the `p`-adic integers: evaluation and division by `X - c`

An arbitrary power series `ψ ∈ ℤ_[p]⟦X⟧` can be evaluated at a `p`-adic integer `c` exactly when
`p ∣ c`: this is the condition `PowerSeries.HasEval c`, which for `ℤ_[p]` is topological
nilpotence (`TauCeti.Huber.PadicInt.isTopologicallyNilpotent_iff_dvd`), and `ψ ↦ ψ(c)` is then
Mathlib's continuous `ℤ_[p]`-algebra homomorphism `PowerSeries.aeval : ℤ_[p]⟦X⟧ →ₐ[ℤ_[p]] ℤ_[p]`,
given by the convergent sum of the monomials (`PowerSeries.hasSum_aeval`). The linear topology
on `ℤ_[p]` that this evaluation needs is `TauCeti.Huber.PadicInt.instIsLinearTopology`. For such
`c`, a power series is divisible by `X - c` exactly when it vanishes at `c`: this is the special
case of Weierstrass division that produces the basis corrections in Labute's classification of
Demushkin groups, and the specialisation to `ℤ_[p]` and its maximal ideal `(p)` of
`PowerSeries.X_sub_C_dvd_iff_aeval_eq_zero`.

## Main results

* `PadicInt.X_sub_C_dvd_iff_aeval_eq_zero`: for `p ∣ c`, `(X - C c) ∣ ψ ↔ ψ(c) = 0`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), §4, p. 122.
-/

public section

open IsLocalRing

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- **Division by `X - c` over `ℤ_[p]`.** For a `p`-adic integer `c` divisible by `p`, a power
series over `ℤ_[p]` is divisible by `X - C c` exactly when its value at `c` is zero. -/
theorem X_sub_C_dvd_iff_aeval_eq_zero {c : ℤ_[p]} (hc : (p : ℤ_[p]) ∣ c) (f : PowerSeries ℤ_[p]) :
    (PowerSeries.X - PowerSeries.C c) ∣ f ↔
      PowerSeries.aeval (TauCeti.Huber.PadicInt.isTopologicallyNilpotent_iff_dvd.mpr hc) f = 0 :=
  PowerSeries.X_sub_C_dvd_iff_aeval_eq_zero (I := maximalIdeal ℤ_[p])
    (by rwa [maximalIdeal_eq_span_p, Ideal.mem_span_singleton]) _ f

end PadicInt
