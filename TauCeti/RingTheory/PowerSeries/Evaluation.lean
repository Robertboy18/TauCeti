/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation

/-!
# Evaluation of power series and divisibility by `X - C c`

Mathlib evaluates a power series over `R` at a topologically nilpotent point `a` of a complete,
separated, linearly topologized `R`-algebra `S` through `PowerSeries.aeval`. This file records the
values of that evaluation on the generators, `X ↦ a` and `C r ↦ algebraMap R S r`, and proves the
divisibility criterion for a linear factor over a complete local ring `A`: for `c` in the maximal
ideal at which power series can be evaluated,

```text
(X - C c) ∣ f  ↔  f(c) = 0.
```

One direction is that `X - C c` evaluates to zero. The other is Weierstrass division
(`PowerSeries.IsWeierstrassDivisorAt.isWeierstrassDivisionAt_div_mod`): the image of `X - C c`
modulo the maximal ideal is `X`, of order one with unit coefficient, so `f = (X - C c) * q + r`
with `r` a constant, and evaluating at `c` identifies that constant with `f(c)`.

The hypothesis `c ∈ maximalIdeal A` is not decoration: for a unit `c` the series `X - C c` is a
unit of `A⟦X⟧`, so it divides everything, while `f(c)` need not vanish.

## Main results

* `PowerSeries.aeval_X`, `PowerSeries.aeval_C`: the values of evaluation on the generators.
* `PowerSeries.map_mk_X_sub_C`: modulo an ideal containing `c`, the series `X - C c` becomes `X`.
* `PowerSeries.X_sub_C_dvd_iff_aeval_eq_zero`: divisibility by `X - C c` is vanishing at `c`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Proposition 7.2 (Weierstrass division).
-/

public section

namespace PowerSeries

section Aeval

variable {R S : Type*} [CommRing R] [CommRing S] [UniformSpace R] [UniformSpace S]
  [IsUniformAddGroup R] [IsTopologicalSemiring R] [IsUniformAddGroup S] [T2Space S]
  [CompleteSpace S] [IsTopologicalRing S] [IsLinearTopology S S] [Algebra R S]
  [ContinuousSMul R S] {a : S}

/-- Evaluation at `a` sends `X` to `a`. -/
@[simp]
theorem aeval_X (ha : HasEval a) : aeval ha (X : R⟦X⟧) = a := by
  rw [← Polynomial.coe_X, aeval_coe, Polynomial.aeval_X]

/-- Evaluation at `a` sends a constant to its image in `S`. -/
@[simp]
theorem aeval_C (ha : HasEval a) (r : R) : aeval ha (C r) = algebraMap R S r := by
  rw [← Polynomial.coe_C, aeval_coe, Polynomial.aeval_C]

end Aeval

section LinearFactor

open IsLocalRing

variable {A : Type*} [CommRing A]

/-- Modulo an ideal containing `c`, the power series `X - C c` becomes `X`. -/
theorem map_mk_X_sub_C {I : Ideal A} {c : A} (hc : c ∈ I) :
    (X - C c : A⟦X⟧).map (Ideal.Quotient.mk I) = X := by
  rw [map_sub, map_X, map_C, Ideal.Quotient.eq_zero_iff_mem.mpr hc, map_zero, sub_zero]

variable [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [T2Space A]
  [CompleteSpace A] [IsLinearTopology A A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]

/-- **Divisibility by a linear factor is vanishing at its root.** Over a complete local ring `A`,
for `c` in the maximal ideal at which power series can be evaluated, a power series is divisible
by `X - C c` exactly when its value at `c` is zero. -/
theorem X_sub_C_dvd_iff_aeval_eq_zero {c : A} (hc : c ∈ maximalIdeal A) (hcev : HasEval c)
    (f : A⟦X⟧) : (X - C c) ∣ f ↔ aeval hcev f = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    simp
  · intro hf
    -- Weierstrass division by `X - C c`: its image in the residue field is `X`, of order one,
    -- with unit leading coefficient.
    have H : (X - C c : A⟦X⟧).IsWeierstrassDivisorAt (maximalIdeal A) := by
      rw [IsWeierstrassDivisorAt, map_mk_X_sub_C hc, order_X, ENat.toNat_one]
      simp
    obtain ⟨hdeg, heq⟩ := H.isWeierstrassDivisionAt_div_mod f
    set q := H.div f
    set r := H.mod f
    rw [map_mk_X_sub_C hc, order_X, ENat.toNat_one, Nat.cast_one,
      Nat.WithBot.lt_one_iff_le_zero] at hdeg
    -- The remainder is the constant `f(c)`, which vanishes.
    have hr : r = Polynomial.C (r.coeff 0) := Polynomial.eq_C_of_degree_le_zero hdeg
    have h0 : r.coeff 0 = 0 := by
      have h := congrArg (aeval hcev) heq
      rw [hf, hr] at h
      simpa using h.symm
    refine ⟨q, ?_⟩
    rw [heq, hr, h0, Polynomial.C_0, Polynomial.coe_zero, add_zero]

end LinearFactor

end PowerSeries
