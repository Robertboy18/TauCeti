/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.LinearCombination

/-!
# Linear relations between polynomials over a field

A relation `A * q + B * p = 0` between polynomials over a field says that `A * q` is divisible by
`p`; dividing by the gcd of `p` and `q` and using its Bézout identity shows that in fact
`p / gcd p q` divides `A`.  So a nonzero `A` in such a relation has degree at least
`deg p - deg (gcd p q)`: this is the degree bound behind the nonvanishing of the principal
subresultant coefficient at the degree of the gcd.
-/

public section

namespace TauCeti

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

/-- In a relation `A * q + B * p = 0` with `p ≠ 0`, if `A` has degree below
`deg p - deg (gcd p q)`, then `A = 0`: dividing by the gcd and using its Bézout identity shows that
`p / gcd p q` divides `A`. -/
theorem _root_.Polynomial.eq_zero_of_mul_add_mul_eq_zero_of_degree_lt {p q A B : K[X]}
    (hp : p ≠ 0) (hAB : A * q + B * p = 0)
    (hA : A.degree < ((p.natDegree - (EuclideanDomain.gcd p q).natDegree : ℕ) : WithBot ℕ)) :
    A = 0 := by
  set g := EuclideanDomain.gcd p q with hg
  clear_value g
  have hg0 : g ≠ 0 := fun h => hp (EuclideanDomain.gcd_eq_zero_iff.mp (hg ▸ h)).1
  obtain ⟨p', hp'⟩ : g ∣ p := hg ▸ EuclideanDomain.gcd_dvd_left p q
  obtain ⟨q', hq'⟩ : g ∣ q := hg ▸ EuclideanDomain.gcd_dvd_right p q
  set u := EuclideanDomain.gcdA p q
  set w := EuclideanDomain.gcdB p q
  have hone : p' * u + q' * w = 1 := by
    refine mul_left_cancel₀ hg0 ?_
    calc g * (p' * u + q' * w) = (g * p') * u + (g * q') * w := by ring
      _ = p * u + q * w := by rw [← hp', ← hq']
      _ = g * 1 := by rw [mul_one, hg]; exact (EuclideanDomain.gcd_eq_gcd_ab p q).symm
  have hrel : A * q' + B * p' = 0 := by
    refine mul_left_cancel₀ hg0 ?_
    calc g * (A * q' + B * p') = A * (g * q') + B * (g * p') := by ring
      _ = A * q + B * p := by rw [← hp', ← hq']
      _ = g * 0 := by rw [hAB, mul_zero]
  have hpA : p' ∣ A := ⟨A * u - B * w, by linear_combination (-A) * hone + w * hrel⟩
  have hp'0 : p' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hp'
    exact hp hp'
  refine eq_zero_of_dvd_of_degree_lt hpA (hA.trans_le ?_)
  rw [degree_eq_natDegree hp'0]
  have := natDegree_mul hg0 hp'0
  rw [← hp'] at this
  exact WithBot.coe_le_coe.mpr (by omega : p.natDegree - g.natDegree ≤ p'.natDegree)

end TauCeti
