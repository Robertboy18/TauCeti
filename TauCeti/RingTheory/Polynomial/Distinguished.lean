/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished

/-!
# The polynomial `(1 + X) ^ n - 1`

The polynomial `(1 + X) ^ n - 1` over a commutative ring `R` is monic of degree `n` for `n ≠ 0`,
with constant coefficient `0` and `k`-th coefficient the binomial coefficient `n.choose k`. When
`n = p ^ m` is a power of a prime `p`, every binomial coefficient `(p ^ m).choose k` with
`0 < k < p ^ m` is divisible by `p`, so the polynomial is *distinguished* at the ideal `(p)`: monic
with all non-leading coefficients in `(p)`. Over the `p`-adic integers this is the shape of divisor
for which Mathlib's Weierstrass division in `ℤ_p⟦X⟧` is available.

This is the polynomial cutting out the finite levels of the power-series coordinate on the
completed group algebra `ℤ_p[[Γ]]` of a procyclic pro-`p` group `Γ`: at a level `Γ ⧸ U` of order
`p ^ m`, the class of the topological generator satisfies `σ ^ (p ^ m) = 1`, so
`(1 + X) ^ (p ^ m) - 1` vanishes at `X = σ - 1`.

## Main results

* `TauCeti.Polynomial.monic_one_add_X_pow_sub_one`,
  `TauCeti.Polynomial.natDegree_one_add_X_pow_sub_one`: `(1 + X) ^ n - 1` is monic of degree `n`.
* `TauCeti.Polynomial.isDistinguishedAt_one_add_X_pow_sub_one`: `(1 + X) ^ (p ^ m) - 1` is
  distinguished at `(p)`.
-/

public section

namespace TauCeti

open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The polynomial `1 + X` is monic. -/
theorem monic_one_add_X : (1 + X : R[X]).Monic := by
  rw [add_comm, ← C_1]
  exact monic_X_add_C 1

/-- The constant coefficient of `(1 + X) ^ n - 1` vanishes. -/
theorem coeff_one_add_X_pow_sub_one_zero (n : ℕ) : ((1 + X) ^ n - 1 : R[X]).coeff 0 = 0 := by
  simp [coeff_one_add_X_pow]

/-- The `k`-th coefficient of `(1 + X) ^ n - 1`, for `k ≠ 0`, is the binomial coefficient
`n.choose k`. -/
theorem coeff_one_add_X_pow_sub_one (n : ℕ) {k : ℕ} (hk : k ≠ 0) :
    ((1 + X) ^ n - 1 : R[X]).coeff k = (n.choose k : R) := by
  simp [coeff_one_add_X_pow, coeff_one, hk]

/-- The polynomial `(1 + X) ^ n - 1` has degree `n`. -/
@[simp]
theorem natDegree_one_add_X_pow_sub_one [Nontrivial R] (n : ℕ) :
    ((1 + X) ^ n - 1 : R[X]).natDegree = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h : ((1 + X : R[X]) ^ n).natDegree = n := by
    rw [monic_one_add_X.natDegree_pow, natDegree_one_add, natDegree_X, mul_one]
  rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [natDegree_one, h]; exact hn), h]

/-- The polynomial `(1 + X) ^ n - 1` is monic for `n ≠ 0`. -/
theorem monic_one_add_X_pow_sub_one {n : ℕ} (hn : n ≠ 0) : ((1 + X) ^ n - 1 : R[X]).Monic := by
  nontriviality R
  refine (monic_one_add_X.pow n).sub_of_left ?_
  rw [degree_one, degree_eq_natDegree (monic_one_add_X.pow n).ne_zero,
    monic_one_add_X.natDegree_pow, natDegree_one_add, natDegree_X, mul_one]
  exact_mod_cast Nat.pos_of_ne_zero hn

/-- **`(1 + X) ^ (p ^ m) - 1` is a distinguished polynomial at `(p)`**, for a prime `p`: it is
monic, its constant coefficient is `0`, and its other non-leading coefficients are the binomial
coefficients `(p ^ m).choose k` with `0 < k < p ^ m`, which `p` divides. -/
theorem isDistinguishedAt_one_add_X_pow_sub_one {p : ℕ} (hp : p.Prime) (m : ℕ) :
    ((1 + X) ^ p ^ m - 1 : R[X]).IsDistinguishedAt (Ideal.span {(p : R)}) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨⟨fun hk ↦ by simp [natDegree_of_subsingleton] at hk⟩, monic_of_subsingleton _⟩
  refine ⟨⟨fun {k} hk ↦ ?_⟩, monic_one_add_X_pow_sub_one (pow_ne_zero m hp.ne_zero)⟩
  rw [natDegree_one_add_X_pow_sub_one] at hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [coeff_one_add_X_pow_sub_one_zero]
    exact Ideal.zero_mem _
  · rw [coeff_one_add_X_pow_sub_one _ hk0.ne', Ideal.mem_span_singleton]
    exact Nat.cast_dvd_cast (hp.dvd_choose_pow hk0.ne' hk.ne)

end Polynomial

end TauCeti
