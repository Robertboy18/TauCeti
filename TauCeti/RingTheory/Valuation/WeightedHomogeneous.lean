/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Valuations of weighted homogeneous polynomial expressions

Let `v` be a valuation on a commutative ring `R` and let `φ` be a weighted homogeneous polynomial
of weight `m` with integer coefficients, for weights `w`. If `v (x i) ≤ C ^ w i` for every variable
`i` occurring in `φ`, then `v (φ (x)) ≤ C ^ m`: each monomial `∏ x i ^ d i` of `φ` has
`∑ d i * w i = m`, so its valuation is at most `∏ (C ^ w i) ^ d i = C ^ m`, and the integer
coefficients have valuation at most `1`.

This is the ultrametric estimate behind the Gauss norms on Witt vectors, where the addition
polynomials are weighted homogeneous for the weights `p ^ i`
(`TauCeti.WittVector.isWeightedHomogeneous_wittAdd`).

## Main results

* `Valuation.map_intCast_le_one`: a valuation is at most `1` on the image of `ℤ`.
* `Valuation.map_aeval_le_pow_of_isWeightedHomogeneous`: the bound `v (φ (x)) ≤ C ^ m` for a
  weighted homogeneous `φ` of weight `m` and `v (x i) ≤ C ^ w i`.
-/

public section

namespace Valuation

open MvPolynomial

variable {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)

/-- A valuation is at most `1` on the image of `ℕ`, by the ultrametric inequality. -/
theorem map_natCast_le_one (n : ℕ) : v (n : R) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ]; exact v.map_add_le ih (by simp)

/-- A valuation is at most `1` on the image of `ℤ`. -/
theorem map_intCast_le_one (k : ℤ) : v (k : R) ≤ 1 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa using v.map_natCast_le_one n
  · simpa using v.map_natCast_le_one n

/-- **Weighted homogeneous expressions are bounded by the power of the weight.** If `φ` is weighted
homogeneous of weight `m` for the weights `w` and `v (x i) ≤ C ^ w i` for every variable `i` of
`φ`, then `v (φ (x)) ≤ C ^ m`. -/
theorem map_aeval_le_pow_of_isWeightedHomogeneous {σ : Type*} {w : σ → ℕ} {φ : MvPolynomial σ ℤ}
    {m : ℕ} (hφ : φ.IsWeightedHomogeneous w m) {x : σ → R} {C : Γ₀}
    (hx : ∀ i ∈ φ.vars, v (x i) ≤ C ^ w i) : v (aeval x φ) ≤ C ^ m := by
  classical
  rw [φ.as_sum, map_sum]
  refine v.map_sum_le fun d hd ↦ ?_
  rw [aeval_monomial, map_mul, Finsupp.prod, map_prod, ← hφ (mem_support_iff.mp hd),
    Finsupp.weight_apply, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
  refine (mul_le_mul' (by simpa using v.map_intCast_le_one _)
    (Finset.prod_le_prod fun i hi ↦ ?_)).trans_eq (one_mul _)
  rw [map_pow, smul_eq_mul, mul_comm, pow_mul]
  exact pow_le_pow_left' (hx i ((mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩)) _

end Valuation

end
