/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Multiplicity

/-!
# The prime `p` divides `(x - 1) ^ p ^ k` when `x ^ p ^ k = 1`

In any ring, an element `x` with `x ^ p ^ k = 1` for a prime `p` satisfies
`(p : A) ∣ (x - 1) ^ p ^ k`: expanding `1 = (1 + (x - 1)) ^ p ^ k` by the binomial theorem, the
extreme terms are `1` and `(x - 1) ^ p ^ k`, and every other binomial coefficient
`(p ^ k).choose m` with `0 < m < p ^ k` is divisible by `p`. No commutativity is needed, because
`x - 1` commutes with `1`.

This is the integral shadow of the freshman's dream `(x - 1) ^ p ^ k = x ^ p ^ k - 1 = 0` in
characteristic `p`. It is what makes the group-like elements `g - 1`, for `g` of `p`-power order
in a group algebra over the `p`-adic integers, topologically nilpotent.

## Main result

* `Nat.Prime.dvd_sub_one_pow_of_pow_eq_one`: `(p : A) ∣ (x - 1) ^ p ^ k` when `x ^ p ^ k = 1`.
-/

public section

/-- If `x ^ p ^ k = 1` in a ring, for a prime `p`, then `p` divides `(x - 1) ^ p ^ k`. -/
theorem Nat.Prime.dvd_sub_one_pow_of_pow_eq_one {A : Type*} [Ring A] {p : ℕ} (hp : p.Prime)
    {x : A} {k : ℕ} (hx : x ^ p ^ k = 1) : (p : A) ∣ (x - 1) ^ p ^ k := by
  obtain ⟨N, hN⟩ : ∃ N, p ^ k = N + 1 := Nat.exists_eq_succ_of_ne_zero (pow_ne_zero k hp.ne_zero)
  -- Expand `1 = ((x - 1) + 1) ^ p ^ k` and isolate the top and bottom terms.
  have h := (Commute.one_right (x - 1)).add_pow (p ^ k)
  simp only [one_pow, mul_one] at h
  rw [sub_add_cancel, hx, Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, mul_one, hN,
    Finset.sum_range_succ', pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul,
    add_right_comm] at h
  have h' := add_right_cancel (h.symm.trans (zero_add 1).symm)
  rw [hN, eq_neg_of_add_eq_zero_right h', dvd_neg]
  refine Finset.dvd_sum fun m hm ↦ ?_
  rw [← (Nat.cast_commute _ _).eq, ← hN]
  refine Dvd.dvd.mul_right (Nat.cast_dvd_cast (hp.dvd_choose_pow m.succ_ne_zero ?_)) _
  rw [hN]
  exact Nat.ne_of_lt (Nat.succ_lt_succ (Finset.mem_range.mp hm))
