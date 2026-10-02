/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Defs
public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Weighted homogeneity of the Witt structure polynomials

Give the variable `(b, i)` of `MvPolynomial (idx × ℕ) R` the weight `p ^ i`, so that the `i`-th
Witt component has weight `p ^ i`. The `n`-th Witt polynomial `W_n = ∑ p ^ i X_i ^ (p ^ (n - i))` is
weighted homogeneous of weight `p ^ n`, and the Witt structure polynomials of a homogeneous
polynomial `Φ` of degree `m` are weighted homogeneous of weight `m * p ^ n`: they are determined
over `ℚ` by the recursion `p ^ n S_n = Φ(W_n(X_b)) - ∑_{i < n} p ^ i S_i ^ (p ^ (n - i))`, every
term of which has weight `m * p ^ n`. In particular the polynomials `wittAdd p n` giving the
components of a sum of Witt vectors are weighted homogeneous of weight `p ^ n`.

This is the structural fact behind the ultrametric inequality for the Teichmüller coordinates of a
sum of Witt vectors: a weighted homogeneous polynomial evaluated at elements whose valuations are
bounded by the corresponding powers of a constant is bounded by the constant to the power of the
weight (`Valuation.map_aeval_le_pow_of_isWeightedHomogeneous`).

## Main definitions

* `TauCeti.WittVector.wittWeight`: the weight `p ^ i` of the variable `(b, i)`.

## Main results

* `TauCeti.WittVector.isWeightedHomogeneous_wittPolynomial`: `W_n` is weighted homogeneous of
  weight `p ^ n` for the weights `i ↦ p ^ i`.
* `TauCeti.WittVector.isWeightedHomogeneous_wittStructureInt`: the Witt structure polynomials of
  a homogeneous polynomial of degree `m` are weighted homogeneous of weight `m * p ^ n`.
* `TauCeti.WittVector.isWeightedHomogeneous_wittAdd`: `wittAdd p n` is weighted homogeneous of
  weight `p ^ n`.

## References

* J.-P. Serre, *Corps locaux*, Chapitre II, §6, for the Witt polynomials and the recursion
  defining the structure polynomials.
-/

public section

namespace TauCeti.WittVector

open MvPolynomial Finset

variable (p : ℕ) {idx : Type*}

/-- The weight `p ^ i` of the variable `(b, i)`: the `i`-th component of a Witt vector carries the
weight `p ^ i`. -/
def wittWeight : idx × ℕ → ℕ := fun bi ↦ p ^ bi.2

@[simp]
theorem wittWeight_apply (bi : idx × ℕ) : wittWeight p bi = p ^ bi.2 := (rfl)

/-- **The Witt polynomial `W_n` is weighted homogeneous of weight `p ^ n`** for the weights
`i ↦ p ^ i`: each term `p ^ i X_i ^ (p ^ (n - i))` has weight `p ^ (n - i) * p ^ i = p ^ n`. -/
theorem isWeightedHomogeneous_wittPolynomial (R : Type*) [CommRing R] (n : ℕ) :
    (wittPolynomial p R n).IsWeightedHomogeneous (fun i : ℕ ↦ p ^ i) (p ^ n) := by
  rw [wittPolynomial]
  refine IsWeightedHomogeneous.sum _ _ _ fun i hi ↦ isWeightedHomogeneous_monomial _ _ _ ?_
  rw [Finsupp.weight_single, smul_eq_mul, ← pow_add,
    Nat.sub_add_cancel (mem_range_succ_iff.mp hi)]

variable [hp : Fact p.Prime]

/-- **The rational Witt structure polynomials of a homogeneous polynomial of degree `m` are
weighted homogeneous of weight `m * p ^ n`**, by induction along the recursion
`p ^ n S_n = Φ(W_n(X_b)) - ∑_{i < n} p ^ i S_i ^ (p ^ (n - i))`. -/
theorem isWeightedHomogeneous_wittStructureRat {Φ : MvPolynomial idx ℚ} {m : ℕ}
    (hΦ : Φ.IsHomogeneous m) (n : ℕ) :
    (wittStructureRat p Φ n).IsWeightedHomogeneous (wittWeight p) (m * p ^ n) := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  rw [wittStructureRat_rec]
  refine (IsWeightedHomogeneous.sub ?_ ?_).C_mul _
  · exact IsWeightedHomogeneous.aeval hΦ fun b ↦ by
      simpa using (isWeightedHomogeneous_wittPolynomial p ℚ n).rename (f := fun i ↦ (b, i))
        fun i ↦ by simp
  · refine IsWeightedHomogeneous.sum _ _ _ fun i hi ↦ ?_
    have hi' := mem_range.mp hi
    convert (((IH i hi').pow (p ^ (n - i))).C_mul ((p : ℚ) ^ i)) using 2
    rw [smul_eq_mul, mul_left_comm, ← pow_add, Nat.sub_add_cancel hi'.le]

/-- **The Witt structure polynomials of a homogeneous polynomial of degree `m` are weighted
homogeneous of weight `m * p ^ n`**, for the weights `(b, i) ↦ p ^ i`. -/
theorem isWeightedHomogeneous_wittStructureInt {Φ : MvPolynomial idx ℤ} {m : ℕ}
    (hΦ : Φ.IsHomogeneous m) (n : ℕ) :
    (wittStructureInt p Φ n).IsWeightedHomogeneous (wittWeight p) (m * p ^ n) := by
  rw [← isWeightedHomogeneous_map_iff (Int.castRingHom ℚ).injective_int, map_wittStructureInt]
  exact isWeightedHomogeneous_wittStructureRat p
    ((isWeightedHomogeneous_map_iff (Int.castRingHom ℚ).injective_int).mpr hΦ) n

/-- **The addition polynomials of Witt vectors are weighted homogeneous of weight `p ^ n`.** -/
theorem isWeightedHomogeneous_wittAdd (n : ℕ) :
    (_root_.WittVector.wittAdd p n).IsWeightedHomogeneous (wittWeight p) (p ^ n) := by
  simpa [_root_.WittVector.wittAdd] using
    isWeightedHomogeneous_wittStructureInt p ((isHomogeneous_X ℤ 0).add (isHomogeneous_X ℤ 1)) n

end TauCeti.WittVector

end
