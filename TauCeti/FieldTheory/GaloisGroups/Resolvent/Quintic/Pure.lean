/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Basic

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Orbit

/-!
# The resolvent sextic of a pure quintic

For every integer `a`, the resolvent sextic of the pure quintic `X⁵ - a` is `X⁶ - 3125a⁴X`. The
roots of `X⁵ - a` in `ℂ` are `ζⁱθ` for a primitive fifth root of unity `ζ` and a fifth root `θ` of
`a`. Each of the ten monomials of Dummit's `F₂₀`-invariant is `θ⁴` times a fifth root of unity,
and the six values of the invariant along its orbit are `0` and the five numbers `5θ⁴ζʲ`, so the
orbit product is `X(X⁵ - 5⁵θ²⁰) = X(X⁵ - 3125a⁴)`. This agrees with Dummit's closed formula for
the resolvent sextic of `X⁵ + aX + b` at `a = 0`.

For `a ≠ 0` the sextic is separable over `ℚ`, being the product of `X` and the binomial
`X⁵ - 3125a⁴`, and its root `0` is therefore separation evidence for the pure quintic.

## Main results

* `TauCeti.resolventSextic_X_pow_five_sub_C`: the resolvent sextic of `X⁵ - a` is
  `X⁶ - 3125a⁴X`.
* `TauCeti.separable_map_resolventSextic_X_pow_five_sub_C`: for `a ≠ 0`, that sextic is
  separable over `ℚ`.

## References

* D. S. Dummit, *Solving solvable quintics*, Mathematics of Computation **57** (1991), §1,
  formula (2′).
-/

public section
noncomputable section

open Polynomial Equiv
open MvPolynomial (galResolvent)

namespace TauCeti

/-- The values of the renamings of Dummit's `F₂₀`-invariant at the family `ζⁱθ`, for `ζ` a fifth
root of unity: each of the ten monomials `xₐ² x_b x_c` contributes `θ⁴` times a power of `ζ`, with
exponent read modulo `5`. -/
private theorem eval₂_rename_quinticF20Invariant_pow_mul (ζ θ : ℂ) (h5 : ζ ^ 5 = 1)
    (σ : Perm (Fin 5)) :
    MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun i : Fin 5 => ζ ^ (i : ℕ) * θ)
      (MvPolynomial.rename (⇑σ) quinticF20Invariant) =
    θ ^ 4 * ∑ a : Fin 5, (ζ ^ ((σ a + σ a + σ (a + 1) + σ (a - 1) : Fin 5) : ℕ) +
      ζ ^ ((σ a + σ a + σ (a + 2) + σ (a - 2) : Fin 5) : ℕ)) := by
  have hz : ∀ i j : Fin 5, ζ ^ ((i + j : Fin 5) : ℕ) = ζ ^ (i : ℕ) * ζ ^ (j : ℕ) := by
    intro i j
    rw [Fin.val_add, ← pow_add, ← pow_eq_pow_mod _ h5]
  rw [rename_quinticF20Invariant]
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_add, MvPolynomial.eval₂_X, hz, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- The orbit resolvent of Dummit's invariant at the roots `ζⁱθ` of a pure quintic: the identity
gives the value `0` and the five other coset representatives give the values `5θ⁴ζʲ`. -/
private theorem galResolvent_quinticF20Invariant_pow_mul {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (θ : ℂ) :
    galResolvent quinticF20Invariant (fun i : Fin 5 => ζ ^ (i : ℕ) * θ) =
      X * (X ^ 5 - C ((5 * θ ^ 4) ^ 5)) := by
  have hsum : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
    have := hζ.geom_sum_eq_zero (by norm_num)
    simpa [Finset.sum_range_succ, add_assoc] using this
  have hval := eval₂_rename_quinticF20Invariant_pow_mul ζ θ hζ.pow_eq_one
  have e3 : ((3 : Fin 5) : ℕ) = 3 := rfl
  have e4 : ((4 : Fin 5) : ℕ) = 4 := rfl
  -- The six orbit values, one for each coset representative: each is `θ⁴` times a sum of ten
  -- fifth roots of unity, and `1 + ζ + ζ² + ζ³ + ζ⁴ = 0` collapses that sum to `0` or `5ζʲ`.
  have h1 : MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun i : Fin 5 => ζ ^ (i : ℕ) * θ)
      (MvPolynomial.rename (⇑(1 : Perm (Fin 5))) quinticF20Invariant) = 0 := by
    rw [hval]
    simp only [Fin.sum_univ_five, Perm.coe_one, id_eq, Fin.isValue, Fin.reduceAdd, Fin.reduceSub,
      Fin.val_zero, Fin.val_one, Fin.val_two, e3, e4, pow_zero, pow_one]
    linear_combination (2 * θ ^ 4) * hsum
  have h2 : MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun i : Fin 5 => ζ ^ (i : ℕ) * θ)
      (MvPolynomial.rename (⇑(swap 2 3 : Perm (Fin 5))) quinticF20Invariant) =
      ζ ^ 0 * (5 * θ ^ 4) := by
    rw [hval]
    simp only [Fin.sum_univ_five, Fin.isValue, Fin.reduceAdd, Fin.reduceSub, swap_apply_def,
      Fin.reduceEq, ↓reduceIte, Fin.val_zero, Fin.val_one, Fin.val_two, e3, e4, pow_zero, pow_one]
    linear_combination θ ^ 4 * hsum
  have h3 : MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun i : Fin 5 => ζ ^ (i : ℕ) * θ)
      (MvPolynomial.rename (⇑(swap 3 4 : Perm (Fin 5))) quinticF20Invariant) =
      ζ ^ 4 * (5 * θ ^ 4) := by
    rw [hval]
    simp only [Fin.sum_univ_five, Fin.isValue, Fin.reduceAdd, Fin.reduceSub, swap_apply_def,
      Fin.reduceEq, ↓reduceIte, Fin.val_zero, Fin.val_one, Fin.val_two, e3, e4, pow_zero, pow_one]
    linear_combination θ ^ 4 * hsum
  have h4 : MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun i : Fin 5 => ζ ^ (i : ℕ) * θ)
      (MvPolynomial.rename (⇑(swap 2 4 : Perm (Fin 5))) quinticF20Invariant) =
      ζ ^ 2 * (5 * θ ^ 4) := by
    rw [hval]
    simp only [Fin.sum_univ_five, Fin.isValue, Fin.reduceAdd, Fin.reduceSub, swap_apply_def,
      Fin.reduceEq, ↓reduceIte, Fin.val_zero, Fin.val_one, Fin.val_two, e3, e4, pow_zero, pow_one]
    linear_combination θ ^ 4 * hsum
  have h5 : MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun i : Fin 5 => ζ ^ (i : ℕ) * θ)
      (MvPolynomial.rename (⇑(swap 2 3 * swap 3 4 : Perm (Fin 5))) quinticF20Invariant) =
      ζ ^ 3 * (5 * θ ^ 4) := by
    rw [hval]
    simp only [Fin.sum_univ_five, Fin.isValue, Fin.reduceAdd, Fin.reduceSub, swap_apply_def,
      Fin.reduceEq, ↓reduceIte, Perm.coe_mul, Function.comp_apply, Fin.val_zero, Fin.val_one,
      Fin.val_two, e3, e4, pow_zero, pow_one]
    linear_combination θ ^ 4 * hsum
  have h6 : MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun i : Fin 5 => ζ ^ (i : ℕ) * θ)
      (MvPolynomial.rename (⇑(swap 3 4 * swap 2 3 : Perm (Fin 5))) quinticF20Invariant) =
      ζ ^ 1 * (5 * θ ^ 4) := by
    rw [hval]
    simp only [Fin.sum_univ_five, Fin.isValue, Fin.reduceAdd, Fin.reduceSub, swap_apply_def,
      Fin.reduceEq, ↓reduceIte, Perm.coe_mul, Function.comp_apply, Fin.val_zero, Fin.val_one,
      Fin.val_two, e3, e4, pow_zero, pow_one]
    linear_combination θ ^ 4 * hsum
  rw [← MvPolynomial.map_universalResolvent_eq_galResolvent,
    universalResolvent_quinticF20Invariant, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, MvPolynomial.coe_eval₂Hom]
  rw [X_pow_sub_C_eq_prod hζ (by norm_num) rfl, quinticF20OrbitRepresentatives]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton, h1, h2, h3, h4, h5, h6]
  simp only [C_0, sub_zero, pow_zero, pow_one, one_mul]
  ring

/-- **The resolvent sextic of a pure quintic.** For every integer `a`,
`resolventSextic (X⁵ - a) = X⁶ - 3125a⁴X`. This is Dummit's closed formula for the resolvent
sextic of `X⁵ + aX + b` in the case `a = 0`, and it exhibits `0` as an integral root. -/
theorem resolventSextic_X_pow_five_sub_C (a : ℤ) :
    resolventSextic (X ^ 5 - C a) = X ^ 6 - C (3125 * a ^ 4) * X := by
  apply Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective
  obtain ⟨θ, hθ⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ) (by norm_num : 0 < 5)
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 5 := ⟨_, Complex.isPrimitiveRoot_exp 5 (by norm_num)⟩
  have hmap : (X ^ 5 - C a : ℤ[X]).map (Int.castRingHom ℂ) = X ^ 5 - C (a : ℂ) := by simp
  have hroots : ((X ^ 5 - C a : ℤ[X]).map (Int.castRingHom ℂ)).roots =
      Finset.univ.val.map (fun i : Fin 5 => ζ ^ (i : ℕ) * θ) := by
    rw [hmap, X_pow_sub_C_eq_prod hζ (by norm_num) hθ,
      ← Fin.prod_univ_eq_prod_range (fun i => X - C (ζ ^ i * θ)) 5,
      Finset.prod_eq_multiset_prod]
    conv_rhs =>
      rw [← roots_multiset_prod_X_sub_C (Finset.univ.val.map fun i : Fin 5 => ζ ^ (i : ℕ) * θ)]
    simp only [Multiset.map_map, Function.comp_def]
  rw [resolventSextic_def, quinticF20Spec.map_specialize_eq_galResolvent _
    (monic_X_pow_sub_C a (by norm_num)) natDegree_X_pow_sub_C hroots, quinticF20Spec_Φ,
    galResolvent_quinticF20Invariant_pow_mul hζ θ]
  -- The constant term `(5θ⁴)⁵` of the orbit product equals `3125a⁴` since `θ⁵ = a`.
  have hconst : ((5 : ℂ) * θ ^ 4) ^ 5 = 3125 * (a : ℂ) ^ 4 := by rw [← hθ]; ring
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, hconst]
  rw [eq_intCast]
  push_cast
  ring

/-- Over `ℚ`, the resolvent sextic `X⁶ - 3125a⁴X` of a pure quintic `X⁵ - a` with `a ≠ 0` is
separable, so its root `0` is separation evidence for the quintic certificate. -/
theorem separable_map_resolventSextic_X_pow_five_sub_C {a : ℤ} (ha : a ≠ 0) :
    ((resolventSextic (X ^ 5 - C a)).map (Int.castRingHom ℚ)).Separable := by
  rw [resolventSextic_X_pow_five_sub_C]
  set c : ℚ := Int.castRingHom ℚ (3125 * a ^ 4) with hc_def
  have hc : c ≠ 0 := by
    simp only [hc_def, eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    positivity
  have hmap : (X ^ 6 - C (3125 * a ^ 4) * X : ℤ[X]).map (Int.castRingHom ℚ) =
      X * (X ^ 5 - C c) := by
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C]
    ring
  rw [hmap]
  refine separable_X.mul (separable_X_pow_sub_C _ (by norm_num) hc)
    ⟨C c⁻¹ * X ^ 4, -C c⁻¹, ?_⟩
  have hinv : (C c⁻¹ : ℚ[X]) * C c = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hc, C_1]
  linear_combination hinv

end TauCeti
