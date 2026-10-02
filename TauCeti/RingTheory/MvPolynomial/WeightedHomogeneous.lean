/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Weighted homogeneity under renaming, base change and substitution

Give the variable `i` the weight `w i`. Weighted homogeneity of weight `m` is preserved by renaming
the variables along a map that respects the weights, is reflected and preserved by an injective
change of coefficients, and is transformed by substitution: substituting for the variable `i` a
polynomial that is weighted homogeneous of weight `w i * e` (for the weights on the new variables)
produces a polynomial that is weighted homogeneous of weight `m * e`. When the new weights are all
`1` and `e = 1`, this says that substituting homogeneous polynomials of degrees `w i` turns weighted
homogeneity into homogeneity. When moreover the substitution is injective the converse holds: a
polynomial whose substitution is homogeneous of degree `m` is itself weighted homogeneous of weight
`m`.

Two substitutions motivate this. One sends the variable `i` of `MvPolynomial (Fin n) R` to the
elementary symmetric polynomial `eᵢ₊₁`, which is homogeneous of degree `i + 1`
(`MvPolynomial.isHomogeneous_esymm`). By the fundamental theorem of symmetric polynomials it is
injective, so the expression of a homogeneous symmetric polynomial in the elementary symmetric
polynomials is weighted homogeneous for the weights `i + 1`. The coefficients of a product
`∏ (X - C Ψ)` of linear factors with homogeneous constant terms of a common degree `m` supply
such symmetric polynomials (`MvPolynomial.isHomogeneous_coeff_prod_X_sub_C`). The other is the
substitution of the Witt polynomials into a homogeneous polynomial, which makes the Witt structure
polynomials weighted homogeneous for the weights `p ^ i`
(`TauCeti.WittVector.isWeightedHomogeneous_wittStructureInt`).

## Main results

* `MvPolynomial.IsWeightedHomogeneous.rename`: renaming along a weight-respecting map preserves
  weighted homogeneity.
* `MvPolynomial.isWeightedHomogeneous_map_iff`: an injective change of coefficients preserves and
  reflects weighted homogeneity.
* `MvPolynomial.IsWeightedHomogeneous.aeval`: substituting weighted homogeneous polynomials of
  weights `w i * e` multiplies the weight by `e`.
* `MvPolynomial.IsWeightedHomogeneous.isHomogeneous_aeval`: substituting homogeneous polynomials
  of the weights turns weighted homogeneity into homogeneity.
* `MvPolynomial.isWeightedHomogeneous_of_isHomogeneous_aeval`: the converse, for an injective
  substitution.
-/

public section

namespace MvPolynomial

variable {σ τ R : Type*}

section CommSemiring

variable [CommSemiring R]

/-- Renaming the variables along a map `f` that respects the weights, `w (f i) = w' i`, preserves
weighted homogeneity. -/
theorem IsWeightedHomogeneous.rename {M : Type*} [AddCommMonoid M] {w : τ → M} {w' : σ → M}
    {φ : MvPolynomial σ R} {m : M} (hφ : φ.IsWeightedHomogeneous w' m) {f : σ → τ}
    (hf : ∀ i, w (f i) = w' i) : (rename f φ).IsWeightedHomogeneous w m := by
  rw [← φ.support_sum_monomial_coeff, map_sum]
  simp_rw [rename_monomial]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd ↦ isWeightedHomogeneous_monomial _ _ _ ?_
  rw [← hφ (mem_support_iff.mp hd), Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (by simp) (by simp [add_smul])]
  simp_rw [hf]

/-- An injective change of coefficients preserves and reflects weighted homogeneity. -/
theorem isWeightedHomogeneous_map_iff {S M : Type*} [CommSemiring S] [AddCommMonoid M]
    {f : R →+* S} (hf : Function.Injective f) {w : σ → M} {φ : MvPolynomial σ R} {m : M} :
    (map f φ).IsWeightedHomogeneous w m ↔ φ.IsWeightedHomogeneous w m := by
  simp only [IsWeightedHomogeneous, coeff_map, ne_eq, map_eq_zero_iff f hf]

/-- Substituting, for each variable `i`, a polynomial that is weighted homogeneous of weight
`w i * e` for the weights `w'` into a polynomial that is weighted homogeneous of weight `m` for the
weights `w` gives a polynomial that is weighted homogeneous of weight `m * e` for the weights
`w'`. -/
theorem IsWeightedHomogeneous.aeval {w : σ → ℕ} {w' : τ → ℕ} {φ : MvPolynomial σ R} {m e : ℕ}
    (hφ : φ.IsWeightedHomogeneous w m) {g : σ → MvPolynomial τ R}
    (hg : ∀ i, (g i).IsWeightedHomogeneous w' (w i * e)) :
    (MvPolynomial.aeval g φ).IsWeightedHomogeneous w' (m * e) := by
  induction hφ using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isWeightedHomogeneous_zero (R := R) w' (m * e)
  | add p q _ _ ihp ihq => simpa using ihp.add ihq
  | monomial d r hr =>
    rw [aeval_monomial, Finsupp.prod, algebraMap_eq]
    have hprod := IsWeightedHomogeneous.prod d.support (fun i ↦ g i ^ d i)
      (fun i ↦ d i • (w i * e)) fun i _ ↦ (hg i).pow (d i)
    convert (isWeightedHomogeneous_C w' r).mul hprod using 1
    rw [← hr, Finsupp.weight_apply, Finsupp.sum, zero_add, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_eq_mul, smul_eq_mul]; ring

/-- Substituting, for each variable `i`, a polynomial homogeneous of degree `w i` into a
polynomial that is weighted homogeneous of weight `m` for the weights `w` gives a homogeneous
polynomial of degree `m`. -/
theorem IsWeightedHomogeneous.isHomogeneous_aeval {w : σ → ℕ} {φ : MvPolynomial σ R} {m : ℕ}
    (hφ : φ.IsWeightedHomogeneous w m) {g : σ → MvPolynomial τ R}
    (hg : ∀ i, (g i).IsHomogeneous (w i)) : (MvPolynomial.aeval g φ).IsHomogeneous m := by
  simpa [IsHomogeneous] using
    hφ.aeval (w' := 1) (e := 1) fun i ↦ by simpa [IsHomogeneous] using hg i

/-- **Weighted homogeneity from homogeneity of a substitution.** If `g i` is homogeneous of
degree `w i` for every variable `i` and substitution of the `g i` is injective, then a polynomial
whose substitution is homogeneous of degree `m` is weighted homogeneous of weight `m`. -/
theorem isWeightedHomogeneous_of_isHomogeneous_aeval {w : σ → ℕ} {g : σ → MvPolynomial τ R}
    (hg : ∀ i, (g i).IsHomogeneous (w i)) (hinj : Function.Injective (aeval (R := R) g))
    {φ : MvPolynomial σ R} {m : ℕ} (h : (aeval g φ).IsHomogeneous m) :
    φ.IsWeightedHomogeneous w m := by
  classical
  -- The substitution of the weight-`n` component of `φ` is homogeneous of degree `n`, so the
  -- degree-`m` part of the substitution of `φ` is the substitution of its weight-`m` component.
  set s := (weightedHomogeneousComponent_finsupp (w := w) φ).toFinset
  have hsum : ∑ n ∈ s, weightedHomogeneousComponent w n φ = φ := by
    rw [← finsum_eq_sum _ (weightedHomogeneousComponent_finsupp φ),
      sum_weightedHomogeneousComponent]
  have hcomp (n : ℕ) : (aeval g (weightedHomogeneousComponent w n φ)).IsHomogeneous n :=
    (weightedHomogeneousComponent_isWeightedHomogeneous n φ).isHomogeneous_aeval hg
  have key : aeval g φ = aeval g (weightedHomogeneousComponent w m φ) := by
    calc aeval g φ = homogeneousComponent m (aeval g φ) := (homogeneousComponent_eq_self h).symm
      _ = ∑ n ∈ s, homogeneousComponent m (aeval g (weightedHomogeneousComponent w n φ)) := by
        conv_lhs => rw [← hsum]
        rw [map_sum, map_sum]
      _ = homogeneousComponent m (aeval g (weightedHomogeneousComponent w m φ)) := by
        refine Finset.sum_eq_single m (fun n _ hn => ?_) fun hm => ?_
        · simp [homogeneousComponent_of_mem (hcomp n), hn.symm]
        · have hzero : weightedHomogeneousComponent w m φ = 0 := by
            by_contra hne
            exact hm ((Set.Finite.mem_toFinset _).mpr hne)
          rw [hzero, map_zero, map_zero]
      _ = aeval g (weightedHomogeneousComponent w m φ) := homogeneousComponent_eq_self (hcomp m)
  rw [hinj key]
  exact weightedHomogeneousComponent_isWeightedHomogeneous m φ

end CommSemiring

end MvPolynomial
