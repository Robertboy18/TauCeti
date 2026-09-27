/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic

/-!
# The minimal polynomial of a primitive element of a Galois extension

Let `L/K` be a finite Galois extension and let `x` generate `L` over `K`. The Galois group acts
freely on `x`, so the conjugates `σ x` for `σ ∈ Gal(L/K)` are exactly the roots of `minpoly K x`,
each once, and

`(minpoly K x).map (algebraMap K L) = ∏ σ : Gal(L/K), (X - C (σ x))`.

Differentiating and evaluating at `x` kills every summand with a factor `X - C x` and leaves

`(minpoly K x)' (x) = ∏_{σ ≠ 1} (x - σ x)`.

This is the form in which the derivative of the minimal polynomial enters the theory of the
different: for a Galois extension of local fields it expresses the different exponent as a sum
of valuations `v (σ x - x)` over the nontrivial automorphisms.

## Main results

* `TauCeti.minpoly_map_eq_prod_X_sub_C_of_adjoin_eq_top`: the minimal polynomial of a primitive
  element is, in `L[X]`, the product of `X - C (σ x)` over the Galois group.
* `TauCeti.aeval_derivative_minpoly_eq_prod_of_adjoin_eq_top`: its derivative at `x` is the
  product of `x - σ x` over the nontrivial automorphisms.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §6 and Chapter IV, §1.
-/

public section

open Polynomial IntermediateField

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The image in `L[X]` of the minimal polynomial of a primitive element `x` of a finite Galois
extension `L/K` is `∏ σ : Gal(L/K), (X - C (σ x))`. -/
theorem minpoly_map_eq_prod_X_sub_C_of_adjoin_eq_top {x : L} (hx : K⟮x⟯ = ⊤) :
    (minpoly K x).map (algebraMap K L) = ∏ σ : L ≃ₐ[K] L, (X - C (σ x)) := by
  classical
  have hint : IsIntegral K x := .of_finite K x
  -- An automorphism is determined by its value at the generator `x`.
  have hinj : Function.Injective fun σ : L ≃ₐ[K] L ↦ σ x := fun σ τ h ↦
    AlgEquiv.coe_toAlgHom_injective <| AlgHom.ext_of_adjoin_eq_top
      ((adjoin_eq_top_iff_of_isAlgebraic fun y _ ↦ IsAlgebraic.of_finite K y).1 hx)
      (Set.eqOn_singleton.2 h)
  have hmonic : (∏ σ : L ≃ₐ[K] L, (X - C (σ x) : L[X])).Monic :=
    monic_prod_of_monic _ _ fun σ _ ↦ monic_X_sub_C _
  have hdeg : ((minpoly K x).map (algebraMap K L)).natDegree ≤
      (∏ σ : L ≃ₐ[K] L, (X - C (σ x) : L[X])).natDegree := by
    rw [natDegree_prod_of_monic _ _ fun σ _ ↦ monic_X_sub_C _, (minpoly.monic hint).natDegree_map]
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    rw [← adjoin.finrank hint, hx, finrank_top', ← IsGalois.card_aut_eq_finrank,
      Nat.card_eq_fintype_card]
  refine eq_of_monic_of_dvd_of_natDegree_le hmonic ((minpoly.monic hint).map _) ?_ hdeg
  -- The conjugates `σ x` are distinct roots of the minimal polynomial.
  have hmap : (Finset.univ.val.map fun σ : L ≃ₐ[K] L ↦ (X - C (σ x) : L[X])) =
      (Finset.univ.val.map fun σ : L ≃ₐ[K] L ↦ σ x).map fun a ↦ X - C a := by
    rw [Multiset.map_map, Function.comp_def]
  rw [Finset.prod_eq_multiset_prod, hmap,
    Multiset.prod_X_sub_C_dvd_iff_le_roots ((minpoly.monic hint).map _).ne_zero,
    Multiset.le_iff_subset (Finset.univ.nodup.map hinj)]
  intro r hr
  obtain ⟨σ, -, rfl⟩ := Multiset.mem_map.1 hr
  rw [mem_roots ((minpoly.monic hint).map _).ne_zero, IsRoot, eval_map, ← aeval_def,
    ← minpoly.algEquiv_eq σ x, minpoly.aeval]

/-- The derivative of the minimal polynomial of a primitive element `x` of a finite Galois
extension, evaluated at `x`, is `∏_{σ ≠ 1} (x - σ x)`. -/
theorem aeval_derivative_minpoly_eq_prod_of_adjoin_eq_top [DecidableEq (L ≃ₐ[K] L)] {x : L}
    (hx : K⟮x⟯ = ⊤) :
    aeval x (derivative (minpoly K x)) =
      ∏ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), (x - σ x) := by
  rw [aeval_def, eval₂_eq_eval_map, ← derivative_map,
    minpoly_map_eq_prod_X_sub_C_of_adjoin_eq_top hx, derivative_prod_finset, eval_finsetSum,
    Finset.sum_eq_single (1 : L ≃ₐ[K] L)]
  · simp [eval_prod]
  · intro σ _ hσ
    rw [eval_mul, eval_prod]
    refine mul_eq_zero_of_left (Finset.prod_eq_zero (i := 1) ?_ (by simp)) _
    exact Finset.mem_erase.2 ⟨hσ.symm, Finset.mem_univ _⟩
  · exact fun h ↦ absurd (Finset.mem_univ _) h

end TauCeti
