/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

import Mathlib.Logic.Equiv.Fintype

/-!
# Uniqueness of elementary divisors with a fixed base

An additive equivalence between finite products of `ZMod (b ^ e i)`, with `b > 1` and positive
exponents, determines the exponents up to reindexing. For a prime `b = p` the exponents are the
elementary divisors of a finite abelian `p`-group, so this is the uniqueness clause of the
classification of finite abelian `p`-groups; it also identifies the finite factor of a topologically
finitely generated abelian pro-`p` group up to reindexing of its cyclic summands.

The exponents are required to be positive because a factor `ZMod (b ^ 0)` is trivial and leaves
the product unchanged.

## Main results

* `ZMod.exists_equiv_exponents_of_pi_pow_addEquiv`: two such products have the same exponents
  after a bijection of their finite index types.
-/

public section

namespace ZMod

open Finset

private theorem card_nsmul_ker_pi_pow {b : ℕ} [NeZero b] {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (k : ℕ) :
    Nat.card (nsmulAddMonoidHom (b ^ k) :
      ((i : ι) → ZMod (b ^ e i)) →+ ((i : ι) → ZMod (b ^ e i))).ker =
        b ^ (∑ i, min k (e i)) := by
  classical
  calc
    _ = Nat.card ((i : ι) →
        (nsmulAddMonoidHom (b ^ k) : ZMod (b ^ e i) →+ ZMod (b ^ e i)).ker) := by
      apply Nat.card_congr
      exact (Equiv.subtypeEquivRight fun x ↦ by
        simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, funext_iff, Pi.smul_apply,
          Pi.zero_apply]).trans Equiv.subtypePiEquivPi
    _ = ∏ i, Nat.card
        (nsmulAddMonoidHom (b ^ k) : ZMod (b ^ e i) →+ ZMod (b ^ e i)).ker := Nat.card_pi
    _ = ∏ i, b ^ min k (e i) := by
      apply prod_congr rfl
      intro i _
      rw [IsAddCyclic.card_nsmulAddMonoidHom_ker, Nat.card_zmod]
      rcases le_total (e i) k with h | h
      · rw [Nat.gcd_eq_left (pow_dvd_pow b h), min_eq_right h]
      · rw [Nat.gcd_eq_right (pow_dvd_pow b h), min_eq_left h]
    _ = _ := prod_pow_eq_pow_sum _ _ _

private theorem sum_min_eq_of_pi_pow_addEquiv {b : ℕ} (hb : 1 < b)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι → ℕ) (e' : κ → ℕ)
    (f : ((i : ι) → ZMod (b ^ e i)) ≃+ ((j : κ) → ZMod (b ^ e' j))) (k : ℕ) :
    (∑ i, min k (e i)) = ∑ j, min k (e' j) := by
  have : NeZero b := ⟨by omega⟩
  apply Nat.pow_right_injective hb
  dsimp only
  rw [← card_nsmul_ker_pi_pow (b := b) e k, ← card_nsmul_ker_pi_pow (b := b) e' k]
  apply Nat.card_congr
  refine f.toEquiv.subtypeEquiv fun x ↦ ?_
  simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, AddEquiv.toEquiv_eq_coe,
    EquivLike.coe_coe, ← map_nsmul f, map_eq_zero_iff f f.injective]

private theorem sum_min_add_card_fiber {ι : Type*} [Fintype ι] (e : ι → ℕ) (k : ℕ) :
    (∑ i, min (k + 2) (e i)) + (∑ i, min k (e i)) +
        Fintype.card {i // e i = k + 1} =
      (∑ i, min (k + 1) (e i)) + (∑ i, min (k + 1) (e i)) := by
  classical
  have hcount : Fintype.card {i // e i = k + 1} =
      ∑ i, if e i = k + 1 then 1 else 0 := by
    simp only [sum_boole, Nat.cast_id, Fintype.card_subtype]
  rw [hcount, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  split_ifs <;> omega

/-- Finite products of nontrivial cyclic groups with orders powers of the same base `b > 1`
have uniquely determined exponents up to reindexing. Primality of the base is not needed. -/
theorem exists_equiv_exponents_of_pi_pow_addEquiv {b : ℕ} (hb : 1 < b)
    {ι κ : Type*} [Finite ι] [Finite κ] (e : ι → ℕ) (e' : κ → ℕ)
    (he : ∀ i, 0 < e i) (he' : ∀ j, 0 < e' j)
    (f : ((i : ι) → ZMod (b ^ e i)) ≃+ ((j : κ) → ZMod (b ^ e' j))) :
    ∃ σ : ι ≃ κ, ∀ i, e i = e' (σ i) := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  have hsum := sum_min_eq_of_pi_pow_addEquiv hb e e' f
  have hcard (k : ℕ) : Fintype.card {i // e i = k} = Fintype.card {j // e' j = k} := by
    cases k with
    | zero =>
      have : IsEmpty {i // e i = 0} := ⟨fun i ↦ (he i.1).ne' i.2⟩
      have : IsEmpty {j // e' j = 0} := ⟨fun j ↦ (he' j.1).ne' j.2⟩
      simp
    | succ k =>
      have h := sum_min_add_card_fiber e k
      have h' := sum_min_add_card_fiber e' k
      have h₀ := hsum k
      have h₁ := hsum (k + 1)
      have h₂ := hsum (k + 2)
      omega
  let σ := Equiv.ofFiberEquiv fun k ↦ Fintype.equivOfCardEq (hcard k)
  exact ⟨σ, fun i ↦ (Equiv.ofFiberEquiv_map _ i).symm⟩

end ZMod
