/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.RamificationIndex
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# The decomposition type at an odd ramified prime of a multiquadratic field

Let `K = ℚ(√d₁, …, √dₙ)` be a number field generated over `ℚ` by square roots `r i` of squarefree
integers `d i`, and let `p` be an odd prime. The decomposition law at `p` is known when `p` divides
no radicand (`TauCeti.NumberTheory.Multiquadratic.ResidueDegree`), and the ramification index at
`p` is known in general: it is `2` exactly when `p` divides some radicand
(`TauCeti.NumberTheory.Multiquadratic.RamificationIndex`). This file supplies the remaining
invariant, the residue degree `f` at an odd ramified prime, and with it the number `g` of primes
above `p`, completing the decomposition type `(e, f, g)` of every odd prime in `K`.

The residue degree divides `2` at every prime of `K`, ramified or not and `p = 2` included: it is
the order of the residue Frobenius, a homomorphic image of an element of the exponent-two group
`Gal(K/ℚ)` (`inertiaDeg_dvd_two`). At an odd prime `p` the residue degree is `1` exactly when an
arithmetic Frobenius `σ` at a prime `Q` above `p` lies in the inertia group of `Q`
(`Ideal.inertiaDeg_eq_one_iff_mem_inertia`). The inertia group is `{1, τ}` with `τ` the sign change
negating exactly the roots of the radicands divisible by `p` (`mem_inertia_iff`). The Frobenius
acts on the root of a radicand prime to `p` by its Legendre symbol, and on the quotient
`r i * r j / p` of two roots of radicands divisible by `p`, a square root of the integer
`(d i / p) * (d j / p)` prime to `p`, by the Legendre symbol of that integer. Comparing the two
actions gives the criterion: `f = 1` iff every radicand prime to `p` is a quadratic residue mod `p`
and every product `(d i / p) * (d j / p)` of two `p`-free parts is a quadratic residue mod `p`; the
second condition says that the `p`-free parts of the radicands divisible by `p` all have the same
Legendre symbol. These integers are exactly the radicands of the inertia field of `Q`, the largest
subfield of `K` in which `p` is unramified, and `f = 1` says that `p` splits completely there.

The `p`-free parts are not themselves radicands of `K`, so the residue degree at a ramified prime
is not read off the Legendre symbols of the radicands alone. In `ℚ(√3, √6)` the prime `3` has
residue degree `2`: the field contains `√2 = √6 / √3`, and `2` is a non-residue mod `3`. In
`ℚ(√3, √21)` it has residue degree `1`, since `7` is a residue mod `3`.

## Main results

* `TauCeti.Multiquadratic.inertiaDeg_dvd_two` and
  `TauCeti.Multiquadratic.inertiaDeg_eq_one_or_eq_two`: the residue degree of any prime of a
  multiquadratic field divides `2`.
* `TauCeti.Multiquadratic.isArithFrobAt_apply_mul_apply_eq_mul_iff`: a Frobenius fixes the product
  of two roots of radicands divisible by `p` iff the product of their `p`-free parts is a residue.
* `TauCeti.Multiquadratic.inertiaDeg_eq_one_iff` and
  `TauCeti.Multiquadratic.inertiaDeg_eq_two_iff`: at an odd prime `p` and squarefree radicands,
  the residue degree is `1` iff every radicand prime to `p` is a residue mod `p` and the `p`-free
  parts of the radicands divisible by `p` have pairwise residue products; otherwise it is `2`.
* `TauCeti.Multiquadratic.ncard_primesOver_eq_two_pow_sub_one_of_dvd` and
  `TauCeti.Multiquadratic.ncard_primesOver_eq_two_pow_sub_two`: under square-class independence
  of `n` radicands, an odd prime dividing some radicand has `2 ^ (n - 1)` primes above it when the
  residue degree is `1`, and `2 ^ (n - 2)` when it is `2`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §5.B.
* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9.
-/

public section

open NumberField Ideal Module MulAction
open scoped NumberField Pointwise

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} {d : ι → ℤ} {r : ι → K}
  {p : ℕ} [Fact p.Prime]

/-! ### The residue degree divides two -/

variable (p) in
/-- **The residue degree of a prime of a multiquadratic field divides `2`.** Let `K` be generated
over `ℚ` by square roots of integers `d i`, and let `Q` be a prime of `𝓞 K` above a prime `p`,
ramified or not. The residue degree of `Q` is the order of the residue Frobenius, a homomorphic
image of an element of `Gal(K/ℚ)`, a group of exponent `2`. -/
theorem inertiaDeg_dvd_two [Finite ι] (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] : Q.inertiaDeg ℤ ∣ 2 := by
  have := isGalois_rat hr htop
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt_int_of_liesOver (p := p) Q
  exact (Ideal.inertiaDeg_dvd_orderOf (p := p) Q hσ).trans (orderOf_dvd_of_pow_eq_one
    (aut_pow_two_eq_one_of_adjoin_eq_top (d := fun i => (d i : ℚ))
      (fun i => by rw [hr i]; simp) htop σ))

variable (p) in
/-- The residue degree of a prime of a multiquadratic field is `1` or `2`. -/
theorem inertiaDeg_eq_one_or_eq_two [Finite ι] (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] : Q.inertiaDeg ℤ = 1 ∨ Q.inertiaDeg ℤ = 2 :=
  (Nat.dvd_prime Nat.prime_two).mp (inertiaDeg_dvd_two p hr htop Q)

/-! ### The Frobenius on the product of two ramified roots -/

/-- **A Frobenius fixes the product of two ramified roots exactly at a residue.** Let `Q` be a
prime of `𝓞 K` above an odd prime `p`, let `r i`, `r j` be square roots of integers `d i`, `d j`
divisible by `p` but not by `p²`, and let `σ` be an arithmetic Frobenius at `Q`. Then
`σ (r i) * σ (r j) = r i * r j` iff `(d i / p) * (d j / p)` is a quadratic residue mod `p`, because
`r i * r j / p` is a square root of that integer, which is prime to `p`. -/
theorem isArithFrobAt_apply_mul_apply_eq_mul_iff (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (hodd : p ≠ 2) {i j : ι} (hi : (p : ℤ) ∣ d i) (hi2 : ¬ (p : ℤ) ^ 2 ∣ d i)
    (hj : (p : ℤ) ∣ d j) (hj2 : ¬ (p : ℤ) ^ 2 ∣ d j) (Q : Ideal (𝓞 K))
    [Q.LiesOver (span {(p : ℤ)})] {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q) :
    σ (r i) * σ (r j) = r i * r j ↔ legendreSym p (d i / p * (d j / p)) = 1 := by
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [← isArithFrobAt_apply_sqrt_eq_self_iff hodd (not_dvd_ediv_mul_ediv hi hi2 hj hj2)
    (mul_div_natCast_sq hr hi hj) Q hσ, map_div₀, map_mul, map_natCast, div_left_inj' hp0]

/-! ### The residue degree at an odd prime -/

variable (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
  (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hodd : p ≠ 2)
  (hsf : ∀ i, Squarefree (d i)) (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]
include hr htop hodd hsf

/-- **Residue degree one at an odd prime.** Let `K` be generated over `ℚ` by square roots `r i` of
squarefree integers `d i`, and let `Q` be a prime of `𝓞 K` above an odd prime `p`. Then `Q` has
residue degree `1` iff every radicand prime to `p` is a quadratic residue mod `p` and, for any two
radicands `d i`, `d j` divisible by `p`, the product `(d i / p) * (d j / p)` of their `p`-free parts
is a quadratic residue mod `p`. When `p` divides no radicand the second condition is empty and this
is `inertiaDeg_eq_one_iff_forall_legendreSym_eq_one`. -/
theorem inertiaDeg_eq_one_iff [Finite ι] :
    Q.inertiaDeg ℤ = 1 ↔
      (∀ i, ¬ (p : ℤ) ∣ d i → legendreSym p (d i) = 1) ∧
        ∀ i j, (p : ℤ) ∣ d i → (p : ℤ) ∣ d j → legendreSym p (d i / p * (d j / p)) = 1 := by
  have := isGalois_rat hr htop
  have hd (i : ι) : ¬ (p : ℤ) ^ 2 ∣ d i := fun h =>
    (Nat.prime_iff_prime_int.mp Fact.out).not_isUnit (hsf i _ (by rwa [← pow_two]))
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt_int_of_liesOver (p := p) Q
  rw [Ideal.inertiaDeg_eq_one_iff_mem_inertia (p := p) Q hσ]
  constructor
  · intro hmem
    refine ⟨fun i hi => ?_, fun i j hi hj => ?_⟩
    · exact (isArithFrobAt_apply_sqrt_eq_self_iff hodd hi (hr i) Q hσ).mp
        (apply_eq_self_of_mem_inertia (hr i) hodd hi Q hmem)
    · exact (isArithFrobAt_apply_mul_apply_eq_mul_iff hr hodd hi (hd i) hj (hd j) Q hσ).mp
        (apply_mul_apply_eq_mul_of_mem_inertia hr hodd hi (hd i) hj (hd j) Q hmem)
  · rintro ⟨hfix, hpair⟩
    -- `σ` fixes the roots of the radicands prime to `p`, and multiplies the roots of the
    -- radicands divisible by `p` by a common sign; so it is the identity or the sign change.
    have hfix' (i : ι) (hi : ¬ (p : ℤ) ∣ d i) : σ (r i) = r i :=
      (isArithFrobAt_apply_sqrt_eq_self_iff hodd hi (hr i) Q hσ).mpr (hfix i hi)
    by_cases hneg : ∃ i, (p : ℤ) ∣ d i ∧ σ (r i) = -r i
    · obtain ⟨i, hi, hi'⟩ := hneg
      have hri : r i ≠ 0 := by
        intro h0
        apply (hsf i).ne_zero
        have h := hr i
        rwa [h0, zero_pow two_ne_zero, eq_comm,
          map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ K)] at h
      refine (mem_inertia_iff hr htop hodd Q hsf hi).mpr (Or.inr fun j => ?_)
      split_ifs with hj
      · have h := (isArithFrobAt_apply_mul_apply_eq_mul_iff hr hodd hi (hd i) hj (hd j) Q
          hσ).mpr (hpair i j hi hj)
        rw [hi', neg_mul, neg_eq_iff_eq_neg, ← mul_neg] at h
        exact mul_left_cancel₀ hri h
      · exact hfix' j hj
    · push Not at hneg
      suffices σ = 1 by rw [this]; exact one_mem _
      refine TauCeti.IntermediateField.algEquiv_eq_one_of_adjoin_eq_top htop ?_
      rintro _ ⟨i, rfl⟩
      by_cases hi : (p : ℤ) ∣ d i
      · have hsq : σ (r i) ^ 2 = r i ^ 2 := by rw [← map_pow, hr i]; simp
        exact (eq_or_eq_neg_of_sq_eq_sq _ _ hsq).resolve_right (hneg i hi)
      · exact hfix' i hi

/-- **Residue degree two at an odd prime.** Let `K` be generated over `ℚ` by square roots of
squarefree integers `d i`, and let `Q` be a prime of `𝓞 K` above an odd prime `p`. Then `Q` has
residue degree `2` iff some radicand prime to `p` is a quadratic non-residue mod `p`, or two
radicands `d i`, `d j` divisible by `p` have `p`-free parts whose product `(d i / p) * (d j / p)` is
a non-residue mod `p`. Together with `inertiaDeg_eq_one_iff`, the residue degree is always `1`
or `2`. -/
theorem inertiaDeg_eq_two_iff [Finite ι] :
    Q.inertiaDeg ℤ = 2 ↔
      (∃ i, ¬ (p : ℤ) ∣ d i ∧ legendreSym p (d i) = -1) ∨
        ∃ i j, (p : ℤ) ∣ d i ∧ (p : ℤ) ∣ d j ∧ legendreSym p (d i / p * (d j / p)) = -1 := by
  have hd (i : ι) : ¬ (p : ℤ) ^ 2 ∣ d i := fun h =>
    (Nat.prime_iff_prime_int.mp Fact.out).not_isUnit (hsf i _ (by rwa [← pow_two]))
  -- Away from `p`, a Legendre symbol that is not `1` is `-1`.
  have hneg {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) : legendreSym p a = -1 ↔ ¬ legendreSym p a = 1 :=
    legendreSym.eq_neg_one_iff_not_one p fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  have h1 : (∃ i, ¬ (p : ℤ) ∣ d i ∧ legendreSym p (d i) = -1) ↔
      ¬ ∀ i, ¬ (p : ℤ) ∣ d i → legendreSym p (d i) = 1 := by
    simp only [not_forall, exists_prop]
    exact exists_congr fun i => and_congr_right fun hi => hneg hi
  have h2 : (∃ i j, (p : ℤ) ∣ d i ∧ (p : ℤ) ∣ d j ∧ legendreSym p (d i / p * (d j / p)) = -1) ↔
      ¬ ∀ i j, (p : ℤ) ∣ d i → (p : ℤ) ∣ d j → legendreSym p (d i / p * (d j / p)) = 1 := by
    simp only [not_forall, exists_prop]
    exact exists_congr fun i => exists_congr fun j => and_congr_right fun hi =>
      and_congr_right fun hj => hneg (not_dvd_ediv_mul_ediv hi (hd i) hj (hd j))
  rw [h1, h2, ← not_and_or, ← inertiaDeg_eq_one_iff hr htop hodd hsf Q]
  rcases inertiaDeg_eq_one_or_eq_two p hr htop Q with h | h <;> simp [h]

/-! ### The number of primes above an odd ramified prime -/

/-- **The number of primes above an odd ramified prime of residue degree one.** Let `K` be
generated over `ℚ` by square roots of `n` square-class independent squarefree integers `d i` (no
nonempty subset product is a square), and let `p` be an odd prime dividing some `d i` such that
every radicand prime to `p` is a residue mod `p` and the `p`-free parts of the radicands divisible
by `p` have pairwise residue products. Then there are exactly `2 ^ (n - 1)` primes of `𝓞 K`
above `p`. -/
theorem ncard_primesOver_eq_two_pow_sub_one_of_dvd [Finite ι]
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, (d i : ℚ)))
    {i : ι} (hi : (p : ℤ) ∣ d i)
    (hres : (∀ i, ¬ (p : ℤ) ∣ d i → legendreSym p (d i) = 1) ∧
      ∀ i j, (p : ℤ) ∣ d i → (p : ℤ) ∣ d j → legendreSym p (d i / p * (d j / p)) = 1) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 2 ^ (Nat.card ι - 1) := by
  obtain ⟨Q, _, _⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) (span {(p : ℤ)})
  refine eq_two_pow_sub_of_mul_two_pow_eq_finrank hr htop hindep (k := 1) ?_
  have h := ncard_primesOver_mul_inertiaDeg_mul_two_eq_finrank hr htop hodd Q hsf hi
  rwa [(inertiaDeg_eq_one_iff hr htop hodd hsf Q).mpr hres, mul_one, ← pow_one 2] at h

/-- **The number of primes above an odd ramified prime of residue degree two.** Let `K` be
generated over `ℚ` by square roots of `n` square-class independent squarefree integers `d i` (no
nonempty subset product is a square), and let `p` be an odd prime dividing some `d i` such that
some radicand prime to `p` is a non-residue mod `p`, or two radicands divisible by `p` have `p`-free
parts with a non-residue product. Then there are exactly `2 ^ (n - 2)` primes of `𝓞 K` above `p`:
the decomposition type is `e = 2`, `f = 2`, `g = 2 ^ (n - 2)`. -/
theorem ncard_primesOver_eq_two_pow_sub_two [Finite ι]
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, (d i : ℚ)))
    {i : ι} (hi : (p : ℤ) ∣ d i)
    (hnr : (∃ i, ¬ (p : ℤ) ∣ d i ∧ legendreSym p (d i) = -1) ∨
      ∃ i j, (p : ℤ) ∣ d i ∧ (p : ℤ) ∣ d j ∧ legendreSym p (d i / p * (d j / p)) = -1) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 2 ^ (Nat.card ι - 2) := by
  obtain ⟨Q, _, _⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) (span {(p : ℤ)})
  refine eq_two_pow_sub_of_mul_two_pow_eq_finrank hr htop hindep (k := 2) ?_
  have h := ncard_primesOver_mul_inertiaDeg_mul_two_eq_finrank hr htop hodd Q hsf hi
  rwa [(inertiaDeg_eq_two_iff hr htop hodd hsf Q).mpr hnr, mul_assoc, ← pow_two] at h

end TauCeti.Multiquadratic
