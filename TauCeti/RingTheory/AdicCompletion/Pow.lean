/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Adic completeness for powers of an ideal

For an ideal `I` of a commutative ring `R` and a positive natural number `n`, the `I ^ n`-adic
filtration `(I ^ n) ^ m • ⊤ = I ^ (n m) • ⊤` of an `R`-module `M` is cofinal in the `I`-adic one.
So an `I`-adically Hausdorff, precomplete, or complete module has the same property for `I ^ n`.

The main use is Hensel's lemma at `I ^ n`: an `I ^ n`-adically complete ring is Henselian at
`I ^ n` by Mathlib's `IsAdicComplete.henselianRing`, which lifts an approximate root modulo `I ^ n`
to a root congruent to it modulo `I ^ n`, and not merely modulo `I`.

## Main results

* `IsHausdorff.pow`, `IsPrecomplete.pow`, `IsAdicComplete.pow`: adic Hausdorffness,
  precompleteness, and completeness for `I` imply the same for `I ^ n` when `n ≠ 0`.
-/

public section

variable {R : Type*} [CommRing R] {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]

/-- The `I ^ n`-adic filtration is finer than the `I`-adic one: `(I ^ n) ^ m • ⊤ ≤ I ^ m • ⊤`. -/
private theorem pow_pow_smul_top_le {n : ℕ} (hn : n ≠ 0) (m : ℕ) :
    ((I ^ n) ^ m • ⊤ : Submodule R M) ≤ I ^ m • ⊤ := by
  refine Submodule.smul_mono_left ?_
  rw [← pow_mul]
  exact Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero hn))

/-- An `I`-adically Hausdorff module is `I ^ n`-adically Hausdorff for `n ≠ 0`. -/
theorem IsHausdorff.pow [IsHausdorff I M] {n : ℕ} (hn : n ≠ 0) : IsHausdorff (I ^ n) M where
  haus' x hx := IsHausdorff.haus' x fun m ↦ (hx m).mono (pow_pow_smul_top_le hn m)

/-- An `I`-adically precomplete module is `I ^ n`-adically precomplete for `n ≠ 0`. -/
theorem IsPrecomplete.pow [IsPrecomplete I M] {n : ℕ} (hn : n ≠ 0) : IsPrecomplete (I ^ n) M where
  prec' f hf := by
    -- A sequence that is Cauchy for the `I ^ n`-adic filtration is Cauchy for the `I`-adic one,
    -- so it has an `I`-adic limit `L`; the subsequence `f (n m)` shows that `L` is also the
    -- `I ^ n`-adic limit.
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' f fun {m k} hmk ↦ (hf hmk).mono (pow_pow_smul_top_le hn m)
    refine ⟨L, fun m ↦ (hf (Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero hn))).trans ?_⟩
    have := hL (n * m)
    rwa [pow_mul] at this

/-- An `I`-adically complete module is `I ^ n`-adically complete for `n ≠ 0`. -/
theorem IsAdicComplete.pow [IsAdicComplete I M] {n : ℕ} (hn : n ≠ 0) :
    IsAdicComplete (I ^ n) M where
  toIsHausdorff := IsHausdorff.pow hn
  toIsPrecomplete := IsPrecomplete.pow hn
