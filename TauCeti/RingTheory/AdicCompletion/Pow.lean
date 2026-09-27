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
Precompleteness holds for `n = 0` as well, since every module is `⊤`-adically precomplete.

The main use is Hensel's lemma at `I ^ n`: an `I ^ n`-adically complete ring is Henselian at
`I ^ n` by Mathlib's `IsAdicComplete.henselianRing`, which lifts an approximate root modulo `I ^ n`
to a root congruent to it modulo `I ^ n`, and not merely modulo `I`.

## Main results

* `Submodule.pow_pow_smul_top_le`: the filtration comparison `(I ^ n) ^ m • ⊤ ≤ I ^ m • ⊤` for
  `n ≠ 0`.
* `IsHausdorff.pow`, `IsAdicComplete.pow`: adic Hausdorffness and completeness for `I` imply the
  same for `I ^ n` when `n ≠ 0`.
* `IsPrecomplete.pow`: adic precompleteness for `I` implies precompleteness for every `I ^ n`.
-/

public section

variable {R : Type*} [CommRing R] {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]

variable (I M) in
/-- **Filtration comparison for powers.** The `I ^ n`-adic filtration of `M` is finer than the
`I`-adic one: `(I ^ n) ^ m • ⊤ ≤ I ^ m • ⊤` for `n ≠ 0`. -/
theorem Submodule.pow_pow_smul_top_le {n : ℕ} (hn : n ≠ 0) (m : ℕ) :
    ((I ^ n) ^ m • ⊤ : Submodule R M) ≤ I ^ m • ⊤ := by
  rw [← pow_mul]
  exact Submodule.pow_smul_top_le I M (Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero hn))

/-- An `I`-adically Hausdorff module is `I ^ n`-adically Hausdorff for `n ≠ 0`. -/
theorem IsHausdorff.pow [IsHausdorff I M] {n : ℕ} (hn : n ≠ 0) : IsHausdorff (I ^ n) M where
  haus' x hx := IsHausdorff.haus' x fun m ↦ (hx m).mono (Submodule.pow_pow_smul_top_le I M hn m)

/-- An `I`-adically precomplete module is `I ^ n`-adically precomplete for every `n`. -/
theorem IsPrecomplete.pow [IsPrecomplete I M] (n : ℕ) : IsPrecomplete (I ^ n) M := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [pow_zero, Ideal.one_eq_top]
    exact IsPrecomplete.top M
  refine ⟨fun f hf ↦ ?_⟩
  -- A sequence that is Cauchy for the `I ^ n`-adic filtration is Cauchy for the `I`-adic one,
  -- so it has an `I`-adic limit `L`; the subsequence `f (n m)` shows that `L` is also the
  -- `I ^ n`-adic limit.
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' f fun {m k} hmk ↦
    (hf hmk).mono (Submodule.pow_pow_smul_top_le I M hn m)
  refine ⟨L, fun m ↦ (hf (Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero hn))).trans ?_⟩
  have := hL (n * m)
  rwa [pow_mul] at this

/-- An `I`-adically complete module is `I ^ n`-adically complete for `n ≠ 0`. -/
theorem IsAdicComplete.pow [IsAdicComplete I M] {n : ℕ} (hn : n ≠ 0) :
    IsAdicComplete (I ^ n) M where
  toIsHausdorff := IsHausdorff.pow hn
  toIsPrecomplete := IsPrecomplete.pow n
