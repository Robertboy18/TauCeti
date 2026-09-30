/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Extending additive homomorphisms between groups killed by a prime

An additive commutative group killed by a prime `p` is an `𝔽_p`-vector space, through
`AddCommGroup.zmodModule`, and every additive homomorphism between two such groups is `𝔽_p`-linear.
Since an injective linear map of vector spaces has a linear left inverse, an additive homomorphism
out of a group killed by `p` extends along any injective additive homomorphism with that source into
another group killed by `p`. In other words, `Hom(-, N)` is exact on the additive groups killed by
`p` whenever `N` is one of them; this is the algebraic input to the duality statements for finite
`𝔽_p[G]`-modules.

Primality is essential: with `p = 4`, the identity of `2ℤ/4ℤ ≅ ℤ/2ℤ` does not extend along the
inclusion `2ℤ/4ℤ ⊆ ℤ/4ℤ` to a homomorphism `ℤ/4ℤ → ℤ/2ℤ`, since every such homomorphism kills
`2ℤ/4ℤ`.

## Main results

* `AddMonoidHom.exists_comp_eq_of_injective`: for `p` prime and `B`, `N` killed by `p`,
  every additive homomorphism `A →+ N` is the restriction along an injective `f : A →+ B` of an
  additive homomorphism `B →+ N`.
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {A B N : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup N]

/-- **Extension along an injection of groups killed by a prime.** If `p` is prime and `B` and `N`
are killed by `p`, every additive homomorphism `φ : A →+ N` extends along an injective additive
homomorphism `f : A →+ B` to a homomorphism `ψ : B →+ N` with `ψ ∘ f = φ`. -/
theorem _root_.AddMonoidHom.exists_comp_eq_of_injective (hB : ∀ b : B, p • b = 0)
    (hN : ∀ x : N, p • x = 0) {f : A →+ B} (hf : Function.Injective f) (φ : A →+ N) :
    ∃ ψ : B →+ N, ψ.comp f = φ := by
  have hA : ∀ a : A, p • a = 0 := fun a => hf (by rw [map_nsmul, hB, map_zero])
  let := AddCommGroup.zmodModule hA
  let := AddCommGroup.zmodModule hB
  let := AddCommGroup.zmodModule hN
  obtain ⟨g, hg⟩ := (f.toZModLinearMap p).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hf)
  refine ⟨((φ.toZModLinearMap p).comp g).toAddMonoidHom, AddMonoidHom.ext fun a => ?_⟩
  have h := LinearMap.congr_fun hg a
  simp only [LinearMap.comp_apply, AddMonoidHom.coe_toZModLinearMap,
    LinearMap.id_apply] at h
  simp [h]

end TauCeti
