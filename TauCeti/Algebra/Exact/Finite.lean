/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import TauCeti.GroupTheory.Index.Exact

/-!
# Finiteness of the middle term of an exact sequence

For an exact sequence `A₀ → A₁ → A₂` of groups, the order of `A₁` divides `|A₀| * |A₂|`
(`MonoidHom.card_dvd_card_mul_card_of_exact`). Hence `A₁` is finite as soon as `A₀` and `A₂` are.
This file records that consequence for bundled homomorphisms of any type, in the form in which a
long exact cohomology sequence delivers it: finiteness of two consecutive outer terms forces
finiteness of the term between them.

## Main results

* `Function.MulExact.finite`, `Function.Exact.finite`: the middle term of an exact sequence of
  groups with finite outer terms is finite.
-/

public section

namespace Function.MulExact

variable {A₀ A₁ A₂ : Type*} [Group A₀] [Group A₁] [Group A₂] {F₀ F₁ : Type*} [FunLike F₀ A₀ A₁]
  [MonoidHomClass F₀ A₀ A₁] [FunLike F₁ A₁ A₂] [MonoidHomClass F₁ A₁ A₂] {f₀ : F₀} {f₁ : F₁}

/-- **The middle term of an exact sequence of finite groups is finite.** If `A₀ → A₁ → A₂` is an
exact sequence of groups and `A₀`, `A₂` are finite, then `A₁` is finite: its order divides
`|A₀| * |A₂|`, which is nonzero. -/
@[to_additive /-- **The middle term of an exact sequence of finite additive groups is finite.** If
`A₀ → A₁ → A₂` is an exact sequence of additive groups and `A₀`, `A₂` are finite, then `A₁` is
finite: its order divides `|A₀| * |A₂|`, which is nonzero. -/]
theorem finite (h : Function.MulExact f₀ f₁) [Finite A₀] [Finite A₂] : Finite A₁ :=
  Nat.finite_of_card_ne_zero fun h₁ ↦ Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
    (zero_dvd_iff.1 (h₁ ▸ MonoidHom.card_dvd_card_mul_card_of_exact (MonoidHom.ofClass f₀)
      (MonoidHom.ofClass f₁) (Function.MulExact.monoidHom_ker_eq
        (f := MonoidHom.ofClass f₀) (g := MonoidHom.ofClass f₁) h).symm))

end Function.MulExact
