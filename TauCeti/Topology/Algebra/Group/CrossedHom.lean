/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Crossed homomorphisms twisted by a character

Let `H` be a group, `R` a commutative ring and `χ : H →* Rˣ` a character. A function `F : H → R`
is a **crossed homomorphism** for `χ` when

  `F (x * y) = χ x * F y + F x`

for all `x y : H` (`TauCeti.IsCrossedHom`). These are the `1`-cocycles of `H` with values in `R`
on which `H` acts through `χ`, written without a module structure on `R`: for `R = ℤ_p` and a
continuous character `χ : G →ₜ* ℤ_pˣ` of a pro-`p` group, the continuous crossed homomorphisms
`G → ℤ_p` for `χ` are the compatible systems of continuous `1`-cocycles with values in the twisted
coefficients `I(χ)/pⁱ`, and their values on a minimal generating tuple are what Labute's
prescription property of `χ` prescribes.

This file records the elementary calculus of crossed homomorphisms: the values at `1`, at an
inverse and at a power, the value on a product of elements on which the character is trivial, the
composite with a homomorphism, and the fact that two continuous crossed homomorphisms for the same
character into a Hausdorff ring agreeing on a topological generating set of `H` are equal.

## Main definitions

* `TauCeti.IsCrossedHom`: `F : H → R` is a crossed homomorphism for `χ : H →* Rˣ`.

## Main results

* `TauCeti.IsCrossedHom.map_pow`: `F (x ^ k) = (1 + χ x + ⋯ + χ x ^ (k - 1)) * F x`.
* `TauCeti.IsCrossedHom.map_list_prod_of_forall_eq_one`: on a product of elements on which `χ` is
  trivial, `F` is additive.
* `TauCeti.IsCrossedHom.eq_of_eqOn_of_topologicalClosure_closure_eq_top`: two continuous crossed
  homomorphisms agreeing on a topological generating set are equal.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §2.3.
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2.
-/

public section

namespace TauCeti

variable {H : Type*} [Group H] {R : Type*} [CommRing R] {F' : Type*} [FunLike F' H Rˣ]

/-- A function `F : H → R` is a **crossed homomorphism** for the character `χ : H →* Rˣ` when
`F (x * y) = χ x * F y + F x` for all `x y : H`: it is a `1`-cocycle for the action of `H` on `R`
through `χ`. -/
def IsCrossedHom (χ : F') (F : H → R) : Prop :=
  ∀ x y, F (x * y) = (χ x : R) * F y + F x

variable {χ : F'} {F : H → R}

/-- The defining property of `IsCrossedHom`. -/
theorem isCrossedHom_iff : IsCrossedHom χ F ↔ ∀ x y, F (x * y) = (χ x : R) * F y + F x :=
  Iff.rfl

namespace IsCrossedHom

variable (hF : IsCrossedHom χ F)
include hF

/-- The cocycle identity of a crossed homomorphism. -/
theorem map_mul (x y : H) : F (x * y) = (χ x : R) * F y + F x :=
  hF x y

variable [MonoidHomClass F' H Rˣ]

/-- A crossed homomorphism vanishes at `1`. -/
theorem map_one : F 1 = 0 := by
  have h := hF.map_mul 1 1
  rw [one_mul, _root_.map_one, Units.val_one, one_mul] at h
  simpa using h

/-- The value of a crossed homomorphism at an inverse, multiplied through by the character. -/
theorem mul_map_inv (x : H) : (χ x : R) * F x⁻¹ = -F x := by
  have h := hF.map_mul x x⁻¹
  rw [mul_inv_cancel, hF.map_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The value of a crossed homomorphism at an inverse. -/
theorem map_inv (x : H) : F x⁻¹ = -(((χ x)⁻¹ : Rˣ) : R) * F x := by
  calc F x⁻¹ = (((χ x)⁻¹ : Rˣ) : R) * ((χ x : R) * F x⁻¹) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = -(((χ x)⁻¹ : Rˣ) : R) * F x := by rw [hF.mul_map_inv, mul_neg, neg_mul]

/-- The value of a crossed homomorphism at a power is a geometric sum in the character times the
value at the base. -/
theorem map_pow (x : H) (k : ℕ) :
    F (x ^ k) = (∑ j ∈ Finset.range k, (χ x : R) ^ j) * F x := by
  induction k with
  | zero => simp [hF.map_one]
  | succ k ih =>
    rw [pow_succ, hF.map_mul, ih, _root_.map_pow, Units.val_pow_eq_pow_val,
      Finset.sum_range_succ, add_mul, add_comm]

/-- On an element on which the character is trivial, a crossed homomorphism is additive along
powers: `F (x ^ k) = k * F x`. -/
theorem map_pow_of_eq_one {x : H} (hx : χ x = 1) (k : ℕ) : F (x ^ k) = k * F x := by
  rw [hF.map_pow, hx, Units.val_one]
  simp

/-- On a product of elements on which the character is trivial, a crossed homomorphism is
additive. -/
theorem map_list_prod_of_forall_eq_one {l : List H} (hl : ∀ a ∈ l, χ a = 1) :
    F l.prod = (l.map F).sum := by
  induction l with
  | nil => simp [hF.map_one]
  | cons a l ih =>
    rw [List.prod_cons, hF.map_mul, hl a (by simp), Units.val_one, one_mul,
      ih fun b hb ↦ hl b (by simp [hb]), List.map_cons, List.sum_cons, add_comm]

omit [MonoidHomClass F' H Rˣ] in
/-- The composite of a crossed homomorphism for `χ` with a homomorphism `φ` is a crossed
homomorphism for the character `χ ∘ φ`. -/
theorem comp {H' : Type*} [Group H'] {F'' : Type*} [FunLike F'' H' H] [MonoidHomClass F'' H' H]
    (φ : F'') {F''' : Type*} [FunLike F''' H' Rˣ] {χ' : F'''} (hχ' : ∀ x, χ' x = χ (φ x)) :
    IsCrossedHom χ' (F ∘ φ) := fun x y ↦ by
  rw [Function.comp_apply, _root_.map_mul, hF.map_mul, hχ', Function.comp_apply,
    Function.comp_apply]

section Topology

variable [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace R] [T2Space R]

omit hF in
/-- **Two continuous crossed homomorphisms for the same character agreeing on a topological
generating set are equal.** The set where they agree is a closed subgroup. -/
theorem eq_of_eqOn_of_topologicalClosure_closure_eq_top {F₁ F₂ : H → R} (h₁ : IsCrossedHom χ F₁)
    (h₂ : IsCrossedHom χ F₂) (hc₁ : Continuous F₁) (hc₂ : Continuous F₂) {s : Set H}
    (hs : (Subgroup.closure s).topologicalClosure = ⊤) (h : Set.EqOn F₁ F₂ s) : F₁ = F₂ := by
  -- The two functions agree on the subgroup generated by `s`, hence on its closure.
  have hsub : ∀ x ∈ Subgroup.closure s, F₁ x = F₂ x := fun x hx ↦
    Subgroup.closure_induction (p := fun x _ ↦ F₁ x = F₂ x) (fun x hx ↦ h hx)
      (by rw [h₁.map_one, h₂.map_one])
      (fun x y _ _ hx hy ↦ by rw [h₁.map_mul, h₂.map_mul, hx, hy])
      (fun x _ hx ↦ by rw [h₁.map_inv, h₂.map_inv, hx]) hx
  have hcl : closure ((Subgroup.closure s : Subgroup H) : Set H) ⊆ {x | F₁ x = F₂ x} :=
    (isClosed_eq hc₁ hc₂).closure_subset_iff.2 fun x hx ↦ hsub x hx
  funext x
  have hx : x ∈ (Subgroup.closure s).topologicalClosure := by
    rw [hs]
    exact Subgroup.mem_top x
  exact hcl (Subgroup.topologicalClosure_coe.subset hx)

end Topology

end IsCrossedHom

end TauCeti
