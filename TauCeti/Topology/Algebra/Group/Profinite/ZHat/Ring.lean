/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Basic

/-!
# The ring of profinite integers

The profinite integers `ℤ̂ = zHat` are a profinite group written multiplicatively; this file puts
the ring structure on their additive presentation `Additive zHat`. Multiplication by `a` is the
unique continuous endomorphism of `ℤ̂` sending the generator `zHat.gen` to `a`, exactly as
multiplication by an integer is on `ℤ`: so `a * b` is `zHat.lift a b`, read additively. The unit
is the generator, and the casts of natural numbers and integers are its powers.

Every ring axiom is an instance of the universal property of `ℤ̂` or of the density of `ℤ` in it:
`1 * b = b` because the lift of the generator is the identity, `a * (b + c) = a * b + a * c`
because each lift is a homomorphism, `(a + b) * c = a * c + b * c` and `a * b = b * a` because
both sides are continuous and agree on the integers, and `(a * b) * c = a * (b * c)` by
naturality of the lift. The multiplication is jointly continuous, so `Additive zHat` is a
compact, totally disconnected topological ring.

This is the ring by which a profinite group is powered: the profinite power of an element `x` of
a profinite group by `a : ℤ̂` is `zHat.lift x a`, and by naturality of the lift (`zHat.map_lift`)
powering first by `a` and then by `b` is powering by the product `a * b` defined here.

## Main definitions

* The `CommRing (Additive zHat)` and `IsTopologicalRing (Additive zHat)` instances.

## Main results

* `TauCeti.zHat.toMul_mul`, `TauCeti.zHat.ofMul_lift`: the product is the lift.
* `TauCeti.zHat.toMul_one`, `TauCeti.zHat.toMul_natCast`, `TauCeti.zHat.toMul_intCast`,
  `TauCeti.zHat.ofMul_ofInt`: the unit and the casts of integers are the powers of the generator.

## Implementation notes

The multiplicative notation of `zHat` is the *addition* of the ring: the group product of two
elements of `zHat` is their sum in `Additive zHat`, and the ring product exists only on
`Additive zHat`. There is no second carrier of the profinite integers.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 2.3 and 4.1.
-/

public section

namespace TauCeti

namespace zHat

universe u

open Additive

/-- **The ring of profinite integers.** On `Additive zHat` the product of `a` and `b` is
`zHat.lift a b`, the value at `b` of the continuous endomorphism of `ℤ̂` sending the generator to
`a`; the unit is the generator, and the casts of `ℕ` and `ℤ` are its powers. -/
noncomputable instance instCommRing : CommRing (Additive zHat.{u}) :=
  { Additive.addGroup with
    add_comm a b := congrArg ofMul (mul_comm' a.toMul b.toMul)
    mul a b := ofMul (lift a.toMul b.toMul)
    one := ofMul gen
    natCast n := ofMul (gen ^ n)
    intCast n := ofMul (gen ^ n)
    natCast_zero := congrArg ofMul (pow_zero gen)
    natCast_succ n := congrArg ofMul (pow_succ gen n)
    intCast_ofNat n := congrArg ofMul (zpow_natCast gen n)
    intCast_negSucc n := congrArg ofMul (zpow_negSucc gen n)
    mul_assoc a b c := congrArg ofMul (map_lift (lift a.toMul) b.toMul c.toMul).symm
    one_mul a := congrArg ofMul (lift_gen_apply a.toMul)
    mul_one a := congrArg ofMul (lift_gen a.toMul)
    left_distrib a b c := congrArg ofMul (map_mul (lift a.toMul) b.toMul c.toMul)
    right_distrib a b c := congrArg ofMul (lift_mul_apply a.toMul b.toMul (mul_comm' _ _) c.toMul)
    zero_mul a := congrArg ofMul (lift_one_apply a.toMul)
    mul_zero a := congrArg ofMul (map_one (lift a.toMul))
    mul_comm a b := congrArg ofMul (lift_comm a.toMul b.toMul) }

@[simp]
theorem toMul_mul (a b : Additive zHat.{u}) :
    (a * b).toMul = (lift a.toMul : zHat.{u} →ₜ* zHat.{u}) b.toMul := by
  rfl

@[simp]
theorem ofMul_lift (a b : zHat.{u}) :
    ofMul ((lift a : zHat.{u} →ₜ* zHat.{u}) b) = ofMul a * ofMul b := by
  rfl

@[simp]
theorem toMul_one : (1 : Additive zHat.{u}).toMul = gen := by
  rfl

@[simp]
theorem ofMul_gen : ofMul (gen : zHat.{u}) = 1 := by
  rfl

@[simp]
theorem toMul_natCast (n : ℕ) : (n : Additive zHat.{u}).toMul = gen ^ n := by
  rfl

@[simp]
theorem toMul_intCast (n : ℤ) : (n : Additive zHat.{u}).toMul = gen ^ n := by
  rfl

/-- The canonical homomorphism from `ℤ` to the profinite integers is the integer cast of the
ring. -/
@[simp]
theorem ofMul_ofInt (z : Multiplicative ℤ) :
    ofMul ((ofInt : Multiplicative ℤ →* zHat.{u}) z) = (z.toAdd : Additive zHat.{u}) := by
  rw [← ofAdd_toAdd z, ofInt_ofAdd, ← toMul_intCast, ofMul_toMul, toAdd_ofAdd]

/-- The ring of profinite integers is a topological ring: its additive group is the topological
group `zHat`, and the product is jointly continuous. -/
instance : IsTopologicalRing (Additive zHat.{u}) where
  continuous_mul :=
    continuous_ofMul.comp (continuous_lift.comp (continuous_toMul.prodMap continuous_toMul))

end zHat

end TauCeti
