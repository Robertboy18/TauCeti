/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# The integral trace on extended ideals

Mathlib's `Algebra.intTrace A B` is the trace of a finite extension of integrally closed domains
`B / A`, restricted from the fraction fields to the rings themselves. This file records that it
is compatible with the ideals of the base: the trace carries the extended ideal `p · B` of an
ideal `p` of `A` back into `p`, because it is `A`-linear with values in `A`.

This is the elementary half of the computation of the trace of an ideal of `B`. The other half,
which reads the exact image off the different ideal, is in
`TauCeti.RingTheory.DedekindDomain.Different.Trace`.

## Main results

* `Algebra.intTrace_mem_of_mem_map`: `Tr(p · B) ⊆ p`.
-/

public section

namespace Algebra

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [IsIntegrallyClosed B]
variable [Module.Finite A B] [Module.IsTorsionFree A B]

/-- The integral trace carries the extended ideal `p · B` of an ideal `p` of the base ring back
into `p`. -/
theorem intTrace_mem_of_mem_map {p : Ideal A} {x : B} (hx : x ∈ p.map (algebraMap A B)) :
    intTrace A B x ∈ p := by
  have hx' : x ∈ p • (⊤ : Submodule A B) := by
    rw [Ideal.smul_top_eq_map]
    exact hx
  refine Submodule.smul_induction_on hx' (fun a ha y _ ↦ ?_) fun y z hy hz ↦ ?_
  · rw [map_smul, smul_eq_mul]
    exact p.mul_mem_right _ ha
  · rw [map_add]
    exact p.add_mem hy hz

end Algebra
