/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Lying over along an algebra map into an integral algebra

Mathlib's lying-over theorem `Ideal.exists_ideal_over_prime_of_isIntegral` is stated for an
algebra `T` over `S` that is integral over `S`. Here the map `S → T` is an arbitrary `R`-algebra
map `g` between two `R`-algebras, of which only `T` is assumed integral over `R`: then `T` is
integral over `S` through `g`, so every prime of `S` containing the kernel of `g` is the
contraction of a prime of `T`. Stating this for `g` rather than for an `Algebra S T` instance
means it can be applied to a map between subalgebras, such as integral closures, without installing
an algebra structure at the point of use.

## Main results

* `Ideal.exists_comap_eq_of_isIntegral`: a prime of `S` containing the kernel of `g` is the
  contraction along `g` of a prime of `T`.
-/

public section

namespace Ideal

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- Lying over along an `R`-algebra map `g : S → T` with `T` integral over `R`: a prime `P` of `S`
containing the kernel of `g` is the contraction along `g` of a prime of `T`. -/
theorem exists_comap_eq_of_isIntegral [Algebra.IsIntegral R T] (P : Ideal S) [P.IsPrime]
    (g : S →ₐ[R] T) (hP : RingHom.ker g ≤ P) : ∃ Q : Ideal T, Q.IsPrime ∧ Q.comap g = P := by
  let _ : Algebra S T := g.toRingHom.toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  have : Algebra.IsIntegral S T := ⟨fun x => (Algebra.IsIntegral.isIntegral (R := R) x).tower_top⟩
  obtain ⟨Q, -, hQ, hQP⟩ := exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal T)
    (by rwa [← RingHom.ker_eq_comap_bot])
  exact ⟨Q, hQ, hQP⟩

end Ideal
