/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.GaloisDual.Basic
public import TauCeti.FieldTheory.Finite.Frobenius

/-!
# Hermitian duals for the Frobenius automorphism

The Galois dual of a code for a semiring automorphism `σ` uses the form
`h(x, y) = ∑ i, x i * σ (y i)`. This file specializes `σ` to the Frobenius automorphism
`frobeniusEquiv R p`, sending `x` to `x ^ p`, of a perfect ring of exponential characteristic
`p`: membership in the dual is the vanishing of `∑ i, x i * y i ^ p` against every codeword.

Over a finite field of order `p ^ 2` the Frobenius is an involution, so its Galois dual is a
Hermitian dual: taking the dual twice recovers the code, and a matrix generates a code exactly
when its entrywise `p`-th power checks the dual. For `p = 2` this is Hermitian duality over the
field of four elements, the setting of the Hermitian self-dual hexacode. Omitting the entrywise
`p`-th power computes the Euclidean dual instead.

The conventions follow Huffman and Pless, *Fundamentals of Error-Correcting Codes*, §1.3.
-/

public section

namespace RingEquiv

variable {ι : Type*} [Fintype ι]

section PerfectRing

variable {R : Type*} [CommSemiring R] {p : ℕ} [ExpChar R p] [PerfectRing R p]

/-- Membership in the Frobenius Galois dual means orthogonality to every codeword for the form
`∑ i, x i * y i ^ p`. -/
@[simp]
theorem mem_galoisDual_frobeniusEquiv (C : Submodule R (ι → R)) (y : ι → R) :
    y ∈ galoisDual (frobeniusEquiv R p) C ↔ ∀ x ∈ C, ∑ i, x i * y i ^ p = 0 := by
  simp only [mem_galoisDual, frobeniusEquiv_def]

end PerfectRing

section Field

variable {K : Type*} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]

/-- Over a field of order `p ^ 2`, the Frobenius Galois dual of a row space is the kernel of the
entrywise `p`-th power of the generator. -/
theorem galoisDual_range_vecMulLinear_frobeniusEquiv (hK : Nat.card K = p ^ 2)
    {ρ : Type*} [Fintype ρ] (G : Matrix ρ ι K) :
    galoisDual (frobeniusEquiv K p) (LinearMap.range G.vecMulLinear) =
      LinearMap.ker (G.map (frobenius K p)).mulVecLin := by
  simpa only [coe_frobeniusEquiv] using
    galoisDual_range_vecMulLinear_of_involutive _
      (TauCeti.FiniteField.frobeniusEquiv_involutive hK) G

/-- Over a field of order `p ^ 2`, taking the Frobenius Galois dual twice recovers the code. -/
theorem galoisDual_galoisDual_frobeniusEquiv (hK : Nat.card K = p ^ 2)
    (C : Submodule K (ι → K)) :
    galoisDual (frobeniusEquiv K p) (galoisDual (frobeniusEquiv K p) C) = C :=
  galoisDual_galoisDual _ (TauCeti.FiniteField.frobeniusEquiv_involutive hK) C

/-- Over a field of order `p ^ 2`, a matrix generates a code exactly when its entrywise `p`-th
power checks the Frobenius Galois dual. -/
theorem range_vecMulLinear_eq_iff_ker_map_frobenius_eq_galoisDual_frobeniusEquiv
    (hK : Nat.card K = p ^ 2) {ρ : Type*} [Fintype ρ] (G : Matrix ρ ι K)
    (C : Submodule K (ι → K)) :
    LinearMap.range G.vecMulLinear = C ↔
      LinearMap.ker (G.map (frobenius K p)).mulVecLin = galoisDual (frobeniusEquiv K p) C := by
  simpa only [coe_frobeniusEquiv] using
    range_vecMulLinear_eq_iff_ker_map_eq_galoisDual_of_involutive _
      (TauCeti.FiniteField.frobeniusEquiv_involutive hK) G C

end Field

end RingEquiv
