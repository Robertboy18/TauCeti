/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Generators
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.DiagonalCartan
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

/-!
# The simple-coroot basis of the split type-D Cartan

The explicit type-D Chevalley generators use the Bourbaki simple roots as diagonal coordinates.
Over a commutative ring with invertible two, these vectors form a basis of the diagonal Cartan.
Their coordinates are prefix sums along the chain and half-total sums at the fork. The basis
expansion gives the Lie-span theorem used by the native split Lie algebra basis.

Independence over a commutative domain only requires that `2` be nonzero. This weaker result
comes from `DynkinType.linearIndependent_typeDSimpleRoot_cast`: the doubled fundamental
coweights pair with the simple roots diagonally by `2`, which is regular in such a domain.
The generator membership and coordinate lemmas live in `Root/Generators.lean`.

## Main declarations

* `TypeDStd.typeDSimpleCorootBasis`: the numbered simple coroots form a basis of the diagonal
  Cartan when two is invertible.
* `TypeDStd.typeDSimpleCorootBasis_repr_apply`: explicit coefficients from upper diagonal entries.
* `TypeDStd.linearIndependent_cartanGenerator`: the ambient Cartan generators are independent.
* `TypeDStd.typeDDiagonalCartan_eq_lieSpan_cartanGenerator`: they span the diagonal Cartan as a
  Lie subalgebra.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §13.
-/

public section

namespace TauCeti

namespace TypeDStd

section Domain

variable {K : Type*} [CommRing K] [IsDomain K] [NeZero (2 : K)]

private theorem linearIndependent_cartanGenerator_subtype (n : ℕ) (hn : 4 ≤ n) :
    LinearIndependent K (fun i : Fin n =>
      (⟨cartanGenerator (K := K) n hn i,
        cartanGenerator_mem_typeDDiagonalCartan n hn i⟩ : typeDDiagonalCartan K (Fin n))) := by
  have hrows : LinearIndependent K (fun i j =>
      (DynkinType.typeDSimpleRoot n hn i j : K)) :=
    DynkinType.linearIndependent_typeDSimpleRoot_cast
      (IsRegular.of_ne_zero (NeZero.ne (2 : K))).right hn
  have hcoord : LinearIndependent K (fun i =>
      typeDDiagonalEquiv (K := K) (ι := Fin n)
        (fun j => (DynkinType.typeDSimpleRoot n hn i j : K))) :=
    hrows.map' (typeDDiagonalEquiv (K := K) (ι := Fin n)).toLinearMap
      (typeDDiagonalEquiv (K := K) (ι := Fin n)).ker
  convert hcoord using 1
  funext i
  apply Subtype.ext
  exact cartanGenerator_eq_typeDDiagonalEquiv (K := K) n hn i

/-- The explicit simple-root Cartan generators are linearly independent in the ambient
type-D Lie algebra. -/
theorem linearIndependent_cartanGenerator (n : ℕ) (hn : 4 ≤ n) :
    LinearIndependent K (cartanGenerator (K := K) n hn) := by
  exact (linearIndependent_cartanGenerator_subtype (K := K) n hn).map'
    (typeDDiagonalCartan K (Fin n)).toSubmodule.subtype (Submodule.ker_subtype _)

end Domain

section InvertibleTwo

variable {K : Type*} [CommRing K] [Invertible (2 : K)]

/-- The Bourbaki simple coroots as a basis of the split type-`Dₙ` diagonal Cartan. -/
noncomputable def typeDSimpleCorootBasis (n : ℕ) (hn : 4 ≤ n) :
    Module.Basis (Fin n) K (typeDDiagonalCartan K (Fin n)) :=
  (DynkinType.typeDSimpleRootBasis K n hn).map typeDDiagonalEquiv

/-- The simple-coroot basis consists of the numbered Cartan generators. -/
@[simp]
theorem coe_typeDSimpleCorootBasis_apply (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    ((typeDSimpleCorootBasis (K := K) n hn i : typeDDiagonalCartan K (Fin n)) :
      LieAlgebra.Orthogonal.typeD (Fin n) K) = cartanGenerator n hn i := by
  rw [typeDSimpleCorootBasis, Module.Basis.map_apply, DynkinType.typeDSimpleRootBasis_apply]
  exact (cartanGenerator_eq_typeDDiagonalEquiv n hn i).symm

/-- The upper diagonal entries determine the coefficients in the simple-coroot basis. -/
theorem typeDSimpleCorootBasis_repr_apply (n : ℕ) (hn : 4 ≤ n)
    (A : typeDDiagonalCartan K (Fin n)) (k : Fin n) :
    (typeDSimpleCorootBasis (K := K) n hn).repr A k =
      if (k : ℕ) + 2 < n then ∑ j ∈ Finset.Iic k, A.1.1 (Sum.inl j) (Sum.inl j)
      else if (k : ℕ) + 1 < n then
        ⅟ (2 : K) * (∑ j, A.1.1 (Sum.inl j) (Sum.inl j)) -
          A.1.1 (Sum.inl ⟨n - 1, by omega⟩) (Sum.inl ⟨n - 1, by omega⟩)
      else ⅟ (2 : K) * (∑ j, A.1.1 (Sum.inl j) (Sum.inl j)) := by
  -- Unwrap Basis.map; the diagonal inverse itself is rewritten by its public coordinate lemma.
  change (DynkinType.typeDSimpleRootBasis K n hn).repr
    ((typeDDiagonalEquiv (K := K) (ι := Fin n)).symm A) k = _
  simpa only [typeDDiagonalEquiv_symm_apply] using
    DynkinType.typeDSimpleRootBasis_repr_apply K hn
      ((typeDDiagonalEquiv (K := K) (ι := Fin n)).symm A) k

end InvertibleTwo

section Field

variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- The explicit simple-root Cartan generators span the diagonal Cartan as a Lie subalgebra. -/
theorem typeDDiagonalCartan_eq_lieSpan_cartanGenerator (n : ℕ) (hn : 4 ≤ n) :
    typeDDiagonalCartan K (Fin n) =
      LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeD (Fin n) K)
        (Set.range (cartanGenerator (K := K) n hn)) := by
  let := invertibleOfNonzero (NeZero.ne (2 : K))
  apply le_antisymm
  · intro x hx
    let y : typeDDiagonalCartan K (Fin n) := ⟨x, hx⟩
    have hy := (typeDSimpleCorootBasis (K := K) n hn).sum_repr y
    have heq := congrArg (typeDDiagonalCartan K (Fin n)).toSubmodule.subtype hy
    simp only [map_sum, map_smul, Submodule.subtype_apply, coe_typeDSimpleCorootBasis_apply,
      y] at heq
    rw [← heq]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (LieSubalgebra.subset_lieSpan ⟨i, rfl⟩)
  · rw [LieSubalgebra.lieSpan_le]
    rintro x ⟨i, rfl⟩
    exact cartanGenerator_mem_typeDDiagonalCartan n hn i

end Field

end TypeDStd

end TauCeti
