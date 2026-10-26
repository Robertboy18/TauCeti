/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.AllGenerators
public import Mathlib.LinearAlgebra.Basis.Defs
import TauCeti.LinearAlgebra.Matrix.Alternating

/-!
# Native matrix coordinates for the split even orthogonal Lie algebra

A matrix in the split even orthogonal Lie algebra has blocks `[[A, B], [C, -Aᵀ]]`,
where `B` and `C` are skew-symmetric. When doubling has trivial kernel, their diagonals vanish.
The entries of `A` and the strict upper triangles of `B` and `-C` give coordinates, without
dividing by two. The corresponding basis consists of the existing difference-root generators,
positive sum-root generators, and reversed negative sum-root generators.

The diagonal basis members are the individual hyperbolic diagonal matrices. For `ι = Fin n`
with `4 ≤ n`, the simple coroots instead span the even-sum sublattice over `ℤ`, of index two
in the full diagonal lattice.
-/

public section

namespace TauCeti.TypeDStd

variable {R ι : Type*} [CommRing R] [LinearOrder ι]

private def upperCompletion (b : {p : ι × ι // p.1 < p.2} → R) : Matrix ι ι R :=
  fun i j => if h : i < j then b ⟨(i, j), h⟩
    else if h : j < i then -b ⟨(j, i), h⟩ else 0

private theorem upperCompletion_transpose (b : {p : ι × ι // p.1 < p.2} → R) :
    (upperCompletion b).transpose = -upperCompletion b := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [upperCompletion, h, not_lt_of_ge (le_of_lt h)]
  · simp [upperCompletion]
  · simp [upperCompletion, h, not_lt_of_ge (le_of_lt h)]

private theorem upperCompletion_diag (b : {p : ι × ι // p.1 < p.2} → R) (i : ι) :
    upperCompletion b i i = 0 := by
  simp [upperCompletion]

private theorem upperCompletion_apply (b : {p : ι × ι // p.1 < p.2} → R)
    (p : {p : ι × ι // p.1 < p.2}) :
    upperCompletion b p.val.1 p.val.2 = b p := by
  simp [upperCompletion, p.property]

private theorem upperCompletion_entries
    (h2 : ∀ x : R, x + x = 0 → x = 0) (M : Matrix ι ι R) (hM : M.transpose = -M) :
    upperCompletion (fun p => M p.val.1 p.val.2) = M := by
  apply Matrix.ext_of_lt_of_transpose_eq_neg
    (upperCompletion_transpose _) hM (upperCompletion_diag _)
    (Matrix.diag_eq_zero_of_transpose_eq_neg hM h2)
  intro i j hij
  exact upperCompletion_apply _ ⟨(i, j), hij⟩

/-- The full upper-left block and the two strict upper triangles index the native matrix basis. -/
abbrev RootEntryIndex (ι : Type*) [LT ι] :=
  (ι × ι) ⊕ ({p : ι × ι // p.1 < p.2} ⊕ {p : ι × ι // p.1 < p.2})

variable [Fintype ι]

/-- Entry coordinates on the split even orthogonal Lie algebra when doubling has trivial kernel.

The negative-root coordinates are the negatives of the lower-left upper entries. For
`ι = Fin n` with `4 ≤ n`, this makes the basis member at `(n - 2, n - 1)` agree with
the numbered lowering generator at the fork. -/
def rootEntryEquiv (h2 : ∀ x : R, x + x = 0 → x = 0) :
    LieAlgebra.Orthogonal.typeD ι R ≃ₗ[R] (RootEntryIndex ι → R) where
  toFun X
    | .inl p => X.val (.inl p.1) (.inl p.2)
    | .inr (.inl p) => X.val (.inl p.val.1) (.inr p.val.2)
    | .inr (.inr p) => -X.val (.inr p.val.1) (.inl p.val.2)
  invFun a := ⟨Matrix.fromBlocks (fun i j => a (.inl (i, j)))
    (upperCompletion fun p => a (.inr (.inl p)))
    (upperCompletion fun p => -a (.inr (.inr p)))
    (-Matrix.transpose (fun i j => a (.inl (i, j)))),
    Matrix.fromBlocks_mem_typeD _ _ _
      (upperCompletion_transpose _) (upperCompletion_transpose _)⟩
  left_inv X := by
    have hB : Matrix.transpose (fun i j => X.val (.inl i) (.inr j)) =
        -(fun i j => X.val (.inl i) (.inr j) : Matrix ι ι R) := by
      ext i j
      exact LieAlgebra.Orthogonal.typeD.apply_inl_inr X j i
    have hC : Matrix.transpose (fun i j => X.val (.inr i) (.inl j)) =
        -(fun i j => X.val (.inr i) (.inl j) : Matrix ι ι R) := by
      ext i j
      exact LieAlgebra.Orthogonal.typeD.apply_inr_inl X j i
    apply Subtype.ext
    ext (i | i) (j | j)
    · rfl
    · exact congrFun (congrFun (upperCompletion_entries h2 _ hB) i) j
    · change upperCompletion (fun p => - -X.val (.inr p.val.1) (.inl p.val.2)) i j = _
      simpa only [neg_neg] using
        congrFun (congrFun (upperCompletion_entries h2 _ hC) i) j
    · exact (LieAlgebra.Orthogonal.typeD.apply_inr_inr X i j).symm
  right_inv a := by
    funext p
    rcases p with p | (p | p)
    · rfl
    · change upperCompletion (fun q => a (.inr (.inl q))) p.val.1 p.val.2 = _
      exact upperCompletion_apply _ p
    · change -upperCompletion (fun q => -a (.inr (.inr q))) p.val.1 p.val.2 = _
      rw [upperCompletion_apply, neg_neg]
  map_add' X Y := by
    funext p
    rcases p with p | (p | p)
    · rfl
    · rfl
    · exact neg_add _ _
  map_smul' a X := by
    funext p
    rcases p with p | (p | p)
    · rfl
    · rfl
    · exact (smul_neg a _).symm

/-- Difference-root coordinates read the entire upper-left block. -/
@[simp]
theorem rootEntryEquiv_difference (h2 : ∀ x : R, x + x = 0 → x = 0)
    (X : LieAlgebra.Orthogonal.typeD ι R) (p : ι × ι) :
    rootEntryEquiv h2 X (.inl p) = X.val (.inl p.1) (.inl p.2) := by
  rfl

/-- Positive sum-root coordinates read the strict upper triangle of the upper-right block. -/
@[simp]
theorem rootEntryEquiv_sum (h2 : ∀ x : R, x + x = 0 → x = 0)
    (X : LieAlgebra.Orthogonal.typeD ι R) (p : {p : ι × ι // p.1 < p.2}) :
    rootEntryEquiv h2 X (.inr (.inl p)) = X.val (.inl p.val.1) (.inr p.val.2) := by
  rfl

/-- Negative sum-root coordinates negate the strict upper triangle of the lower-left block. -/
@[simp]
theorem rootEntryEquiv_negSum (h2 : ∀ x : R, x + x = 0 → x = 0)
    (X : LieAlgebra.Orthogonal.typeD ι R) (p : {p : ι × ι // p.1 < p.2}) :
    rootEntryEquiv h2 X (.inr (.inr p)) = -X.val (.inr p.val.1) (.inl p.val.2) := by
  rfl

/-- A native matrix basis, including individual hyperbolic diagonal elements, without division
by two. -/
noncomputable def rootEntryBasis (h2 : ∀ x : R, x + x = 0 → x = 0) :
    Module.Basis (RootEntryIndex ι) R (LieAlgebra.Orthogonal.typeD ι R) :=
  Module.Basis.ofEquivFun (rootEntryEquiv h2)

/-- The matrix basis has the coordinates of `rootEntryEquiv`. -/
@[simp]
theorem rootEntryBasis_repr (h2 : ∀ x : R, x + x = 0 → x = 0)
    (X : LieAlgebra.Orthogonal.typeD ι R) (p : RootEntryIndex ι) :
    (rootEntryBasis h2).repr X p = rootEntryEquiv h2 X p :=
  Module.Basis.ofEquivFun_repr_apply _ _ _

private theorem rootEntryEquiv_basis (h2 : ∀ x : R, x + x = 0 → x = 0)
    (p : RootEntryIndex ι) :
    rootEntryEquiv h2 (rootEntryBasis h2 p) = Pi.single p 1 := by
  ext q
  rw [← rootEntryBasis_repr, Module.Basis.repr_self]
  simp only [Finsupp.single_apply, Pi.single_apply, eq_comm]

/-- The first basis family consists of all difference-root matrices, including the diagonal. -/
@[simp]
theorem rootEntryBasis_difference (h2 : ∀ x : R, x + x = 0 → x = 0) (p : ι × ι) :
    rootEntryBasis h2 (.inl p) = differenceRootGenerator p.1 p.2 := by
  rcases p with ⟨i, j⟩
  apply (rootEntryEquiv h2).injective
  rw [rootEntryEquiv_basis]
  ext q
  rcases q with ⟨a, b⟩ | (p | p)
  all_goals
    simp [rootEntryEquiv_difference, rootEntryEquiv_sum, rootEntryEquiv_negSum,
      val_differenceRootGenerator, differenceRootMatrix_def, Matrix.fromBlocks,
      Matrix.single_apply, Pi.single_apply, eq_comm]

omit [Fintype ι] in
private theorem upper_single (p q : {p : ι × ι // p.1 < p.2}) :
    (Matrix.single p.val.1 p.val.2 (1 : R) - Matrix.single p.val.2 p.val.1 1 : Matrix ι ι R)
        q.val.1 q.val.2 = if p = q then 1 else 0 := by
  have hrev : ¬(p.val.2 = q.val.1 ∧ p.val.1 = q.val.2) := by
    rintro ⟨h₁, h₂⟩
    have h := p.property
    rw [h₁, h₂] at h
    exact (not_lt_of_ge q.property.le) h
  have heq : (p.val.1 = q.val.1 ∧ p.val.2 = q.val.2) ↔ p = q :=
    ⟨fun h => Subtype.ext (Prod.ext h.1 h.2), fun h => by subst q; exact ⟨rfl, rfl⟩⟩
  simp [Matrix.sub_apply, Matrix.single_apply, hrev, heq]

/-- The second basis family consists of the positive sum-root matrices above the diagonal. -/
@[simp]
theorem rootEntryBasis_sum (h2 : ∀ x : R, x + x = 0 → x = 0)
    (p : {p : ι × ι // p.1 < p.2}) :
    rootEntryBasis h2 (.inr (.inl p)) = sumRootGenerator p.val.1 p.val.2 := by
  apply (rootEntryEquiv h2).injective
  rw [rootEntryEquiv_basis]
  ext q
  rcases q with ⟨a, b⟩ | (q | q)
  · simp [val_sumRootGenerator, sumRootMatrix_def, Matrix.fromBlocks]
  · rw [rootEntryEquiv_sum, val_sumRootGenerator, sumRootMatrix_def]
    simpa [Matrix.fromBlocks, Pi.single_apply, eq_comm] using (upper_single (R := R) p q).symm
  · simp [val_sumRootGenerator, sumRootMatrix_def, Matrix.fromBlocks]

/-- The third basis family reverses the negative sum-root indices, as at the native fork. -/
@[simp]
theorem rootEntryBasis_negSum (h2 : ∀ x : R, x + x = 0 → x = 0)
    (p : {p : ι × ι // p.1 < p.2}) :
    rootEntryBasis h2 (.inr (.inr p)) = negSumRootGenerator p.val.2 p.val.1 := by
  apply (rootEntryEquiv h2).injective
  rw [rootEntryEquiv_basis]
  ext q
  rcases q with ⟨a, b⟩ | (q | q)
  · simp [val_negSumRootGenerator, negSumRootMatrix_def, Matrix.fromBlocks]
  · simp [val_negSumRootGenerator, negSumRootMatrix_def, Matrix.fromBlocks]
  · rw [rootEntryEquiv_negSum, val_negSumRootGenerator, negSumRootMatrix_def]
    simpa [Matrix.fromBlocks, Matrix.sub_apply, Pi.single_apply, neg_sub, eq_comm] using
      (upper_single (R := R) p q).symm

/-- Every split even orthogonal matrix expands in the three native root-matrix families.
Only strict upper pairs occur in the sum-root families, so no coefficient is divided by two. -/
theorem eq_sum_rootEntryBasis (h2 : ∀ x : R, x + x = 0 → x = 0)
    (X : LieAlgebra.Orthogonal.typeD ι R) :
    X =
      (∑ p : ι × ι, X.val (.inl p.1) (.inl p.2) • differenceRootGenerator p.1 p.2) +
      (∑ p : {p : ι × ι // p.1 < p.2},
        X.val (.inl p.val.1) (.inr p.val.2) • sumRootGenerator p.val.1 p.val.2) +
      (∑ p : {p : ι × ι // p.1 < p.2},
        (-X.val (.inr p.val.1) (.inl p.val.2)) • negSumRootGenerator p.val.2 p.val.1) := by
  simpa only [Fintype.sum_sum_type, rootEntryBasis_repr, rootEntryEquiv_difference,
    rootEntryEquiv_sum, rootEntryEquiv_negSum, rootEntryBasis_difference,
    rootEntryBasis_sum, rootEntryBasis_negSum, add_assoc] using
    ((rootEntryBasis h2).sum_repr X).symm

end TauCeti.TypeDStd
