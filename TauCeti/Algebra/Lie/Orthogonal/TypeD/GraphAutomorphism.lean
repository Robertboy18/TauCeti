/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Generators
public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations

/-!
# The native type-D fork involution

Exchanging the last hyperbolic pair preserves the split orthogonal form. Conjugation by this
swap gives an involution of the native type-D Lie algebra and exchanges its two fork generators.
The construction works over every commutative ring, including in characteristic two.
-/

public section

open Matrix LieAlgebra.Orthogonal

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable {I : Type*} [DecidableEq I] (c : I) (A : Type*) [CommRing A]

/-- Exchange the two coordinates of one hyperbolic pair. -/
def typeDForkIndex : Equiv.Perm (I ⊕ I) := Equiv.swap (.inl c) (.inr c)

/-- The index permutation exchanges the two coordinates of the chosen pair. -/
theorem typeDForkIndex_apply (s : I ⊕ I) :
    typeDForkIndex c s = Equiv.swap (.inl c) (.inr c) s := by
  rfl

/-- The permutation matrix exchanging one hyperbolic pair. -/
def typeDForkMatrix : Matrix (I ⊕ I) (I ⊕ I) A :=
  (typeDForkIndex c).permMatrix A

/-- The swap matrix has one entry in the column selected by the index permutation. -/
theorem typeDForkMatrix_apply (s t : I ⊕ I) :
    typeDForkMatrix c A s t = if typeDForkIndex c s = t then 1 else 0 := by
  simp [typeDForkMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

/-- The hyperbolic-pair swap matrix is symmetric. -/
@[simp]
theorem typeDForkMatrix_transpose : (typeDForkMatrix c A)ᵀ = typeDForkMatrix c A := by
  simp [typeDForkMatrix, typeDForkIndex]

variable [Fintype I]

/-- The hyperbolic-pair swap matrix squares to the identity. -/
@[simp]
theorem typeDForkMatrix_mul_self : typeDForkMatrix c A * typeDForkMatrix c A = 1 := by
  simp [typeDForkMatrix, ← Matrix.permMatrix_mul, typeDForkIndex]

private theorem typeDForkMatrix_conj (X : Matrix (I ⊕ I) (I ⊕ I) A) :
    typeDForkMatrix c A * X * typeDForkMatrix c A =
      Matrix.reindexAlgEquiv A A (typeDForkIndex c) X := by
  simp only [typeDForkMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  rfl

private theorem typeDForkIndex_form :
    Matrix.reindexAlgEquiv A A (typeDForkIndex c) (JD I A) = JD I A := by
  ext (i | i) (j | j) <;> by_cases hi : i = c <;> by_cases hj : j = c <;>
    simp_all [Matrix.reindexAlgEquiv, Matrix.reindexRingEquiv, Matrix.reindex,
      typeDForkIndex, Equiv.swap_apply_def, JD, Matrix.fromBlocks, Matrix.one_apply, eq_comm]

/-- Exchanging a hyperbolic pair preserves the native split orthogonal form. -/
theorem typeDForkMatrix_orthogonal :
    (typeDForkMatrix c A)ᵀ * JD I A * typeDForkMatrix c A = JD I A := by
  rw [typeDForkMatrix_transpose, typeDForkMatrix_conj, typeDForkIndex_form]

/-- The fork involution on the native split type-D Lie algebra. -/
def typeDForkLieEquiv : typeD I A ≃ₗ⁅A⁆ typeD I A :=
  (skewAdjointMatricesLieSubalgebraEquivTranspose (JD I A)
    (Matrix.reindexAlgEquiv A A (typeDForkIndex c)) (fun _ => rfl)).trans
      (LieEquiv.ofEq _ (typeD I A)
        (by rw [typeDForkIndex_form]; rfl))

/-- The fork involution acts by conjugation with the hyperbolic-pair swap. -/
theorem typeDForkLieEquiv_apply_val (X : typeD I A) :
    (typeDForkLieEquiv c A X : Matrix (I ⊕ I) (I ⊕ I) A) =
      typeDForkMatrix c A * X * typeDForkMatrix c A := by
  rw [typeDForkMatrix_conj]
  rfl

/-- The fork involution permutes both matrix indices by the chosen pair swap. -/
theorem typeDForkLieEquiv_apply_entry (X : typeD I A) (s t : I ⊕ I) :
    (typeDForkLieEquiv c A X : Matrix (I ⊕ I) (I ⊕ I) A) s t =
      (X : Matrix (I ⊕ I) (I ⊕ I) A) (typeDForkIndex c s) (typeDForkIndex c t) := by
  rw [typeDForkLieEquiv_apply_val, typeDForkMatrix_conj]
  rfl

/-- Applying the fork involution twice returns the original matrix. -/
@[simp]
theorem typeDForkLieEquiv_apply_apply (X : typeD I A) :
    typeDForkLieEquiv c A (typeDForkLieEquiv c A X) = X := by
  apply Subtype.ext
  simp only [typeDForkLieEquiv_apply_val]
  simp only [← mul_assoc, typeDForkMatrix_mul_self, one_mul]
  rw [mul_assoc, typeDForkMatrix_mul_self, mul_one]

/-- Fixed matrices are precisely those commuting with the hyperbolic-pair swap. -/
theorem typeDForkLieEquiv_eq_self_iff (X : typeD I A) :
    typeDForkLieEquiv c A X = X ↔
      typeDForkMatrix c A * (X : Matrix (I ⊕ I) (I ⊕ I) A) = X * typeDForkMatrix c A := by
  rw [Subtype.ext_iff, typeDForkLieEquiv_apply_val]
  constructor
  · intro h
    have := congrArg (fun Y => Y * typeDForkMatrix c A) h
    simpa [mul_assoc] using this
  · intro h
    rw [h, mul_assoc, typeDForkMatrix_mul_self, mul_one]

private theorem typeDForkReindex_single (s t : I ⊕ I) (a : A) :
    Matrix.reindexAlgEquiv A A (typeDForkIndex c) (Matrix.single s t a) =
      Matrix.single (typeDForkIndex c s) (typeDForkIndex c t) a := by
  change (Matrix.single s t a).submatrix (typeDForkIndex c).symm
    (typeDForkIndex c).symm = _
  simp only [Matrix.submatrix_single_equiv, Equiv.symm_symm]

open TypeDStd

variable (n : ℕ) (hn : 4 ≤ n)

private theorem raisingMatrix_chain_single {i : Fin n} (hi : (i : ℕ) + 1 < n) :
    raisingMatrix (K := A) n hn i =
      Matrix.single (.inl i) (.inl (chainNext n i hi)) 1 -
        Matrix.single (.inr (chainNext n i hi)) (.inr i) 1 := by
  rw [raisingMatrix_of_chain n hn hi]
  ext (j | j) (k | k) <;> simp [Matrix.fromBlocks, Matrix.single_apply]

private theorem raisingMatrix_fork_single :
    raisingMatrix (K := A) n hn (forkRight n hn) =
      Matrix.single (.inl (forkLeft n hn)) (.inr (forkRight n hn)) 1 -
        Matrix.single (.inl (forkRight n hn)) (.inr (forkLeft n hn)) 1 := by
  rw [raisingMatrix_of_fork n hn (by simp; omega)]
  ext (j | j) (k | k) <;> simp [Matrix.fromBlocks, Matrix.single_apply]

private theorem typeDForkReindex_raising (i : Fin n) :
    Matrix.reindexAlgEquiv A A (typeDForkIndex (forkRight n hn))
        (raisingMatrix n hn i) =
      raisingMatrix n hn (graphPermD n (by omega) i) := by
  have hac := forkLeft_ne_forkRight n hn
  have hchain : (forkLeft n hn : ℕ) + 1 < n := by simp; omega
  have hnext : chainNext n (forkLeft n hn) hchain = forkRight n hn := by
    apply Fin.ext
    simp
    omega
  have hfl : forkLeft n hn = (⟨n - 2, by omega⟩ : Fin n) := Fin.ext (forkLeft_val n hn)
  have hfr : forkRight n hn = (⟨n - 1, by omega⟩ : Fin n) := Fin.ext (forkRight_val n hn)
  have hleft : graphPermD n (by omega) (forkLeft n hn) = forkRight n hn := by
    simpa only [hfl, hfr] using graphPermD_apply_left n (by omega)
  have hright : graphPermD n (by omega) (forkRight n hn) = forkLeft n hn := by
    simpa only [hfl, hfr] using graphPermD_apply_right n (by omega)
  by_cases hi : i = forkLeft n hn
  · subst i
    rw [hleft, raisingMatrix_chain_single A n hn hchain, raisingMatrix_fork_single A n hn]
    rw [map_sub, typeDForkReindex_single, typeDForkReindex_single]
    simp [hnext, typeDForkIndex, Equiv.swap_apply_def, hac]
  by_cases hi' : i = forkRight n hn
  · subst i
    rw [hright, raisingMatrix_fork_single A n hn, raisingMatrix_chain_single A n hn hchain]
    rw [map_sub, typeDForkReindex_single, typeDForkReindex_single]
    simp [hnext, typeDForkIndex, Equiv.swap_apply_def, hac]
  have hiv : (i : ℕ) ≠ n - 2 := by simpa [Fin.ext_iff] using hi
  have hiv' : (i : ℕ) ≠ n - 1 := by simpa [Fin.ext_iff] using hi'
  have hic : (i : ℕ) + 1 < n := by omega
  have hinc : chainNext n i hic ≠ forkRight n hn := by
    intro h
    have := congrArg Fin.val h
    simp only [chainNext_val, forkRight_val] at this
    omega
  rw [graphPermD_apply_of_ne_of_ne n (by omega) i hiv hiv',
    raisingMatrix_chain_single A n hn hic]
  rw [map_sub, typeDForkReindex_single, typeDForkReindex_single]
  simp [typeDForkIndex, Equiv.swap_apply_def, hi', hinc]

private theorem loweringMatrix_eq_transpose (i : Fin n) :
    loweringMatrix (K := A) n hn i = (raisingMatrix n hn i)ᵀ := by
  by_cases hi : (i : ℕ) + 1 < n
  · rw [loweringMatrix_of_chain n hn hi, raisingMatrix_of_chain n hn hi]
    simp [Matrix.fromBlocks_transpose]
  · rw [loweringMatrix_of_fork n hn hi, raisingMatrix_of_fork n hn hi]
    simp [Matrix.fromBlocks_transpose, neg_sub]

/-- The native fork involution exchanges exactly the two terminal simple-root generators. -/
@[simp]
theorem typeDForkLieEquiv_rootGenerator (k : Fin n ⊕ Fin n) :
    typeDForkLieEquiv (forkRight n hn) A (rootGenerator n hn k) =
      rootGenerator n hn (Sum.map (graphPermD n (by omega)) (graphPermD n (by omega)) k) := by
  apply Subtype.ext
  rw [typeDForkLieEquiv_apply_val, typeDForkMatrix_conj]
  rcases k with i | i
  · simpa only [val_rootGenerator_inl, Sum.map_inl] using typeDForkReindex_raising A n hn i
  · simp only [Sum.map_inr, val_rootGenerator_inr, loweringMatrix_eq_transpose]
    change (Matrix.reindexAlgEquiv A A (typeDForkIndex (forkRight n hn))
      (raisingMatrix n hn i))ᵀ = _
    exact congrArg Matrix.transpose (typeDForkReindex_raising A n hn i)

/-- The native fork involution acts on the Cartan generators by the same diagram permutation. -/
@[simp]
theorem typeDForkLieEquiv_cartanGenerator (i : Fin n) :
    typeDForkLieEquiv (forkRight n hn) A (cartanGenerator n hn i) =
      cartanGenerator n hn (graphPermD n (by omega) i) := by
  have hi : ⁅rootGenerator (K := A) n hn (.inl i), rootGenerator (K := A) n hn (.inr i)⁆ =
      cartanGenerator (K := A) n hn i := by simp
  rw [← hi, LieEquiv.map_lie, typeDForkLieEquiv_rootGenerator, typeDForkLieEquiv_rootGenerator]
  simp

end TauCeti
