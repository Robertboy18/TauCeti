/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.OfMulAction.OrbitBasis
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Gram geometry of orbit averages

An invariant integer matrix induces a rational bilinear form on a permutation
representation. Its restriction to the invariant subspace has an explicit Gram
matrix in the basis of normalized orbit sums. Positive definiteness descends to
that matrix, and the orbit projection preserves pairing against invariant vectors.
-/

public noncomputable section

open MonoidAlgebra MulAction Module Representation

namespace Matrix

variable {Γ I : Type*} [Group Γ] [MulAction Γ I] [Fintype I]

open Classical in
/-- The sum of one column over a row orbit, evaluated at a representative of the column orbit. -/
def orbitColumnSum (A : Matrix I I ℤ) (O P : orbitRel.Quotient Γ I) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i ↦ Quotient.mk (orbitRel Γ I) i = O), A i P.out

open Classical in
/-- Invariance of the original matrix makes its orbit column sum independent of the
chosen representative of the column orbit. -/
theorem orbitColumnSum_eq_sum (A : Matrix I I ℤ)
    (hact : ∀ (g : Γ) i j, A (g • i) (g • j) = A i j)
    (O P : orbitRel.Quotient Γ I) (j : I) (hj : Quotient.mk (orbitRel Γ I) j = P) :
    orbitColumnSum A O P =
      ∑ i ∈ Finset.univ.filter (fun i ↦ Quotient.mk (orbitRel Γ I) i = O), A i j := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : Γ, g • j = (Quotient.mk (orbitRel Γ I) j).out :=
    Quotient.mk_out (s := orbitRel Γ I) j
  rw [hj] at hg
  unfold orbitColumnSum
  rw [← hg]
  symm
  apply Finset.sum_bij (fun i _ ↦ g • i)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      orbitRel.Quotient.quotient_smul_eq] using hi
  · intro i hi k hk h
    exact MulAction.injective g h
  · intro i hi
    refine ⟨g⁻¹ • i, ?_, by simp⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      orbitRel.Quotient.quotient_smul_eq] using hi
  · intro i hi
    exact (hact g i j).symm

open Classical in
/-- Pairing an orbit-average basis vector with a standard basis vector gives the normalized
orbit column sum. -/
theorem toBilin_ofMulActionOrbitBasis_single (A : Matrix I I ℤ)
    (hact : ∀ (g : Γ) i j, A (g • i) (g • j) = A i j)
    (O : orbitRel.Quotient Γ I) (j : I) :
    toBilin (MonoidAlgebra.basis I ℚ) (A.map (Int.castRingHom ℚ))
        (ofMulActionOrbitBasis Γ I O).val (MonoidAlgebra.single j 1) =
      (orbitColumnSum A O (Quotient.mk (orbitRel Γ I) j) : ℚ) /
        (Nat.card O.orbit : ℚ) := by
  classical
  have hs (i : I) :
      toBilin (MonoidAlgebra.basis I ℚ) (A.map (Int.castRingHom ℚ))
          (MonoidAlgebra.single i 1) (MonoidAlgebra.single j 1) = (A i j : ℚ) := by
    exact congr_fun (congr_fun
      (LinearMap.BilinForm.toMatrix_toBilin (MonoidAlgebra.basis I ℚ)
        (A.map (Int.castRingHom ℚ))) i) j
  rw [ofMulActionOrbitBasis_eq_sum]
  simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul, hs]
  rw [← Int.cast_sum, ← orbitColumnSum_eq_sum A hact O _ j rfl]
  ring

omit [Fintype I] in
private theorem orbit_card_ne_zero [Finite I] (O : orbitRel.Quotient Γ I) :
    (Nat.card O.orbit : ℚ) ≠ 0 := by
  have : Nonempty O.orbit := O.nonempty_orbit.to_subtype
  exact_mod_cast Nat.card_pos.ne'

open Classical in
/-- The actual Gram entry of two orbit averages is the orbit column sum divided by the
size of the row orbit. This formula does not require symmetry or positive definiteness. -/
theorem toBilin_ofMulActionOrbitBasis (A : Matrix I I ℤ)
    (hact : ∀ (g : Γ) i j, A (g • i) (g • j) = A i j)
    (O P : orbitRel.Quotient Γ I) :
    toBilin (MonoidAlgebra.basis I ℚ) (A.map (Int.castRingHom ℚ))
        (ofMulActionOrbitBasis Γ I O).val (ofMulActionOrbitBasis Γ I P).val =
      (orbitColumnSum A O P : ℚ) / (Nat.card O.orbit : ℚ) := by
  classical
  have hn : (Finset.univ.filter (fun i ↦ Quotient.mk (orbitRel Γ I) i = P)).card =
      Nat.card P.orbit := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext i
    simp [orbitRel.Quotient.mem_orbit]
  rw [ofMulActionOrbitBasis_eq_sum Γ I P, map_smul, map_sum]
  simp only [smul_eq_mul, toBilin_ofMulActionOrbitBasis_single A hact]
  calc
    _ = (Nat.card P.orbit : ℚ)⁻¹ *
        ∑ _j ∈ Finset.univ.filter (fun j ↦ Quotient.mk (orbitRel Γ I) j = P),
          (orbitColumnSum A O P : ℚ) / (Nat.card O.orbit : ℚ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]
    _ = _ := by
      rw [Finset.sum_const, hn, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (orbit_card_ne_zero P), one_mul]

open Classical in
/-- The matrix of the restricted bilinear form in the orbit-average basis is the
normalized orbit column-sum matrix. -/
theorem toMatrix_restrict_ofMulActionOrbitBasis (A : Matrix I I ℤ)
    (hact : ∀ (g : Γ) i j, A (g • i) (g • j) = A i j) :
    ((toBilin (MonoidAlgebra.basis I ℚ) (A.map (Int.castRingHom ℚ))).restrict
      (ofMulAction ℚ Γ I).invariants).toMatrix (ofMulActionOrbitBasis Γ I) =
      fun O P ↦ (orbitColumnSum A O P : ℚ) / (Nat.card O.orbit : ℚ) := by
  classical
  ext O P
  rw [LinearMap.BilinForm.toMatrix_apply]
  exact toBilin_ofMulActionOrbitBasis A hact O P

open Classical in
/-- Positive definiteness of an invariant integer matrix descends to the actual Gram
matrix of the normalized orbit sums. -/
theorem posDef_orbitColumnSum (A : Matrix I I ℤ)
    (hact : ∀ (g : Γ) i j, A (g • i) (g • j) = A i j)
    (hA : (A.map (Int.castRingHom ℚ)).PosDef) :
    Matrix.PosDef (fun O P : orbitRel.Quotient Γ I ↦
      (orbitColumnSum A O P : ℚ) / (Nat.card O.orbit : ℚ)) := by
  classical
  let B := toBilin (MonoidAlgebra.basis I ℚ) (A.map (Int.castRingHom ℚ))
  have hB : B.IsSymm := by
    simpa only [B, isSymm_toBilin_iff_isSymm] using
      (isHermitian_iff_isSymm.mp hA.isHermitian)
  have hpos : B.toQuadraticMap.PosDef := by
    apply (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix
      (MonoidAlgebra.basis I ℚ) B hB).mpr
    simpa only [B, LinearMap.BilinForm.toMatrix_toBilin] using hA
  have hres : (B.restrict (ofMulAction ℚ Γ I).invariants).toQuadraticMap.PosDef := by
    intro w hw
    exact hpos w.val (fun h ↦ hw (Subtype.ext h))
  rw [← toMatrix_restrict_ofMulActionOrbitBasis A hact]
  exact (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix
    (ofMulActionOrbitBasis Γ I) (B.restrict (ofMulAction ℚ Γ I).invariants)
    (hB.restrict _)).mp hres

open Classical in
private theorem toBilin_ofMulAction (A : Matrix I I ℤ)
    (hact : ∀ (g : Γ) i j, A (g • i) (g • j) = A i j)
    (g : Γ) (x y : ℚ[I]) :
    toBilin (MonoidAlgebra.basis I ℚ) (A.map (Int.castRingHom ℚ))
        (ofMulAction ℚ Γ I g x) (ofMulAction ℚ Γ I g y) =
      toBilin (MonoidAlgebra.basis I ℚ) (A.map (Int.castRingHom ℚ)) x y := by
  classical
  let B := toBilin (MonoidAlgebra.basis I ℚ) (A.map (Int.castRingHom ℚ))
  have hs (i j : I) : B (MonoidAlgebra.single i 1) (MonoidAlgebra.single j 1) = (A i j : ℚ) :=
    congr_fun (congr_fun (LinearMap.BilinForm.toMatrix_toBilin
      (MonoidAlgebra.basis I ℚ) (A.map (Int.castRingHom ℚ))) i) j
  have hB : B.compl₁₂ (ofMulAction ℚ Γ I g) (ofMulAction ℚ Γ I g) = B := by
    apply (LinearMap.BilinForm.ext_iff_basis (MonoidAlgebra.basis I ℚ)).mpr
    intro i j
    simpa [LinearMap.compl₁₂_apply, hs] using congrArg (Int.castRingHom ℚ) (hact g i j)
  exact congrArg (fun C : LinearMap.BilinForm ℚ ℚ[I] ↦ C x y) hB

open Classical in
/-- Orbit projection preserves the pairing against every invariant vector. Neither
symmetry nor positive definiteness of the original matrix is required. -/
theorem toBilin_ofMulActionOrbitProjection (A : Matrix I I ℤ)
    (hact : ∀ (g : Γ) i j, A (g • i) (g • j) = A i j)
    (x : ℚ[I]) (w : (ofMulAction ℚ Γ I).invariants) :
    toBilin (MonoidAlgebra.basis I ℚ) (A.map (Int.castRingHom ℚ))
        (ofMulActionOrbitProjection Γ I x).val w.val =
      toBilin (MonoidAlgebra.basis I ℚ) (A.map (Int.castRingHom ℚ)) x w.val := by
  classical
  let B := toBilin (MonoidAlgebra.basis I ℚ) (A.map (Int.castRingHom ℚ))
  have hconst (i j : I) (hij : Quotient.mk (orbitRel Γ I) i =
      Quotient.mk (orbitRel Γ I) j) :
      B (MonoidAlgebra.single i 1) w.val = B (MonoidAlgebra.single j 1) w.val := by
    obtain ⟨g, hg⟩ : ∃ g : Γ, g • j = i := Quotient.exact hij
    have h := toBilin_ofMulAction A hact g (MonoidAlgebra.single j 1) w.val
    simpa only [ofMulAction_single, hg, w.property g] using h
  have hav (i : I) :
      B (ofMulActionOrbitBasis Γ I (Quotient.mk (orbitRel Γ I) i)).val w.val =
        B (MonoidAlgebra.single i 1) w.val := by
    let O : orbitRel.Quotient Γ I := Quotient.mk (orbitRel Γ I) i
    have hn : (Finset.univ.filter (fun j ↦ Quotient.mk (orbitRel Γ I) j = O)).card =
        Nat.card O.orbit := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
    rw [ofMulActionOrbitBasis_eq_sum]
    simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
    calc
      _ = (Nat.card O.orbit : ℚ)⁻¹ *
          ∑ _j ∈ Finset.univ.filter (fun j ↦ Quotient.mk (orbitRel Γ I) j = O),
            B (MonoidAlgebra.single i 1) w.val := by
        congr 1
        exact Finset.sum_congr rfl fun j hj ↦ hconst j i (Finset.mem_filter.mp hj).2
      _ = _ := by
        rw [Finset.sum_const, hn, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ (orbit_card_ne_zero O), one_mul]
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, Submodule.coe_add, LinearMap.add_apply, hx, hy]
  | single i r =>
      have hs : MonoidAlgebra.single i r = r • MonoidAlgebra.single i (1 : ℚ) := by simp
      rw [ofMulActionOrbitProjection_single, Submodule.coe_smul, map_smul,
        LinearMap.smul_apply, hs, map_smul, LinearMap.smul_apply]
      exact congrArg (r • ·) (hav i)

open Classical in
/-- For a symmetric invariant matrix, orbit projection is self-adjoint. -/
theorem toBilin_ofMulActionOrbitProjection_eq (A : Matrix I I ℤ)
    (hact : ∀ (g : Γ) i j, A (g • i) (g • j) = A i j) (hA : A.IsSymm)
    (x y : ℚ[I]) :
    toBilin (MonoidAlgebra.basis I ℚ) (A.map (Int.castRingHom ℚ))
        (ofMulActionOrbitProjection Γ I x).val y =
      toBilin (MonoidAlgebra.basis I ℚ) (A.map (Int.castRingHom ℚ))
        x (ofMulActionOrbitProjection Γ I y).val := by
  classical
  let B := toBilin (MonoidAlgebra.basis I ℚ) (A.map (Int.castRingHom ℚ))
  have hB : B.IsSymm := by
    rw [isSymm_toBilin_iff_isSymm]
    exact hA.map _
  calc
    _ = B y (ofMulActionOrbitProjection Γ I x).val := hB.eq _ _
    _ = B (ofMulActionOrbitProjection Γ I y).val
        (ofMulActionOrbitProjection Γ I x).val :=
      (toBilin_ofMulActionOrbitProjection A hact y (ofMulActionOrbitProjection Γ I x)).symm
    _ = B (ofMulActionOrbitProjection Γ I x).val
        (ofMulActionOrbitProjection Γ I y).val := hB.eq _ _
    _ = _ := toBilin_ofMulActionOrbitProjection A hact x (ofMulActionOrbitProjection Γ I y)

end Matrix
