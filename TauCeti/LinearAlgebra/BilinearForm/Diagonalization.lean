/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.BilinearForm.Isometry
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Diagonalization of symmetric bilinear forms in every characteristic

Over a field in which `2` is invertible, every symmetric bilinear form on a finite-dimensional
space has an orthogonal basis (`LinearMap.BilinForm.exists_orthogonal_basis`). In characteristic
two this fails: a nonzero alternating form is symmetric, and an orthogonal basis for it would make
every basis pairing vanish, hence the whole form. This file shows that the alternating forms are
the only obstruction, in every characteristic: a symmetric form has an orthogonal basis if and
only if it is zero or not alternating (`LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_iff`).

The proof is the classical induction on the dimension, with one extra step. A non-isotropic vector
`x` splits the space as `K x ⊕ x^⊥`, and the induction continues on `x^⊥` as long as the
restriction of the form there is zero or not alternating. If instead it is alternating and
nonzero, choose `u, w ∈ x^⊥` with `B u w ≠ 0` and replace `x` by `x + u`: its self-pairing is
still `B x x`, and the vector `w`, corrected to lie in `(x + u)^⊥`, has nonzero self-pairing, so
the restriction to the new complement is not alternating.

For a nondegenerate form over a field in which every element is a square, for instance a finite
field of characteristic two (`isSquare_of_charTwo'`), the orthogonal basis can be rescaled: a
symmetric form that is not alternating has an **orthonormal basis**, one in which its matrix is
the identity (`LinearMap.BilinForm.IsSymm.exists_basis_toMatrix_eq_one`). Hence it is equivalent
to the standard form `Matrix.toBilin' 1`, and any two such forms of the same dimension are
equivalent. Together with the symplectic normal form of
`TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis` this gives the dichotomy for nondegenerate
forms that are alternating or symmetric: a symplectic basis when the form is alternating, an
orthonormal basis when it is not
(`LinearMap.BilinForm.Nondegenerate.exists_basis_toMatrix_eq_J_or_toMatrix_eq_one`). Over `𝔽₂`,
where every form that is alternating is symmetric, this classifies the nondegenerate symmetric
bilinear forms, which is the input to the normal forms of one-relator pro-`2` groups.

## Main results

* `LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_of_isAlt_imp_eq_zero`: a symmetric form
  that is zero or not alternating has an orthogonal basis, in every characteristic.
* `LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_iff`: this condition is also necessary.
* `LinearMap.BilinForm.IsSymm.exists_basis_toMatrix_eq_one`: over a field in which every element
  is a square, a nondegenerate symmetric form that is not alternating has an orthonormal basis.
* `LinearMap.BilinForm.IsSymm.equivalent_toBilin'_one`,
  `LinearMap.BilinForm.IsSymm.equivalent_of_finrank_eq`: such a form is equivalent to the standard
  form on `Fin n → K`, so any two of them of the same dimension are equivalent.
* `LinearMap.BilinForm.Nondegenerate.exists_basis_toMatrix_eq_J_or_toMatrix_eq_one`: the
  symplectic-or-orthonormal dichotomy.
* `Matrix.isAlt_toBilin'_one_iff`: the standard form is alternating only in dimension zero.

## References

* A. A. Albert, *Symmetric and alternate matrices in an arbitrary field, I*, Trans. Amer. Math.
  Soc. 43 (1938), 386–436.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)
open Module

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

/-- If `x` is non-isotropic for a symmetric form `B` and the restriction of `B` to the orthogonal
complement of `x` is alternating and nonzero, then some non-isotropic vector has an orthogonal
complement on which `B` is not alternating: given `u, w` orthogonal to `x` with `B u w ≠ 0`, the
vector `x + u` works. -/
private theorem IsSymm.exists_apply_self_ne_zero_and_not_isAlt_restrict_orthogonal
    (hB : B.IsSymm) {x : V} (hx : B x x ≠ 0) (halt : (B.restrict (B.orthogonal (K ∙ x))).IsAlt)
    (hne : B.restrict (B.orthogonal (K ∙ x)) ≠ 0) :
    ∃ y, B y y ≠ 0 ∧ ¬ (B.restrict (B.orthogonal (K ∙ y))).IsAlt := by
  obtain ⟨u, w, huw⟩ : ∃ u w : B.orthogonal (K ∙ x), B u w ≠ 0 := by
    by_contra! h
    exact hne (LinearMap.ext fun u => LinearMap.ext fun w => by simpa using h u w)
  have hxu : B x u = 0 := (mem_orthogonal_span_singleton_iff B).1 u.2
  have hxw : B x w = 0 := (mem_orthogonal_span_singleton_iff B).1 w.2
  have huu : B u u = 0 := by simpa using halt u
  have hww : B w w = 0 := by simpa using halt w
  set z := x + u with hz
  have hzz : B z z = B x x := by
    rw [hz]
    simp only [add_left, add_right, hxu, hB.eq u x, huu, add_zero]
  have hzw : B z w = B u w := by rw [hz, add_left, hxw, zero_add]
  refine ⟨z, hzz ▸ hx, fun halt' => huw ?_⟩
  obtain ⟨c, hc⟩ : ∃ c, c * B z z = B z w := ⟨B z w / B z z, div_mul_cancel₀ _ (hzz ▸ hx)⟩
  have hw' : w - c • z ∈ B.orthogonal (K ∙ z) := by
    rw [mem_orthogonal_span_singleton_iff, sub_right, smul_right, hc, sub_self]
  have h0 : B (w - c • z) (w - c • z) = 0 := by simpa using halt' ⟨w - c • z, hw'⟩
  rw [sub_left, sub_right, sub_right, smul_left, smul_left, smul_right, smul_right, hww,
    hB.eq w z] at h0
  have hcb : c * B z w = 0 := by linear_combination -h0 + c * hc
  rw [← hzw]
  rcases mul_eq_zero.1 hcb with hc0 | hb0
  · rw [← hc, hc0, zero_mul]
  · exact hb0

/-- A symmetric form that is not alternating has a non-isotropic vector `x` such that the
restriction of the form to the orthogonal complement of `x` is zero or not alternating. -/
private theorem IsSymm.exists_apply_self_ne_zero_and_restrict_orthogonal_isAlt_imp_eq_zero
    (hB : B.IsSymm) (h : ¬B.IsAlt) :
    ∃ x, B x x ≠ 0 ∧
      ((B.restrict (B.orthogonal (K ∙ x))).IsAlt → B.restrict (B.orthogonal (K ∙ x)) = 0) := by
  obtain ⟨x, hx⟩ : ∃ x, B x x ≠ 0 := by simpa [IsAlt, LinearMap.IsAlt] using h
  by_cases hW : (B.restrict (B.orthogonal (K ∙ x))).IsAlt ∧ B.restrict (B.orthogonal (K ∙ x)) ≠ 0
  · obtain ⟨y, hy, hy'⟩ :=
      hB.exists_apply_self_ne_zero_and_not_isAlt_restrict_orthogonal hx hW.1 hW.2
    exact ⟨y, hy, fun h' => (hy' h').elim⟩
  · exact ⟨x, hx, fun h' => not_not.1 (not_and.1 hW h')⟩

/-- Adjoining a non-isotropic vector `x` to an orthogonal basis of the orthogonal complement of
`x` gives an orthogonal basis of the whole space, for a reflexive form. -/
theorem IsRefl.exists_orthogonal_basis_of_orthogonal_span_singleton (hB : B.IsRefl) {x : V}
    (hx : B x x ≠ 0) {d : ℕ} {v : Basis (Fin d) K (B.orthogonal (K ∙ x))}
    (hv : (B.restrict (B.orthogonal (K ∙ x))).iIsOrtho v) :
    ∃ b : Basis (Fin (d + 1)) K V, B.iIsOrtho b := by
  have hli : ∀ c : K, ∀ y ∈ B.orthogonal (K ∙ x), c • x + y = 0 → c = 0 := by
    intro c y hy hc
    have hxy : B x y = 0 := (mem_orthogonal_span_singleton_iff B).1 hy
    have := congrArg (B x) hc
    rw [map_add, map_smul, hxy, add_zero, map_zero, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_right hx
  have hsp : ∀ z : V, ∃ c : K, z + c • x ∈ B.orthogonal (K ∙ x) := fun z =>
    ⟨-(B x z / B x x), by
      rw [mem_orthogonal_span_singleton_iff, map_add, map_smul, smul_eq_mul, neg_mul,
        div_mul_cancel₀ _ hx, add_neg_cancel]⟩
  refine ⟨Basis.mkFinCons x v hli hsp, ?_⟩
  rw [iIsOrtho_def, Basis.coe_mkFinCons]
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij <;>
    simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
  · exact (hij rfl).elim
  · exact (mem_orthogonal_span_singleton_iff B).1 (v j).2
  · exact hB.eq_zero ((mem_orthogonal_span_singleton_iff B).1 (v i).2)
  · simpa using iIsOrtho_def.1 hv i j fun h => hij (congrArg Fin.succ h)

variable [FiniteDimensional K V]

/-- **A symmetric bilinear form that is zero or not alternating has an orthogonal basis**, in
every characteristic. Away from characteristic two the hypothesis is automatic for symmetric
forms (`TauCeti.BilinForm.eq_zero_of_isSymm_of_isAlt`), which recovers
`LinearMap.BilinForm.exists_orthogonal_basis`; in characteristic two it excludes exactly the
nonzero alternating forms. -/
theorem IsSymm.exists_orthogonal_basis_of_isAlt_imp_eq_zero (hB : B.IsSymm)
    (h : B.IsAlt → B = 0) : ∃ v : Basis (Fin (finrank K V)) K V, B.iIsOrtho v := by
  suffices ∀ d, finrank K V = d → ∃ v : Basis (Fin d) K V, B.iIsOrtho v from this _ rfl
  intro d hd
  induction d generalizing V with
  | zero => exact ⟨basisOfFinrankZero hd, fun i _ _ => i.elim0⟩
  | succ d ih =>
    obtain rfl | hB₀ := eq_or_ne B 0
    · exact ⟨finBasisOfFinrankEq K V hd, fun _ _ _ => rfl⟩
    obtain ⟨x, hx, hW⟩ :=
      hB.exists_apply_self_ne_zero_and_restrict_orthogonal_isAlt_imp_eq_zero
        fun halt => hB₀ (h halt)
    have hd' : finrank K (B.orthogonal (K ∙ x)) = d := by
      rw [← Submodule.finrank_add_eq_of_isCompl (isCompl_span_singleton_orthogonal hx).symm,
        finrank_span_singleton (ne_zero_of_not_isOrtho_self x hx)] at hd
      omega
    obtain ⟨v, hv⟩ := ih (hB.restrict _) hW hd'
    exact hB.isRefl.exists_orthogonal_basis_of_orthogonal_span_singleton hx hv

/-- **A symmetric bilinear form has an orthogonal basis if and only if it is zero or not
alternating.** The forward direction is the observation that an orthogonal basis of an alternating
form pairs every two basis vectors to zero. -/
theorem IsSymm.exists_orthogonal_basis_iff (hB : B.IsSymm) :
    (∃ v : Basis (Fin (finrank K V)) K V, B.iIsOrtho v) ↔ (B.IsAlt → B = 0) := by
  refine ⟨fun ⟨v, hv⟩ halt => ext_basis v fun i j => ?_,
    hB.exists_orthogonal_basis_of_isAlt_imp_eq_zero⟩
  obtain rfl | hij := eq_or_ne i j
  · simp [halt.self_eq_zero]
  · simp [iIsOrtho_def.1 hv i j hij]

/-- **A nondegenerate symmetric form that is not alternating has an orthonormal basis**, over a
field in which every element is a square: rescaling an orthogonal basis by inverse square roots of
the self-pairings makes the matrix of the form the identity. The hypothesis on squares holds in
every finite field of characteristic two (`isSquare_of_charTwo'`). -/
theorem IsSymm.exists_basis_toMatrix_eq_one (hsq : ∀ a : K, IsSquare a) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) (h : B.IsAlt → B = 0) :
    ∃ v : Basis (Fin (finrank K V)) K V, BilinForm.toMatrix v B = 1 := by
  obtain ⟨v, hv⟩ := hB.exists_orthogonal_basis_of_isAlt_imp_eq_zero h
  have hvv : ∀ i, B (v i) (v i) ≠ 0 := hv.not_isOrtho_basis_self_of_nondegenerate hnd
  choose s hs using fun i => hsq (B (v i) (v i))
  have hs0 : ∀ i, s i ≠ 0 := fun i h0 => hvv i (by rw [hs i, h0, mul_zero])
  refine ⟨v.isUnitSMul (w := fun i => (s i)⁻¹) fun i => (inv_ne_zero (hs0 i)).isUnit, ?_⟩
  ext i j
  rw [toMatrix_apply, Basis.isUnitSMul_apply, Basis.isUnitSMul_apply, smul_left, smul_right,
    Matrix.one_apply]
  split_ifs with hij
  · subst hij
    rw [hs i, inv_mul_cancel_left₀ (hs0 i), inv_mul_cancel₀ (hs0 i)]
  · rw [iIsOrtho_def.1 hv i j hij, mul_zero, mul_zero]

/-- Over a field in which every element is a square, a nondegenerate symmetric form that is not
alternating is equivalent to the standard form `∑ i, x i * y i` on `Fin n → K`, for `n` the
dimension. -/
theorem IsSymm.equivalent_toBilin'_one (hsq : ∀ a : K, IsSquare a) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) (h : B.IsAlt → B = 0) :
    B.Equivalent (Matrix.toBilin' (1 : Matrix (Fin (finrank K V)) (Fin (finrank K V)) K)) := by
  obtain ⟨v, hv⟩ := hB.exists_basis_toMatrix_eq_one hsq hnd h
  exact ⟨TauCeti.BilinForm.isometryEquivOfToMatrixEq v (Pi.basisFun K _)
    (by rw [hv, toMatrix_basisFun, toMatrix'_toBilin'])⟩

/-- Over a field in which every element is a square, two nondegenerate symmetric forms that are
not alternating, on spaces of the same dimension, are equivalent. -/
theorem IsSymm.equivalent_of_finrank_eq {V' : Type*} [AddCommGroup V'] [Module K V']
    [FiniteDimensional K V'] {B' : BilinForm K V'} (hsq : ∀ a : K, IsSquare a) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) (h : B.IsAlt → B = 0) (hB' : B'.IsSymm) (hnd' : B'.Nondegenerate)
    (h' : B'.IsAlt → B' = 0) (hdim : finrank K V = finrank K V') : B.Equivalent B' := by
  have e := hB.equivalent_toBilin'_one hsq hnd h
  rw [hdim] at e
  exact e.trans (hB'.equivalent_toBilin'_one hsq hnd' h').symm

/-- **The normal-form dichotomy for a nondegenerate form that is alternating or symmetric**, over
a field in which every element is a square: an alternating form has a symplectic basis, and a
symmetric form that is not alternating has an orthonormal basis. In characteristic two every
alternating form is symmetric, so the hypothesis is just symmetry there. -/
theorem Nondegenerate.exists_basis_toMatrix_eq_J_or_toMatrix_eq_one (hsq : ∀ a : K, IsSquare a)
    (hnd : B.Nondegenerate) (h : B.IsAlt ∨ B.IsSymm) :
    (B.IsAlt ∧
        ∃ (m : ℕ) (v : Basis (Fin m ⊕ Fin m) K V), BilinForm.toMatrix v B = Matrix.J (Fin m) K) ∨
      (¬B.IsAlt ∧ ∃ v : Basis (Fin (finrank K V)) K V, BilinForm.toMatrix v B = 1) := by
  by_cases halt : B.IsAlt
  · exact Or.inl ⟨halt, halt.exists_basis_toMatrix_eq_J hnd⟩
  · exact Or.inr ⟨halt, (h.resolve_left halt).exists_basis_toMatrix_eq_one hsq hnd
      fun h' => (halt h').elim⟩

end Field

end LinearMap.BilinForm

namespace Matrix

/-- The standard form `∑ i, x i * y i` on `n → R` is alternating only when `n` is empty: it takes
the value `1` on every standard basis vector. -/
@[simp]
theorem isAlt_toBilin'_one_iff {n R : Type*} [Fintype n] [DecidableEq n] [CommSemiring R]
    [Nontrivial R] : (toBilin' (1 : Matrix n n R)).IsAlt ↔ IsEmpty n := by
  refine ⟨fun h => ⟨fun i => ?_⟩, fun hn x => ?_⟩
  · have := h (Pi.single i 1)
    rw [toBilin'_single, one_apply_eq] at this
    exact one_ne_zero this
  · simp [Subsingleton.elim x 0]

end Matrix
