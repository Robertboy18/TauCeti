/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.CharacterKernel

/-!
# The kernel of a character of a free pro-`p` group trivial on all generators but one

Let `F = freeProP p (Fin n)` with its `ℕ`-indexed generators `x_i = freeProPGen p n i`, which are
`1` out of range, and let `χ : F → A` be a homomorphism with closed kernel (for instance a
continuous homomorphism to a `T1` group, by `ContinuousMonoidHom.isClosed_ker`) with `χ (x_i) = 1`
for every `i ≠ j` and `χ (x_j)` of infinite order. Then `ker χ` is the closed normal closure of
the `x_i` with `i ≠ j`
(`TauCeti.freeProP.ker_eq_topologicalClosure_normalClosure_image_freeProPGen`), and the
abelianized kernel `(ker χ)^{ab}`, a module over `ℤ_p[[F ⧸ ker χ]]` through conjugation, is
spanned by the classes of those generators
(`TauCeti.freeProP.span_completedGroupAlgebraModule_topologicalAbelianization_ker_eq_top`). If a
second generator `x_k` is not killed but `χ (x_k)` is the `p`-adic power `χ (x_j ^ l)`, then `x_k`
is traded for `x_k * (x_j ^ l)⁻¹` and the same holds
(`TauCeti.freeProP.ker_eq_topologicalClosure_normalClosure_insert_image_freeProPGen`).

These are the specializations to a free pro-`p` group of finite rank of the kernel theorem
`TauCeti.IsProP.ker_eq_topologicalClosure_normalClosure_of_not_isOfFinOrder`: the generators
generate topologically, and the hypotheses on `χ` are read on the generator tuple; the span
statements are the kernel statements read through
`TauCeti.IsProP.span_completedGroupAlgebraModule_topologicalAbelianization_eq_top`. They describe
the module `E = X ⧸ (X, X)`, `X = ker χ`, of Labute's classification of Demushkin groups, for the
orientation `χ` of a group in normal form, which is trivial on all but one or two generators
(Labute, §4, p. 121): `E` is generated over `Λ = ℤ_p[[F ⧸ X]]` by the classes of the generators
lying in `X`.

## Main results

* `TauCeti.freeProP.ker_eq_topologicalClosure_normalClosure_image_freeProPGen`: **the kernel of a
  character trivial on every generator but `x_j`**, with `χ (x_j)` of infinite order, is the closed
  normal closure of the other generators.
* `TauCeti.freeProP.ker_eq_topologicalClosure_normalClosure_insert_image_freeProPGen`: the same
  with a second marked generator `x_k` with `χ (x_k) = χ (x_j ^ l)`, traded for `x_k * (x_j ^ l)⁻¹`.
* `TauCeti.freeProP.span_completedGroupAlgebraModule_topologicalAbelianization_ker_eq_top`: the
  abelianized kernel is spanned over `ℤ_p[[F ⧸ ker χ]]` by the classes of the generators other
  than `x_j`;
  `TauCeti.freeProP.span_completedGroupAlgebraModule_topologicalAbelianization_ker_eq_top_insert`:
  with a second marked generator, by the classes of the other generators and of `x_k * (x_j ^ l)⁻¹`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §4,
  p. 121.
-/

public section

namespace TauCeti.freeProP

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {A : Type*} [Group A] (χ : freeProP p (Fin n) →* A)
  (hker : IsClosed (χ.ker : Set (freeProP p (Fin n))))
include hker

/-- **The kernel of a character trivial on every generator but one.** If `χ` has closed kernel,
`χ (x_i) = 1` for `i ≠ j` and `χ (x_j)` has infinite order, then `ker χ` is the closed normal
closure of the generators `x_i`, `i ≠ j`. -/
theorem ker_eq_topologicalClosure_normalClosure_image_freeProPGen {j : ℕ}
    (hχ : ∀ i, i ≠ j → χ (freeProPGen p n i) = 1) (hj : ¬ IsOfFinOrder (χ (freeProPGen p n j))) :
    χ.ker = (Subgroup.normalClosure (freeProPGen p n '' {i | i ≠ j})).topologicalClosure :=
  (isProP_freeProP p (Fin n)).ker_eq_topologicalClosure_normalClosure_of_not_isOfFinOrder χ hker
    (topologicalClosure_closure_eq_top_of_range_freeProPGen_subset p (by
      rintro _ ⟨i, rfl⟩
      by_cases h : i = j
      · exact Or.inl (by rw [h])
      · exact Or.inr ⟨i, h, rfl⟩))
    (fun _ ⟨i, hi, hs⟩ ↦ hs ▸ hχ i hi) hj

/-- **The kernel of a character with two marked generators.** If `χ` has closed kernel,
`χ (x_i) = 1` for `i ≠ j, k`, `χ (x_j)` has infinite order and `χ (x_k) = χ (x_j ^ l)` for a
`p`-adic exponent `l`, then `ker χ` is the closed normal closure of the generators `x_i`,
`i ≠ j, k`, together with `x_k * (x_j ^ l)⁻¹`. -/
theorem ker_eq_topologicalClosure_normalClosure_insert_image_freeProPGen {j k : ℕ}
    (hχ : ∀ i, i ≠ j → i ≠ k → χ (freeProPGen p n i) = 1)
    (hj : ¬ IsOfFinOrder (χ (freeProPGen p n j))) {l : ℤ_[p]}
    (hk : χ (freeProPGen p n k) =
      χ ((isProP_freeProP p (Fin n)).padicPow (freeProPGen p n j) l)) :
    χ.ker = (Subgroup.normalClosure (insert
      (freeProPGen p n k * ((isProP_freeProP p (Fin n)).padicPow (freeProPGen p n j) l)⁻¹)
      (freeProPGen p n '' {i | i ≠ j ∧ i ≠ k}))).topologicalClosure :=
  (isProP_freeProP p (Fin n)).ker_eq_topologicalClosure_normalClosure_insert_mul_padicPow_inv χ hker
    (topologicalClosure_closure_eq_top_of_range_freeProPGen_subset p (by
      rintro _ ⟨i, rfl⟩
      by_cases hij : i = j
      · exact Or.inl (by rw [hij])
      by_cases hik : i = k
      · exact Or.inr (Or.inl (by rw [hik]))
      exact Or.inr (Or.inr ⟨i, ⟨hij, hik⟩, rfl⟩)))
    (fun s hs ↦ by obtain ⟨i, hi, rfl⟩ := hs; exact hχ i hi.1 hi.2) hj hk

/-- **The abelianized kernel of a character trivial on every generator but one is spanned by the
classes of those generators.** If `χ` has closed kernel, `χ (x_i) = 1` for `i ≠ j` and `χ (x_j)`
has infinite order, then `(ker χ)^{ab}` is spanned over `ℤ_p[[F ⧸ ker χ]]`, for the module structure
`TauCeti.IsProP.completedGroupAlgebraModule` through conjugation, by the classes of the `x_i`,
`i ≠ j`. For the orientation of a Demushkin normal form this is the generation of Labute's module
`E` by the classes of the basis elements lying in `X = ker χ` (Labute, §4, p. 121). -/
theorem span_completedGroupAlgebraModule_topologicalAbelianization_ker_eq_top {j : ℕ}
    (hχ : ∀ i, i ≠ j → χ (freeProPGen p n i) = 1) (hj : ¬ IsOfFinOrder (χ (freeProPGen p n j))) :
    haveI := hker
    letI := ((isProP_freeProP p (Fin n)).topologicalAbelianization
      χ.ker).completedGroupAlgebraModule (freeProP p (Fin n) ⧸ χ.ker)
    Submodule.span (completedGroupAlgebra ℤ_[p] (freeProP p (Fin n) ⧸ χ.ker))
      (Additive.ofMul ''
        ((QuotientGroup.mk : χ.ker → TopologicalAbelianization χ.ker) ''
          (Subtype.val ⁻¹' (freeProPGen p n '' {i | i ≠ j})))) = ⊤ :=
  (isProP_freeProP p (Fin n)).span_completedGroupAlgebraModule_topologicalAbelianization_eq_top _
    ((finite_range_freeProPGen p n).subset (Set.image_subset_range _ _))
    (ker_eq_topologicalClosure_normalClosure_image_freeProPGen χ hker hχ hj).symm

/-- **The abelianized kernel of a character with two marked generators is spanned by the classes
of the other generators and of `x_k * (x_j ^ l)⁻¹`.** If `χ` has closed kernel, `χ (x_i) = 1` for
`i ≠ j, k`, `χ (x_j)` has infinite order and `χ (x_k) = χ (x_j ^ l)`, then `(ker χ)^{ab}` is
spanned over `ℤ_p[[F ⧸ ker χ]]`, for the module structure
`TauCeti.IsProP.completedGroupAlgebraModule` through conjugation, by the classes of the `x_i`,
`i ≠ j, k`, and of `x_k * (x_j ^ l)⁻¹`. -/
theorem span_completedGroupAlgebraModule_topologicalAbelianization_ker_eq_top_insert {j k : ℕ}
    (hχ : ∀ i, i ≠ j → i ≠ k → χ (freeProPGen p n i) = 1)
    (hj : ¬ IsOfFinOrder (χ (freeProPGen p n j))) {l : ℤ_[p]}
    (hk : χ (freeProPGen p n k) =
      χ ((isProP_freeProP p (Fin n)).padicPow (freeProPGen p n j) l)) :
    haveI := hker
    letI := ((isProP_freeProP p (Fin n)).topologicalAbelianization
      χ.ker).completedGroupAlgebraModule (freeProP p (Fin n) ⧸ χ.ker)
    Submodule.span (completedGroupAlgebra ℤ_[p] (freeProP p (Fin n) ⧸ χ.ker))
      (Additive.ofMul ''
        ((QuotientGroup.mk : χ.ker → TopologicalAbelianization χ.ker) ''
          (Subtype.val ⁻¹' insert
            (freeProPGen p n k * ((isProP_freeProP p (Fin n)).padicPow (freeProPGen p n j) l)⁻¹)
            (freeProPGen p n '' {i | i ≠ j ∧ i ≠ k})))) = ⊤ :=
  (isProP_freeProP p (Fin n)).span_completedGroupAlgebraModule_topologicalAbelianization_eq_top _
    (((finite_range_freeProPGen p n).subset (Set.image_subset_range _ _)).insert _)
    (ker_eq_topologicalClosure_normalClosure_insert_image_freeProPGen χ hker hχ hj hk).symm

end TauCeti.freeProP
